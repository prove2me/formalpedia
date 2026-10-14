-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0980
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:37:53.271122+00:00
-- url     : https://prove2.me/submissions/07d56e96-5e47-4f3b-8703-f70c8c9a6b95

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 176079136 ≤ n < 176258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 176080386 1250 176079136 176079143
    0x90a06020f160b041e090513050c030304051008250507062301060f02160914070c0b010504020904020c150114091b0304050a0c03050709050703051b13030510020304 72
    0x2080303009000803104003949010f0343c00c0540510326182c01d04414650b0100c0c2040c01600f00b900c6920001000e00c03144c401d0034014a42044440d1a80f0b046050983c5880740345900148690000c102c100440d543d131040a4020507400e0405440c5a940c1c0600d41c14592082030405034200c5801e68500d11141e030150091070b01c60320900042100103100f07000c8200c071641040300f0035030010300c0c880144031031030142500034201c3e080c0b03104880325810034100100010038194004540551520a0030f0b680c18640300145510400724070b06080756083c0e0741c4885001c52011b100b01e0340100c3d400940b96016031600c3c0c040340d910040c88011140e18011503c0c11140201d400d202d40c507210401285840341c1840d200e501c1e140201d0300030316120080120300c1e00340c0100c2e0384040d03c100c4035481340b5008400011901021000114000c1e40078205c6189025040010b561000344418101480c240802c0f0001c00c200300d180d04510902030560342c6820300e40c80c1c940310700d100d1a0009001032184055500c80c1c5410342c0c0007503210f00d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 176081636 1250 176080386 176080393
    0x71d040b0c031608060d06020c01020c120c06160e0d1506440d030f0c0c200111010e010902040b0307030209010b09060d0603080a18050d080d02090a06020f 68
    0x444207001006800305840d459280030056640f203048034460440d42ea003240008005d05400e00c042d42d59101203074040c100d00321461350007040e40c40d820f1800780700d564450200c4000940c5032409484a4a803200402000c0d11040d8030080c4580401d54441c000d41c810540020f841108a8421420706095400c0c04a403500c0d0300a041035004a0a1030820024a140400c00c1400028143c0d110b04095a5003141020f00c01c1206003801040d008a0f5042081d2010556183c900041011b00380d8040e0080e5468a091101400ba208498400040115480d10541c4100b90a081010010440100c030a031710180b05021540d8240400501d00c8041940705260891080303800300421131200d4140750b201c80c81840042d43c0000c201380100541402e8030024041108014569840c00d0400d49182c800c0307030741d141c00035110180c02180e0345030916008031b00300001240f101c40f904542441d20002803100c00c1d68050007003801c41c0220b000c80004415405031504034600a00204050380c50340740081d0303104180c16040103d4030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 176082886 1250 176081636 176081641
    0x7050105160e01021e01270c060c02090402040c0338100203030105060313170301031a31052e0204080c040b01180f081006051c0203071d040b 62
    0x103010302c10992000e4810380103002c20fa0000710b505411925a8100e0752929500c0d004207500e810888107152281e10300641d03003880782d03484d40e00f01408488601e40014040c05512080000982d484040707059005a0403680032031440b03c642405c03030103410008032035100c46141142044415118034000000b110b0050380a0782508003042c100410311200311036070005600100010f21641c02d0803002190301811501039982c1c040030569641506602c81300080d101d100c2d005c0014000c01541d1100d04003016101044000c0a08248ac244000180543c10745095406d80107074051140212000d003d06658101066528610143c0c15440d5a818500d05088203411000c1c05414081d400f8804c0d103042e925a04000c010740824101400300070079022105506008120707044030079550841c662400074140301503031619014500420b183c9080002a06400703880d040100510050b01c4c0c881d40c083e00400344001c03054501c19203002290500e40720b50006440c00290b25580315420310f20800c502e004a11490f1480c0701a03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 176084136 1250 176082886 176082931
    0x2121b09100302010309030c120504090b18220f050714010503010e060f0a030813050406080d02030d110708030a05040b0a14060907020c040e07030501060f0f031401060b07050105 78
    0x4140803120440708011140007030015501c00d90000e40050300c6401e1441e11141540c880785c80d500c1c120f20490001480c000b40c1404441128010320708982c81c00d4810b5900e031202400000f0304404000c0054001c0c04070341020811130482c55403100381c51504581e03034a04684040c1421600c605407070003149ca5100d04412541015445481120704a0300c00a04408881d04e90070b08000b00c016107842c4040c2d04c07400018011000c030301d030007000346642c0d2006026070403590301c3e001c14041950215030041c1c030315800038035081c00e2943c0c010007112008880034030001241e21000420040754000c5003405000e000c404010886041003d9103c903020b00c0c064007404e0300c04d58400d500b8806862210284000c0602e00c1d43c00308180d03042c4215a642c1140145c015102c1b6020014042011034801c030030100c2d80c41d8030291040042c41070a1151310003a0069502c801c80307103818414590520521880b0091244004456480c850070003988074102410036001e0140e99a412424103a0203400155401d404118150540e041c41 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 176085386 1250 176084136 176084149
    0x608060c0405060a120f140601110115050105030c0f04060f030f0203060604061107270609020a0503011707030605010b090f0904021309020103060e040602031b03010303020a060905030702121b 84
    0x11101d000300018030301004c81c2c1c01145c810a40300381d000c04481d111511094941400d001c2c0004040c8000c1c0b00c14010310b01000010220100c044018095904d000d45020045007088203540c00e885080c03c5c8156240c9904624500d030384615200c00306005d8000c600401c81540c014005075006140e95410302188000320303668000c80c88203031160755124000b004100080781c09640d60030b01401d4100306991700c8a40c1e42c0010100f20500705241502d82d1600d0a80c001c03c01254460f00780506144a0210700b00003082d1406070040c8410301400042086c01020b110003c8410810304010319444602070225580d6080e0040c3e040d0840c060b03451094104281d035060506044110314030658008203580c0703003034100c088124010a804442a8100b507119030001c06c4c10b001201c01d480c0a644a2000141c1d43d1800c42c1e129044c0d03003051054008410130030001000030030380c0054502c040c181c00c08800150200c41d032801a00d544510000250000d61015004049c00001314410254044031401203002840000030002c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 176086636 1250 176085386 176085389
    0xf03160e03070302100e1008061e0d02061e0a031a04090317060d2301060501020f060f0c2209050901061802070309081605010915020322090f0608060c04 67
    0x200342c1e10180040015140c0103070451040003260034040110141500461302160214601d040426948810700c00c403400c24140000c4078440303440c46a100250300c500090f107402c840702c0c0080e01c60f0a022900603140c0c2310b1040c01d101d2859016038481c1d580c0700d1584001d8081d00c4140500d0b101c1920354244c00c000790a10740180401a40e042e42c80c0c00c0c1c01000344000030101c58001e0510f81d000580d44004200240240901d0100c0501c1301d28000b1109000c4180f146c00e4030140d80121341150070640c0200d00044e80052200d0300160301502c41111540c505681e00028042d052150a10150488001405d601101c22901c04e480c0048018401d40c1d440f07418190a0702c800c0d10800d940d10090044403190141c1580c040c0a40d03e110345000340100340e039208280d14105a54403882c0901c00c0b5120204600c0d03801c030510000034906405c0303028034400748400194903802810407040c1240b500301400c03c40b01d03c40c54200c9000d0304440001300a40c1c1c0c6c0700d40003040104139a016650040c481c901c041101c8140348802c0e00d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 176087886 1250 176086636 176086639
    0x905060c0c0907020102091012050c121306291201110d02071104060303080f06090408070b0405011d100b0d1212090c03200405040809240f03160e 64
    0x10310700200100307100354568010984030440d50b00740708510b180d41d04c00318115000c01460303840e1600c02142011200449501421041d0188810480034031103408031180e0507030000e008000c0051003080d50a10750f01800f0b15201c10071850000030014150550480c010308103080e030035240042500110a030031404ca80c0030b0200192101c0781404a80c9615406400500019100d286140d950101c90404203003a50900c1c2c0045020400810402c807008103a101040d80c0b158040300c0c0c0d42584c1c2815128280f60341f04400c000750600c2403940001d820701900350480ea07070f1034060300c44034405410903255242d2600100b0300f68450300b41c1006000e129624001008503081d030740260100c036031007442030070660740300c41c003030b11041d111a03103c4200c403002ca84245107840003180a402501e01940603801c01d40f810b84610144180705e2031a241c03d105c04500d940d41903651f0070f070094610031203450700d41e01c0310f031404092b0030441d0503880000a140070f80500400c01660040c610104a0010711254a0058640d5074503050043e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 176089136 1250 176087886 176087893
    0x41e0f0e0c060d020409020a02030715051909060b0d05030d06060905100309051f0902040506011b1707200306090613110402071e050d0e030319021203070201060302010905060c 77
    0x34a030782c0361072401414070b02002c0308010328040e07031045404c003aa0410807404025800101d6481c0c24801c03000c7c0000040569031108110f41d1400c4040c22101c500c00d0408040c0035540c43c0090400c2240301d83c40008103010080041d5202e40e03c03072400e1a525440219a40803c5041c002c0c00226039001e158000141c420003441e40a02003043c60084008000ca2113003601c2a10407000c20440d041e15103281680400300e0200003252410840c014002941d40160060b4104418102080d418070210151050156484118241c40841d04940c24189000b580c9003d44454003840301f10000342401701504070741d65020760980346a81d403100091903d5010459500b100d6035001044640010b4401c45044442c19008100500300320864884c40e101400041c02004000f17a818600d41c14020100b201c10803440700391410300d4011000c103001c26228068030b0203407082c168281c12900307c645d0090000408104120b0741c4c16880b464410402070103424903201c00d81c08100c1511000c2006d003416400c50360204c00c01d1005 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 176090386 1250 176089136 176089153
    0xc0111010c090e09010b100503060a1d0601030e07080102040e091b061c090f0302030307030509010515090a0204120c0914040c12050c06030c0406080c12061509041e0f0e 74
    0x690f244004020041111035580300c580c02c2103a03a0b80350303000c0b030700d1401640c0319a100d00e0203c0601083c224240c1150079032610601146030b0500c0361424080d4040350030700c1d02066110100740f80b0392802d1060f412500c080d50000c00d0101e0400c50310607119100b44040e0040710064504407041400e002d40f0040c20a80103401007205e00c2080d9080841e1340c0740d500c04003100081c0e01440340c65554413202c02950441c0180c0002007844049941800f44540010800000700030500301300c0b8a101c5507040340042c190240c0e60b03a030700082210103a0f5060b0350003000000c0c2c2d05001c4554038544010110320f00c0c095070240c1884c0442070702005209901d018410f40d4440c8100c0012421300c03c4040d0003094148048506200e0102c1801041d01d8620145024041d20802c080e03c03076080100c0500401d0300180070400310b81040c8403001031200e0302501d154020310b05564120159038414540040c0c0c0c480d80d0800c5070017905002a00003d940718040191510200c80400c12903800700d0403640041d10344c024540851039104049 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 176091636 1250 176090386 176090399
    0xe120c090408091c02030c01080121170316080906131e0f06020301090e0a08120619030b0103120c0506060906040902040f0c0801060f080c0a0504080a050c0111010c09 73
    0x14140d0014002d004050400d0b000e000090852000c8801900e4528207659404086041c05c106460501c4824200019258144001e4507400460380400f1103409082503e100d092005164480301245182e032040399803460a00c00d2880b0011021540302c1c00900d41b64001076402201180d41343c0500d2030701500c1c402160460f00c50010001c00c8604070406159404d50510001c0c208040f0700c1c4e60b2901c10403001d6182d41c07520ba079003406c407649848032600b180c00071140d050000d49688101c4502400f403240d44c07401a03c40001090070090710401c07284000c402404084140024500340700c4c105ca12a445440402c044a24215020820050f008081ea070081d00498158500820010381c040009040014103000c0394000800359450000c00c034a115035540946030f4240d0303128040c03602611045c2000250f07824821070082149000402090420601044201c12248039104989c000d080301e8007110041110303070516544a109041415010a01d2080005883c4806000d56400300da801e031600c4280c14903050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 176092886 1250 176091636 176091649
    0x6080c0a05040504050a0609061403120a0c05100e070b07020f090a0b13020711010e06030a050606040905151905010903030305041b030b0114040207020906100c05070b09010e120c 78
    0x1810340c02403003070030b01c000705094445108083c42160800b0001c11a6407a0455600403940c6070307000031040c480c40d10302c0e21000b6100001c0f41c40c0a442c500240365558400c0c0032048a10350004000140a4012081802289061038001d4524034032003100303441d06150744003501e104601c120384000350089090340960000f440d00c4840b59502402c6d03200702084101104000440404140310030381041607020a00400344444075031066041c28007802c014000003140400900c0c1404003d0804e8000c41d101e03000145180c1381c44042c1d070020702c44500d0a204c03a00f0701c826504000429400014043c102420096181400d1040103408071001a107a520302d460440d10b089016140c020815034440c109061080000c80c0d8078880b01c0f00030b43c0105003440d0154181910360700740701d20003400d40b0301c20390040c0050005a500d0440300f9070809800c544289000c0e9019009072031040307082c1c0c030150480c002c404002480380201c80c02003120b45026a244056851800104038403040e0400146042d5404641da034003c0c0d0a040e0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 176094136 1250 176092886 176092897
    0x17030a18180e010e0d05130503060408030408030a0209040906060801050708070f031a0604060e1305010518041b091a03030301030b0610090b0c100e010209010e060d0608070e061002030406080c 84
    0x44004a03812680d000305500d0410b1525041740001c0d400514010144024440c81029040031030140000c1e09150b120b02640c0d004c042d0010f8183c40c8000b000c0f800000c141da0403109601c90142050000296500b8803100800c5039104000303c80d403c0c0400100414411082644106038945a02e030b106141160100e0041001d40b000e81c40210340816618200e945000150000b04401d40d10782c041c01003104103001c030000009140000103070a10300180919a80c240690033b40108203da00112a51542810a029449842c1c1c05103114402600800c0650721364000c041940304012a94103003030381000c14117503648024072024002c0e202c1d80003c0382c158a800145802c0702c00e69071a0000d100c07500c40c110b000781c40d070000a1902c1d4582c070801c5941d011940c81d010700b55801e8010002142481c2081002902000d0245141e501c10b0100081021b058400b0b0b5105c00054503501003151800c80e00c42c03203a4032200704250342051140040300c9680c9800d61000007142c054a4107952030000a48403008042c07110b4010303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 176095386 1250 176094136 176094161
    0x91c17070e0a060c0b04060c020718020c0f0307081804020421050d05161e120e01020c0409021c0c0b0a0206040b10080a030c050307150219050a09050f030717030a1818 73
    0x100000001c6030f1803642c04902f020744404a005a5075500c0c0f0318075a1410b8900c00f00c1060f1a082800701c1004a521030b01620b0400c0303000144a03540e02c6030340c80094028802c80c0c110340c1000c0b200342200c1448500d04460a030301c69128600303c4622442c0c0d10802d81b00790040e909001c00c101d03d244a24000500800d1100d00100b04040f1460215481c642e6001150b11251248200150309507840003080d6034108aa218910000c0d58200b0440d036080c0c0114524000c0d001003c2d10f02c0e00c078a40c0c50300400900c01030280c014031034000429114022800000e48522050b1800c0d10a11040300108200400518108085602d60001002d00e84e5150b038080e80e00c1040b60b00c01740d4041c0004d225050100f202d104001c500d031508030300700694070b5131104104048454291031400c100b04090209000454110044009941040383c0340c542100411001030714004080c3c1100d000000514112881d000c0000080c103101401a102c81122070400841d40203024003502c41c9509100750102c1c041c2c01c0d0500355004500740b020 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 176096636 1250 176095386 176095393
    0x20c01020c060906071103010509030c0c0a0e0403030b030a050102161a0c0301120501110d060e0a0903050a141902010b0108130503090111011404030e01020114091c17070e0a060c0b04060c02 83
    0x1001b90019084803c04c0b500081035800c001400f01c1d0581007031080300c0ba00e000c03c5400f9989642841180c5000030030091000303041c16542c40c410640c0e541c04211a00741140d00030004e6503240d081d085000350503c00654111340d183c2240c144014041c0007078a045216040000010381541c0c64504400c20419041009403210355858003421459240800205403030100c0000200c1e01d01d06d0180440b4400d039009200078500780ca81048040042d0344007040301c003100201d18100305602a080070351041d074440d8081e940640001c000c1e018984a4042d00000d2940009895902da16910050642440f66a0040040c2207400c20082600f056000381c40000c1c1c4000e100000084952401d070309000080030548040e0041107111818886640e82401441e010b024039145d81c40850400841240c0d88801d5030ba80e13944e5060040c0550b01d411841001414141030b030340401c452842c108801c020313001c2001c01645034010540e121011544500031b0b10358043c01a803129135094581ea840d1924002030000f0400c0008500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 176097886 1250 176096636 176096663
    0x40f0602031009150e0702010b0a15170f070219050a030302070f0506090a02130e06163c030c0206041b09020a0e0301152d0e011203020c01020c06090607 67
    0xe410707104d41c0c4c1401100701030343d4482c0741c113009840005000040046c01168104030b10043c2d40d49035000c0c0f00048860000d03840000707200c4a44195000f041240b9009a00342054042004a40c402c01e401070040c4003a80030366600300d51041200d0300b81103660a000d0b00c243e110310010000030f0b2084c0d0042103214002c0c6000740514000d039079041e05048042d40c0100d0a81d006400d01401d502d03008019647c00403030f041080200c4804055502d88a260081c00c041c03003150005d181540b45409051000c01c0b10301e080e200001c5250120070a0f40d6104080507040d40030032241c00426a00c0c40c060300ca910078200c859001001d41c3e03a9140e81e5a000610301401c0d00400d110402f030001400d281ca070010342803200b0503445400c4000119800d0600311a6004071216800202602c204030500100d440601500c1c0c4541e03c9024442c0e43c034032089030201441d070003081074440b480000201429444070050003a44260b00b83c0301241c080ba00126512000f6079446c1d5881a810045004a450204001d1501e80d200304203181542 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 176099136 1250 176097886 176097899
    0x11040204150305160305090c1212042c01140d030905030106060504170303012603070507060f110d05030705070c03061404120309031202030612070b0a0e010206040f06020310 76
    0x80400381c1c200080380d1503c05101d01c2070450800c4030b084983e1890704114914000d0259035540348002d0415000b55104201045a018184254046030b1111180c0d41d5649988211407581d622581d41000082d06d03d440343e241800e80800c400c5812907200420b075039440d207280c17400c101c806160b50408800b4000b10480c0018503031020302a0500407c400d449480d2a00d18200703004018030902e41035550941c004100601200c98100c3c02ca0050104110034182e0070b4920420300e52442c030030300320064030324440c440000541340d81c414500d108007841c1d0350f075800480c109070784402e40d501100301046022503c28000503008a201d070029180310343c05041c1880c1b66a5480d240c9000f01c4026011060380c8003003a1041105000c40100300400c07288207850200400243e58500800030180c0d01a103210560700000030071000e54900c10a84420180c14060302e11840da80e003080c01403036010442c640049080108014032640c00428a40d110710740000150408200c1d1380e4418000798001080348126011a200102e800c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 176100386 1250 176099136 176099159
    0xa020a08010905132001020c01050c060a0203181902010e0301020a08060f0301090611031803070c050616081209010e0f07090906020f0a050901090e22060f0903030b0f010f080411040204 81
    0x1240b0b00c60241721009203030310002400c01c00120481d9040c810300f000380400c00840080c00d50b60102d010100103860340c5546010311494281a84e4103103c038841c0c1c24441e220812004941186680b01340c803540313041095001403600340e0140001201c04900b04d00300050090030f040055403600f0400400004040102ea684c00c800c840000c039142d070020801108021005003149080039075442c20800450500710b0a5441d50012407860042d80d010311004100d000b10101229044030701198003488045e00e803080a80c03203071842e42e811a4a450b540d801c028030318001d0100421517100d141103200c06041514101903c3c1d00c00b03010311100417a54140d08008088103200480c01621458074981d584940e44c424160004004090b15000180300d00e080a0900c0390782078011418140c11540101030141900b01c80c14044001c1403281e9039510058105000d0804050781507100e6200141304980904c001c9980d4001101c00d03003c2d541c02100855444000301b4007048100700380c2685203c00402c05440d040e11215440c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 176101636 1250 176100386 176100413
    0x40201110a06060311010504030c092004080303040201030f18022704080301030c06020d0c02010e01120f09051005010302090601050c0a05030f04062019050109020a0e0f0a020a0801090513 82
    0x1419030f0358030030a1042014064980d058441d00346489800c140c11a1640c0d80c115900d445101440c1d9581c0e1692060340744050ba40c405503007080c0c0682629141d4503183c3d15107951003210101d0000c4d10780740419048140303901c1030100043c0c207505412002c481960910010300341030b00305101d0643c008280d00340b035007404071180c0c4d1007503119250440c3c8035491840c100114400031b800200564011035664510540d20a07000100f00741c091038420944450800140c40c0c10098802c0c18401c54202462840407880e1600800e901034460001c40340700385460510241141c00c207002c007e61100d1207101080107584600c0140203901c0705a011354201e6402c59035000d20711303800600b84c000b945001050401c621608240d107040f0704514801030740d4018081b55401c54840c0c0f40407516030b020031007c0c24401c042c400b003540200c590035805004a81e5a684825003540500022907508800050365030000da031240d010b00079a10300e40100c3c5c64440d80c0740d013842001c0000d0300000381010041c141c0000c0e00004a40320541169 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 176102886 1250 176101636 176101643
    0x901050f16030309050615010f0f051201061805091005010507020a2301030c0e010f080702100504150501120c05040c052205040605030c0108040602030604061208040513091109040201110a 82
    0x880c0382c100e10700f1505000f4000c00c10107c62986901c81a01030f6040035000070464018a802050f80705020f00960310350003211850114038a07200c0010031480c0d0481c007480400604541c01403c00c41c0d80300104007203070307004072028201d0290b2403004100c15406400075014192008094a400d0394860640041582401c11800d280c1c8030030348030b18110365801d4424902040c40703515144c50071285040c0040c0104d05001c001c4010401140c2c0091b041d40d20074823052000c54201d60040c03003203040505060f40140c0060b0070900b5564500000082c0305800c6c881e11020281d440b9001e00790b214079000402000b0821000d00200703018080010a01210a20300103041080712403806083d02810070b0180400c951300358000d5406a8815202038003582c0e0092034541d482644144096500d60b01d40000c200646000d501a05840711410b0600b42000901320150013613038401e80b03030b07207511000d2440100706031a003801000e00410040c3c642d83d01181062180e040c0e1260041c1000000b8410301044140b80c05407881058 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 176104136 1250 176102886 176102891
    0x6071103030a120f0e061501110a030203031602011b050f12040308040b280b0d021801090b03070605070809030a0b013005060601110c06030705040513060b0901050f160303 75
    0x4406081413482613510524490b60200000b0f514a441d00c2c1c0c0ea282c01428501d1024075888100c0010ba200e0f03040340458151700400e95040302918600a592508207a03000c2018225410610000350320504c10502c017410300c03090300000c050038002c05031402e50101c0c0050101c00300030800100ca8540f0b10030030794050f030300c2660b4014161900d0b0405403201240035094900798407250250030130881d00340704203030310125035404001940d83c3c40c1c000081100030030080081d0031986070401c0050070702c0c51300794040c1203500740c510500900c0e070110201921220b0902401012070000c0c03100a000c21032103406440d1000003e0115000c050840c0c071001680c4038241c6c0101a03414881c00304000381e00f103483d204070b841030030001e045501740c0d45542c032a511241300520320ba04108403010b104e104e0420420000b01d020b070010340115501e080516004040c3c0c0e225001c0c0d9030003200025107099100fa040d1041c7d40480341d2041d01d00e400c1040020044503240d0004128088a0106101c0d100000c00f0500040011310b21a4400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 176105386 1250 176104136 176104157
    0x7230f0115062007061103090a0e040b0f04050a330b01030e070b040302040c050d0e0307020f010e150c01060305071e061b0303020d021218161406071103030a 69
    0x3000c1c6602a4540600e03c05454003042c4400000035804082d01c0c1241002c05840748440045807460088020ba15840b840a40000a00f0042152400d005078000c0c00000c821f03550b21550000c030040c0a8131b009041d5401003102401103a045107000f9110080d0190a4002c7c00e0200040e200e003201c0e40780d11220160362440c19985a40e0144150141c0f05040000703001c2c814500611590140290301c00070340201d450324a40078055101c1c400304c400ea8003224200308080f84404d4451b41d80d85e004810308a016500c05054291658020258241e181c0c80040900008007450041c41813a0381060502c68219900c0c1c10b800b000081040c4940c501802c0c00c040e0001c08029040d840941032102d0354840028000c44500c2c4110342d403440d1072100b841340e8160401581e0703a200c0072100d000911031312558885055140d010b00445103c4944240800d1501c04211003c5a00a0840d00010340c0035128a424003007107554502100d00340100941a194000c14848901176041d90100781503600241110000441c42c0c6036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 176106636 1250 176105386 176105399
    0x7030b0c300714030a09050a05060a061404060b03190b060c010e010c030504080f0906120103120e0108100317041d011a04060c03051b01061d0a0207230f0115 69
    0x1260b2041e01c52908080d14000514001c0003848094a01198030392100f0342482485800c22420707040381c0d400012940c144c80d081052600070003140c0100310401d01d4034030f1303100070910b0140922826034503c6600c0303d15585489080480440d90402c5000007580c450441a019550344005022607116000012480300c01c440501421a83d1202c640421b1618110030f00010690f080141c0b01c809824400c00e680c0c030b8500000164041c014a4180320110f0b850000200c100242601c14079501201d98555900000100d030040d1007884c412078200c215021035400402c0071031140c0d5031801040d41551183d51920740c45580f44488044980446003250011000411061014920300040c4c150001c6586052504050001b04881c200c090b0207801c22001051540d00407164280380d8420115140003049240e907126400452407443c02d0500309000c0420f0005120a030703d500841310000c1e03019006001f812101c101528011403245050300031031040c1101c0840e10030342403140c00c192250610340b00304458501403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 176107886 1250 176106636 176106727
    0xc051309060308032413020a0807020604080d0207080f1b070e04080a0809100903020c130e06061507060204030507050f030d02070605090102010b09010f090b0d030207030b0c 76
    0x18403180005141240400c0491410b005076508078850f1580d9102c1c41d400c1200038940083d56014082e44908070601c20b4408030b04030b0f80241008521030321803140c51342d41c4010030303030310b03284212000742052104101d01c076902ea501c0d41c0203000003885481e001307080c84c99203031020140b41c1141c00300311541004001c1c0c14004000801804e00103004002c03080440d4a0256035460b00d600400c0b01e424140300f001000710740c01403414007107041c141b402e00c0e600300400e071861f0800039910300c140319a40707004510344200704078440a903004001d41510128024070164a541c814441e081e50220302d060040e070f00a120000000d1940c2c001000114001c2c030052041504060400c10302c1d0300c0b030010641c0b117035004014243c070454000c01c0030303800c5485904000d510350400e40010303800742a40c54101d9500c82209000814516520700d100d005a5055803410008218001d00b8840000452100900582e0040800f0400070311021030303250340020036000441c20840d810b061600204031840c41c1c82d400101600d0322400d101e0724030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 176109136 1250 176107886 176107889
    0x9060605030307030f08060d0206161203020c0309060708070b0906010305060703021819050409050f0709110d020a170103060e06060307050f011b05031c0f0504030f0c0609060c0513 79
    0x301c000d18070b001402e039409020405681d102c0400c0c01400300000300d0701d503034007420b002403e41c02414441e17031588820340305c448001e181c030012107140c030281d10944407192292083c0c5075544c3c0e5042c01945819031a80400c1001d40008408a91070b02c010441a0001100180614002c0b02181e009007031a50551421301e04145c0d0050103c0101481400441101845d102e06a58044801d541e1141c107400e01b0321030092a480079401554010782000c1c103080c20480000356542003150310809980c0001d46852480c0b0a42d404031031650240c2c039007800003000b980c0b5141e00500c207050722814000c1111411501400d038a450981c403c0e64140d9594409549003035052000652000003140505010f9041000141030b1010380700d1500d04200c1500003200b01c10f801100d0120071103801c0f1048a03100d00341410004a2810003004240e075650400e0103c40d1028a14081c0500496154a82c000601d032481e00071501d520508400b6550a6150420070010590a200e91007501c9856601c90307075200000f091201c50600c50313 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 176110386 1250 176109136 176109139
    0x312040603060602061918021e01080105060301050901030816050115050102010f0501081b0d0c080721030f051c150501171009020c1e030a110f0a02010e1302030a09060605 75
    0x60300030419001e220381400703a15007031700a50014060003510b221f0103c2c652035080082d006810120020443c0c50605600b00301508260f852002070703a200c3d010303c1000c0c0801e10500780c10420000051002446c44005890300b141c0665000840000d035889060a481c6d8030524664000f00f144421f210b00d590a01590186402c0c83d0750601c59545000d021a6039000181c0c040000035500320300300000f6a0780d101204994503081032050503c1c9840d00296925201540b0500c18001d20404540103020608400003020030342507141d1410802d01100107940d50340c459000d52202d14411140300703200700c2e010310607040340c3e441d0b81c030441000a003404000340000101c1100600c440307060808001c500e00c01c220480c0140d43c170304400561128012490b252402c1500c0e60f02041c1010150b210300703500c00000024100e07540c7c5130340e41d40000c0355804070102e0f02c4103101d60b0803000c550440038815000d54021007440c00f2042000d44808103415021469004903041521408041d6454030722007001d000c03107400740c6c5014080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 176111636 1250 176110386 176110393
    0x52505040e010b0c0a02010302210a06051c030c1b1502100506060c030906160804170114060315070225090b010503061c020a09020f030426040614090312040603060602 73
    0x103090402e603680e05e00c003450090404d134000480840d29001c0d06918040c05c0b00314501d0b2451820003031000030150045000d4203008000072007548050541a280313180d4810f406480e0000c04603056210790340701e080c0c501402c07100d40c0d40da1140060007403069071744181d9541c880e601501518001140040517640f015013200d1045030103000d2841d4464011044a13800b22007280e005581c1d00c013800041142d43c0d000407000d09500780c040350016504014012018030503105100812201e4030a205902d00c120069503516010b81c0708500240241841c001c0c1c81d40c002c40140120f0f60080600d480588a00c56013041c0e07049600408207080160003214000c04503016000d09010f41189803040c045651030013103c039100445582c09002e2001e548690990303201420f0782420a43da292022402084140c0c8240d6084400f0440c0c151080110b20540039440b910089000c4460700d420b1401c5e100b2070700540045144244800200070401159804100544003980311681140e26940340c0000582200c40c160700917000d641 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 176112886 1250 176111636 176111647
    0x3020c0708070f060503180f0a05061e0a09230c03060a1406100e0904120806030d02060114061204030f08010801060b04090f091a01170708030d052505040e010b 70
    0x50700301c3e10000581e4198039080e83c4954540d5070b0b094525200c5051f015042c0122280e0039816a004140310740c03024000d208039070854403240c02010480080c6840d92030f40c0c10a40303020440c84905074214100c541d0080440942107001c12540041195801918000d903a2000c051901346040600550341d022000c800100911130a40200b280c0402006203024441c214120780c6c40c048501450305201c4c0208050f02d01d00403861706143c00303071405d01429400c1d8041443c1c0700010380980b8000a01c5624022154050b1100342d10f000c600100c0b444810141c60740c050000d0212940c1c91001001f41c1d03100c1c034042c4e921000401054500030306402c81c1a0000401c1d80d04103141031000c60381d448101c8040740e0307498000052940309020440010b0009502c0145140301c0d000195074014228031942c1c0c1aa03080840e040700414940c084542c1c1d41d41507201e14005030300b09100c214122a9194091507011aa42a02251b0600140355400300e4a09030ba000c04041500031409001c2d1214000030380d800b4011762004149440d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 176114136 1250 176112886 176112899
    0x1804020f0f03031b060f0108010c0207030b070e0303280c0c0b0915030a0c031104062c0904050a0303050105040b13090809031204090e011107080d060b03040303020c070807 75
    0x2200c039520554080e064001d07070114580c50070021158054110f81380003029142c08042141c0394002940d083e0076400000001003400c41c018410321449800c960001d00c0c21519603542e061201c280181040c040c0700c01c50b0b41c0c1c8216900c09000134070f00c1e0000c01d81a0607803600340e006580b01144c04108040100310200c1103c00004031030646040a5440d0318a006441c0c1c5515000200200c0d4481c04070700346e100c40801480303011030702c0760000c01d102c0e0150b840900212005049525450242d40308400c00a044441c1c1c81c500e080ca905003024803540c0a0818806148006005c00c807844001e0720126060751002d0038210a040e414031966024000807079080c801d00d550100001c01140c01090502c200691f944030f08030400c40b94034200e8680040107000d4039012030500c0100c1d1070310741144c4640501030b81070481020b144d00040c410781d4465075a942080e804c180c1c5079254880b2582101105040c1c8030340d103000c041750040da50006140304038030980c2e025036100f890702c610a00f4070170543d114001c140d02284060052 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 176115386 1250 176114136 176114149
    0x18060415170708010503280c1d1627050303040605120109050403050714011506020f060f07091203110303010e150108071b060603081603110609100b0d02040f020405180402 75
    0x94452000f5020720482c98a110000c0503050503001800f001441d00c0c0040d86152028000744282c0d0103104401013691810480c2c01c501c01c1c030700e1484ac00100024080142034003161070301110482030300c50050a060300e0341c0c04030b171a59000742c0144011410225860300c114450001c1e250140c8280f00c2c0904c440c0c105613401410500500000030312a2400c5298103d181900f50702c00c1840228001d60750340c807a41d50b05006500c071b50348192081e02502900000441100711a062140a041306a41d480111403500412220085181c00101c003001041c1701c040106210400c0598080d007820900b06005080c000c40d201e100143c203080781818003240c4d40401211a8002d100320b00340068402d0800d0107030102d46020300003410290802000320001250722400c91042805549000d80b2030340714214440c0840000d0b6070342e8041100c071315016600080540160902d03e80008140030b2001d0300c000315001c110390018055984030300003c140b00d54085020031962034a00640c1030110211880307025141442d4010078036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 176116636 1250 176115386 176115403
    0x3070b04140d0204020c010c031d0a021e0105130e010626011806080111090301050708010b030604091e060c030b04020a0c0212031b0102030108160b18060415170708010503 75
    0x2c2142215000015074035280c04946210100710002c0288480c240c10203401481c8040005040420052500c0c008110000c0c03401300d0b40c3d40003401880e114805c18010300c20181c00350a4030703041140500075010001c0c058000d5001514000e00070100b15030420340001c0668801500503490140b809070b00100441d1581405410345a004100101e10220401990050b01c2540e01003c0d0541c80c0001060207241c41d070000d020760010490003071140c0d48034940212112a820b0003020201c02040000c40c3d107520f410f500c0f00007014420290343c8849880c440703008501040010382603400b41d0310350304661806689881602050101250210700b4811050402400e03031048010080c00350341d840a60710b117964410019203004008000b84080c151440c4000342d40030350003e11840302c25100d0b0040c0003241000044441c000d603100030404504108440d041950811801c00d84181c02a404000c0420a108138440249a02c4c00325125001c3d00d201c0c481c52202407072001030811003040036100042c8015980404e0500c2d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 176117886 1250 176116636 176116639
    0x2030708130302030405030a061a060405031903030b100c1401060b0412050709020a09030515042001140c071d1308130b030103150c0201050c030a091b030602030603070b0414 76
    0x5810400c1d460164031314422600010b0b4140302e01d0303285408200c117a4100f60000c040816030400611148418801a8002c501502e54160480b04000303039011031f076400000b01c05000b071030042004541c8001080002c40755002c80d1002807844000c803000d2181c44034000c808041d4013002085000c1c58466901424003c9000e29141c03100c4142d29003090103010042407001e0202810215a9851030b240041c100500c144022109409581d030744080082e24090120f00c21500084005c01003011007145100424144a801d410710503c03425407984422000058080066a10020445e00b414400350358440f40807000354031900140ca204201503801c06010002181d91f0142c5080c2d01c901c0f43e1520b030f500d5400380307800c41e80c041d0a02000006c14042c0900c0a010502440c2100b0881203d039036200300c0c01c0c0d403411501c0076465041000030441e11401ca0340840801d03401002040300400706800d000142d00c02642c02510590780100c00e00c5414582440000014482d01d18001d1070030785420400c45803400c14080c0b05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 176119136 1250 176117886 176117911
    0x1060e01180e0108070618050402030c07050105073f0207080c060a140c3405010905011a0109120b0613090b0109060b0c07050405130b01030302150a02030708 69
    0x2816141d00982045100c003a840c6281e00095444124081c94002c00344102c48a91054210001d60103020b0b000c4103050424008062000900380828400070f94806040c04c030000c0403c1040d000030170420310800e40118600d41d10900000008400c0c1055610307102c0044500f0201013401c03510900700c2c120682081c905105015849a43e0f501b0850600d0050244e1810341740034000400a042060398400314490110b40020701d4151500803401d02540950500d00144181007407000d200100e20541010b01049081502903e4000c240d03642400d5a13901401103509139110311210810b0344a41c022068801003c1c41d02d6405a4500150102d00c2c07840c000300a021142c5410100b0a1501c03504261188039202d85014806d40504e854642400d803030034070a403802d4900e40140400c0000f900f00032036082050f0800204101810001000000e0402605c0845070108506400d80000e4000c00d80704c2c000c60107074000c0c003070030b1900b0340e86841f408900501c1003000a10400800490b0358200401d550070038510342c001d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 176120386 1250 176119136 176119157
    0x1807120b06071205120117073c0803070f1205030906040b1b03090a0c0b13030b0c041d010e07020105041a181f0e0c01020a0f060209040908040501030c0f02060106 71
    0x13503a8030321603100e164201c0000700d00045030100b080c83c2541c01042500301103034119076036040100001106074905504143c0c00340380d06000b00c43c1580f0f48117100012102c507010303043d540318041803035035101c0e4000b15410200300d2100000d006076030034130070080100c40c01c00da0702e1480c054407240d80301c00307000704010301c0c5c100c1d03ca000c1800100c0300044110b500120f0002c480c0d4034204160315540d00d10998604460004d03040c0d0002c10041c01200694100c0c132165000890130608540c0c034801d0b0f03440c000b0040d01080c50140310000e082e040c260003011151610901800055052185c0c40341048002031841007960704040500001681007145550400644110100c0076120301c00c20591041c03641c1d4104034148071703040d02c20001d5402c4c1c030300c01d00444810302410042000c42003c81600c0e4103c09543d00d000d0780050550901080030615240c803914032a81700140b82c1300090001500b2112800c10a071014140864280260358061141015803000b50816823894175840c240207545a905005507810088039944 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 176121636 1250 176120386 176120423
    0xa0e0c0705030406050912010903082403060c0a1202070201051803031207050409180b04110112020f040e0c03060a06111608151602070e06010e1807120b0607 69
    0x640e03010540c860141c079076490b0384a03c000c02507000400424807030202c904c030103040d51105104400d43c882d8541c031003200c0c0e5580d01035403c1100080802445407d1039003101c10344603503000d01c01c480c4a408120101626402c001c20300034124019484049126441080090090307a0801305803060781940c011800a03441041c1c0200b0b065005a410740703001c4444200c00e00088a400030050710036180400003c001c1c144042c0154160b4207415840030300182e02c05408907000c2442c00008400202c01070401d107075440d0500d180702c400c9038000060001c107030001050a0103808840c410042d040402143c2460031410958001110000e232445158203101001c485202c80350002d1000b080c0d10320070301d5000c880b01c80d940c034403c54403000b4141015052001e9a80010003a0010b0030341d0110070501a4000d1201a080182041c40b01c2c902030f00b51030501c403d40c00000c485664149001c0312010080c00445032a0401910180031500c420541402040c10000c03002101d4031582c05841c080b540140408071204684103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 176122886 1250 176121636 176121661
    0x3160611040e1e070e0607120201091401050411011409120705041406040b04050705040e070909020712120e031c09060905030304051b181b0c010b18060a0e 68
    0x240701c032541c0035009041280c1042100400900c00c0c010f24000301d03481d55443c00c211064039007090702c03a0707110310700340803201c086201d0b050400207550803400009400300454480f010480c10903a2011401c4e13460b8010081081110748841030030140a0800010080c0101310109050151800050140020000b0003034895010040b00f4014a0081e0040105206940c604600c024085820318001d9040880c2c00e0081e091900c80c1912a1001d03903107090515061039100d0003680b5000e402401004100034020920003d148010210a44181c0907074501100c40503015204910f8249105000307490109800038156020040b28406290703945009000d0192502c50b20081c01c182c44046e0015141421410030000000015401035000304200c0d401c01079040d80840311003003c880c1e1190881d10218405ca105008015866000b07401103403802d0b00a90b041d02009425000280d4140a82c0e450f00704bc030031907090480b010007032a443c03034007941d24500d400408201010361a110713451450f521400042d4142424130f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 176124136 1250 176122886 176122889
    0x70318050603160201050906220f06021201210c1e1a2212020f0315070305060f041a010c020307030c03050a0b06031b090702030919090e0316061104 65
    0xc20715600c0382040c2c00100300d00450200d1030000341d0300c0d01022840006000030200c3c880c18250135041d80303420340c0c030324269070b00f50401d002100c0764040e1407555000a0018009884100303411680c1350744030740c908980b00f2900481c035103501d07a02c542640d0110307000ca81c0000c6244191202040d10411044100d441d94034590208c4d030059060001e5010320b005544110802401c48200380032121802945d1302d0890008a500381c031031800145160b94a40005007000c2c40b601d400c415000701a210700c112880110182150119040c50009640741e0800125240014003002000420341c0c0422041c8000d10000340d402424104441c18481412807840071075400308103c401a690003049901035942d00e10b030150b0b9072080303030004840c001c80c0d180000c1e0740e904001824000b00c0d1801d007025501030b0001402d03c4084d09020b0548011400100102c585a46036010302d0b803544140c81160b05000c3c1d2501241200312607010203003800c2a0002c003c0d030400b54650340100e13092150030050000d03107625080040c0140e0301c00e070b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 176125386 1250 176124136 176124139
    0x708150a0b0708040f1502072705090601080d0c030e04090222051605070b0604090c0803040e01080c01020c010818011d010c0201110301050a120602040e090d090f05010507031805 78
    0x24122041254542c0900100d443c02c8003000004c2d0780314100810115014516a801a88100020090649c0009580304910080c1c00c4401c44202c015107818181d5108540ea07101c640d01440041000000c10807041ca280300103441c00b00c0e070411141d030340101f410504800e00b91150703455420180035540ca003041040c8d244204038803081103a82d00c0e144400506000c030743c51903a0b02d0710540c01951031402030f021180c000d58801d28031789090350741c40d0405c0004c1021840640e500c0707003040b00104a4910400040c0040c0ca1005104135496140c50380301382c41e0102080d01d190440d0009400600141d80054201d40c0201c171001d0a001c007052380e02001801411071031038102d2240f09810800c42030b561b0650089406540300ea00a03c4080e0300344603518402c1c030080c071445801c2803488404001401c80b40046040d464440c0401500d0682e0340c02070154000c905464000564110130122501d99400162a41c014200302500c885080e2410300040d009020765880a401c0c4001480d0710300c3d10416042080c00074200 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 176126636 1250 176125386 176125409
    0xb0706050c0c010903120b01020a031205190c0201060302130b0904020603090a1a070806010306060203090d030203120c09090a09020a090504050109021f0207080303130201050702030f0729030708150a 87
    0x180c5050040280081c0100b4111b035910b014145a603551011070215806501500e0310781c00803903828103880003480000d11000141351001d54003881a0303910300031400004d54590003c5a85401c0d401045a9020101090380c541403030403003403140588aa405542e4440c0c1c040b14100d44958600101c942018500d180040c2901184040e001c1400f031401500c0c0d0141e03507a40e0740c0030382d02d82e42c1e1001502155490300408001d41e00610261490380f400340b64a8548902c01e20541e070a000c004070155021a13400e03100403401c100c020452300080e0a2030140c541c1d02c98090042888141540d40105151030b07114010044040c0c2c40340001020300209403c55642a42c2c090100c910f80003c40c0720b1295101c1c0c00c03160500c01401400c800140580000007601c4c054000681000f508180950040d16158405a0100c0e01401491078040d250303201070000600400c02581400d101990010354114003c084e41402c80c0d101c8001d005001170706500c0985168444111001000020340030000640e101220f540064000c03103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 176127886 1250 176126636 176126651
    0xc1c0201051e13050102160e13050a051b0105130504020f040305031b0606121f2003040302010b010503133002010207020a050904030c03030f0f09050c15040b0706050c0c01 75
    0x600384003c0c400110b40e54055007050f61600012070b20780419000c6040c840500c5201440009003046259800c040c130300e280c008495016a84250a110151006680384e41101e84c100e41c00029254510f07200c28824030b412480d00c030000711002101a44c0780039940c011580442d00f03101400c1f080c402c4801454015007241c0d200d964a030158414540340c200e50768050302410780800c66a060442e460712514031030202901d6001030310354094007043c60700705003946501d8030b441c800d11580b042c05080481094a100e0b185640c1d1030603040190944515800590401c2400c0041050140d01c0f01600f0016a50040300c80b00c0e0031484000b250030199001d10280c8080068003030710000b00e1340542c01024144d20035195000d40964400c20425058012240a4007240302c401c0784a0020b84254815000d0090b010b000042d02500810404200c60030090222044d62000e00304481528058804e0b082c46035070412444d1070182440d64090b100d02400078010020b81c0c036540403941064003c0b0640345070307100e41c400800160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 176129136 1250 176127886 176127937
    0x103150b1f02010605040b0607020d080712022503080306090415240b0406050a140d05010311040f060605180406090c17010b03010602060601080915091e0c1c020105 72
    0xd84481d950002540c80d00900081030b040034002e10880d0200108800e050503095000e0000c80a170202003110200c204101600c0010304441c01e544103144107a0040c294000e07006580c5070080301d0030b804c5c400c200d01d28150810014209030b0460341d001c0801d0314a00d040b03445034540b032103049144982e04080300d8101b9004081c40d0703421010101701c9418255801800310359850f94040a841913000d801c00042040240c4056207000c1d80101051420342c0800700c2c60928200150012908203800841e0011344140400c469803800d800b0718070b1401c0c1c0000c1c1c10007005203040d4019120b4400d00302001d0880004d103001c007c10b6034039903001d0001061614000e001e50701041e00c000b084010309681400086000c040081100b40e95101540d040e180180c00070501500c41100540381d41c2c81c014200c0e81c051145031500d0505200008a05006100e0280200a2001440c6c1c1590741c207118003003c078007a68400001582d0541c2e442e0724040c0c4d0301e1b11507024a0110445800100c42d140f00b24113440345409502e04400311107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 176130386 1250 176129136 176129179
    0x30e0d03020f210f090111010f0507120b090f101707051207271118010f030c0206010302040c03020f03010609030b010b09010519120c0203040e09150103150b 69
    0x28196031a0a6604088103c80780e0160340c4000400000014003e20500384005900c00c01880514014100004c1018070481c0300d40c00d450072480b00c20f2030142c503441404101508400308a4407031128030420b001080420002c03440c612070003009071b02100c41140101c0c0702c0941d04a1880d01404c030b0140900d01803140c40001c66030740e981c5441054000c0c100108941a6600c0c04250b0900b13640020415001d40300c0000c01c030011100d81c5e20560020296a22064645030711048020003444e60a48a0030f4003420002c400940680e5122050200380341c140540b492040742e011807420705480d0704071000252401d064070200c0090041c09207104070420700000210320039800c4081b40b001c5911501720b4048030303078031a0318150ba2806040b2120340428014840c62403402c0c2821802030300c003003081c6801001500ca072080f80041c0c41100c41c03030a004d40c01c00102848500c00e0805a550b01540501c010104007400f010300061070041440040c1100101c1c0c510040580f00d00e0700100755842d001003440520707801300c06030441c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 176131636 1250 176130386 176130403
    0xa23031201080601080f030a030b040f02190e1f0c0f0f14060702030f090d02040b0405070903050c09090d110f030d3306051e030907060206091603030c030e0d0302 71
    0xb00b441001c000240182000410203401c58959024506080d079200c0154045c0402510043e0300c6500d038451034180030818406410689203220034003c1d0280680006003800f0680442580140c4080d01cac0d0300c503038049001c0c03081e8a21145240072214140e04e0700308114004441200149042d0700511031605104241d903001a40e01040c6c0180e44890311400c00030b0381d4902c600003041c884488140074580042c0b0305940d10904090000c1e0011036402c0c5c02e14000740842d2800c94012003c81c1a140003802445400c00080d06100c03000d81e200401130409203089980d03503c0c1400e40310100030303c2c003c10070700008007401815910740c0a0011aa1541001407a0901420703084d0384003031119081e00c0300480000080d2a03d00600e11a000030b0401403810300f4011101070f8400910b07080840c0d606070170011264141e100451103a4070b210f028004150400d04000d0a21801506665041c0e100040e1141d0003500103041e001104c2c0d16080450410106250644641c0c00004e40c195018024401c01b03414160041007249 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 176132886 1250 176131636 176131649
    0x30a0b010501170f0105060a030e01110c1002130e060a08010f0b1305060907080702070e091b0102030a08060f04060b03040c030b07050403030c330c03050705040302030a23031201 78
    0x40c244401c1115101154030200c60703015031031340d000c401009541400c070f00500c006400d81c540802c0d403030100d020803820360701c0b01d040d0341e552000001440c0c21400340a000c8591280024501507180100c40500484541d9850103503441c0f000c11207010548030390380d448141c40104180c0d002407024a5034600568000c00f02141094050700c0c50407503a1800104520903180300e0000100115882d0b11154002c4464807001001841507209002d008a02c41101c0d01e003a621400d244401440100d04482d00100a5800c54110f24195030050010b8243e040d00100415485a01920b019801246140000b4081d00080e03115445007280001804284101c482005098174011100e0f01180d4585120468407481184000380000b14000c40e0b2000003001188082108003d410080003100036070010040313010201c01490300d0807a55245540342c440d405004065010314241841030405245070003003a110480b40400600e441000c4200040c0d01e41d010845c641041410b030700701c90b11001c0106403000e50303c0080c010302 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 176134136 1250 176132886 176132897
    0x1715040f020414010506160212160f170613020619170601050315060d090b0f01030605090106150e010909020301080f10090206040510120c08271b040902030a0b010501 73
    0x40242803c0c00100358102c60300a80401d00d002103250080400b46007030001280d00030a54106c501c07030280b04201050b41d0a03055616401c1a518010100230106130542c032240c5181d040c0d051801003003c1c08035070b455003c8241d07003035403d030340e41c0030710008480707200e0401c40155643e5217100440c541035001500f2205401002c3c0d2200481d12524010364443c0800c8415098000f140030168185041000141c11f0942c0d03d0140410004038641e03c00710800c2d001c5441d0554114200010414002240541078002150000070003525080481d030030304c41c1d41d1001d9003e09005541036000c129074403502c030100c01803070003103821074882d41c440b410301c1d1300c07100554080410707072254013071a040345170240c4100c01c1d03441d500408080c5000c0c941020700c000050503603a0b5001703019901d40040700c0780d6400d010340c0303e12030791a580e9400c8070300e00b5040b00e2486480c260f00d102d043c03d800005603502040c0018584070700c5c10391441090301c3d0081e030100080c084e2481c20002901401890110001c02040c11303180c40c16140c0980b101e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 176135386 1250 176134136 176134151
    0x2b29041412030612010b04020309011407170414030d050c13050109050a030b0606041502060402041d0d08130807060608060f040503090f060f120105030c010f091715040f0204 76
    0x1440d41d034006400040e03000c1c003080011612034580414500e07961403000c80007181d81d06081c80081c049800840d46010140d444641111f0040c2c06200d102e41d00131800d041003001032919158091000d030000f04010034145483c0302c40b12541c0400c00680f100c40240c6402030000b460610350500311500200c19042119480e00d10106056008040c820706a680150001031103070300d542c440c1d841c00000a460300d601309000300004581060514001203004080f6001003180e41440d20510080300c410740f40340410080c800101c440c5880000c21140111050392401094a80f00c2e481003200c1d1820b01c56008185a4000901d40c0800401d6081042115501c000342d42681c1c0e6180d920340c80c014005c49005040c0c2d001008450300301d24000c00840005000a00214240100e004a842036580705050f0340c86070443d00c500401c56460108120340900100380f0f03190341c0c000000000900a503500340a10780d940c03510017015040019080000311220030081070442c0190905017031507403204403211800c1c1c5c000ca003080b21 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 176136636 1250 176135386 176135423
    0x10507030606120f0e06010e060a09050402011b0c08150411040c02120d09063803030406080c0d1424010804030302070f08040f060e2b2904 61
    0xc000c220381880d11412031152114250800400b6951350000307110750303144400300e4590800c00c10385001c0c1c80c3c3c0d101c0c14049400c0c4081084010f1441d07500048500d0300700410000140d80c0901910317150a8444403030300902000b858005c4443d03c00c0e402030f00040c815004480910300403c40124080c5000c0c2481d18032500400381440140c1e8075030042e00000d64408a1504904a461001803502d805100c01c00602c7e04655902c41099a901208091402c10903180300c61114100c400a076000704144400c0b0254070313560f003020a1b102e004611841d4140103180b40040d070440d0089003140c964000d080c00400c00d04829001d100d00b40381c815589522000a0481984002220310645080405058603071446941e41e940d0114040d5000c500304480d082d1124121b0400950990080c102030500d0036851504d50b82000c6009101e40d0042000c2407090306000603004040da51a4418205200d0510b0041418040341c07d100d0380152074205209110f11140007503000c034501c0406803c4c040c62248080007206403019a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 176137886 1250 176136636 176136641
    0x100e131b090e010e130503090a06030f05100509150409060906091403070506150f0d0305090312030f0414030f0a020c1011060a0f1d1615050a0503070c0203010905070801050703 77
    0x600f18420300c80c0804030341c01c01c00040c06000050306c02c20491b454001c140340441c4410066500c1000420703120a4880c5240c1d0180c081d4030f50022140070780d040c2d01441c1c070700024400d0360041d0862001041006c59426a03403142d8114000392504201d043c020040b540c41e0440041514620540d4a80c5401440308180540070080322011070b000001062180c039200254918210090003641c0c1c0262214001081c40d00c440b01070b901403900a0712810303184d40201050500f00588040a205c0c089010420400d845411544e62074002d500007150049410350600380c1451440303444d061568020001c600c20708075a03400030700005183e0082d00c4521800600141c183c0d8410b10541e2800c6031030300844001152101954002c01e90080480d01c085982c3d120b01102c41701c80304003852040c41c2d030303044900000d002144001c0000002c1042102e00c00748000309840041c0300e17010704d11080c1c08010700080815911440744214050117900100204030002c141e26005aa440c1a071090000c1035090100051a61f402031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 176139136 1250 176137886 176137889
    0x20f04050414010e0601050a0c1211060601030b010918090f050a050c0607020d021e06040303020102040e0c0405010f03091b080d14091018241409100e131b090e01 71
    0xb03c580c02c01a01c5420064415030081c060040411421109000100b00c43c074401c8816101a9100e110900c0bd800d6100c90500070000e018138149401c0003440c85030b03039901c50034000032115094520807010f2018041d98010308581000a0154052100e202040c02008180007030164071030011104601c6ea00c4083c004d06000700100a0760152045007100e000d804d1519003620100003051070403000c100d00c00300107195a04203030015801030f9400328050003503081c40044a0b410810404105007860320f000002055100c909607403500301900c400f06041041030340d802120014004a000700c1710704d40c5400045680781010304000000500700c1002041100c240401c450b00600e010f0000300362030554002c143c49682502c00b11006810946100240c82200d405200c000f810300000710401404141000600c540fa00302ea084030001c00402c10b084840d9242c3c1c281000d011480d080c10300031035440742c00058401d001c0e03100322102941480380b901242040c80196001c041c030f00da00e95001164850482480102c0309 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 176140386 1250 176139136 176139149
    0x612030233011203090503010c03061a09030d1b0818041a09071d0d0b10060809061b0702030f06190b060a030e07091401060f0305131113020f0405041401 67
    0x1403100610900f801940c2010106009052140c0c3d155a120003090858103581c9140001a68a550904c03143c020341102507040040c6041050800050000107a00c41a0248131041400170703101d54002145040d60403d08a150010807080d140c1c0740d09003e0358141c15400c085244520714284180310347c0501d0408c048424407014252003070555074030703400b41c500d170312035006885044442c02c0310802c4503620380040d943e0440c441c1e01049001c0c1000104801b0111882d0816400d04c0008010041103071070001c3c0d01c42c0d202d00b0859401c0048890f200142c0f119100700100690540256082507120800c0066a64040c1080e0014002041c202080b490212030121005e1980a18100000681e43d44241c01c02a5519101001e481920780d94071480320072030b001c184042840442281c010408950841c5614100d1305c00780c2000c1c05580b41a0700005510190000020456030103a502e2500c19140c00e505001c54403140d4904643c1c1e40d0a50503c10401c2e0024440c00788a00d01b01000380c5c1810300c44c0040d941c101d400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 176141636 1250 176140386 176140483
    0xb011d07020c09100909080409061d0f0c07060f0605030601080106050a0510030b0a06020a03021903080f180d0206041506030c0314030d02030103080306030c0109060203041806120302 80
    0x200020804040e002030320000b44020404d00c007084144c041d01c92903c5251058a426079120300d0440b40e80260385090b807140740d80e0540c0445200100c0d241100300380e4880e16442c1c0c151300b9a03680000304211409600400b074440c41c85c00c00c2c80a50b45405a0000d000d46a04a0488105e40e980d4022107007a10454014150488a0b0750002c100300d01300074481c0540504541408074021450364007103203c4024684c002d40060b8401c0080c03809058050020a1840c8400e401075a80f50400352000703000c242c0c010b0190180740d00204c0014440d10101d5841085249038403003680e20704007035030000035652401079409030b907d50707403142003400e03036241c2841145c2c22a41d00c1a4a822698559250301c086112201c3d45100240420080380004c400c0c2440154040c5101d045001d4490a0800c01e00d450411090040d9040c4645418280f100c26000825101200c1d040220602610340000d4544042c0c04107600441420301e0280310001016008110744820b544400d120305031740c541302c040c003c10316181060318200142c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 176142886 1250 176141636 176141653
    0x40e090a05010b0303090d1e060213061403010b04050105071407091416020d0c0819050a231903060e04080a120c0903030c211806020a080313021c0b011d0702 69
    0x3480c001c03000540603e41d1408850300c4248c2d488100591780000e982c54011190780c1024048240c01a4512134001e2100d07428904644c103040140c0070511803409024103108002c94407400f0031086104081032039406005480030141c4d00d190a1b030141110b65a0b0141521001c070000b622002c1000251300c950b109a4010190682104000d07283da0100c00c0c420b440944007000303035a0b600041c00090088815907035a8180e941c080a01c00203101c2d10100b00e01c440080319481c942d0403040115015610100d252550a4104951081b020390050030b15a00c9032018480c04402c000904c006d8001604607424680c03655401c040f0100d81c607030100c5103640e40441c0440d20310901400443c4c8540480780c000b074403d00310074a1420750094126182c445a980c084002a00c66200002c040400d142140040210340003c0161901c20b995011280c00010107245e80011102c80140541da00d28881e4500c0b0407503400700c40000c020b14140303103041310390134050b0740384c5020b040940740030750b000d4074a070580300750200e901502400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 176144136 1250 176142886 176142893
    0x1b0f051603030513140c12011b030c050c06010902120601080103031b14100c12060b0301170c1807030510060e090403050d0e0309030f06040c1a040e090a05010b0303090d 74
    0x3090f01620340f0200607841c10341c0b10000703030400810380015200e68009111075102c60040100c5130304042503150b02641800c00c410000051a00201d0070f4282c18100400c0d1942090001c40d03440c010004100582e20404000003407103281e80e0700507d0386104200000803140e640e8001034603414070a21008000546100c042c1c241c028406c400301d800680304002c4078a80746e2139080002d190601c1380603d100c038107030b460b011000519040280004500e48600050207194a0041d40c03034541d01051013844960804c401210540d10f4050020a40d1070310001c2ca050190300180c140454401400c480d682d010034070f800e02143d8404807540701d04007120000d81e100c40c0d000880b81c09000301260003410440c04d0003000e10182d64010018003a46104481400065484100d20010503140c0400f201c0040801d0b007040003444003290400d803040059a401401100030180860f504440b07070310a5901800310901400180310646101195800301d6a011b00c0c000d00c03044a14400b0180c6910544040540c071004e4841c045000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 176145386 1250 176144136 176144141
    0x2a10050f0a03020a050f07060509070503010c140c010b0303041e140d03120e06340c12110118021f08070c0c080708030c060a06050609040b040b041b0f05160303 70
    0xc20300c0d142150610300801480000c41e000080100d40d12303a100c0d0104058003130100602001000b04070001e02124140540140c43c0c0114030102c0c922084002458000c1c0001c2504014000d04010b4100c5c1d68580da10b175907042c04003c02e41c0c50580302c20f110f448001600704401d4414103e00d04000d007035238141c090320343d0152422a072804245070943d03140c0c8010504400148040341c42211030f002c4816064103403110680182c40710500b40d2400828108044201e545c0c840720301840c0560101f000d0300100c09002058680400c0350030315020b25820041d280130103111202d0034010f054030985900c0e5802c900412001505404841c0c08000100b1042c0040c0d0100d10420070722680b01d000700030740703020b050325401d07020305008a6420841aaa2001441c5420310900700012907000b902d00700d0400481d41400c00140035841202c90381d9208640341c040c0702c1e00076501e55010702c9864500400030480c00ca02d09441500031140400004045242c10b0340c213200241c0200116511181e0001c0791000c00169958250700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 176146636 1250 176145386 176145397
    0x7031e060f0c020304140319030806010903050f0705040e010b030a0204151805100515040302010305180d0903030305070e0604031b05030f030c0111120708092a10050f0a0302 76
    0x810a888001004440702640b0800d00144566805580d80d107007040c440d03202d1074411109846c0240c1c80360894056003c02c21081003801d6900d0300e0f00c000d003078403914012104100c80381c2001e031407402115011a1400c0700020035404079141038030701307002d401c40c0b80310b8040c201e514203404660550041071580d4014681030f84042c110201c904007401081d030321408034200d40d008500d100c1802d20f94500034480056100000c1e0002024105da0f44660f010020a109007030740078178400203060544a10104810801000c3c05070b0a000300f40080704c81c0407205070401403a180342d600c000d5002c42c0c030380300100e080311f4440c02443ca490f1002400c66807400e0f24542e01e007602c0e6018640b00850491000c040410340760b03824000740c601c2400d90002192070340111f845907801c50341514014025230320204aa140c484042030360380342d802051410305098564585041604180d410414560a0b0141202e104400c1c0c00c808445030b08440103403141c4803e00103900b0b0503201486101d04070b0660307800078058241c80c1d922a800620 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 176147886 1250 176146636 176146643
    0x11e08091e010915152c1e010e06060a11010b0a0e09060f060d0b0a091202160f030f02090703090c032001020a0201050915040803040905061207031e 65
    0x71107400c021030784800428004001100165100c0d046482400b40148101e901424059420820000303c0401c0510b0345141c1e1080e09041c848900343d00002e89002010407508100042ca095500c0c60580302c07860070b61007030b0f00502850680c448008225528200300080c4130f084003421040c80c09070352070410303a42c85003101582444d40d034940304a920640c0b1824100d81c01485850151030707450508512b91410000001c10031040300580d40c04110041d600c0c24081807455400014402041d1107020210001c0c0071042d002402010312443c021440541c0040c00062408000841ca401261606284c4240c5407243c030015000c16122020b03040540340901455070440c2c4103040001d2600021359074400c02c09403991040d50f103500c10343c0c101550014031084507101c4a1742440604030904c5643c2c0041d185000b0000322500415000c41e143c20400f0f403000c00c49001e403002d582225150703582c40c18260040c2038101da00602821400101618290002580c40c0c1920b610030300c8515840c04242e68980e05680c50b28058 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 176149136 1250 176147886 176147893
    0x6090f0c0221040f0e09100507020c220c0e100c050d0f092102010311070c09020f120a0209040b060f0406050a090b1201050f060c07030807020f030f011a011e0809 71
    0x2a20520845100003c3c0205e080c80050780c6080c4048030b0816504020880c901428502000030303140d40401c82c81e8420b2801c449510780c450180e540002168090195014014038003e04141d05035000005d580c80503500715010881c00a020008592108008500506983c44003501e078203464000c090b400c6a440c40c07460210f0807155600250410404200900342c41d80e0714140026041d542c1c54041c0030060000904802d1514610365121418640b203480b51608555000c603a0301807694444c0d0440d0a842c06929140c1094208030203540000e51120202912a40c80e10303040c0c0c01141000400c2c3c420b10b0200d440f0303190816141500c151810380c8003d03548401c000c042040400e1020300301020b07104008504204072015030520b4140072001d482405500d00c244001d2008002070030f0001403400982e5403010460b501c0c0c800c00e00c0410810194541410b6140c014440c2002c50000c05501030800392030b01100307183c01405020f00550ba1800d0b03501d1214a0460314040526881d4098900d958100800c1000c8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 176150386 1250 176149136 176149139
    0x61a1e010c120f1403070e10140f0405090106090b0a0c020301180b07110102030c0906090f061c050105010c0b0106080702210a030b181f03020301020d06090f0c022104 73
    0x8550746250140c1101000c10a0f0940c1c910546500c00d54072940d040950040030b1640c20480303009440301801c0700c030715446019a452070b807113424403520500d4000d0140c0000700b901d40e104034100072040c0d0403074040da5000d12421000003800e00e22800b2008106c07880482840e02e40007034588200c1e4403103c03000d01a81c05640700c1500181d5060f03500041801ea90007500060b81c10305107018002c11040055126044aa0050007032200d15140c1c0c000316407107042c0880e8900e54415000c404502c1e0340f0f0700c050250f03034070580210307220041c0c56041010b8080010ba0703130300c10013030390ba00d030f20054400703008024002e09060003240040c4403160044454035000718480c01220b41d0b081c034000b41804240c55040d13110260300e00211351010526010b004a190106084030b001004c01483c4407640e0074072070002c10048203d00d4100c1c3d52405815800c40c4007002c1c640280003035603202122003c050240080348207242d0043c0ca81140759a10300c041d407068107141c2480341d001c0e22240172002035000049849401010303800604200 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 176151636 1250 176150386 176150393
    0x909020127170a0f150c030902030c12010b04050c04051c11040507030207060c0504051804080a080c0706020f070b0109020705100c0302090603010905060312032e03050a0609061a1e010c 81
    0x102d440b01303600c140e0052240f80810548041900d0520044209142c14201d030302c0700580c3c1c0499056542c0030282d4112044108801c10075000d4064251910341051428040c03003040240341c0000d100340c40d015074040c0910008030190f036111003030004020340180c0c880d004442c020300d05a0041900510360386030150901c5820f440303000441d01d1000440e00841e00001c1d0821070f41c20118041c58138410510304074109842e158071207003558810480b03000200009040040c8030100c440040c0c4030381580000045440d801c0020380c4201c1a440000140e0f1106940000002c2c152494000c9505032a448000751030318440c0e1014010140c07007030801400c1030540038000040e89031281e101440c002c2c281c1c0300f804500343c14000189420401400c101c240062404c20420141c59661082c0c807005a03424481d0811b0440504000712a00c002604010441e010b4814588184041c0350042d80a10380600401c00c0840c80304505881011040c001c0c0d0b80d0010310108240f02c500800904260302c0300810f04001200704000d07903 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 176152886 1250 176151636 176151653
    0x1a0702030607030603060e0c03060a090609050a0605191b080606160f1101030207030c110303090d0303020901110c010c03050d020702030703051e03070309170a0c0909020127170a 78
    0x11010000070b540ca500400a00000c0c0c02010101d024840c00307803488d4000c107000f083c1c440c10014401c45100d0b8441d41050704024075035000420903a002030079521411010300d042d001801040d540317018500e4182408800840700d0744114101c10164007001c420184221809841080b03000303001543c860b03418098030b118607150340c0860039014490041c2c0c0313420902500d0852842c1c0c1303500c0e205a04051040c40410b0009820107613613203600b40c000e4505002c07010400000b82c510b101d01c4004540041425515004154041e000b400c00d40c031090301c6145040403038040c25681d80401e10102400607034074014a10201380034500503d9401c26072200945000d00a8021034900368055008840c503610082d47c84200107a10350318a0601c00c1e50101662514001e503c00401c01381141c0181c0d00d8445000c808400350000400001045a6010070101044d0380c3e1020504001c4c0a01202039000c1159803000c8482030030540010301c0d50b4181101001175840c14800d40d0495045801240d4a182c882c0241000c082840740b07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 176154136 1250 176152886 176152891
    0x60916150f0306051201090302070b1e0f0f16050c01020f07170304090603030e0307141003051801050411010906080f011505070c08031305100c11010e040e06040302010e030c071a07020306 82
    0x17400003241c42c0d55107103402494844554004442005c0500030001c0642014204103070360390300580910b40f10510340c540700300c8500c100300b001008140d000417401e248540540d402040c072401181170302c0d403214407000160780300ea4500d2a100c17041d4118410500280c0d440309c15240c12803441a040701c1c20943c5802c201001c407040b582068002c10001c204400300d80c5010442c200190102d041c0800c0f0700c0000601041c0d080d00040c0004007411303200e100081035418007007104207960065000030b21041c1802c6c14001540917a41ca61103000420910b804230b1604e000d08509402802c4000301d41015a2a00d106120547c0701d03940804200403081040700041401445071502070000b150185503138a01000c0495103210f41c0354030880c0070300a03080a0f038040c079810000c1c00200e1a006540301029202c9100122029035602030090352041c80d0042a503801d10700042c200c0c1c8503500c01c0d0000c000700781850000c1d942e81e0081e424074485c25401101d0901c28000c0c440a80100202600c0c01c20341404103580c0001d0504208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 176155386 1250 176154136 176154169
    0xa0605060f0c0705010918022b050604051b031b1902010605091006020a0303050612100509061027060b0c010203040c05060a141602060a02060916150f030605 69
    0x41403840c0003103000c3c8440c2c00101403d0034134006851501d800384d02d40108080d1240b0301d0f55408241c00760a0b021207410000300c46030070480c081c072040100705039400515041e07544902451410000071542042104500d04543c15106807034290303070340c0307103144143c44960910040703280c030f02442200103091701c10194608020440c1c0001c59164200010b201e50030000811031564040d500104020264001c1610041d90380c0618001c52584d40d03035004568043c80061a4070f020740b080e40784075018a54144d20107406402c01c3c10a840b201d84a070340051440f40d640b4000c02c1c40503000c00c80c101101d143ea1600704e0410888180003c03a20b180d0f504841a1035800640140a00341d400004200400400075034003005010101c0d241800e104c41c4640050100269041d040d4110f880001e08501a0b980070842da18259401044584d4880c142e01c002515200e060304c10300810301c24070100d0101e40242100040607254110040d107800840c40300c0885135144800c040c101803681da0440801c40d61158031540c0c0090700d0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 176156636 1250 176155386 176155417
    0x2180115050403080318010603050d0302090306061801061b020d060c0206090609030a030b0a12030c0201121e0b01050d060b041a030906042901030f06111903050a060506 74
    0xd400e0a400400810214000c01c1001c10401440000d1840342a80d80243d081030b80b51420356296030449005000d1900098418030400d48940d001e141e15030024600c4910580554100d03407201c20034042e95402c425501400444900018000c0c940b00b60041d00340c60340b103ea844044180c0035004200070440c60394003500d166888042035505d15404101090b0001100e000400c0180b80004620707840b8028580700d8000c15440b1a80b10f0444c0e03590b80d0008015061902d01d40c07806110500c0d002d000440764071400c90110396200b00f000e41039211407242c5840c88985480030103e0b9001010040c0042c8400005581444001c6c1b00c14654034425210740b40180001c488200d07070303da04140c515040b01c55031800c5a06080410801c0200004003c9109504039500020004041c100784c100c44000610964108102d11440000042405072203101703e009140941000c00c80140c1a03100b0b00054031070750012002e1001200e403265030f1148268450344d0701c2070b0340305400207866440d08002102c503440190b10619001c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 176157886 1250 176156636 176156639
    0xc0a08030c030109241e180b010e120601051005070b0406090318031e0309150513050909061801060512060f06010c241407031d01022502060403021801 66
    0xca218090385c00d511010300660f0201844802100d070071300c1d4003892103200d441015200e480c81c1c4180007076015000d6035010160180d280306070403004000c0140954001400c20508140c0b604110803002c5038800801c0c080d00f20f80c0e082c402031103200e0040e40c1411040103030400c6842c0201e03100021903801039104140200307100c800c5081c000e004802d09240001c0c00036600d142040010b141c5841d86433202c0c04442158402105410103451a03d000d50000340100d4001d4141040c10b54800020201060080c035203106442c0c641091016400b02203d800c4400d9000380003160303a480414203d01e5000702c00e00000302d04141c0701c8000c1501c0340c038030100c0140294414814081d0040900821552041080c6417101c40c050154481140c180b0150696000c05411010304158060b81034001d603452171008114a2010b09004a00800812012001c4041c0e04e06055680851300c2041c0200c0e01c04821500d410115440440c07048909201c107100201d81c080f408001c0000180c44032041070000b5108540b0145075036 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 176159136 1250 176157886 176157899
    0x5160e21100609140a02040f03030e060c010207210207030c14120706021005060402030903030f1e010b0408011505010909180501050a0b0a0609050306040305071406090304090c08130201050c0a08030c0301 89
    0x480540b0301c41c106070040c8418040e500070f180c54523048070341510385840e03e100c0c240045106032080c2c40015065500019590ac00c3c050328000e9000511030803450301f03c400c40740110403030f101c2001c1c0c040103282d0301103800104040c0fa12808100c00b0090000c03d4100815140d007000b614210043c3c0c403e00258122080700300e504008c1e4452154007001c1500e0039491440c000440c55103d00c0010008402c4162030070100d01300e0081c80c0c1c1c0312007084414518804103541c545402603900e41042c892002c035903081c0b0000040c88404518008111241038490030003940c20b00540c1c030082c00d048030701800c47d80101d988000c00302c0c0090040501812a43d00c000030003000704003e10108001c5500300d02c060050450b0104125180003902d19445601898040c2e02c0c1c2020f031420200b81d0006452110031403040f00b080c051814008001041100c4521354104000025101c041e0b40c4810b0484480303092500c003101d000055401000200390724142031041d038444207200e5940e4804d64000782ea4036400c1900c04401072142 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 176160386 1250 176159136 176159171
    0x10c0201060602190318090906091401090c050906151801020c0102060f010612110705010b0a1208040302120c03030301061d0402070807060c02030c030d05160e21100609 74
    0x1400507440030b84200c020740c0900c0c202810360300e030b001800c1280c00300611b107600a5454811015040d10002032101141c141088006001001010745003004510310b100030542c0c05229060910f0381c04906403540510b45070070000c0b60f030001080560030090290036404001401402008a20558882894040f04240c002031401c40c110240c941954400001c0c84103004182845504441440c5042701e540340d00142548054400140f10310a20000030a40d501004011b40003ca001076068911000705035580315501d00781d400050000d003080304200070a1003d42407404000142d1b03449841119205008500481d2941e48241e121400080d9091410b201401c0c03090f003400b0b00c08108071001d5080000e00d4685406510031400d0080c0703400d1b0b94500f440760a81c024026a40c22099003000d681e2034075000d040c02c4001e080103da080c00c1031030703404070b11512641c06a10000190031000c0c0c107000705401070a40680b186000708183c0c4009120320807103c4110199801040050900300502040042c9040c880c03142 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 176161636 1250 176160386 176160389
    0x6150316030c0e060604030b0a150302060a12110a14090f10050703120501060504051e03011107170703020309090703090b13060f06140f0f040203100303080a0e06181e010c020106 78
    0x5c1994104810000704d000c0c0d03401950012140503000403d001c080500440c0300440c0c1e8070080d0000d0001c07400ca09a590841c1d071403803442d02062014824051001452100351141810500100e03207a00741c030701c81c5210120080c048484010701081c0a692101c400180c048801107603d00c00264000360084c101035010020204034460900144000d504080d0090700b140603500415001d4020542c84003000040d0110841d501c04020b4000c00000345550303001c505650150009488000d03402c041c01040d80309070004c4800700c54041d1f02541c1001c0701f001c20000b1140002d4014001c160f1078503144004603445200c0e15002e00380d8444014031449840c5000001c0c1c800341c40c0642c1550f0314042c401c0003200c500300311810307071490110303510a240c4803000001751060440118141d0024400301c00c0000c0b401150401c40160b0740a5164403902d545c6104450087e50807880485681c2e8001401041c00401d415000d810910046e006070f941c030310024044209075004694240c001c4d607440c1c00c00c1c03461580d0280304010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 176162886 1250 176161636 176161639
    0xc03021c03020c0f1c0815060a0c06050106030606020118020607020f0a0b04060815011d040c020f01090807020102120406090504020d060e0a091106040506040308030903071a01050307050d0506150316030c0e06 91
    0x11110b20305141c0b028019800f0002d508d000c0e0900180314a10144502c41030b90300f5640c060010003640d6140e000040081003180200300c050740c80c1142540a00003044224a01d8550080c00c5c9071500c505a400e000303d01c1c00340e480b400d0300300a0080000c1803050610000d0000342069943e03e400034507207001540c1c07010350250112030500c0f60100c03004c501c981070402001000785081d80c0210b4418500c48040749004000c00e800403155192190440411408200516400e07000b43c0c00c84064441129001c0134511035440350102240b2004410041030405070050407510042d4403000034895a662020080c4040450b84a19299511850f440802504201d03c04400206172500303828681402c0120340b443c8268000a09403003800700009001400c100111091070780d00c450f48006100840000a19055007805414480d000e85c000116003424800088030010760040018002c0b0344458411800e0340032591601d54050290000780b03a01ca61880304100c0c021480384a00149052809600c4d0b0880032018100d82d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 176164136 1250 176162886 176162897
    0x902010801050f03030d110405030d17010b040b16050a02090c0d05010e1909060b120a050106081f0f111b0606100512070207180218010c03021c03020c0f1c 68
    0xf00c580d80340001a2002608034900004c3e88030b03035807102e10002e40039560086505206007000c0150710780e44038010403020300c46001c4135000c990300c500305030f16580124010f50907801024891624090604105215142c1c012015282c03a00705035001f094032003004071aa41c030020000120310f00101030510036540180740c0c1200da441c107400d010396108000c1ca0803494032400903440e0303940c20041c060113a1181a00802c010300d140e0a0400030308c0c402c0e8451142d080140c455520709080007c034503401051071000030a0041e8170110b407101e070140e4a8001c0103c0c87c40c00d08800d54801c0700361007030003408004040456081c0c42e80e1491541d4969441c0c50316400416203406000d2410181c03881982000642e00c030b18a42240c02810340d070b40c5810407490845e142c3d2065004500c0b03078a400503c0b51095004040a424811810305940482e5006442c001c0e01000f00a00507032040320207030101c4c0782000008104800b035180140c54220b07042c590306d252203014603180b034207038110425070700600c0b100d0f00850600c0e601d43e0918 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 176165386 1250 176164136 176164159
    0xd0f1a041b0c110301020d09021305090618030d0f020415030b061218030f030a0608030901021b0105070203031918150f030e010e0606010207230d050a0510090201080105 74
    0x220450007080d2034a050511400c0d000c690104840308200c00f042c0c100c0980215110700340c065000c80a0b0100074816800780116040d012130f843c115000d964800c0581500400b0603445800d000c14001c40d00e1010711030207010a0102440c2800180503581c28010180c07405178645007429a0420340514504080c828103142c5240c2c140c0e240c40e00416184a0001084d0361080c682d145544154080d245a00022040c00000fa2000c0d030041002d02450056001c81c1d0304000060301c07070064684d24890302e041320380580d01428118208100c40c011000c032100d010301d0217071f04103c0300368007003451074001c0104941d5000d01c83c1d40c40640785500c44185820301c401c1142c3c01c90351616140215203500f464400e41410400d82020301c2507030501a401a00f2800107180080080c02e40c1c5030803043d12000162112801401346540000b0003000f0030401c28100c8540b4102d41c04030306416803c20100818590003102c085c050000301c2c1020410a000007043d411020001098561007440010110032058120501c1003100310b06c03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 176166636 1250 176165386 176165411
    0xd0b0f090f0c0a0306150803040303110c010c02030c0918030703120e06060d03080601031e0903081602031b0a060504030503010e0a060f030b040f02120c041d210d0f1a04 74
    0x90f581141e400100c0000c1c1c045540c200160180b640341c10180340e52000060000405a0100c501101c054005c1c05803002e0410f00b00c01112440500c1d40c02951640c00804c4859062904c0d0b07040c540c1100d00b40304803285140400c0c400d1415504040c2d000d40121b04080040081034101d406030260f49150300c03028200310f01c0c0160002da00301c000010054100046107000400340d0b40654040a407030ba401044440000d2180300c852005005217010441c0050a0900400c041210303542580400c0350841d00a58203095000c0c0c9030f24061540c0c03154a80382c500c16000c245c00400c010b4411240180d0181d40c9036a600c1d8140b40d46080c90450190892080f5490301d8070420070060748101800503130340d005400e00d0700c60f21030341842c9102c0d81c05124082d500500c540720080349480b00180c810408001940c0a0104258907080c0d82440414000c1580c2960400c0f10005002500e0b0181e14240150643ca4a070a11a40156030402c80d88000e181c00021381e034441d40c803600c02c0c030045943d02900004550512800f8074480 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 176167886 1250 176166636 176166649
    0x105010e161d06070c031101080f012c0c071e0812152d010e0d03030203090a0b010602010c12052401091d010905060d0503040605090d0b0f090f0c 64
    0x1581c00081064401c2074280d00d402082c99055140740003094070b51281a00d060401899000e488110743d01d0400b680412129400381030054412020403400803030303d17071070700c144c000340030039030480100004170b0004100007065440f128035405480700b81c1710203071110000d01c0c0c800d04400e442a0f011030409210381c1010002810304049640002e041aa231229075221400c2d0140282c1550b442d0b60b92001c0c03205c412221140c1000640d6032024410100f07911100007420055554050902040b50001028040000800c2c0641c00031a009884c600072a0100f20b038a4a8040e500203081e0080310050751501440050385a000410034000c19112904001c10306104d850b60b45c80142808804506020018048010341e008802c500b0003000760350f00c0c4400001c070005800b8207a500900a070005149410041f4856007051056044501e81c0040190315083c04d0000079a00b58210032250b55005944100100010b0b462002040c05035030008000c26450501e4641d950426a80101d140460b50146102c410540d903082e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 176169136 1250 176167886 176167921
    0x308031f1a0a180b070302061005010e1e0f06030907030b01210201080402011101060305010605030f0115120606030f0605060108070302090a1e0f0608011809080307050d0615050c0105010e 82
    0x6061883c1103041096000720b012030581e20991070031002103030300c40a050700840c142e8821070303109002d41580d90300c6500541c0c501c20381c108aaa0002d0390240040945015080742036050140145844c081254820001d5030790347c011510a01c07284c1140c101041003020f03118010b070150415007a0260003240380d440c4030700005030481020b810000110003190559019081940340c0703220301d030021305c07641e40c480c14498003812a9105007800703841010210002aa018401c41800410240590310018a001d06000081e079403031505640d490b588503070000001c0d2610000745d1103a072281001191074504a000034186d6800140400c01703050041060b982c85540703081d900015548800c4861511081c52018000c0b0024560001503506030016004141e00c1c4c1c000350100d0484189095501034409642c3c8003501341c94200d08000d0450206001054206001e040901500e1a4100c0001b070710306d41d0303800e00c40c088a2076640101c0c0456000914030381c2d0002c00f03008103805840b45140804190400254461a0300d811 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 176170386 1250 176169136 176169157
    0xd08031609030206030c090a0f0f0b0d0f2a0e090711030712021e1203010b09062715070b01030602030702030c0114060405151003020f040308031f1a 65
    0x2003040840e0a03034000e00d200005075401420158032841d01410360074480d80700e4000a81300b25400900000c8003214035550109941d8480e44003801c1c140703040c40d003c4064000441002e140c41d01c6850000381000d0610441010004030688441c40191004020001c8021800101304104010b141000340d42c490402043d08106a03107400141e410301407480c18118050301c03100500465034003507030440d8a07500060034800080f400c114170301a00e65151480380d80e104c0c18006141d00c0310003400100305103494040604081c0c100036003010b182101c080300d000269000c61560507106009900c103d00e0781c1c01c1111002b21154152002c2a103405c100d500da00c20352020511000703141c6500007000860300c501c05d00075241d405070290004d0051155100888440507000c90300c00c0e00130751500b030005401840c0001e03d08002c98000d807008080c0000b4010450107507010f4801040109000c110020000d03034960001d42c0f04141d10f88148003443c3e4031480c05001c2d9a0a03510813515000f18400c104c0c0b0000303550084070304205030f = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 176171636 1250 176170386 176170411
    0xe01020a05150705072405240d0c05130f060501020703020108040f0c030803011203140703080411210a060b010e030706031503060203090d031d0d08100503190507050d0803 75
    0x83c0c2d103074119018420741c08000c09031300c041c0c480c420303182965421480c1a80c20b0b1510511035643c07801c1c540b80c0c640544800001d0700f07031072509512849090419000c510a8003400b4450441030312039010820300034182403036440050b55103180e09905482c80c41a40b01600e0309101a111032482c58000801181020300050168400030103020204070041200b000119400800c2c84c0e01c946c0e651000f8082c40e80000740640c08607028402c43c1c40301e01c010030b04448009900d03858030f2843da01c450301d421032074000c043d01094004010180e281c48010344603409041c441c0046005000c1142a89032043c10382d40c08885031030502800907035561455030302180070816122549400a00e8541c0e24a451200c458580d00103401e00c5e01c000b05215030000040303107500e90300c0c4e20317905c2c10b0000d0348100030301e604242c24900300c2600e01c0e040b4864080f51148241d01482e013240c260108180d031151a0380029040c42c01043e031101421420315124000c2060510107800140812110b140f031036085030321401c00d03500c40106040450b61 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 176172886 1250 176171636 176171641
    0x6090c04270603080309061302060a0305060d0606140111160b0c0102070b130219060504140d050105070e09010f050901030809041404060b0a0b0c102703050403030e01020a0515 77
    0x210305515280c0d040010781014032002e41d80303040424865000b511500c040b400380c1400511090b8120301c8981d406540941081d24044183c102203004110117003000b030744802011501404182c40e0300070080980501d091000c0b40514200025240c440815001c205c0d0741c01c540a80040d0850701008842141e4009075820380e100c60a1801c030380240700c0d520000744440e9006c010300400c41001648440c010303109507800c10a0841010814501e500d483c4100000118100801d100140014031f6100000300701408641120860b540c681c5e0070f45904569040010750240124540d514000d1700c281d00402c9504503001700b16051401040c0340280c140000391101500003801200754545074071100c0c20800d03070344130202c086c1030500c0e00e04082d21806000a02c01c042c08000072883c07500aa00315100f00c2ca0305402030081214040c2800b016240b4110501e8508040115664044200c1c46250402c6442552402d503254210f14001d1710b40100c800516045600c560051800204002000c041d080078114002401c0e5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 176174136 1250 176172886 176172929
    0x1050903071407080a0515070507020a150903060908071a01060c0b060111010f0b032a0f1f0f180312030e10020a030e100216061112090a060506090c04 66
    0x40d81984607001c14840d0f81c8203441489000314030001c034401c0700c80d41f4048540300d00da000c075038900035680040e6000e8032480e0104400100f00c01e911008000745e0070880e441a0792503d4100480760032903c1955a6440021801c04109072044485001000a8115100c65040810040c00f00462040003040e9020b91400301365242c1c010715401c401c84040304000c2c800c81c0f0581a00360b01a060307640c0c500b4001e00c5902e10b150740044081c0300e0400c17084002c0b00088001c0c0038050401603555460812140c11504800046c1c03606000ca01128540e861291140001c3e1001400024101c040f0780c0b0008030165032012042c800a0003031151400d64541c28500450000400002e031402c051800350030048140c0b00041d08525240c05801005154100000786c0d0702a0056044003010780c445d94001d41c0c1c1303003504021403030700140643d4000368030760980c80c0000303083c4602510704c50f0344003c2c19500a400c560100c00003a04101a5024681c1d0100040c1c07030a1010741044d454a08c018011400740c0c4551082825050403003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 176175386 1250 176174136 176174143
    0x18080d09030513060c150501082109040203010f030b0604060b0a0804150e0a0c0902310506030f04261605010e240906100e1909060e010608010509030714 67
    0x8028203d40f66807000e030746030000740501400c044c0c00c607100b0120941c10807034a5114840d0398102c4d50708030080c2189012a001e00c0b120400745e0403404030120b1080c0001c40345601d031403001d107002e01544440401941c6c1541000168800300400d10780c0b0440c00c0c594103010072140316003a120b80340c40500f050100da403582d182002c65040d02d110381c070400724940010007081e02000244a042035010b480c01110003919000980160b1080000f1040c072036211401540c02a000f540030329480d40c0049100c80241c0d5150000a00302e507005075044659150400709110501000d54190340c040480154400d01d0010100f1a54849000d02d0001d14040b810190750b10060207420741200f40c1d0103204200b914801190b14032494403110841c2409054001c3c0f180019180020002c1d5840c0101c8009603804c0c0914a8000100740804000f03044d071070081d107a038441285ca034580380030b81d1104c14441c1202255a400c0d6046980c02c40d9110340c84035020780c0c14081030114160010040b500c0107604414116150405444c03110318 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 176176636 1250 176175386 176175397
    0x3070f0303090f021905011d1005031f0602010b01030c02010b010c02040513080f0307080f0403051e0c0a050a0b15010507120c051506041406090f07110a0b040618080d090305 76
    0x1088588000358a80814207081740c1001d4610076212180c6241c020544000010580c401c0640c00010840c00e2305851401071002e0341e40840d140c04d035200d0540410824140b1260a5445240541e4480066001d59a0140100000b0159500c000c0145c61000c1d00001c00c1c544203804080c4c0101c0d9100d02003a01c19443e050603404c102c0d04a01407a070740b800340c40326021043d4021100a400a154035000c0f900c81200c00b2203960085415503a03e03030500a20300d5404c419100c03c1090150f0f006d200300801d03a0b80380e4040c02100b5800340208090070000415040c40000c229000300b00b1075020351000d100c4883c0ea038104081d00e00d031a81060072540461410001620003080504014080e4403404a984a807000c03c2d00320f41d84544000d41d424030103c00c00111003840c68400340d50455000500000184901036032000d0307990300020510380095109085400ca03801c0c00803014058900045000c100014000d090103284021092034507108081069925489801d0081d049018940c0c0e032038180e40c00505104071b040da00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 176177886 1250 176176636 176176639
    0x15091403040305070311030303010f0e130c0e06010201050c0a090603020708040801110d0608012304240608010b030d0e060f0d0f05070206090105060906010c08040b0d020a020f03070f0303090f02 85
    0x81e9126102d0510030341e04c105900c411503421510101e414600d00b0b0100c1660304940c0c1e2503811015090a0001c211070710080141100190b400c01138207030002c910303504445402005005414000e0f803c281c00020700f03544c4002c3c00d0001d0208200320319a00f0940c040300800441c0c0d054a00142c80380003c0c07810901c28070482d031100701d585d17003020503010715201c041004100c5c0d0344110004004082ea40c41400e8242c80464448803d0f0400804440c103103000522070383d6031700c02c0c881c6d400003090159a0320041c2c0740006c4504080c50307040d59002c0c180b00002c824032039001811402c40081c0003040c00c0c10b03001445889403170b4104c1d004460108614141c12516001e450766003032003000c24020000e90741d003d10010300d400c4030402c005115080104e4180134040c4600c1d400365002500d17130801a90b4000040d00c1412941c90102c40d4144100400104000c0420180c40c241442e15000350b601c1d443e04034001e1409401c00c10350751268004120440008040f00d0740c0c0a01d11340c2c1030074003050940950401207800186c003000139 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 176179136 1250 176177886 176177893
    0x91c0c02040f050a05190509060f1f03080c0f06010302130c0512070f140a0c021c0b16030608030307020d180512071505090a050904060902060a02070e01060c150914 72
    0x4100c02042d0005c0b4404e140881580450308a00d00820040e504191990f003404c0d08828045403164078060300d501d5124905079581e25490003036072041403180d01103038010342d03600ca00403400300e0b86072505100e106007080301d01e00100380650450f000203c0484c4005028400300e03944940110791103014105481940c40811403490042c508180050803c0c400c1d18841c00003d4031542200c001c004202c400d80d0b800c5665036442050070119542845001504105440c15803190b0310311100006030f0015505215100c2c0a12516101c20380c21009001d0781e0882d0800c103031641040c001c10440d10381c0005c1c40030500c149071038081c000000008c7d009180400c20781090750000d045803520b04004600044541c02c80d418401c40c41d20f5136880c000c003204e041c010440f04590100244004100601d04002016082170180e000050600d50790b50004160b544891040703400360300020401c10020040c444280c2c0140303a6030401c41e031113050560303810710701d080b20584801c0c040341e0300c061680910080003003460451440390700700c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 176180386 1250 176179136 176179141
    0xc0106081504030201050f010b091011010903170c1e090a0f080102071209060e09060301020d150e071d0103051806190f1116080c01021305010305091c0c02040f05 71
    0x120101c9401120203030007541c00c202c00306a9442c14421032074102e5404902080c10300d42d0769400c100b00700b0810798032081006404d607840007501c85c00b0b110f060b074114071940300c1d01003640050f061640080002003070010300c00024085c00d2104030401035482d82c2d0060885159503100b9008001078041e07003d0b9001100d104040c00b1021564510540c001e103541c90054501052850049200310340400060140704000344901e43d42d800d46040c060b601e50b4219900400141c14100d894940c0011248114100c0c1010051200c040080c4440000a283c10180c149848248540700380e086410381a844010241016500c00010b0140701e040c5d07009000060a0006640f500e00305820100714050100b14442005450902e131105030300014490707c0c507801c04c03c02c120340c03d017540268204081c182404056440324000c01440103280401c0c401024a2000400c0d10b0b540075040000050840320700600311100f60340440d90520002c00c2100c08940594018a0200c540c3c103054070108010b0b00c84600c1c2e50340103c0c1030000f03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 176181636 1250 176180386 176180413
    0xf040c0902191b020f060a1205100f06140708031302030a26030f040602090102120d0c09050603091f020c07121205070c05090606070b0907091a0a05060c010608 70
    0x482c0c140d100781c240d84003418401a58000b072000b480090000750301030649034541d400c60820344040c06001c640360411403000500c2c0c0c89402c0958004403003440f6000740b0010b080c00b00c20b0110300e4080281400d40351280314015020001066403040c0407000c0c001d068040001542d0f52201070030320701040c0d8090283c3e2030303040d038071302d42888914407140389060903445040d500c6800480b145c040e04e100c0c003031640320801da544807910307075000030341c0b1030340d41c0b01c0c110300652081e0700390480c030302e0000d11115400040000c2c0b07000301c4c0000240b2000464008038404c1030208240079040e40c0010f92580e1000c0c420540603c40d100c031380e03c00c5000788035071308404c40d190041040019401c00280403802200d8007810719076940f0b80212404441d80e2103080c2d0014400c5140c50400e100c80d00b01100700913400f50015100b2840d054441c0c49610f4800000c030740042455008500620070162103000380895207801210402c86812824001094035980c1d01074140510408a01905170070800d4010318000c0480c802900c040ca6510304 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 176182886 1250 176181636 176181667
    0x908030708070204021c0509010c030b060f0307030b120d02101e0f021b070f080c01170405150c0a020d030b01050d090c052e0c0f080a021c02071404050f0f040c0902 72
    0x8d88072080f5528100031180268003900507031040d90b4009120310b20700944016400d8107900040e012070b0405654010b600902d032100031511001050110080c54400c9110300c00034500442d030f00342110001d0130400c500307609402d8251216880c1907400c1c00421480c1e0018800002400b584241c01020740310b24201d08110007000c184001507a050703074201c4070350390b4442c1c081580c4c844400c0e500354001855a2003c2080d0702d10414050380151140c0c0940c1c4020402000000381e030700007590708400081d400074907042d100341c04200354411480c0c02e0900f44400185800003070003501802c14070100079502c0b0444802007000e8400f80b0006400003c10b1005201d00001400c40a02c501180d40d481c8220001440c1143d503005203107203096558080c1074803a5502d407a50319031009400085117041036104034a83d1041401c101c48924404d85020b03030003040d000b03241018590491100c211094011407a040034025103580c1c030443d1650110038900d950005031924a42005464655400301e1402c6201103901107190313070081c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 176184136 1250 176182886 176182891
    0x20c090a090c05090402210a02040c031b0207061e0e0a060203120a0b030303010911070b01030b1504020c0c06090a031707020108011409150103021303080d06060908030708070204021c05 81
    0x104075210005843e0020300021803020b44003e0b620600144014000015281c445100350685009884460360a68042403d440400c0c01c14004641c48651511810f480c4019080c040c000a20042c200c1d0307842c0c514054480c90030014850001008461003c00d01030003050301c4048900098080e80e0920f980d1800251070342c000d0b41c0c072000301807280b00100306c542003e4003034503c1040004000d940b450740b038441403000500060b000e1410b5008144496008900c10f0b64021f802103005101811152a00b44102d8a507081e40e00c003c540310302e10500540c59204000201d010143c4004d498031540e031180b107030000c1c000940c00d50004140381c01c4d6420725910b005128020f0300710140300303885554480e601c0d84002242140441843c0d60401d6480c1c0029441449640c5085031020060500501c0e21366054031074800c10415400076202003034001101041428180b11f00c40060074140340072401e0f203007420f04041d100d200e1540090321001d070105616082d59115811a101d0041a1a10110071081c1c000c444000c4c0104 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 176185386 1250 176184136 176184143
    0x80f0a030c02070602031204020a030222050112080301050d03051c0c021b01120f0e030d0618020a08070806030102041d0601020706111f020c06040b160c0b0412020c090a09 75
    0x9050420641a0000030f569041e0340d0710340c000d14200301c1e6420f940c0e849101d0041040c0d81c002c0d41420000090303111450b200650b900c03101c0b072111040034603c8406041d45c2d0180c1c04540d40d13041d5003030140c0c00301d203072030707040c2e03410340e030040f19034076500011801e0883c5c00d4000ea107846010f4522503100903508800302e500c62110f942e02c0d5001c3e68003c0f00c0c82507042c3c60244019000e14085110a12142c010341d00540c094081c3ea250b82c0701c002a81459480c19030300d16001100442040303035807141d05002510142c10320000600d00c2c0c1405520780680b010300101445c1016040505111800001c03407503a940030b4041e41c004d803000350040b8020804025003141500c5055603c540540203083d0041070852140c001d021050004000800c0040000c821180d168840103403260181c40e42400484000310b800c4c441d45004a0041810740030900b00104100c0361038422540e61024415158440c4c40040c0c501e40e9200d9109400080d00d41078030884100590802c0b102c6c1c1110b40d441038140d400c0082255182d440005030360300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 176186636 1250 176185386 176185391
    0xb0c0a05060f0c04030803100b0c0708061f1203110a06050412090e060613050607050606011e02060a0c0221040f06083706090605090f07080402120a080f0a03 69
    0x55034030035140b00394002e95003185180d10400050000ca0051401103800140b1201c0202c0604e81d5480044000e0b0000500d04d405604204810440700c00104580c0e0340044600c00041c0e0181948410241c10b0040c901c960300d216002d00309020141401a801d4815a04104055039031081e81458100c008000440b070440d0341d5840c48000052191140007a00203071520800d400c8900e0310f40e44108003454216400d05003c0055000003c03c15840700c1001d042d001d482100240400e0502030001741010742c140401007248000c7d064010076041d80022601d402c0303610100c0005502c0480c450890800380807002104d91800c0148d1071041042c20403000b801241d131002170b560341640c0c0b07501c0101c401a505031420614642089003c54858104072100d0701c581d114031070621042d008040488003074442503448441f82a81d296800c202030306041a145920804800010219152448000d016900041c00281c01000503452699031004100251460244c01401d0580c41c0e030480586400c1c180c0c030800800001a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 176187886 1250 176186636 176186641
    0x8010209010f020a02030a0b060f0612010e130f12090503030c0706020d0306080a08090a0e09010605030c010306030f0b061c0f02033f041206092105070602130b0c0a0506 74
    0xa01c042810b011340d55004001c3c009215594680c003448400260041e279000e8016000c500340d6584600046c5001c400341c0504155541c0f410f240e1081d42da90042405c24041905000400000d40c9007001c800019404000d41c419038080b82d4080750707101860307040180c00d44030010381105200340c0047c40600300c035480da08a400d64040c0741c6c0d00b2400d40f00e02c0e100b05540d40e800714140c50b00080c002406042078010141203200c50a039202e0012900000595281005940d02c01c0184850f0500740110008900700b03007030501c856440d40c1e50305402d900c400c0801602024001010880c140d4441c0c0b2114130701540500051006800f40c02d10144040c10000101c0c405d100725542842030180074401c4442105d44107005202e8004803003210b00407280d50701c01140300c0c10320800c0045000e200c2c0200d80300e0306038003c000c000360740c40180c0342c01803421070070350207040d00e58088030612a85198000110740d01da40e444040540c40b1141180c61007210000c5400c000044003002c20300c0340d02c201d030009041040320701590456410b034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 176189136 1250 176187886 176187917
    0x20307140c0406240e04020c0114010e07020a120305071e090612050405030a05030907030b0c0910020114070c020a0503060406051608070503070305090c03070306060602070b031501140f040801020901 87
    0x2003000131401c511188210151006603401380c4162201d011001c1c0c8090700c6c0901020341a800c48044541401300c04003d030380140a545c103030218159104409000070440817100351250a03001291400541c10142c03100001801540300e68860f400130011000c0e4113500b11080d02c8040c02401060043d0360018810100e0750010411a0013514001c64012019611307007040c2042c1214180c3c0010a10364862180140010000c1c40030a01d461080c01c000707000c030b52150342102c100205442c40800e43c404580c100380ba040b42000740f56070296001034160a140f55018124400b06108101d25402030344d05010b03081c200428440684c0115104402c0d54100404030001c003402034900040039140c000000b2030500000e451680284c0c0300907040750805e001c40c0c1c25a50700100080c90890075030012211a41c0390803080010396010400c08001e0b000e030219580c1545800c2101e100d010b4040c1140604101d0b40c00c2c0906035203044c41084034030640c510aa400d6899489001d800e003c2c1d448840840d000440156001c50780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 176190386 1250 176189136 176189159
    0x3100e19050d180e040308040314030901050105101718070902120901060b04120221061906050a0b07021302161103070609180c09091a030d020304030819020307140c0406 74
    0x60f00e50b00c1c5034140954545c0c0e1011580503400400880030b1004113005000300504400c0a58419441c1c000003081c40e60404083c011171605d40d084940038044801e10807034243c01001c2100c0e0344034881068008629600040c203510301091a803006d01218400139035041d88a0701c55100500c030b182104000d000450f41e42640603d24800c500c070301514403a2130f500000061405031310440d00c0c1d208000001100d541c014102c0e03802d04030203482e40202c0f44034100f003811455155014020086c601160900c280a2500d1000410352041c008000c0c4585404204481d02d281c050b03050380c9648020b480c0003c85440c4a241141c0320007008900700381f0030310a180001070924800d59604060350f1761031490400e0944801b5155000e40008203201080c408083d402081004152240140d84462040b00b149035a010070b05250a0020549103202103400410080c0007052011003107031505081c940e07001d200010070890032421402001c8000b40003e09a10380385035842e0000640d5200e0b4801207030b04002c075940c0c4075a0101c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 176191636 1250 176190386 176190389
    0x53109021306090b1c150903021203130209150d171315080f060f04020a142a0604030804080a0c0209040c0801050f0402030c011b150606020f03070203100e19050d18 72
    0x83e06c2c9a01c002c4036440e040b103801c04070001d807103401203803580081c9010725081d940040310702d249915409080e020652800c20400da40060110070428103120702400814001000580042d114034020301864604804179000c43c0c4440c6085c1343d0040e00e1a46075004074045590305403c40002496804c003144811580114603030040b4001418503c00d41c00c03440c02e000103500600440424440703028848854454010010000c20820402c0034110510300c0a01d8552000c0c03a00100720300b03501900c00c000000343c004c6034082c2c101f07070080603554440c281c1690840b0082414900250800310613002d0108000f8044c60b402d090b111100700074015a07a40d81d42485e000041100c010b50326501001151040d540110f07055941c15002d01001650190309484450700000049920800c4990303900b8100040c0d41d051014180000800d4051031420005400096484c4140c3c140310003507583d2440c003da83c02c407040084440c00180b15840c02c070740311051308086465a00201c1c3d0b83c00404c81084110030109034489801c0d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 176192886 1250 176191636 176191643
    0x3020c01020f061e180709060906061d210102120a1b0f080c0405040e0a02030706080112080a030f05040303141513020306040605060c07053109021306090b1c 69
    0x34445a03105684841344801505005c0e2242c20007035000090781c014800d0f4409446284400b02d00c0b00c7c03510484808440c09a400541040b9030481c008150703051140c520b10320544101e9a0321048a40c18418004104000702c400b082c640c80000d001c412605034510385841240407210400c0030060070741d8010000c80111001e00009403501c00c1c2d03080c40602640d00e094211152400aa04003500d070008501100c01c0805410090b0b880060300400b14a01008500040e100b6440d000e215075140007019144110300e550010948440443c86482c09413080e80511201d140c00d0806101504150130050014100600d105521500a80018000802c580ca8440c0c2d00540138184480b004c9006441c18000d40001d0304195105850b134100007010784e03882006c0c102c0e500000d005859050302d004204280008a14421030009404401c0381c40303d034284a07c807043c0c192081101107202c000710f100140880104580541e109840d1840200315000d55a00c01500c0001c04d0310255210301c030b400350303c50038580c0400004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 176194136 1250 176192886 176192911
    0x40b0102030a20010908070221061303031104180c08090a0609141204090c0c030906050a0903020618090a0b06031303050403120e0102012a0f050c010903020c01020f06 73
    0x79034910400103041803c41c0c8600c903020700e60000266031300f5103a210348103075011440400c280080d49450302d50480a0060041000c0191001c01110342e02c1d0315000b000640c903030088401c1401450701a0300041f00465120321802d50392904c402009101403540c1d00e603200755030f29003080702c0ca11500a407c018080c442102c001e00c02950640d5030040502210b1000b1030303101d14083c9180f4243e01013009156503040c80d080d403003901c0c2d43c00d2035454001c88003001c6015080200340020440480c1c0c1181d04981134900c1380c5010b580c1c695980d1001d50b8141c0c240d138002900500d002425a910301e4060200005a920403a901c151980320f028548050b541c600c0259548001c1c10408150400140c541d03042c8128460704195080c16a81e071181d440300419100300d4004104140c1d80d800c84e17581e0a03c0742c0c004030301c008030b42018290030405200b9010280f0310910010701c07080e040706d20b0506000301c0558581d2007030500248410440e500d0001d44451515040502602c140040c100644402146640c49042090741c038 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 176195386 1250 176194136 176194147
    0x504022b0605010b0304050d0306140607061b02030c0114041e02030a12080604061e0303030b0316030f02010806120604020103230906070f0203120c0c01060b0d05010311040b010203 79
    0x2002800d0906401116811000c0d0042400140c038a00446000307200d42000340e512440c1a0814508001840100d54105490a4002c5c80000382c1c945628400031000d45140307803a051103240c510005d001d01c40344500c2ca8509184001c02c66540000203007684070f0894028015525a413440c4100c0c400240e4008100003242c029501e0514604140302c0e4123180014100d4050a000361a0000f240400b041c1010004140e401000b41500b094003800c0010100d0120310a142102c0e80003030000d00b40076003c010109600c40c003003100c255400300803d03d00c0d14401c684e080c00c801d503a4030700b010042c1c0300940128086022000014001d2904141202c1e81e4030241c00070b0426640d841e03004600411310603481c800c4004130b03008968021280004002e21444007400200380700c0c00c1a80018198580402d210700c210740c010443c004000e0403103040c0ca500020150f41c226287d00d800b0510b00c0c05001c040e0025410840049802d0050316001d810150407680134401d00310550604e01c052009458154142501581c410440c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 176196636 1250 176195386 176195419
    0xb300d110616090506031f120803071107050a0b130503030304020604150507060e0313090c05040509150402072612150111010e0304030201080a0507020d0807090305070f1404050402 79
    0x2104101c2c07a85860145000303516240000c150b5042600d074003c203000207000800d0400c2184401102900c80d40b0404000340e40640e84540c00b0384401084031080044600148814040403c0044041d103c001c7c003c1c03501c03945400d113109130fa8002d4415001c085084040c0041d082c1008800c480c006d6401500191400d8100f500342d841601240707040c6410040b0400000f40071810600c00c0d04284900703c3c02865660030301d08980c410b8a40e80d60000700c64149800c1c00320303030b42d6600300e02201d003224025150000d156541d100e0f0400da1000c0c3c0609141c10038000142c4004204100b80e8070007230200e092070f1045041111402281581c050702086072204050384010a0140394906040e044e2940145440300c0524100451f4500b5180c07c4021002c0035031003c90140110340e0003404c03071544003d00e0f41003040b1b84c0c54000c8000f951905c80c00105000c2c0080000440d85107071040c14040f000c0c5410008030385d420b9596040001580c41b09111302484446135681e410300b1031519001e441e00560b0010143c40f090343d0502c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 176197886 1250 176196636 176196661
    0x3030801060c21090e06010212030114120d020309090702070303020d1101092a050402030906010e0705071b060801080102030f0c0a0908010501180506060f030a0b300d1106 75
    0x82c0c4038507121041400c40c03442d0745020540303c051103a5910350703020700d0070355800e910b0310004e00140c1c15500a01e45040402c41c108081c0c90450358008541880d003030071700000c900752100d0a81b8800142c054031140d0400c40d90000b005191855080c2d41c6980350ba5583c200403a160811804002c00507080801d42045407841035a888602c60b052000005640d076039940c418945112003504444848105c808410344803141c00441d100408081d00c0c00e602d0f6240003030000e0b0f101c1005024005c113040710b9101040d50144140d007a01d000c41d505c9148000300701c07250844400c0c0841144140310004951398004100e101040c000d403405403008903010307095610341c0f0f1086504d40d04189030103820810411000226190240100e5008103c0c0005400403a4010344070780050b1040284058002d0900700a2100e0303411800d0212a801301c8042070000703040d40b0003000161010044610306070301c40b90b2905102942111188640070350310030700044800c02200e0120035508411100c54aa24682110001428652500303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 176199136 1250 176197886 176197907
    0xc040b04060b0f090315240f10020d1e0c02090c0403020a0308040f09021c05190617060c090a090c03090227090c31140406110319090212100e0105060a0303080106 71
    0x100042304820131400850115640350841314010fa0058151160f516004440e800549450041c04141c7e40e0210802500e0008105402070081110000040760900420107840207940d00804243c1c1803075403400c14071707140d8120b402000b0a4646c051030000d40048607200300e0b0402882c42c2c100f99030580515580d10b00402000b4030b2001d02000303403095140e6100d900d1249a02615007200918074403244203007000d2030050024816030b03448108100d4100d15640b112003c1c0e0803248162404102252020350481c080e007850900290040c255107816004c4901d072010fa8400c461032280324031031030369030101c010344e9500350401030b02d42020314810200d00380039202103540b440a00c046228000e40da03481c2c00c1c1d2012690503819119660700070314103220400c070690243d000015100a0028154241b1803240c07900340b80400150f00d50701c1e07650034420007151a03e82054100200803c1a03940720340a8141f41405413036040700310300281d41392500241681c0784c42d12000064981581c0d132055640c2c2001d9042d510440700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 176200386 1250 176199136 176199139
    0x503070608061908011e0605182e0b0703020c01230f09030a0f0b070807050d0e0f06070302041805040804090510080607050d0c0806030c040b04060b0f09031524 70
    0x100701001c0f42035102405004c10300c21030008110440001c01c03501c003040741c000e80c000c00d1180c418042c0751002c51000354800c50b001340b4120000c2b000d000808038200c80f4852030742c0050030079441c1441c0c0021685002005888168069000c2c0c8050703c010344011035441240c2001d400c0c500040e101c04a80f03210000001e032508bd044d1000c0c02e0303d4001031100080c88c140d82207808484822402c218001000703201c503003141d00614a400c015800b03083c0284c02901e18080c0706607189440380da40894031141d160405c4146400324100007610500c1c00c14420080203507106000d8440c541100c80b03110b4482c2c100c94880c091180346c00c000e0039814242060942000b6100c040d22503903d46c0c0001c0700c040342a00051003510300840417a2600c030380e210240c02c00c40b07058038280d4040100f4000c1040411450f07440100f0905440107041706c00040f204803076400540189250b8002c41d007006000b182440e45450702100030071041200720100e0315a44034441c501200c0380701c200d449600000700204c000b10208405003004100510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 176201636 1250 176200386 176200429
    0x30712032c0c0406030b06030c10020c1903060207060b03010b01020d0221070c0905040b06040e1903032903100c0c0305030604110705060f0f01060e13061a0a09050307060806 76
    0xb200000901552010303002550b218043c00244052840c003085401a20741d0140d9860004032200f6002a4882c03000403902c0d406055512200703241c0070368044801c400b65901400c110b4a03010740d0304114004160f11100c150081d807902808100940c00022103034403807209a80100070300c20121200c40d20f41d05260b00c140008a00a01c600d20000d901400904040c10440c240002c0c249031504101d4400032000e4042d500481c54903481012000b40820044140380c40001c0c444c1602407140b6044000380b00c0d0001c003030800a45050500a0f2144080d101001d0304ca00310110344070550207603248401c030368004e1101300c0401d845880380382c0081d0084002d1948540002c02c0016031031514882c1650301d90101c101210715402c030004103c200e0031882401074100c081044811910743c100741c3d02900c0b4a440b4001d1501c031f001f203104070030042c4c40941c0040c4080c0034100350380e04107401c541c0c001d070707000707070026a0344101182c0301c00004900342c2400503040040700d42c0f40d512001d1940350502800b550210301030000d00c1416 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 176202886 1250 176201636 176201653
    0x7020f0318040f021612050412080c1c090528120501020f04060f0315050a050105070606050315010f080607080a0b1201050403081906120201030e071205030712032c 72
    0x45452001d404601c19100315100ea17403d00e031410340000203c40c1c60450502000f0711080c0040701c04c0104103c072840d413189584d555000865003e925080780e40301c19481c19650719411696503540a00090200d0b44140e8141c48050040000720000d03001c6003800280d00000c84000700300c015034100504861501420005140440d031407000303030f0140e0091300000e010401004040e40a10b51600ca4001801480421b010f4103c0c1041c0000351041164415241007041c007040760020f0005aa1264000f0603009088640c03404001d81d1980d4840d00920560350303040b4400c0070005650700040b40c568410103040d43c0d901000e43e218614240244404180030360070104841038a0b00c07880091007514001da0103602e411840e0300d0030f40c134886484061404200007903801c10b007081255085103082120711560908004c20400300b241070303052034081c2a6000742805107851480f102800390100041070424041c0d01440114010440242d0a5a500700c90380e240ca1082400850b80201c0d442205140060b004010f888012 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 176204136 1250 176202886 176202911
    0x3040b27060403020312090f060118060503010204090e0d050a02061914150a050301060303020613060b030a0b060103150806040210230d050f061c021305040303020c0607020f031804 79
    0x20201c0e001c40159200081c1a0401c00c648000a076200c02011f0090002c0d011070b040c00c64480b20180302d0070a01c2e101c04203c042100056030000b1000d0800a0b0085440d1a0384028490107445201301c1c02c0d909004418000303086a03c00c60445481c00060780003003c00d80c0301c002245c250020024401981141c0c0c0f690162181d16800801c1170140000d940c110307a4030305d542c904105010140d81d0006220360301d03005041001035004200c155000c220000c500004111034140303070010306400080640d04d4050600024100500600f1460092000703a034204176242070195504040030650284403016440180043d005245c0314070842e1080807146800e08003080d4140d04d8080140441010b0505104041900d0404c0a01803013480c2c5e010501c3d1420880c9070a007840850120003018070b40c5030395080d2601c60340c3c09640394111a24040c602c0c0d504100118036241c18010300075040600e40201c18090702000c03402c003d200107100c02c225081140690300d000d11080704480b52890702201d1540154441300b40081c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 176205386 1250 176204136 176204143
    0x90b160e0a0905090c0103050709060806120105010806041401020301050105070602131e0503060c13180204081506100e0303030c090415030605270c0904020103180809031203040b27 79
    0x2e0110304000310740c0c1e00b40800d82c0d6091101043c400c604251801c0200100303079a00c0004c0c14112215400c00219079160350b030100d100107007920b00c3c907d034541c00c2000010300c950000443c41e01c20740c02096082000a001d128003800d0703100a100700e42c00680c06010160201e421a801130a25020403000800e0190355a40302210203445503000000d50b200c0038104100604083c4080340e4092420030714145000a402d1a0b030304c85012600a1078202e80ea4803190182d5012558111005004440200c0f040704003e096601c00c0181c088543c1d80c020706549070f4030aa01c3c2d0040e00c0c400d01707168004000e1415542d0300d00d070481b415000030107601e5102d074607641ca0002c5100b509044034051030142c0303130210707440c9001046010340d030204818000c1001ca0000603444c04100104080c82d080c101252400d40c2130701c803400100c01074000e040c2e814410042d04400d0000300000f580050180800a80c251042c4000c00e04244909010882d4050b1007815501c000801c4220800c0b03000030b0f008034241e4900d02c0180307410b080030b14 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 176206636 1250 176205386 176205389
    0x602030a0e010806061c050a0b0a030210050331121b03271202030d020d0909020304030e1c110d03090e060406151706101d0f100206010f09090b160e0a 66
    0x140d480daa1012302900d804c8a00a0692208080e90380c203004034a5036004c5213000884840660400a000c00458103158084408440b55800e2940040903600e80c0c126250880c500324100b00c0c0c43d4008420040c0c501e60040602e807000b80040917200c3c1040855450540784000c41440c400010307009080d401102c140414481800340c03a4113081c8054610191040c0740c80c00f0061540f02c025580079240d800115544101240b056400d0003001507103c0d03e95180540c1c0019084000541c40640f04403c80c030b007001e500d40500740b07540c09190b86144610030f007018002440c0e010030000c0c00081e01414188039083d80d010305c03260005005000001c60681d0f03046410660324200c1861400600d4130100015013040074541c035071700702004a8904844c6d50300980041d003038902c00903072000c82c500c080344070074074503034454550504400e80601000c004080c5211b00a459060034024004420800c2c2c0c004228142c1612401d400c20741e0104800d8010b460750103800f00050414102502000455000e0380500e4480d0b48a140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 176207886 1250 176206636 176206687
    0x1005030a0e031303080d0f020c0a030c020f0a0b1c020405010c0602071e0b010f0602030405061b013b0105090c0d050a061406040507020d230c15010e010602030a0e01080606 75
    0x5861b1101c0109010a641800424a02850050040118540002c151000c803103030303d8100030300b0049540c408114182c406000c40c56000c1710300307040040d080f6215002030071007213012800280b00c0c16115804070124016030141d07900203a5100340000016416038010042c490195280c81c4103000e21102d02c03460b0241d0301c4004c0310f0f20b04200c001003102c0113038032910b90003410003400035600301810500414458000e1402404c2900407001403507040010070760007626200a00d841180a0310000c1203580a50b00282c40c200a032080e020800100d004811301c52a8059280280902550b16030a0304011124000e420282c41c2d6015590020300003c2c031600c10807110001c00c211094203032500004201c102d480007042c0c7c6081d0b401a41d45501501d43c041083d01c20148182d040a5804100410b9070102d40624440d0380301510441d9019441d40e840c1c481082d0403960100c110411316a01c4520407610303401644d03410400304400c0300c0d0041003580514081031f40081c2c003420240c01c000d0030b03111091501d41c02e494850b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 176209136 1250 176207886 176207903
    0x616021005012c06010807051c0908090a121203090c090c030f05070206040c0e090c0d0605150a1508220b060a09060509010b18060304050115051005030a0e031303 71
    0xf4501c40302050740f079600c100010105101515041c0000780062130010501c4040043c0010360002403c1e004080030031720001d0360030812844400e45001e4403c1d50200f504180710340d11005001680c1003e04442000c69a404019081c5c04081988140c01812040f1030446850701d40c2440418a2a1144944101700a4542d0041082e01c41c03800c60004481c4040d000d002103401c02c404101c08114207510740412103c081032400d010742d0701c5002240c02d080c1c0c81e14180d684010313541000b40038070403160402c40c01800d4450380c0c2803104040000308240aa070a21480c0002c01d02880007030280790040e5952907001090b070308a044a80084400b401c4014000c220460f84d8881c0c00d4240450b5040c00100c110103407440c00c6080040605250005a200f60144900036000b2400924800102103241507169144c4018007165240c0c18140b0f81680604801c0118940b0208410800079152074661202400d000f12629001d2660b142c000070303000900b6038201d041c600c5100c01c00000141603c2c0310710b807030029030150021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 176210386 1250 176209136 176209169
    0x90102160204330e2211040b191401030501080a060203040303060e0a0f050718090506030a1e0308060d0201120b01230406090b040302030d0807170103060e011b02061602100501 77
    0xd01e1000706001c5c182d100380703000408108504114a02c4035071880e030340010009250f094000c001a0260800b0320a00d900300960710051000d80080c5141072082d100e65a005103850a01c0100440031120248100c1940368810383c0c4802c007154450f801160014004d20300071500d00d0302d8510b601070f0300b442900c80c030920030f50303070003800c03814145912a00f03030400d01a18140c1501c0e00003030196038141d003650154504a03075894001c86e040d56010001c00d14001d42c0020b00000c2060100000405120201700680100302d4410000b0201c0c0341001141440b103605850f10031001e80c05001d1003004042c1082d226062012100220031441242c03610844050020b070100d81d6a0707810060001d20800403a440240026070a01081c0300698004c40c00841e03041151900241e20303910b404003201c0e849408601d04000da4114000401030200540100801002d410028080031015000c000d08200c1c0c010100001038000300049451400050f0725480590010310440f00e40890744581d01046400a03844001d0080c02d0740714 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 176211636 1250 176210386 176210399
    0x6130b070e061b16060906020f2404060902040f1a010207030209150a03081207090e0f0601082e0806060604063f0f0509010216020433 59
    0x541650280030303460034640940c8000046400c601070030781c5921600c103031144040d0690302c0811014540160181c105125280e403134101410344506406004018014000e4100381c0150000d2000c10002503422120300b41940070140704109072010f0022039038583c58400300d1025a440380100c2050035010000011a035120a07038810b19903a84500360380c15034004000410150ba41c001c407065100540e0014003c81600318400a00c003492550401440c505001c00c511007455202c0100c0e40c812080d585440020302d490f10804000c0400498280010390b05140c0080c0e00b9520030344030180c0292450b00a020110011107540006083c2d100d00301070b900b1030016081000c08030400080c0c4d00141c054030070707e280509080c0014021552050008140c14941d078504941040e0250780700003072010005000100300a5404840c09010503261000105042c0b1000c101e1011040c03003150341c0598090070b540b01651480d8207010140140500c600500300c0300d88500d8a5a249545c22200b407022a0480341c41154201003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 176212886 1250 176211636 176211653
    0xc09060f0c060a0515010e01080a050618090313090219270801090209061f14040905091005060a0f0608040f120804030f05070b0f10031704060908010b06040e090109050613 75
    0x17604104420781b400503140d80002d0f00303d0300030390366280100d1a80d940d9400b0460408209624001600f0700c1e800f00148000d012000d400b62101240381098003507550722104080e402102102025511001005107045000d500e0a41c14000c00400388048400302480b80e280c504c2c0341da40301d100c250351074810341001c43c9002c00088d50310450403034901c0210041a00607003408420030301207806000000c0e19004020340903200b581d00600c400c040610031803610310500c0d521040c086801e0802d080c00c0c2400708109240c801d48040981c1d102540800700b00b03150080c221200d510280056400d05000c4400300301042504618401003011500c0f6403440307060616004200d00b103004041c0c03040081c10f105c1c01c3c0020701400f141a42020b43d0503683c140350785404c8034a128074a0310307a1000f0f11a0001403044c0c00d8403140703640a03004880e1240c072410f00541d6034407041400d98140561080d48500c00300420700841202840a64102480c1800050040c0d003d984941ca0000107859002896042c800c05c0001c101c401c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 176214136 1250 176212886 176212921
    0x90516080c0a1505040b18040507030911010905090a0b01110a0b01030203070e09030304021003022206090e010e0f0c0f07031725140904060308030405150c09060f0c060a05 75
    0xc010f1030110321031054000e0180c0920f0003001300b003c0300022008240d490051900000d1440104204044e040080c0301500400e0031601c1240e903580c3d000d403480350390343c0203040410442f44094112001680d54000c0703d4001e0150072200303030510000400703082003904100410800c0034401c18042000d035045004061074541c8030351010140003400b0080000403c0007105582d00158103440500c0c0038a40c01000344c0281c010202d044901c62800840c00141c81c01402c0940c0803a0010384030030305016100c040940710200309010340c0c1d41c212202408074103100c0c0350b0384010364015039240303040b8241141c45290340f80303a6100504c103a0009004030001c408100c40321241e150012101c01d048100071b0668120200d00141d01e01246003484400c8042d00c2c0401103042c106d41030300c00c0045c420043c40392603140100c1c1c283c00640d010b4840348030360307500b24880020303c1c3c002d2409400c83d1103803a8104500e0321304018066220307040060b50888140040c00c10f03c41d0401c900b501855040c0e901040e2464286004204200c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 176215386 1250 176214136 176214149
    0xa031409011d0a1e02010e1806100c0b0f090c06030c03010911160308060a090207030c120e01090308030a0207060501060804030f050405060a03020c1207030804050c030d0e0103090516080c0a 83
    0x1821120b8001040c107000e524940d542c1113100c609800e640c2c0016501b034085461800e0308151a181d014442035104090745105003402ca41e203400c044803584007101c100141050041c0a0010310340898100343c0c5501890343c1c00102c00301110010390021300440d61681081d103402000c0d10003c0b005204601080c059910300c400c1c80c941e110f01b270180e400805a002d29403c1009014084001f011400300d4440c0140500075011410b020f5540b00d034203280040c8092458402a46c104410005580c481886981401007050059440e0701869085840705c40042e40060001c1340b80c56401c0143e103001a50078001c3ca0f0003080f16071a01180e9141c141406080b9004c0201b0240401c5002c0000b400300b50386490640e8031030201803a0040c0c5a64000b1300701860004a50f1212004e058081008820154040c00d1188101d100f1000d4030546407a0b08145542c0b9000080c03220045444001640410b520070b911018249020700d080716002441400500c0b10501c107500a40d034541c101f000000c0391070500c1c402d40c1005004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 176216636 1250 176215386 176215393
    0x2100804051c090b031f080c01031d0c1011010c110c0d0c0902070f0c0801021308120301030303050603030d15081203090303060103111309020d0507020c01020d03020a031409011d 78
    0x290b20740082c43e4803414016201c4461022001c00c040000c604182200a082c8a000c4108681c40c5c008055482c0f03041080c1c140001e0074030304100c003041400305244000c60b070754000406103400d002c01080b982064613005c541c200034520303090440400003409036018100783c9031241c502c07c2044c1c84e032060502d03a00310741980c0111088031998000500e8101d07207000710340d0040001615000300f403070300000700610a45e000c0d0882035800000702c1c0010065004080100e05603030240072150792074095545615210040741075815040c001000824025045150302210040543c2e203400c0304a11840101c500d4208001c215041c115414840030740b081010b440e004111008d107505615103454036039500d110082070141019150f040c200451030303c040549500080301400d100007281c45420200c000d40081c855500c1245c18407000c5a00d1030300100304080b00a02c180d020b02926a00c4801c141d02a611000300d01e801c05a941e21800d54000b01c160603a4020014100080f0f4900701c100c40d060641000050b01069a42 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 176217886 1250 176216636 176216683
    0x30412030609020702090f0903040b0301080601090506030d0e0409060605102102180d02030f19030f09030f0b040c0b0705031308010b010504060c0c0b0c0c1002030915090d0210080405 80
    0xd0b070311b102595100740c45020010b490350303071094801d081d07000e282e1000034110400720010480301804940c5038180e84803410300f08495070354801050b41c0d504820001c4008103209203008541c07418150004c0a034940507035800300303480b9035a0002c07581c00501c50300394500095130003031320200080410b07040d1811110301c00000d60900c4406000107501050884a061040001c405c100003103440501420754080b1006003640d0640d288009817881c0c034200c90707008900140c00401042011405519424240e9400030001c44404403e80c1d9925a590006003058503540421880050342180a04c0108a4035100d640650385030044100c1c8090b0300e41282c7c01a8071164140400e084051741d000041d1400c0b58600d281001c41d50103142416003848206d0b0300301019192001540680504000801c1c2105550645802e03043c1d180c84403089803680a180c00e81c40d40060001850307204078252601038101e1050042840d594400c51340d00140071000d0666101c800301c0c21010400c000d0010a0100c0c181da070030740e160060b4011 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 176219136 1250 176217886 176217889
    0x30210050d05071d13090b01030c0608010501030507050405010522120b010504020702061210120b090d02010c02250902041e080604050a02060304110a180f0209030c010f1202030412030609020702 85
    0x200e01084c500800f000b8280000036030540d0481010f0715003109010766907507100d08040030401d41c1ca01402002c1000c040001507654170a2007504c1c803541080d070f685070402c0d0a0000444855010540c60004240b00540c1c40924210702801c0701c008004540480240030300c50310f000c50700880140d005912852050091034003507165101241e118200c0c0d07e07448521f80d034034904c8502c005095500315040304202040038808209004000c2800b5441d600d0454145501800c000c900761415402c0110050300044544105034029034100c8e04e289908213090007806849200702000c80c3c02982c4182c1004000e50811400e41030258606070103020700802800051502d40c60b41540d80e21030740d900034000c490000010b0300707010b0248001180040b0081010b5030240d0b480c840c1c101c0801400038105482032a00d404031030840003d100702d54182c20041c02410518403500b00543c8c4101c40800c8a03000d005002074801c140700c0fa1480114495841010300d484401821a40201100e24940041c0c906078070410611000d03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 176220386 1250 176219136 176219177
    0xc0b31050309090612060106030b1507020a060e04020c011506110d0905010c02060906030a0c03060510121d030403050106060320070f140a0b18070f0303030e07030210050d0507 77
    0x5600036910015961914400309017202201441944640038407000460440d0385500088020441224903c40001c03040003c01c41920540b48001d60001c21440b0412115019030f0f07206d145440014401810100030b00b000c40d0943c0e8004400500c2d2500424040c407040c0e800990451202c11160000d0003481503081010781018007a0103160305100542c071a0340c00b195141022030329500c80181020752a81021120a00944021a501c0000c82d04001002c603d07030804054007941126180e81d00c07860201ca481d911001030804850f00c5003090682d00e040d4124a004000130070042d403141f000065010b107007050040441d9001d8110028035a80c51a8000903000700c40280c42c419034002020400480e541e280485200b045444401e11600401d4184018845030019a0744500300940446851081c0103402c01d8503180f041c068001131041b4900705001180c0320790300000e00004640c041719801354480d000219450b62820001e40081d1001a600a214940b4061190040b03007600700303846003108220303a4401 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 176221636 1250 176220386 176220397
    0x12040e0f0a02041512050a0b18090f07180c08070816020703061107061b082a0318010b0102010e03220506030406020c210403030309030c0b310503 64
    0x203003028908003107a0881c01960481d001445081c5400c5044d9110b400f002d00300150582c2411001c514110008003907500301c1c00752400c0044020030141d0070441d45948001c282101402400303141c030480c0c60082c0c6000b000c0090074050070906c03000380a543c10b1010381c1c1c07050704ca40c000c9600c04c00c81482c1c18450429009000070b40c015141d02d9001c8a2002108003ca1508005500c00303442e0358105402180c3c10303460b11005202403070040d00d06001c1d200b0f40905c1a01c1200600c2203060020f001c0000103110840713031120903207440c2050462030b0720901080d20b828125410585d01051503003880381301c01c030403a0703024890700c65010001e000a029603441c2c80301264483c00341603198101c40704c1015214611001e070300c6c1110003510000b04010f0f184d082505114000b500302003941c0c0850b200340341081c00b00702e807204150912002c1d452071240c070f00303400d65504801814600c40d040b024081c4a042c030000007213044c00480e100d4442c9502e150a07035040c0100116900d0015000d4400c0c00b5404180100843c0f4080125003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 176222886 1250 176221636 176221651
    0x30d020d230706060f050411090a090e15251d090c0408030d0e060f01030b04020d080904142a0421020d05030705060a0501051c0615140312040e 63
    0x31100c1c2000c00d1000c214481e4010041c01103142510100d20036000354158000e0345d0095904009860740308004103030342d1049900c00b542c030100202040005103080d030050130000307114400760340389200504000c410381e140079107141182c15904004c1055000948540013004140c074030340b100f1190103417990004020310701d8944a006d80032500005400402603402c1b41c0061010208896542c10f02c2981000281008001079400d401043c0c00b0802d40040360604605803a00981683c550752140e44c00c02020001040048a44800902c403503540b5540714890104407250545514813a86815000c80d00015500d58800503000c400c01d002422146d602015141901c182c62440780c8100c617a402c540d80000080c1d60002d61088051000c03408104011001d000b40610880481c2d4a64071780c1c00701c000689000b4000c050b000561a4403031320401001c08941c0d041e581c060f82c000560311a40d150300642849041d0001108558444c10562483c14100900030174445a28042030400d810045004503170900a805032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 176224136 1250 176222886 176222927
    0x20a05030406090302011d0609100506010503070e03101d0d020d020c0904021c051606020c010e01030c0c02090907050906031b010f050f040e01060810060f052506020405030d020d 78
    0x40200b6000754010841016030f5547c01e0130401300c149119560b000204c407000e03040d00440000e080d04c141103010311401240c0c1611914103543d2580404c541200c5040c45495140c4640f184c14040d12a0b60b02c500b4695070244d10720303040c01c0740981a0303141c50320308807079000011940200c0320302801503404110360192400484020401391076a00004500e02e002540400071265010401001c0107000076605a404c00c0300c640d4001c003182d46004c180d88400e8000c1c2c0c0f41d4081104140d1001c00c941c882e903c8016200d801c2d0410340074242440c0c0208030103c01c22502442c16500010082c401071500020142e031020f070480080c044070764940d41d903c400101030b001d100e050110f03190f0201c2c215401001541d0000b282d8084a5446076603ca1494540500c04c4c418080880c41e0b02d00820002e5460800d80702c15180d241c2c135101490012000e0442c1e45612102011402940455582850b102c0f9540340c14100703805000d000d070311503040900305414200403021944c00c0d0350008548404841d000001140208958843e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 176225386 1250 176224136 176224151
    0x30201060b2a070303021002210c0c0f071a220f140d082a030c0303040b060607030f0509010c14011b21110c03030f040b0106020f0601050603070c0c0324020a05030406 73
    0x2809a0300052711022141d900544200414004040003518802c200f1034115480c03c0171101405032940d105010b4a03990480c0c070103440407140101002001601c3c2400200640c18020510900100b555500a03501d48201e4036010440c140307200100e500c03c1c10701260103414200755562060107a1040340b0b5610301c4466030040d0110400c0e030750304607411081501c20540c0e5807142d41c6410a0786075881110201e0388102c1500220301d1f40c0c10150143d0340c0ba070394503032140045200d001c0d10903140341e003050396900d04004030340d5141d4001602286004003941b103c5000807500c226014141da90058840b2032482c00c0040100000e100c0d10849180003406003411400000c2a40f0b540790044004e11852203503405034400001800220020b108400b4419801400c0c2e41009076200c880c1203848031301004841c0c9903076125000520a621700f4400458201515041c403038032240d0107940381d48a1300000d90043e518004500b03450410503821642404a494410321b007145440d52280300940706001c00f8002400070340c0e07034100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 176226636 1250 176225386 176225407
    0x302040c1107260607030b09100e070e030c0604030b04120c03140c03040b04030f03090905090a0b060d0209281413060f1d010f02090a0b07030201060b2a070303021002 73
    0x25140180001c003c1910070602c0e10305400f50103400b040380241c1c0201040000516010501480c1400b030315660711102d03800c0d4a85510031240d030a41c0d5030b80190325000b40076180400d5a1610300400040d80f061032071102a1078141824000c2081c3c511001d0300b403000c681c0310240000e81c007101840e404202e01800c20f0300c804407071915515600854105441501c00041c003c424409100c12202c052071103940c0700c0c88481d03203910f205020b40b18282c1d102503060344940c1d81380001503004854640e11078400360080c7c0c01d803141500000d0310000c00f03547c0016030500b146100b0103000100b00c2100c01d4041240c0052290900c1c204c1c5054418000414403a440300e6186529810041c0c503820082c000d2100740d40600a040640d400484078400e41c460908a42d8a080d980041030005030003584c00c1000011706400d5228600302c10074100c1d50043c1c5c811001c55698060208060340600c002e802c014500b0441916424802c20103104c200c815510500c0c00c1e42c0c07201c0c400300b001035400988041034042e03002015880d01407425 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 176227886 1250 176226636 176226689
    0x90806100303050f090306151215011802120412090b0a02060a050c13060306050415080309060304080c031603090e1504020c0a0b040605041b0b0a050310090905070302040c1107 77
    0xc200c1941405400103211144081d07248c0e0b8a10b107101102c42c441e000c01c0304180d00d66188070400c0c2c400c0c178009040004000b0004844003150b0100310642006d4500041055030500155080301c0460301d0b11302c2d0424001c801030703000e80358901130102d04003e2860880d440302c0107559140000c1100ca44980c80d20002180ca072580c605450705880e88450b20300c101500e800000e00503007428000d11303004924000b07030140240c0300d680b1a00221400031014510b8016000d041c08585d6000400c180c50140d8104050400c080003040280f140d8808000c98001421003846c00421440256000070141d00010341407080d1015588561707010b1f408201d0b001655602c081d0f10982c1812405035000d001d00c7ca1800410090190359008244100d02c900e101001411b0b048800c580e01c90050301640175119000c4c480300070300e58000ca0046811038604036041050f07a65580628090750f0440e0001caa4030342100c0360400c2141403501540c1c0300c0058509028030500c07207400006503505140e10403000c0003a0300f414103184407114070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 176229136 1250 176227886 176227897
    0x304030503031f051305070e030c0a0b07020103180f0309050904020108060d0311010c1211121f120515090706020d050d0e0d020a03090b0403020915030c040507020a03090806100303050f 81
    0xd880f12100d1744005110100408007103900c040801d41000c0f03401207170314000c100500101802014840c8031801d28030302c400d09400c2510220f0602d40d07106049850500c49010000c090392142c000b807000c034102450000c0c080112a4011402001d0078001e0100607038000340404d50114064656914491103400c048944200e503d03081c45585d440c1079598041654011007029903502d2510b000d1060b100c80790500c1203140b0840710f42201414000021815598513030b21008086130030b91382100f40498031031600f000c0c84840000c0464840e4022030701c80700b03d103501d0704415030b00003d414040c24a6528103c4041c0d01e8202c002100030411000181550209441e50322040d2664520400c0b9140c0f140e0a5501a544022070301050740030070500703040021002141001c88080c0c9038040c00743c0d44140c40722140030351010403408009038140a541011007068445100303840c414006640101303c001814280034003840d9080d00720070b081d40c0100c4200300c2c0c0c44800103203420031280c0c540b924030341d11408000c601c078540c0500c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 176230386 1250 176229136 176229139
    0x70905060a0903030e0901120b10030203010609020d0f060806180a081b060c0a0f050901030e0609060114030613170c010c0e0a06051204110103090204050a050f07020304030503031f05 80
    0x42100d2181d80e50144002082da886500c80040202c1c0400400180da4024400c40e0484400340403c1d100194203c00010b800000301150503001d80d842e540043d0942e0b800741c021041e204d5002c110120a0041d50040c60b400700d0f59482c04001e00c40c28864042d8450703400a0050440a101501b071940700d01042041c20020368002d20100c3c3c075030f05407605c402d4110341c843c20810314610581c000318200c0c0000204681140b03500d034450810b4540116002d81300c40e045951514181651080300d810500800d0000d644074008000140207658100442070750200420500180240d10101c20030000b4200003110b485c200382c10445541d0038582e0064031030454800e4191070300d02c0b542480d8a140c0d800d030b002081e40003406400c80e042d140e010f845220845041c0242c0e10180c094949480124000c82c030301e66404500d501042c90040340218071381e00428207460050310f1482280f40c1d034000300f101d1880103004ea1500400345101071171409245840d201e03541e0001620300d0b0008510701d01040b1200100e00c04101c0101ba0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 176231636 1250 176230386 176230399
    0x91306090803061503090a020d0f0206030a0606030c022a210c0f0904050604021302250215030403140904140a1a10020703080f0d090c17010605090a05070905 69
    0xc0c1450324800d290025102c450148002c0c1188103610390303500041c0c92256008200a141303001094081041c0d540d4070000540300d40d10842e06400140c3c80310002584200c030000c6002c64000d2030980f0040032030708003804040442d0400c085680d00c00b030900c49041e4408803d800410650365000c0d000403248500300d60343c00302c109404008011200b5000c942001e0340c5c14210b0705440d4401c1c00d0018004c1041049500414940090000030b0040c41c0111141404401c050401030030041c991019454401d081c1c182c0c400a03610842c0d18504618241329542c1185602000c07450941c1010f58010340142c0c2c89082940306060049240480c030f40381c507805803a8a1004506103101400c0a9040b1001081d42c0c101303c0b82c03c80403a0400103c103041c540e00d44040052181d005150442c0755454458068000071641151410100012452400381d802801c2040d4021240500d0241c40c05042ca5880c4068110f40030071641049001c00080d0307104004560f100404800105042d0f031010700131a41d00007541c20141d4800d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 176232886 1250 176231636 176231651
    0xc0c0402071a0c030c0304020105071104020406030b0306010909050606060a11010f1a030a02010e060c0c090c0c0706030b010c03050a05070b0f0615040b030a09052118061602091306 79
    0x40854910032082c40c10a00992990326036101000244c80308996201c1c5200041000c03d005500c244010501d8074050001c0d2580881d05400003030982c4d005602c00c0e00003c0e02e0b19848030b864a001d0100c47d005040d030800c100190381d2070b41c1d905c41d02d454000303000074450340c40070405050850041c00c2000300c00b0810b1000300034005521802c50000c1010202c403000c0c081c0c2410110300035080005000d14050340584038111068126000c1090703d5102072840121400b582d82c0d05a0b240d100e00c1ca180d8011640c8440040c0c48512550381540351852075400038007058182100400e080e60814195882d00703815151403541c422030000c060342c80340710f444e00061916840f481040081180321190f18002c4c4011030341e0800c0c600b01e110230b0042d1400b95000c0d9a40c000c008102181d0030039682d0f070101d0400c1f80308030140d17001e850008041020310703a14440c000d13000c841c1c00036500340140d107290324107121a01d0817101d00b030400c0054200c9030710755890404002d01a00144020427500c2d80c03040000c5114031f80c049401d00110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 176234136 1250 176232886 176232893
    0xf1e01020a0501110d110a080a021309091424010e070507140f0c100912020a0b12070801090e0a140106081009050706080105060d090215030a0506090c03060a03080c0c040207 76
    0x354801000940a1480c14046c2e242c2c41080500310b45010b6255071f20080144c0714112410000e50044000008008141c00c0001c3c01908070b01445c4c040500500302c11402a4422071070318100f07c6109120050f0344003285401c08584080d0100a0644441e41c0b00c0c2c0c10683c0e155001980c1920172508050311510340d4030070b2500300c07140004a403803e2503a10030507950400704640c20b11a600150541c07490100d8103a0205014602c0002c040d10165030002302040700d0035583d6410039040d5400340850a603d40002401c203e045a084021140141365800302000a0b42c0c0c0c90600c291a4003164000508000504824288881d000d40241029000300b1003500c00d4001c000c1c0e804001098002d800311313614068503030005401c9004800300d50499034081c181c0d515040100d01403400505441508903030101b000008040600c012030003461260894210015880c2080340070000d071010010b01c51040340e0820420048140c8410a1100031254854003140c1c58250110a05d0704200003011000d030030900c04203510050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 176235386 1250 176234136 176234171
    0x120f05010b06120702150c04061809050702030a0809070e1618080f012007030c03030e060106030b030c1f031808212a0f2110050f1e01020a0501 63
    0x14072583d40880c6c6454034130b205114104072084614148900d024401008490300481010408070b45550824054607141c440c0c5e002103900640c0c09800687c00403540071641900040c0040d003000850004202185c0780980340c4107100c100525408254924801302c041e01801400d0f07041c0c41001c080f000255050301e90410a9035010410113801d419802d20221003100d81914103407042840c141032041d0329040098800781d511880b102c004404056a400804280340000d0007020702800b01030340d02058460394003013010b2500740d40103041449042d4011410301c0741400310b11800b006034501d0401088042d25005070101030150450007030070344400000c000400700105c04a4070840c002c54002d421442d00c44e81d2421a12096540381c4c02d031282c1007200408220305542010b81502c01800d00960316202a2000818401c46004071a1824011600c2400020b00c0380b0302c0d242c000b80000b070b120365200f43d00842c00140191309030b40381c00130000001c4c020440540d10070300ca52800c29400c4002404108043c2c25200701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 176236636 1250 176235386 176235391
    0xf16032a06081905060901030803040305040f0b03190c09061b021201090b0106081003080f0f13030c050607020609040e07031e020a060503040506070f021f06140901120f05010b0612 79
    0x5443c85403a0324a2011031988521805003101400e210803980c00c6594180b0320740d0010b070098082c000240300005150f0740002a15001d4140e01c40c1c0d45460f03017011899004541640c11041c0a46420031803810302c06075214a516048070524500103030450158946d181c020500d402c1c0c060b40101c0b0032048010020015004400120320079040480355070380c0e400048a0b40e01003602d0810024620f640204007017625400644506e9440c200d06601e0203030f0402d4803c00c05c0d80881d00c0400a21011300040052089040622005101c180c803e5490101103a000456900c80c42041c688103e03607511091910b12400c00005000d15401a00c3c91091501c8102808480c84620800c91289031030003030202d5054802d02c103aa0245500100510440d00c5003001a28600100801d0900314412401d40880e00b00c91408001000d10f41c12400044890520085e44440721000c0e00c264010290700c03004110039020354034401c04964007d41140c1106c00c180c501180541451400c0c20b0703005001140541c0030390500c2071102d0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 176237886 1250 176236636 176236651
    0x403020f0f0a060f1707080618100306020c121201080609010c1202090d0213020703030f02071713050a0311010816020c01030e1212090f16032a0608 65
    0x500103002808001036880301c4030000307402c0490084208030300d03409100240c000c60a24144505c81750f9100a044190940481c0c070f07180011581420b05c999418441400300d60101a013180c40c80b83c1c41e00940300744d5500c507a0b01c03005000560004034000303500d8080c0070945c81100200c0030960740d02c000f13541c001c48510080c014143d180c0201c40208041480510a42003c51034544a600700c034008480e01d84000e401210390960898644075102e00140e54407156003981e001b00350401600d40da040c2c14010125440151488200d0784104a0100441c40c2d50a2513490000405461951071030a45d00501002d80aa03101d907411015000003c0708124001d0302c010000c0e402030b40c980d1314a503609da8150074100305800904000d41c010ba990746055522940040200310b0b1603a00300c810359a52590803d0b081d501a44d042c0014440107010b01042a0080c810000180b01c084020042880202c1c04c0022040c2e05110081002c00707000c001880310104281d4071402c03402c1c60513401c5a0301e9505d40c00035080000c101c4e4400e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 176239136 1250 176237886 176237899
    0x5010f090c061106280e0618010501082d010e0705040b0306040f060f0e0a061a01090b030f10080a0c08060705120c0f090303030709080c09011d0a0e030c03040302 71
    0x42801c522030b040001e0a1100e0b4802400c0310f407145070605402e0103482070800407110400c0703403501217609280265075040c40b2980c010312851406200300754010341040c601e200964100b000400c41030100082c2001550007140448004509840f13183c200b4100e030100c07440e699400d0400c0300800c50b1000c190502120700555040c40110b400303a082544036902160300a0403240c0244400020038042e600011074110004e400250126821010514214024004481c0d16807100081e0684414000e8103028103030003801c021502034100582205c0901000340560f917210411000140e5101c00d400701c0c40b00130030b40001a64880310950400510010460046000c40d12070400410015403007501220441c0c1500c1e02024441d803202c46e010701c55544655656028003100307004c0ca003410b0781e041c00214040c0043d900c50082d01c61401070700740d041c4481102c0b594455040c18004001d00444204801008403039401c4c01303025a0346039014040140b0111119429511010590000902e0000010010350740211442c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 176240386 1250 176239136 176239139
    0x12070305120a08010f0b031612110919030f12180305060f071b0803100b1c0e03030c04030f0f050f01060f080a0302030f030406060506030f070f0206090607051605010f090c 75
    0x850380c6107181d481805a044030400001e23200c000013089003002c8048500c3c040114401000c509000d8400072000344110703410000f20904140350040300c2540701c2540c2001c45001c145144c80b1002c1c0b40e2001e145c050302d2400b10a07104801c040c0700d0003c2d5095407900e0650b200000b5141d04010707030350f0302d405c40356121001c9041d004141941d001e020244580c0e4a4001500c203581c0c2c440c1da03540d036143c1010300003500410658801140a4040b4000380c80050403004c00c1c04004100c090034002900c01096440307007160010401d100c01158044101c1d010307641c05c0181c44074440f18a00d44220020903500d0054114041c1042403040e01ea810f40100d0200c0307401300c451020058035240300d01c0c1c9552401701c0050160740108086200510000702131a8017600a020010740c1070360b030754041442c1e9030084440c001680351860030020915080481c011105809100400e02490031082d03099582e80081c10700418030401190711840300e0212006c22a0480c0c1c07000092140340b05c094511000fa00903038000302e800fa201400c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 176241636 1250 176240386 176240399
    0x2070c03080a120618020f0f040b0903060c0301050a09021b060c0405010212040b03041e080406030b040f02070b0a020c0c0301090b06030d020a0305041e030206160611040b03040212070305120a0801 86
    0x140c0002d072a292051740c40642c1030409584000d41c404010400404028001c03c4640400a0701510041800b100000c0e6140052010513041c103d009280c2c0481d500184014030050311051819800c1c1c605404005130368074400d04141c038104800d0b0020394180d101d03400402c00c004440501910881e202a001c64204880100c0700045501803805413095009040c000a07002ca01c5001ca14042d003243c5103504192410207441d2002543d106800a00200c0d0700c1d40309240305030a0031300ca50000d0094a190450030901103507207104803200301920b048940b6802094000d00241c052101070040740d4010001c2000410030300e0500c2501c0c0c07081702c006200c4d01880d481c0c3d002a0b03001103800226264556200b0340341c80c0c144400d80c504c001e0317010310106103103483d0b150110040e02e525000b0803440d00e07072600000702c4520743d1400c0416900907141003500c0b090144010008000c071841030382d4200c2e43c100c600c070200400c0d20b11043e24020190f400602184110740c5c40c0c1890b04030001c01820102e0050740d5500461380c9454 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 176242886 1250 176241636 176241641
    0xd0f060b041a060a0306050a0b040e0105010903030e01030c121811011701090c020304050904050303090c0105040503071406090901030f11040b090c0a14030a0c0219030507031202070c03080a12 84
    0x1a800302500c640d0710803030b00041c40c10fa401481c08000f5410b00080003502c0708042003103101c050f002240c0441001800340a40f0003040092401040c0074642403000c0c9040d55401807900b000305003480d05240d142c0414407200c5004422042c082144c0c1c1800b00300102406245001203a8441c40075218048050640c440755489400141c1c4022040070003c006646030010070740080c6414003001046010501011400303964440702d0b14003441c010001182c072810205d094608201502c240241440005c020400180c1c40c0031410340202c90140c1d4103207500318183c0c2c000c10000c4c85540846980010094004020400710608002019011341c1404e807480e051803041c071040341c03d100710095001062a00054100d81c1460041c40804114074003442201310302ca107021010b404c2914210019a2204100e0040300d40c100006000c3e0030704201c003031100c5071085c1c40c0940325125000f0060200014050303010810710190301151803035503000301580c0c1071a903623040280f25908010304600008000d504c494035041c3c1d060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 176244136 1250 176242886 176242901
    0x102040501210f0c050712180b0d0608070603140a020304020a0312020c03010c201c0c0c030f03020a0308181203100801050c04080706171906050d0f060b04 68
    0x68440365018901a600703140408004200c10070310684030552100f0010190150001580ca0340d1159603c6040525000b2141c0124180701c801300400d14081074000741101c48402c0858450701c0781240c1d42d004040150018100351381112080303200d03030000002e00030361651001c04512844c140c08003842d01e4051010059100544000c0d40c4001900410300c00704241c1c10131114841034900448203040000008a4291111100402d0104000d44042c0d40951203461108540e6150000605864000c15000808081c180028a401c000441000348100a43d0b81c041601464029100f9019040f8600c0c000b5a1410300070401c0700098a258081112164545401a0051046001390003040f03050516540941c10040c08420042d4054000040450080c400c503801021612071341951107080004140c41c00c40300d548200100b0048609480410105112494112840e03040d1000034080d4002c62a014021540000f0341c0031089281d030300c0c10400700800d0700002511901c0c00b440100c0b072031800c00c02158840d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 176245386 1250 176244136 176244139
    0xc0c0c0303030b01050706051e01050411070f050c09040c091107052e060803040305060c0a09060f03110c0d0201060f0b0405040b0a030501091a060a051021110a1101020405 75
    0x200a0180002402034102e0a04100185405400d01300a5241c40068403c1501c0001c0000c0504240001c540d156207083c90260a040c0d80174080c07008804400056442076009c0546106c01610440e0100721051212029401c001000c402282c285800c0c0643c000006100d000401450101d00c00f02102c902000e0720708040d0403030003404003801c044401e0103841c240e420903d881c10105041b220710f854200d120b40f101401c2070100450706c8901754548140b4101c8080e0600098040901c0100b4540f58008440c0d010340340da0340341692040c460320509402821041403140c1880c20041004c16520300002000c00511241c2d80c02401010354441c011201c1e6805800769030b01c101010072061040e4203150b0004902004060103e00c0c086940f521141d003141c0307181d5002c440b80c1600b0010b010f1420810003110360403441c210303810310f401860840000c06031240580d20b1800d00c415a511581d440000b6001120082d600da40e042c40300d41401070f0013101d90f82c060341070000031401f016a0390041030414803e072001d40b01c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 176246636 1250 176245386 176245403
    0x503030109141006030f0f0c171003080304031b0807060c0e09040507050609030a170a2616030b03010c020c0a1a030a0b1c08040905060f0d1b080f0f010c0c 68
    0x3040001c4010301b21003000c88041a49480c96030043c1c01a500c6920304880c8990344015488002c030000328820f600c00703030049181b040d20600c188003051a100440340c0155041c00c2049440c4500c0c107181c0a541d010740d401600310b00d0041211000c2c00503603040240071000035075401d8600700261301017088000b4266006095036210304000e005600309480244409a001011070b001c210556070b4200400c81d6000803a01c0e040008114884d80540001a4045104807a110132000e0800740c00051f020480c0248540c10122082e00d0b28003500b40654825440444064001d124103078410f000a5591460b10081c1c5024210800001981c8403a00300341d81144020010442d01d1511101202c00142c800810304542c420007030003642a13001458203116099a10502d44030740c07520319285d1100101c45000707041c1402424000760b2220140e03a040071200269520804400e190741080c2084450742c1e00e59005405148075480c5c0003c8540c100041328003e0a01d07101c0240000030284008440329072801c000100501e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 176247886 1250 176246636 176246639
    0x20102130905100504020318070f061d0103021213020108130f02091807060306031a0c03070810090204090f0e0c030a03080702150a0e0d05031b03041401020705030301091410 76
    0x50b08140e8010031260306400c039054561001070200e901c00e03140400ca2607040c0f0b07009042000d061040600810103034a88a840301e250220180c0342032810b00207111420501012031180360300982c191180c541e54000c0039103542c030f01401c00a0a0043d07618080c4e000c205024002444010401c1d00c0d2800305a01140c001c21080c21982440f00d0240003514400313640c072892040c100c0a100400500340200142e507804101c01346035082949211100d551140c00000d058800c0011151700d010071260428102d1404072455a134800550410b100d03140c103c04c400b1130001400088580c810303000208455003a0710100308440145001598808040d21119056040040c100b03001c00e0103940c00d0b60748504140181c44410b0744004203020903040440d01742462507035072032044100100c100300381c0c5242c040f035082c1180745082010560b94640185d2100742d44040001000604000301120244440d040f080700a64a40e6424030b070090322a0824040d86100c2c515006e00c41c501d0510000c0210f016207403964030900c826 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 176249136 1250 176247886 176247899
    0xf03070b1e03072109081603031113050103060503031315090e040c03030314150d0312060e01170703020609010305070c02030a0b0a060b07080a030c0210060801140702010213 76
    0x7604a11000410405007400581a910001d401503115066684c0c450004101c1028801c2c43c1646408021803210302d0020442d001a0303412086071409108280e080b8591031407803800318040c1024004965135904040703904400550000200e2003502c80982342403011580340ca05040d5203014000f001882c84170203090411000f0752090b08100540141e2410030000e9844507080c03c0a0301e0292801c490306910a602001455850b104034450701070203012418140c1850240741c0520704000c04060f10400c280d0010000705802001c0c002580c289040c001d01010381d86d80f1140da40d2260920480e08014410001010b00d000d001c00d901050725801001c150070700c2d500c075004400804004091000b40030030b0381240c0c0c0240e036040003024081445402c8840f03540c0391800e840b00a84556078484408030740705008010004023100c041d184a135805141c005000455080d0407440e1110200d291200d09140410120700c103003041d04900c4800c40e010700411542c0e01c0e200c070103c0c202d00c2401640541b5074052502400b80 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 176250386 1250 176249136 176249159
    0x2030f090d03140304080301170a03080f0a020409181a09031215040e012903030d110f0406090602071d0f04050705060d021e030f040303020f040f03080702030106050f0307 75
    0x94000d1500700d4850014000c003003c1644144e50517a14408040010081c1a00409007090a41d000c40041d1041559070340e0060200d01c0c0140c12107280e28100000580c0200705a41902c005203206a0184030188070040c40301c4030300004100550300c1d15002030300c90590390030320b681c01400b40f150700008524006803c0c8110b0000d10014103001156800d4944200d802c4e96103004c4c20a82c2e0030070b0300c000140031000f454480714000e070a0b40880c0881a010112420b80d41d804015500d2040a107680480c4488800d0048080c610070a003408901c000007150224074903510504280035601180c08840c0c0858407103a203242e010b079a04c1000299a070303000c000998454140180d858001c1e00c40e03801c50340600d03203407000070309590810007d10f800e482d40030660200a0300d05110040e0420907030b02c4030610318108280e01004000004001030705041d000258015603160390305c100c500618040b00c412800702e4481c501780c030240d0712031802030b84290708042c2d001c1807070b01d8001c0781c013a18204002c1c0289040ca241c441070115 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 176251636 1250 176250386 176250409
    0x6070806060706050906072019050114010315050106021506060a141b19021c03090302060a030e0606090c09010f03090b04060b03100e07030209130203010f1b02030f09 73
    0x1c01160a1040c50700140590040b54000d241c200040c00840c0780150001f08003041046070311184032903200c40b00071901e80106c0c0342111a0b0b1400b100e00c1c2c040d007060418a0140c010110300d81880007104d400081801039449480310004581e11080c030040c0d907907507802c0f6035450001e06011403446580d0003203070091500b400108a044510b0804c64629109850345000c41e804c0120441084050988250f1310307503c00780306100f03000481d1105500b001d46190082040d4040707500c06070343c3d080f00800103a41894000c40c3c24030002d560040c1010364800b2a8100140604103402d1225107506c940404600146049444140309044c001c81e0142050b0f04400116808001c1150340c02c180340d0b030b5910040c040b403034125501d88203c0c041ca10204104c00e0704414140342a500c03000300d4091510740301800c192800080340907801c60b034040398540c100345c403082c56004503040fa00324001d5056280001809129640da003040d103400e11a1422504c0d00f0040600a90300d0b4821203001c4240c640080081946c3c038a8030012005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 176252886 1250 176251636 176251639
    0x4140604020a0b09031608070906050919020f0408060a090303050115020604060c030e060c07050c030304060e040902061603080609010b1204150b03030c010203040516031e0503090a03061b030c0206070806 89
    0x1000980c0ca10398000c0d82246c1a04041c81c079801421080c08040c40b603005510003480c0c00d9803d007489150203000082046069080620460380028103200b81c20784a006503005840460241c40041c24007591010041001c510201c001c64200000001e0700c07821500c01d035601c6201500601400e945650b112001003403000e80c10f13000d043d501c02d840115100204181c520039840102c0e89076807000d26090803450009402911882030b4000c010900034544e000c070f488000c516040e2004203110302d0740c1c40010180e005030450f071103520f0b82d0708000806050380001541e004450954181e80242d80b5100c02180703501c00c07282c6102c02d066017600490002940d01104120300010603800207135424035400004d0450384404d040c49aaa034002c010300050203410710040c072090074110452484170f0f1171130b610103d42c4564040c46815002e1105090002c3c01000e008485d4503e4008100b4170f417590300ca00c0c00600078200588031a4102c901c0030300c510802402446986403541ca1a00141000c0e501e600341180c8003600100801d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 176254136 1250 176252886 176252893
    0xf06120302030a083117310b0a03020304150501060e0105130b03040c06030e060106120507090b220503030909040f0804030503040605030f090d051603170403020604140604020a0b0903 80
    0x1740422500030803107800f2200000e0540580d000d410300f64031203140300c2100c0c0c05581c0100101108402d0b068442c008400c685000404040c02044540c401080c160740a105911000148008040e43c99030045104e140314000540500c0c00d0028018112002401000f000c00d002c0078074010fa075030090340075206070301c0b48001011600742c4802c4242e0071508284e500715045115201d00340051900350095003138002080b0010f00c0c041d0b24019000740000c0001c0302c0310341583d40e00c2d40810366031703440b500024010b031196815080c2d03194001c104d13031540b0341d02240741d0040c409941400441d00d0710f03010080f03e003880f10092400c0781c41e40b0b5985802e140100c0e032070000c0b100203204010000000c0c0052000e4402008140c440301e8480c81d26104070026160010480743c1c054201c1a001040b01f600070090700c2c00c2c01c050803004c643c140000d241c02c0c1d4403113114106044010603120704100401d5070018489100c4c0741b0800002c0c40e043c0b218001a42d4508042e10001d50000c450038003404092440c10150156501c0141103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 176255386 1250 176254136 176254171
    0x50d1e03021c02060c0f03041103010e0f0c0f09045d020d0e030f01060e010302100810090b21010905160608010504110c030a030f06120302030a08 64
    0x80001610400004901503005164140201c02c1e50055180410005001034030091410000e10891840354104072041c2100c08000300e801d2040701625100701e40d1016008110082c0c421124594810402c1e400d04c06500c40d0b8980b80d030071803c2c02a0500f030340041c09018507506450b42c0e5514001c002806180b94416040c070109041e5910420844510706c21050064a840111040740784164122062401d2112448401269055036000400e00d84068044c03500c000c9002e005400a414008600b011409642c00c245000c207001c103000c6c10581c1220310850f00c4501c2408030750801e880c070990454421030070345d2002600b001128150782041200700340090040b27100348140101200381c201c0c162071b50106603648520240070844100302078500f000c2260b01e4044c0407803402d00000c01044050182d24001da4407a48680c8004040c141070303c1c00d119149040d00d45519407000c00400810342c040c0b0241d2030608194000440d8020303030303000310398650305540550f18000c0c0c5c050003502d00324405091100c410320142d02 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 176256636 1250 176255386 176255423
    0x11116170304030c050d260405070b1b010509070605040b0a0903150b12013b060103080a020d0309150518030307020102040501030506030708060105120307120309020112060e01050d 79
    0x1540704600c0f0342c13525000301d0075a007081761818040180c518244003800d41d0441070021442914001034201c07210a001d903030b8642c503190b400d0100a030710804c20f189021a041c2562103014104800000d010802007200b40d440c2c9841594500f41c80c030a160220b54100010710042c1c1c80c00c030040401c1c11807030504521403580d03662040e080619402206a440d40d455520300302d5813409032035214070002c030303030000340b0070601c0020100c05039260704c00ba01210030304030840010300c00031102040d04001c075205050b620a9a5241001c5035280e022440d0312f8018004c9902d80f400140c000c2c45481d00164225080b40340e18152109500e00810018081d038444140c10300c0441c900031802c000031845904160700158542e843d01001505540d0042d00c2e103031082d0840d810502500200007503180c11558125171080c5500c0f05180264110701c25518054055000504100046a0180c20104070350b4401ea841030030300006600c003042180d00c680a0507800d000e0364401000245015088011036501480c0511000001c0c1074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 176257886 1250 176256636 176256683
    0x204200a080702070b070305040914070e1c120203031608010303020616030219033e0304080f030709050a050103021905030c09130506040e0607020c131419050108011116 74
    0x5030110001070001a0501041c2b14a014032858a130407e00e000900c0d080101003d0910003a088086014124015140c94905840c16003481c5a517088500e24000c0c404010b4000d4690380b007180d50b03401d05507804c04541d040720b00c10b100c101c0c100c1e81c06074060322030b640301c100c130441c0c500d089920340c0400c00d90240440c10585044c110819a032040540b4009420020120901040a030b01000c2c0080302c0f852403603003141d411401054071080c1c1509983d03156290703103134a401d010601400081c1c0f0300e4480d0220412070469007100382001502c0003101d9072424556640c0044060388600300180d035075412101720071011980070310301564004080400c0f040c1802050b0f0042240c10900c1703001210303215100c40500ca180d050522424002407001c4019240501e040f480c0a5603c06280111500030f000c0400341c416211096030254502c000001d159030190304101da04100f040c008100d007064076501d00320000403119414864080c1408a6201440c107001ea0610309005506010a043e210103112003441c021041906 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 176258992 1106 176257886 176257897
    0x70b0405190609020a0e1e060303091306090f0b0105040605030c070b04050d030c180605030907091b020705030a080706091703070c0204200a080702070b 67
    0x1031410526020028078034000903040d090749182009169000352500310b000700c5140074850f84400c0700041103d41074600c2452042d0380c10903002c0d0f80c00404d43c03441e84510000c050b80d0400c420342c4081a02c8043c821900340e6041d40d00c1030103000b00d40d814803442e040e1240e4104104100040500080d015100794000c1c5000c1c080040005140c0541250803240656440003030100d1500300340c038046507544481c41c4188040707800e1401e0b2102c141c0c441ca1746841009016440c03c1055850f000d42030b100ca0780007402c41116405403543c0410481c0413806100003100e00b0b0321070222074400d4000020300b00f03041504068801e400403108007001c99009010364481136040600010328140c85d1410f0f03005070308158499410144044100401240c1000000800300d000383c078180001e01e09440b4840f101c50803940303d2007030840d0500514101038403441ca015840811070044592041d1501040301498000 = true := by decide +kernel

theorem cover : BRFrame.Cov 176079136 176258992 := by
  have h0 := BRFrame.cov_init 176079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 176079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 176079136 ≤ n) (h2 : n < 176258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
