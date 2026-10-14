-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2186
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:55:19.058017+00:00
-- url     : https://prove2.me/submissions/8f43d4cf-9a14-49f2-9374-3d2a0e51537c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 392985611 ≤ n < 393165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 392986861 1250 392985611 392985623
    0xc041107030314100e13050a14060a14070c02010507051501030c120314070809040e0303070e090103050d030e0319090906141e030a05010614122a040e1504 68
    0x1445500e1086045030240c002c1c500051240b5920f0f04041d030242c842e1400070289041c0003a4000840c000c140c08001d4140c3c524025a01c030070003802c80740c5270a402c0c2400101180002800d100d0b030008641d41800055500062a14210f40701c1d02282c4012a80c611492001030038510600d42030961740d84960080604a900c00e0a00e00503641c3d40b10074001109111090143c0071692013901c99601144540003001c40c40e00c100c13410f0303240544500008007101e18070305c0c0c0f009407a1720100c1080001600b2103500d600c041d1044901c01c80d9903241d580c607155070721035a40413042055240c1a03501d01151040080d1081c00c0410092070a060030000c00040c41500c8600c59603072210705140300010884009001100100c902510340c0c8030a50001149000c03921000000320740511841c1460000700300f003849223002410001c1e0690101c0c0312640d0810041081d100c030960710a07000b4130740c4520081a00b203000c40a5103042541031400c010000c0c0041d00620911000d40450700454011110380350450398102d10a40c070a071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 392988111 1250 392986861 392986871
    0x90501050d051c0908030a0807031d0604061802090a0902010807171303120c02010b0a050102030406020a06150510080601030c030e121b0307030f02120f070210020c0411070303 77
    0x250800200c4001c05501415903001000c2181800d01149050782c1120f11a007001c800c410b079941c1040b03196a110041c0306001800340d1060000f01d40d810301410526644450711804613030b915084081c0c4a02010380024591aa122240c0300c0034007180c25002c01d5183c00400300c00700351502c0704254018002e1280700301c2c0040c40c184001140e0600445145142c80f8003011903221640c4d580c4880a403a96590005030148a44002083c030813034610700071a400800a80e00101e0303090b0300441072245441081d04020305540051106204907540084c512240b80e800207000b00d1000d41c82503003210711007101e4000301d4003c43c098400740c0d01c0c650044c0310b00f03004070820381c0e0070045840300c608101d0840d02c02c08400d400079042034401c41c50290881010300f66001185503068402540003080b189554400d2104070003040340b0000788141140c0500c0f507030310324000c4c003070303c80740381055006040c4428810a60000d00c1055981c11800c0310702e10810011246000180c401c00402c1e101840025039034015940450029080c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 392989361 1250 392988111 392988119
    0x3041d0408040b0307020c1908060604090506070507030302091e18010302010518030f0d0e0a150801031e06110c0d0504081504031b200d020d02060a140d06090501 71
    0x282802442180c11481c254207050604805104680c0050a000b0440c450030390b003000c0760740d2a441c1449020500600090b08541740103500e5080c0358000f130410f882a8600038819010580203d41e0315070110070303490400e0f80d0b21139614050b002400340d02c1e0026088036003070b0700700a04001e413541c40400400b0111011a05118040d0349920141402d0000a0005009002d9450222142c0e100c1c40c80b01c07040103060341ca854004800c0c0c40c4c0340a00c1c0080100000300110141800c2e4142a11440b010780709a44040e881c940c50540301421200701840020040303120540c101170f40ca07000703980082009038025000c3c03103150400d031200b01864001c003c48480c40d010708201c082d00c4030300603000c4038100c41c0c00d04083d0400348000440d000e0b80d03a10041c401c0d0107000c8500740000c0c44045020000d40050310880070340c0c2c1d001d0070700b5104585909502280600514501b0411400b5039504544410708c940c2c11540c10703981d482e407440101c1d5440c81140401e0140709020404018101d1180c018800f50f60b4200c00c100305681e070f5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 392990611 1250 392989361 392989409
    0x40f0b15012c010509010512091c02070f0b070f150b04271b05030a03030e160b031b0c010c03090203060a09080409200a030207050714061c0905010204080304 69
    0x34200c42c1a010414120040800c1d4000d0020b0400c08005042003403c0c007105c41d11184c18404210340c04106504078072140780e850b18240140c14120845440208046401c02c3d48160240d0014000c44000c0040800e5410030000d00000c400e0015138450800030030701c50b28002d9440908400865a0721035401d01c005041010300301a031b9081214440d00c01d504e1040d400740c950b1840c0404d13200b4070403001e0000d46c00100342900d0820003185080d02c81e40d400640aa0a180b0490510301800004818440000e10400080c078410041d00c1c4c100e042003181001c800b50050070503020f84200c0b106e040141d42050026140583c06070700c0301030801e0080d42943d04503911115031504469501100901500060006101e601c480d60b0202c04540c95401d1940e09040c000c003010389864010900c1f6100194002030541c0c2006000d00c512001890ba0b4212a2000d00ca200700145031409084002d2002c1e40c5803010701c844584050704012440c54200008554541d1111011a1070303a000c0d001d80381c000e141d4001da500102d8a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 392991861 1250 392990611 392990657
    0x1b0606030d020d110109080309071a070f03050901091517010e0c190504050d060506040b180c070c030c080a0302120301080a0f03020a02090109150503120301030b040f0b1501 76
    0x10072503000c2c0c900e0681c2d451003600d03132a41c8414501007a40d40c841c2141c00280c41c10004500801c034180003810711601d0301c0c80c010f05103811a1808010910240002c00006200d0040f808405505043c0315451380034020040742c800700070754818519041d070200410750306c0ea0403100e101002034420fa41000b1981e00d5400420314150103640e448014881000300c4000800000070300440c80e01d680c44c0c124500381d6200c000400b00ca41c3c0001c25241c0301d0b031760814868103280a205c1e03c220f0b60416501c0449288203404402d0554070300800c038524211001616108218018134460041c47d0b02001641c1ca403a02d8403101503540840c1e0304120301600c54640305d0941005480241c0e0704070368240000340b114080c10341c1d840b0041a0508002c90130340c42180301031401a502c03607244034041c102404000455120310a011441c401c0f40741d209078042d400c44c1c0d1414048814090031241543d03040a40f1481c191280d18000022204089019001c101c2103401d20101e000000c1c0042500002613960003200b26410350200d006a0f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 392993111 1250 392991861 392991883
    0x30b011403010b03070e1f060503240d0204050901060b03090a020306180c06132d0f0b0405241c1a06031603060f08010501050a0905090d030e010906021b060603 70
    0x40c1c03128804101d8106c560b200d1580c0407200190004001550001000380d040b103d07000003022400110401003250b5032040c02011000b8007080d056460560103022861004407000d000c2d01031038417040094103000094014600400d070102e842d0766240750900c05180c580c05020f000328460700601001c0307403110000c1007042d500648984040d00742d21603100d0811182d60720011a521107078000410015090400341c40351200b55802c00501c000e840030030402110340c41029000f0182d160007a580510a000411040c0d070b06841e403c2c3c624441c0949100c181c455202c0c1500800c100d04500094114072030b820140002071401074061060261180780c170302c103041d11510f009001c0e03001082400064207540f500070001c941080641400214a5281c01c02e040750f098141d00020b00c0c40c2c2d110001000030303042c50b2603090001d041d21b80c0c00704001e0030503280160702e800110b058102010b4584100c00d40182003940105501039200008554540ca008484080310248100c0f0183c00d00031031001036214240807940344442 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 392994361 1250 392993111 392993113
    0x509130209010e070207090c081008060907061202040803040609080105100632040b0a140406140705070b120601110604050607030c0507050105010b040e091609051e01030b011403010b03 81
    0xa83c20b00d55003945840004100b80f00b10322603e480005d1524491050501442c1107a40b1184545081944020065080c0d8000c1400d9031011003000200741c404198081036032000d05d0052502c152825041019001d0b43c0c001a04e580000180001c150f41c1080b0450200c80001001b40b007a6595101c0010740007125104003804211460490b011481c0d81400480220200c2e2101000603c070003400070764590071941150a080c0c03c00981d080809410490320b2413420080032109181c681400d00040a01c4502041c51340e00b0a000300358032003081420302c0a00080c084880d150340d1250022551400500b5094504038042540c3c4c0348040031034100410502d20454108006000503212843c5c101c000780300b103803110020044140308850029800303000f0b09009000b8610090344640c00c100301c10001d000c1c0035080030090b5100031307403c40b100600145080700303c820768140051a5a40c944074107482e00350860908189820940010040103104280c00e416a10040050301804038907105040c221034030380d00c0141d85 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 392995611 1250 392994361 392994379
    0xd020d0206091f1b110f01050103050c040203091e0c09090307020a031205041a0309010506030d080a0506040b10110c0105160b1305100903020c0103060b0a12060b070c05091302 77
    0x3440000f084001c00d0381540d60002030f00301442001043d41031021002c0c0303400204d55035502d000356501042140c0c14003289000800840d49183d680f16134810700621141d00458010000540104003803060040800c1001060b0380001c0500d03240a84030040240140c0c81141100e0203d902c020740002500c40b81035014010181c0783e4259202c5481000104509104100d01000003254510791618004200e0014030405901d90402e08609800c0d140000d0007580031b90b0000403030030482d551100c0181e4209040700b00016860f01c5040100c0c010380107a030380039604901e8121030694026801254a9540c3d00104180e903803644a4100440702885114401840030040905050101e030943c0d2a0a030425404910325165050907502c40e410990010803004c1c81a9480036400180b6405100d80d0110640918042094030300b4a100320b48540100d07800b0604101c605019040c00e8030440d480400036018030030001e0b4450000346028150b05c9e04c07500507a4021414480072410150031425181c00041d07005000e515 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 392996861 1250 392995611 392995633
    0x30f030b010c0f0228030b01060203090d14013b010612031101021e070c0b0703082d0a0c1d15070f1a15090103030221070c06020d020d020609 62
    0x444541c07603001a648082c3c1014180c3c0380d45900003480c1c400705c0d0501d540c004038a00e582043c4a1040059118100355041000302c3c0d28643d4504110b103000561002454485180c4500c20500410414082000403a8046044041450150443c5501050821030f1000f80700c0d180d10320900380e441e58420388080601c201100d100003401220014a02d8101d080018181420704038110000707401030801c0020007070300184100c18002c52481003805440310186c1e062a10050799402440742c07000034110429400d0805880034084002c01d0160344280381c000c002c00240c180303400c4100040650409400c042182c0b0784040c0800c94043d030300424540c100406000f206201e407652142d442e4821401100e502c102c1440e29000541d128540700f01c00d2000300b2060226180c211031b400c8400b189032000c0c80c4929007900040002907400201174006100d1000c06107040e084000003040c0c14012100000c0500e00a40d60204040342c0c0081c81013080403142e402c0f80c141c1e41126401346e032191000c0c0c420810130703080810101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 392998111 1250 392996861 392996873
    0x50c100b1c05011503030306030218041e050307051e1612030320131401050c0d050f210601090b0424050702030a050105061201110405040c0504030b0f04030f030b010c 73
    0xc054000e0002041c5040d52144c3c050410f07100d41c100310042030340c40c1024801e50910750800ca02c402545a140800da08054507811818804031070640c40d551070405d02c7d0303c2045030034420f0780c820321351050403181e100141c05600304480490b00d028131111b08c103d0400c581211012601402100d18003441003800d101a910100c0c06400c0300c880c001c10003488c402c0030f4161024000000d00780056000c1000c4d0b1424200f4a942440120182c030042c1048010720080d45540008544803541d803480c1d04085070340b822400010200e5004002251000005d540030110241e13801c48171842c0300e4507090fa10700c000c103901c640516245000ba4014017459211240b51800200c2c05901d48000f861030f40d040c902d0824015600207841d218616004403481d945880c2030007464244001d081e071004041c60024800414070340d80b648120b004502c0b03081e110741d8942d00e6665846005108503001741d41c014130701d01c281e450012001c1882203800c0d5030803170004124101c1259260f00ca4480e00710b0150050b13440c07190b000e416850758 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 392999361 1250 392998111 392998159
    0x3200c1503061c03031a0f01020c10022d120c100b0109090f0f06150f0c06270b1003030c02010c06141515030c0f030907090c050c100b 59
    0xc183c11109058550070004040600c207028140319950206102103145032010300c9281400340c035402240d8904c1502101e84e004520300306042d00c1a2034600e613600001208919000310407072402c0d164003c1c060440c200d1582056846212a0301e40e04850030f2034045c940c0145d0714031410b2081c1072180c008a5030001300c0b000c2c40d042150300510514005901503140c2d40c2620440300c103001340304101543d86100c5400d00d01070303026180040142084151620603010b00207419201801009810040903401030300401c2095400601e0307010780746001c1043e80e00c024810021b00d088068041d42d0781040e82c4005006e1134002030074002581e902d0b90700c0b0441e660443e070040d104041000411204076407a4507410b0400c0c24a60301b05881003132000ba400c60300b02420018007450306418420b50003030038000c20402401c450080211008060940c8500f0341e03030395403440b00c54180b041e01c0e00031607003441c1003900406165a111000c2c010205108041d00d0169000079080d4007100d905040b2190010301586510082207640140 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 393000611 1250 392999361 392999371
    0x109050616020d14060a09030f0c020a14031f02030714192604050c0a0602010504080405010c0f06060801052d0f090a0c0305060106090807080c19050d03200c1503 71
    0x5001c0741e80824148085c1030070b50880d0030880455944d90385400381a481403030016040c1550402e50b102e20741540108007480150f0068501c0800c0780007103e009614108580105400510a00110040003070704000c00b0354070540d0034070000740122140c084541c07503180c220356181400216045405142c2c0745c040c0c400308085900c9440481a0f90014084104044a000d1160384140c000d0308051400340300304501c04078281c11003021a0326000401c00018807150440f400d444007400d00409149542c0b51200091305107142c002e09d5a414841e00103103200301504a035000b81c05002104540e00000c0000c0b8500580307004884a004034160003049450010540041d04600c00300143c43c00c42c091521400c502550a51040b905940018010411b0307962110080e801780c4502400b4200c9240f910141a43d101e21541c0740500c83c42d200034031111810a00c0c8000c00080c80e01425a80d0710b081d9505002d40000903100110b10040e0341c2c0c010700041914040f601c0c5c2038400340200580402e02300301e0340300406030b000184 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 393001861 1250 393000611 393000623
    0x305040905130b1807120813080d08061008060f0a08011a03010c030e070312051e0a090512070905090c0409080c010e01060b030406020c010b15090109050616020d 71
    0x4004152034000340a414030605810080407034100701458000b05203240108103028016031030303801c24003402021400c0c0c4122200300035203c44980d40c50800b02064407400d0707041c40341c2c1a0302900000e0784942c003258442580320983c03102151617840c0f0090181c6e11804042400020740b1000c006401c519040048044c0030307401803d410300564030b03499114211010840509103140c0c400046405600d801d0040a11031080d91500740030680d11800104c0e540c10300c0b40802003c440020700000070580c414001d40b94282c04100c1c441103582d100b2620804103901508031200003414a920211b4141000d4104040f900c19030002014240d02c3e0640728401002e000d4a410b0442c004d4400800700f035550780c00741d900e91500942000743e584401d81c091a08460a80440d940e043e418402c0412034000d603001036950003034105002581da000510007043c0188054490590300015103044c0190301c3e20a04040c126140c03080c2c032910a025150700c10004075000c2c0741c41d90310712420b40003d0f0100604000d0100050036114030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 393003111 1250 393001861 393001867
    0x2060f1f080f030c062d0a0b0303030f160f020c0d06060503030c07051309020312030604090f08040f0b0c0606120f070947031f0e0105011e060c0305 65
    0x35034071400c05055024640007a4004503a12880000c1405280e802030f00403000c091070800100d2141c10380d4242c0741001c080b05802c0c44001129002075420400c02c1c00c030000c040c1e1fa1b5928005c0641c1110000a980c81c0607005205101e408140d4050340c1c1e01c4101f02c040d40c004142d007100c00002c1200d64501440304403011500c421000440c1d440400241c86c69054a01c00740c1103c500b0704052150311f080d50003814443c01e003403040d100c025860119a051814550002003980d95407030001040c0549242d5030002e004004000c0e8002c00d0143d04000f502c00d80e41c1c01001d81d1403441c0c1d55450900346d4040e01c04c01ea40c0580011010608a00e00750380c1d001d4524108030207031500341031031030003040c100700d0560b1001200725183d1504445150300030800c0d44041042c1101300040b9076a07520050303a10180c02125044410491a406c2c1d01a0f0301001030b40c0740c12481c0c000304128418034507214170180c9056103600c58950308000010130079086c0c0c2c13040066010382c60b1560202040c6440340403180080981d0095080c00420 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 393004361 1250 393003111 393003119
    0x70605092406010c08120601030b011e03360318030b0c091816030605011b0b0606360937020c0307020a05010807050904020c0106080f0f060702060f1f 66
    0x243c0082d00314014112041c03001447c00c00005015906000980c504012001c0302c406103501242035034810200b6107180c00105441406008150386a012010003d002c02c110399044882d0031254188006910036912101030455041c180e0001c4061404000e19031442280003402001190018100040000344800c030101c4084200096008080d90325602d0581950512650f10381c0500502000304405e00e0b04020000f200c501c042410003404900a2201e40c003030b40800c2c140d958490a071081421825a154010034011412501a503800d5400d19003000d8070740354510281c58001d4040d489401d4556a65896281c003112031f04403480320844113181910b101500364801c0d178852014000360420f0780700441d41d40d821801040f0209c1030f550b200c2c070304100c1c4482c100240c4641c040142d8409074000c1e6800b507141e100d90080e59026180c1500103403031502c10b0001e5804400c41c0050717822a401a0034054600b9a01c030801c04036100d140840d030b2900c90500500105480c04a40c0d0030040750f03040da0b0354000f0440c03915 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 393005611 1250 393004361 393004373
    0x9012a1d040c0f0e091b0a1202030709060305010807080604080c030c070e010305010e011e02090103090b0a090b0f061c030e1f18030f0602070203030706020f070605092406010c 77
    0x8042d11240001d26808001c0d402c0c41d0300706006041d000c9080b6400740ca01c4c9809030100090031101d80328101c0e0a030b400309184940500525504e06205411441503459151100b0005c2100180303100b0140001d060a0001a002002140c480b0648004a020749a40c0c2e0b035548070020755500405192685110070488515120824030501024000540c0c080065526604080f802d40310078000344c08083c0d1500402103c40203080d81214000d81d004400541c039240800e0040e00102010000908840c026200708011490290b110720811482044200c082d5152455050780d0107408443e0385410007603000b00c05010b410f11000100c490392007440d0107507001a1070070100d10541010010015402d655400b40307030406800541089020300c1c0040c21045051542d00d4481025004080c040c1c45039500040c0501075480a00031a40f25a80100040d541d840840d07210140701e6120302015614186000e0208500f0350001c5001028003072170100700d5140600c60050302c42008006070031641401071040e40c88000500e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 393006861 1250 393005611 393005621
    0xd08040e07050408031206150c1b1302121f0803041a071a0405010b030a0503030112030306050a030503040f090c2304081203060a060f0210020a0207180509012a1d04 72
    0x1504680851b5500b803140074011a8820200100c44a8100f441713a8802ea6000017240e4614020700317840203003038682030300200d8000c24010321102c108500006e003014203c9820310f50140103440c2443d800c001000054402091410705010701c000702e0300104400c01080d1048500c808181d0701e10221140740940c01d0340c80c0c2178100402e0301142c4482241200308001d0000a1049081040003174002d42503005165450075140d04c4140610b40740080c015140f1814144654418000307440c1c0a04038041d503640700d060982e40d075000f40c8035801643d0696003020600d03841d40d014010a01e03481d5101c04c01d5464a000406894000d11054070400d1242070000240181c01040810180c0c02480c0c0c00d42e6890410100340500c0e00019004017080c0700702d0700a007070041d0382c0c0028036500040141400588130030b4000012402c00c03909070b0101095007603400070800069a10352015004480c000003c00c050721444100d0750b00b0100c47c0040d0a001058030103403c5001d4001c60700e5484410803064440c8402e80f403040000c048507 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 393008111 1250 393006861 393006877
    0x11e0e310b0a0b06040b040e0408190903060c1b0807020102100c110610060f1b0209180f010603210309080c0106050909010b030709090201110a05010e0c0d08040e0705040803 76
    0x7007021024002494140e1040c9007400a0a03921146440c1c1080615540791141d0b215110580060000080600001030151140c5250940d4079610200001000906606140c04260b03002460301d00b442d00324074041c0078047c0302071205c03000a009528403511408055040b810041e8194001c9010003010400d251043e2140c41c00319031200c1e0506c3c01044103184c0f403c90b000303140103443c0c104081d0a005007608544000c030000858502001441826441213004c22807440c0000c2d00040b0402c103010802894407440b03901c00c010312045400c3c4045181060342a6240d610016142c03001040e50740f22000b8a00c1c1b0f5401903a4424200481c1040040d07940c402c043d444040c00c202503035521803080c411442d00901843d040000003000740a4960500000390b00c40200341b1800c0380f00d41d070368440e010459010700080f900300404c20060b60490781c41810700c103000c0c04400300700041c00d000319561280a0314107044040c55079174202494504081c1045483d64080300050901c405100c014000000c103031a0801c000c00c014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 393009361 1250 393008111 393008123
    0x240507090f0902160b0c0c010207060207020f18071103130801020904050709060801092d060303080106020a051506030304030507091b090305030a0f12090308011e0e31 73
    0x40c1c0c0780003180108001a50850804140100300e8a40c0d4401070811400c1d5a9400940d00c032965210809403070001e1042416400c0f880d4004070f421010b1100c2640a05880e40c029105c0c0e41801c20440c0c2002849100c040c14003c08240001c082801213224015542c0ca070004101101e141c82d140f02141a004d00840d4002400e503900000c0701420790509005080d040013031418000241070515401802c05031050146e20301e0f441e9100300700702141a511a0300491265080e00009490071130205038000350006001c00d50104050800014155100080c0340c0d0b2440d0700900500b107050501c0b1030406103000701519803681403000340b00c00b1011030800e0040302c00908030345400240c01500e0032038040035400c07420701003420b21080020400200f003001c8110303515807605181c0742404a100b00000c0c1e455034001c03a20101c10601c0c02180b40209600580c03468162841d1640e1040982c0a0701000741d404401070007400d0010f42d401703011407442c40c85107408050071314403d2148000c1488000c2541743d20807403030743c050f502 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 393010611 1250 393009361 393009377
    0x1103040204061d0a0f0f060b1e03090a0f050705030d02030c06061c06050a0603170406020c04020304051c12091a0907050102030f09010e09091f020304030804240507 72
    0x11441c052207001c0c000e040310500e02200c80b59401000f960524001c0081d103c080d11100720760b168141903484403040320300802e410080d4035100d0815441b80d0b0450150002c07030142442034181100c0301003042c2c0348100ca5400051001c0200f9542d004c100d500240d004481c180b2803030502150b195801d20450f9140909540112344034207110b500701d072400d400500850b0281032462481d58110103c001101c0070030390401c10104035034603420340300c400030585540046c2003121038002248a400801000f042200c5541d42206d1180c101242000200e100c240c030018155803204000d281902c0c00307001940d4400516080c0320191120a51001c0706a0b409018201c505401a1608018030b240580e545900107100341d000385201410080040d41e60b104281d10180e4030403012076508080d80c450002c0c0341307804030041c04103600c0c1e00304a03030341c05c2c0d581080000840492024034080880c0001510949110740d8042d42e5138862901d440c0c603840480221200e4080814000c4007902200f0381c1e160241c00d000c0d17a12540c03400c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 393011861 1250 393010611 393010613
    0x14090303030f060a2112050d0912140f04030209072303042307090e0708010f09050c01050f070609110405090d0e030d051801200303010302190521010f110304 69
    0x343d440780c0c9030485c1c0300c00b0000341031201d08800318020741ca03000c1d684101c092040b41500ea509031030500400340745024160a014410003008a1314288084040e00c0303440e44049107c6031200d00005000712501c0b408905003d00c0200050703e010111650403007200e0904c041018010040c101c17940b42e0765400c012000000205101c00c02c41c50301c102c905584000001c0c10343d0f6032418805107440f104548600f40721503455201001c4020428010b50000700308000003084449400314501014040d0780c00207a070b050055425480007940114101c03140c0c2c1c04180b5903186400340c5991000024484498251225100d1641843d035a8460b4880c45003c0c080700d5004010380883c015004000042d10521180290046c0b0b551010094012040d60005621511160000031120b80101c8030003211941600c115a48c107a605928148040010b5068078000e07039041c81c403030b65141702c101c102c22918450741e500012201981030000c25212104598015414004a207035407280341c0c40300640b10100c219505010000003800 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 393013111 1250 393011861 393011869
    0x60506030a050115030204060f0f0908151509070f12090b131101020319110c040501030312200304061d030408070e0a0506010206060d0c03050d0c12090308090114090303030f06 77
    0x42c21380c83c0340c0d1800354a0682000c0c00200f50406002c035103814008281d04400f00c032030040c40800040c00d5000110f403103d0540e459035036411001556001c21110380991059154101254010300c20b411646401008000c5402d00300c07440742c06145071444940e90b60014071b0004115201c4503010301501c042c0c00c0c074046400e081c0260f0140040c1c6040e41950f00800a0b01c05204c0c41d0000214601c50ba41040c03801140d90700820342c1041c494126165200d8075040010040580124150b256105c0e21001001010310700d424992048500100c00007040782c080c00018006180e075001282c920040d4695940002c920315003039031a60f0402e4029040503041260705000741504608141c0d170040320000140b00768240b07580042d4460310b0190019002c2c12483c00d175a4140400070044070300847d402001c5440580300034074018615210042c044852491046042104500c03e81e6140243c9030000010f5242448030340040d518140345203070802c442c01c41030010501581c0d081c400756108410000ea9001c45180c170200300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 393014361 1250 393013111 393013139
    0xc02010e22020a05071205040f0b03040312020a030b18011806031e0219080a030905040203072106090f061706070905040513050f0705031b061c060506030a0501 70
    0x140128a40300d5000390002a68a881e400211200300c0165036100c000c100300c8080c07290580c06000308402040044040707030b0140040013110071041c0b010400985450400c41144810745001e00040e04c1d103603146420303120725401048190110304001881a0900d03000c90000f00d0f8507400342c0e0400b40320000400c92480b480e031103800c1c0f01f0f042c1a01005501d045035203403051074018102401d09030750705905e04411910b9056031100031803220400c0d050a0340c3c0c0c60300c00317903610329028108500048281c100042c29013454004c1d0390281074542c503003010b02689aa00c4000c00b0300e080f203203c0d03a241d07281c26000880c1c4440e031080da080d03181e40200204d03049080240d50011b44814089000c090307842a010402d409900565100540d217007103c1c04030f4141c45200b80042c0c416855440038001e0f0041c9404c10611550018000301244d40680944890b084039052041040502050303c80c0c22101c10000740c0020801043c41704414074094500140c880e88481c04180d047d0021180584031640d14001401280300d62210 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 393015611 1250 393014361 393014387
    0x3030708130f03090e0a020c031c060b13050307050108040201021b06090613050321030f0c0706060b03040506091902010503040c08070605030103060e0105010f030308040204060515090a0f0303050406080907090203070c0201 97
    0x9502e06000f01239a90b0396807092038840d032908444880d8241c040b0700a038000c040101f2800030625281d044401c025124503080b4860f01d80301e4420319500045650040c800303684a60b405802034080140c5520111016461800650390304c01001c21400c0c0700b07035460401903d0310701500c1c10f03540c01c400d09020900d45012107a1040700910281082e001200c1e210220031a41d101101c100c2e205020749420118148030700807008020300003410424007080c2c003090307000514451130041040745d074075803110011a03450b2070441d014000300e011108440780155014100a6030460303c90010201e04031381d0303840741606098254000f940010400801001403006034040e4460a4421200070006540b410700104200d101ca803000030244410f0300006400d658440d80b260303004102c06040c00c8403000c10304001c640b07280d114015003072103200c041f0008502212110303005400d40c1e9268035260b1519003041410303200c2480c02070a1a4081c803a81c0800b00e0020727854000742d4000d6103184c8800c2d0a40d4150310024144080d50f41c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 393016861 1250 393015611 393015631
    0x6090a03180b07031404090603060b0f04050f07210e070f150206061011060a05010528030f0c03050a030e130b031e030c03041e080d0203030708130f03090e 68
    0x1a007444402d2400301101e80255050614050f085000403041401e03004560000364040d14048000090143c240c0041c418800d044039280b10038000c107020070044803001e9489480d0400396500080d10387d8040c0c0f007003140703040c902400b100030901140804810303100380d00148442c0c0d42022508104410110320310300050414a4480c3c483c0407010b14000390340300c030f008040300c1c415000001d02c82c40c03140c050002882070701c4540098130010300d05090048003520082c8030b4103001e080d1141c03040308400316544013002136500c9400d489454a00d103803106001420068802c0da22140305000c00000600d00f00a1584140c0c4a500c803038030000c013000c04020720540300c400866100ca042000b0662542c0c1c5c082810803800062503140311610300c0d001555491400351140d0810588000980410420340070b50790600b50241c03401e114001c95880340d403c0c54803000c0442100700543d1051011035000d43c001c00c10700d0303840814029000d20401041d2030705079100c10608402d1b80070a01e0038030284014072408107c20781c4108210 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 393018111 1250 393016861 393016907
    0xe04050606042d170a030305060a0e0403080906060114030a0510050310050603120a0206160504081b0411120127050103080903010c08060a0e181606030b0406030206030c031806090a03 80
    0x2601075103070030401711700801b019500c10000350380d603481503d640041d0841400f140c5c0d03180362514010b4040c900139214413482e0301c40da4000400303940c4109a80c2a1600c00c121086d804c5849009030f00380034200180c0a9608070350341d6400410340384c42c20850240b00089001010581e81003900515062544c40340f05445255802c02c01001e40c0e50300080d101e40c0100800c440050240b005000440d96400b0b030303802001c907038007a2100b445210722003044111207041c0f08680c1001081d00007045106a4451064036010400801d401000010b0035a83c18420f110b140700f030201c41c44880e00e03161804480f001d0b0401c07208600c0c003144100083c00c003442a1a120714031428000702900b403c20000704141c00d076105140c07240c400d540029100284020f48855807030240000c980c40b150101c2c40700d04c1422a00c0c003501002900d82418182d192074a4003900040300c0d005094107146482e2448400d03116400100785942180d004801d0003a841000c02ca0240b2804580020b015400e4480c0b030020300e4044c035440c090082200ca6 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 393019361 1250 393018111 393018149
    0xf04061d030a1506242304090b090a0203160507081207090311030708060114040e0a03020c130b0105040605090f13022a100c180f060f0f0e04050606042d 67
    0xf02d036105c0d5590050038180740c2c14a0038613954601c0300c0d9a030709120817020007103000542c000700c5401c12015408125000103069550070201c0e000c0b800129280e01d80c00d800826a0260b0600442c000c01540d800b4600707061a05a0240c2000020001650b02c28005a0220350410601c0301040c0740e441400e03421006002c629141481c016a10f68040c05143d41540b522082500a5a500e50111400c1c252000984e1100c40a608002e52070305614810540203100703a0700da00000c01c4180c0b054100d401c405841e0642041e08040c000c46003a0030103580903403c61081020f03903205545070501d01841c224000300141c1c2e2060b022400d003010345800b0754038141c3d401030905008080500440d81c40e140705400765000601c0c0d460340307e04685070591804050154414202c012075100306018842c026292903403150003404c03081b003408603000030ba10507030100099800f2a001e1217901c0e00d6000340e500100000c2c0400d0901e0b40358038198141520303404d440d02c0c0480c54143c0641c440c80203821890b009002e5100803050f06c00712 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 393020611 1250 393019361 393019409
    0x5070b010b030a090c03050706030507050c150403141303021c0302030f0c0a021305100f0503150c0903030c030d0b0a0b1605032a060c0f04061d030a1506 67
    0x418000c1800c0410080001a81c1941d242d2004c48029006030385000015928104603450700308600503000028148400030309010700800841e4507080d03144c0c00400c40f84072400c20b88040040050b0040741004581512409180d4200e00684141c10710002c010072150318520400c54105c060f4590200340c20710303541c1c26402094010003640c903423804200400d070b034076110268400d050520a540c000c1d404011581c10300108107a503800644907541941b0385034001034803011041040c101e24424181e241d4131007507a255014101c4021140c1110b41074201c50700307001140e00004d04680100d416078416500200e40840344d030300e81d0301641002e8281030320506003c40c2401c8020440d40700e20704003030b6000300c484801502000010402c9131aa000c6990000342d142c40000c9a6a003c03c02c040c042c0c1d58640f261001107011104280100d41240440e030b00410b00d4140380400940c0c94001e0600c01d4440c4035803246003a40b03140ca0600c00c0d61010b901c20340d1803504034207001d0488000c90358160410074140c2000014140c1b000c80c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 393021861 1250 393020611 393020633
    0x14070908120913090305040e06040b0d02011826150705071b081209030615011e0e0a17070f0f0e090c0a03110a0803030c040504180615150507 62
    0x14110000d42e00d0109402054120543c20201000740e072402c50404181a0301c0009403056030607958503408203031241c60412040d2480440700a9000303840b280c003480150300414040d401005030707941880c0215654a000d808442502007960401101c2c0d0100070340c903801c00d01c601c00d14550f140140c2880741c103100200500c00e000e43d11005103101c440d0588002a54010b420303050042107034a0449099119401110003943c102030701c964082d21480c1c003c5101020411900c1e0000501a034610304940411072041005160700341c1001c00b88028250094031544070146e28078054005003108084802400062900d40b0040358417410403803030808010b00440392000a88000c85950b01c0e01d80c801501c500c03240038141188401407079803003125000e00108001c05d0074040807091000b120015101c503603a0002980740c2c403080781d0304020300108005c01c2c0500d00d1b06070f201143d040d055058207450f9104035036840c01165803000c0e24921880114104005001d012070030502c2c0e5248038940a41800720300da0350102e14135 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 393023111 1250 393021861 393021883
    0x10915240b0304031e02070f1203080604051504020f07141b01050a030e030a09240e1203160305030103051c0c0b09030d140a050601030203010f030b0408070204090614070908 76
    0x41000408201410304c244c0028200c01101d8200d154083d2901c0e034003941e501f0141c424a401120800710005120034a0164100184d0701500c8070209a0346100c100b2009040c01854500d07a0104003c1c21440c07a01c40344003403c0100440e14446590703809504054100901c2c00d00155032541c424040007400e0703103100c2e5281d40d40c2c0000303007441c0361070b0300026405402600c00002260154400401c2040850350301900c090110340c2a003442c213040e0200d030300b050700b60f004458180c640421640e80c4801c100b41008982c00c101d05910005684c200440441446444c440c0440d083d000503c0100c010b10900c0010700500804500d10480b00c4606c004411000c1e1442c1e01c0ca0a0240102004000143d0750550500448135402c552034020002c600c0d04a484184014003074a00c5005540341000044280d4001e02c2124140c032010140e05a04500d07641c0d5420a002c0001e00440b0100000d214040068a13680030307804000e4400c1c1400b00d042602544035400c9400024400300400c442c04408000580c00410015504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 393024361 1250 393023111 393023129
    0x9030a0c060b011707080a0f02040b0f070c0503060f0a05090a020d02041a090a090b0a090f081309140103030e01021209010c08041d0105030610150e040e01091524 71
    0x100b4140c00143d50a81541502c0d110364072580b03080050340d55001520f18030805c00315004101d07554284100c2c0080740520300602c07a130840108007030108100c0741e4001d0000c451190459034101a00c03540807a051800995100808042100a1090310b40003405015844080c0702c0c028044001c45800080004409140281c080ca03502c6007142031100d0740c000c070b0004001d07002d0300b261402d090941c90a0002d08035503409540494a50001c100340105034000c160049800000701404951075440703030b6604e54041c542c0c243e0100c0e04007030002000001401045d0402c14802e032503841e6503140d82405030000d40381c03500d11030454100120700344154040c04103450303043c0d01c00e2814400030041443d02d40720710710558000450660704041d0030102c02c40e04407903ca0503668107038142d811740d07150703003401100c00c0e0001e0040c02001c000d900140342210784140e0300d080304035034001c20200d00c01c84204580f40c211f03448003106a0b4040301751908041d000b07441c0d00034600b41d0861981800b0031401c010184080300c1c0e289000e48551 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 393025611 1250 393024361 393024371
    0x1080712050d051c05090303060f330d0501090f0f090c17010905030706091b03150203100302041d1b0604050603130209070809060c030c2217010b0909030a0c06 70
    0x501460544000c1d0fa0380580f10701000039042c0024071b187d032500100e07045440345803100d0683c021818820b0307070300d2155207190300c180c180c00480c0d020140c10701034015640f0040181c107002c02c443c03100160140398000c005410307000030b5030414500108244c0d81c01d0800e0320115070500d040e110025494810500403075011030454844c00011a840302e000d00202c040107483c9110114bd05e070203010a81e03001c8500d0078481c9840e8141c200b052030b02c0c0541c01c0000c0c4400740005200c100709408003481600159484040124a00c1c400303070300c1e41d000404039134807043d203805440c9160580c1c5003880c608100c9400030407040403000b9500c40b0948000303130061080d070042d1750182401002040e40c1312412101110b42c5039005011180c01c0c98929001418088215400364042c441c000118031560014800c40340501c8a000d1345a18051840c3c40d010054103402440c03c01080c200c100c00984401800100390703006180400204040c020b91f401c110700d02d0030280c0307203c945d60003c103c914002c680100d15441c00c15407240010034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 393026861 1250 393025611 393025627
    0x10b1213021f0518090601080a1505211203060d11190e1e040309090c0e04020406050a03050124120e0106151206050a06051b100501080712050d05 64
    0x7a80581000020140405848100d040c10f030000302404d450785000001d003a5000b010410481d0441302a110b40c0e0100e03500c24085821f18401c3e030090360b841d020040c802b6030f180ba070760000703d141015151800c13110490026401020000709122011034001e041c9000d84c11818003000040303020120681c0117008503440c0e003003400c954032841d0070303601482400c0c400d000e5002c0d621211061880c0044132601c1220607130030004a810500b0880b0039000310b07056690504120304160800340140001e0040030144007000364507281d2692a40018800303045180c0c0e0715911800414405026170710103802803005080e05405075503160440c03079034600c0f810440e840c00c90a0b140780d800c0d10500520110b1921a815428440041100c0107402d070341c49400080c0d03a40f049640c40301c0d0295041120176031700a055104610503401c00c0aa03116001411070080c0c000c804003503000f80d03c0c94061404d01c1c0700c0704442d512038540c4010400010144106402440560001a408130f019a640c94441e040e4119101c2400303408207102c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 393028111 1250 393026861 393026869
    0x150f030504030e2b080a1209080304080306060706050711070f03080a0f1e09030201142106060906071a010602030301062a06020c0a20061c0e06130605010b121302 71
    0x864075010102d15030b00303130503850400001d80ea10108000010030f00c205c0c900340c1c80428511883c50196003014a480c2140c4440e0768181d125400a043e20b6031000b01400b0703a10110b1481d11803140113281d55110b0043d000c5010b00c02c01d0030244a90f00c8004900e2820380100082688002191041911450512186000c846040e0b0703105411140c02540b07500000c0c46d0028031a00178210704103490003605d07410808240d400507006a48940324066111850152440b10b08031102c001290300000c00411441c00d03e0032160100d500d9800c104015910181c1c802034911554031501645409002d640c030103145990304000016001c02c40b0301648001030f01c0c0c2031031500040c4c980c5010303903000b140d8408015550744411b0f184581e0764100b038450585081d00001d80c2400c05503500e13910140f550740040c001a0800f0508002c00b00d03030000d03050b44081d8040e19a10500c861000901001d8170a43d46809813007401000d030706220044940c140c00840298a0820621080c003600202c0c07140e02c00b01590b6902480145c40c4086 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 393029361 1250 393028111 393028159
    0xe0603040f172d160302031b07091b050a14090907020303060109062c0d050106030c060e041a0d0c0801020c0a05100207022b0b01150f030504030e 64
    0x150554001007402c0c1030b49994240185000292040d007007010081d410061a207100d001040324102080c100f082054103030540c4072650300e290181c019607050100c3c2c41d5181465100340c801c02c07046a0441617092010700401c0c0701e03000d42044084800407200180b480090010301c1030000c0c40c801d100b00030a006000700712441c02c84001e10300180114016080021f80a036490b0002e40d5414003240c200040400c00318421943c2c01c442c0c1104070081800085d01c05000c1283c82d1a0a0300c2d25002100c4081140c00f06000340107840085229511204503203151800007860340810300042071146051407207500d401140c502d0041d54610040360104002c8015140100c00711b01140c2c45502c06500100f005255041c0100d400b401850080e4292620130300001e40342003ca104100b00250320400c40b40520b1940a0320b803901808699038000d207004000c405407204500e441003680700e10844094244100d0006a100c8000e1132200d0a50500f40000d0600c3c1d90098081e445902046029500d4402030b800401e402042c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 393030611 1250 393029361 393029363
    0x91d070b04182003070e220b010219030c0213150b0904021b1b030604050607030c05070b0a0b04060506030910020901201510080c15091c1103010c0e0603040f 69
    0xc203011120010f103512040b038008031221404038000c00100c40d080d081003a900517004070128182c3e0105209070003030100420404044c103046108440390001083e1001c0c0c1c42800307403402511110030080e41d034410020003806c0e8101420081d0b04010011040c04111603c80054848480c401620381c0c901c400824000e01506e580c103038039428034030702d12107207110049044501003886681c2c0a6541c00a07030185a59150305881c01010743c0e00202c002071855200340e00c01100c48003c0d2604514101046d12041c0d6000f00a032040342e0310903910866203415203401d01c503c00c0240000d0b9429801c515290b105152100061a40b0080d09a00082e000c200b6a105000072030401ca02c500201d00d0349094942d45131380d25a00011490120003d00001c00c400d4800804410101c500340c2c0001c20741d5490040c180145100036141408103a0310502070f201c030341e94817210620104001b40340751400c6e200745c50600005040000e121140640d01d40142400c0362031340310301c48a5203040103a8565907a81c9403450724031040492810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 393031861 1250 393030611 393030641
    0xc051207031502071a0a060626070e060c06150a210c0f030606081605030706050a0c0b0f0601200a081305090124080c0403021e0a091d070b0418 63
    0x1420001c4c145c07400b0051401015540003c100b22a100c080c152422010140d00d03032600c031181050000b46102d03204c2415070251032450480d0301d400e50440030552680207034000d402660030607000c0129507040141d074130102c40340840340c494469161800404d842d40d0402404520031175019410020701144402041c02455656418015903640341004002031081d40641421030140c002240c00d03651800c500c8909035100280a021002c2c6091026241075000b91006d00038407201e00a40e0011a080010042c42039120340703482c50301c614000c0300041c19209190f080143c2600350300c0c05c1c0804004005610740131980d010f96042d9507030f40700c200440d0385000c0541c8003551050400001054003d2540c002200c090001e00404101140380e05040d5603020044036515180321082c0020000b602e880da803070740351410079810103030804500c03400400c44130249c6821483c0d410340c45240d0403c1c680c00c4119180c2c248403e203006050254289850300c101c40c46240702e04000c40a650ba50350780c18092940c011040340a000c0c03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 393033111 1250 393031861 393031883
    0x6080a1a030f010605010201060b07080a050c0109050d0314060d08191e05280206060d110d08041e080c1002030f0d0605090601030902090601080a270c05120703150207 73
    0xa200702d4040c0c4024094a07006500380303d00007540031030b842c05803075005034082c00450410190740320486417030b044284900e8040d0b49a00080001c11014058101c2d40da0305035802007060036180000130401080640814021001c0c0045e80020509110986091880061030841812f8003400e0841d03000c00c0d010441240407101010f1220f6258000c00140768076140070758500003040411203441d05a81b22031181d2005a000040080c010b032034054410442540b24841c108248001036002c60405884900125010400003500348072804803000200040c43c4040d04072902c40d4288042142c44201c0d983c0b2050140041401820340326000b4410354078000200d00c0d0554862482098800140111307105240c000c825490106081c2d500c00d006801d01260064101c2e40240c4854004550844008117a944180d0f62a41c901940500c85a1a01c5030700d444206940c2060080781080307000403039968803a5210b004500f0740003101100c0401c080007129005004564038150309500e00000e13108000f401040d01d9401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 393034361 1250 393033111 393033133
    0x40b011e030b030a240c0c0c03150906021c0b030a050705120304030506070309030906110a11120f0109140109020a031401060f270b0a030f02040f1104091506080a1a03 73
    0xc0039171460171900c5400611200d03002d1881030354030018000d405002201404c03814401b00b101c0d540d4030182001c00a100250100468075150102e070800c000f0065007004a41c1c14610034449401090400402180a0072040d1000d5a9071b84d80e801c0a0310880c3d0180103aa1580c034507608080c401d0b038000707540050594200d4544044000d009058104040340407400260002ca40540b09803112208084200d00400345880c0e20b80b260b0958807641c249040e4802920541d800044409000c7d080020032f00c2000801c030680e06291040c0400386295800b01103038540146030016030754400080c4c0c05c490304045661518000d10a2050151210740c00c100c80b40e041e42c800009444034498504040311680c40100202090515060400d03586c5464809a2200883c001030001c5081120508a040d00c01800055699800e44240b01600d48140c0c03000300c0440045400c00004106004a04100c1404003007000e8482c108040500902c9000e026180815594001069429940e1070b5034000d101d0024202c030300701040c0d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 393035611 1250 393034361 393034403
    0x110d0e01141305060705042105074b06080907030506070c03030c030b01050315041e022835010b0c0708062e0b0d0b040b011e030b030a 59
    0x1000b080382c051240c20006942a44241c3c203840913285c41501034002c228407016100c4514006c000180d500340604480011071500a0100e02d02000d590b60840000c1c140c421f030099691105140c0a0030510044e8640c6030303559481c8600e02c004e4880c2420040030307948030382d42481d1a18031540c10090036803041100340440e50f86c001506c21b075158403d5400340300801500b942102074554030400280403030000c0c004503031514080034954441c50406080013030305101e075401144040501c1c0e8500b002c1564000340c004031688a02203900110152800702c20104070034402d001348000345680615816444410b401103c540d500100041011010300900e00c0342e507183c0610900a174000a105503662140140000d04240003060082c443d110091680160b03800f1040015901501c02d0f03840c10032400450004034510200d817000e002000c556403400120a4100c40a20048403ca0301500e03040c401c0e8009c0d441742c0c554010f643d81c403070f0040500d408030b681e0840e0320100745400a800340c020b08861707004042d0244451 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 393036861 1250 393035611 393035641
    0x303040b070c0b06090717011509240e060d0e010b01020c01021f0e0c0a030332031305031603110705011407060e10020c06040302060a110d0e0114 64
    0x4090640c8800360340710078070241c4002048910041c50a0790b8000040c1c107900d46800201c0d400411820800c1320014035440d43c81420000347c100210341100c0c0b020b200340455024090324003900350741110045000b01c0030a400c02014420070401c003000f00304081843e8584681007601d840e01c045410030f0125800c0e03081d0302d81c060b0202c0244c5600500c10b91070702210301c1d0710004010880110031001114103043e400d000341c001c3c1c2054140300c0364034861040ca051007900c4904181000710700995500311644000501001d05020444460310100701055480142c011600c0c21a5040314251003146d002900314a002130440c018400e511007180b040070034100a0540250880000700407140c00d031100c0f56200c00066810728001c0141040d121010300500340007440c0f41d4400100118844c00b214112491080b6540c1603a00113812058290481d809000416404000d51074200a000c041440520300c02070703000c0030f030740a5000400341558441010b5481658294401d076081c05580312500e2580c5011955040a08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 393038111 1250 393036861 393036863
    0x2030d0203040f06090812280905011b0503010602060f0705031609090507090906050a0b0a0c0302011803030c03200a0e0a0e09011506080c0313020f030a110109091535030304 76
    0x449500c0014008c2c809100505042800c504039484101607c0c0c800070000c02c801002203885660300c1d401d084240c03100700e141036001941a6186942c0b5814008004d080c503201500c80c2100780d214009000d00d450b00201541d600c9680e61f100b00390525281d8100300d403003156545c84902c8191604c0c0900450030341c094005d000359500f881c1d051154a60700c2042c480c540c0c10710312400750011000d0000e0041d403881842c01c68200b901070f10000c1408039030290803030030f00041c00fa02100400d5030340a40b122015098000c00020800d154404040b417450b01c2078220301849107000c5107003006507044201c0f16036692a4421400303044c195171072206914096079401e00810440301d580c8070640800400180346803207513000b240704001001d00c2508544464940700f081d1a001030080340d1041c10402c03894070701c1d1400c20000305014010b807040c0f01c070312820000150071130720b50f60400340e8202d007400518030403090b01d10500e40494600088413545185c902c8000b10200101a050040c40c4000006501401a001000d10700413 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 393039361 1250 393038111 393038137
    0xe060f04091a011508040f080c0f03030109050f07110601060f11010908040815011a07210e0a060e012703050a030302130906031505070324150504030302030d0203040f060908 76
    0x100313107154000e440c401e0040380e0050a100d24448220002195900501a610785500440700b94130f026044890558000360454a8415a40c0080006203051150201e400c0380b01824a0b003413201c02080116202d400500410081c40903001c404c2d1846446800903800328071444000b01b158160521b41180d803079105105501c900c0c843e41c43c0c0450f101c2034030001c3ca8100d481d54004c20881c10004808803681d600304201c00d0302c01c1034180b20301241d40784640c1c00720101e21400d80e58038a0380c003086004008810000f500000c0402001282804150f600814140c0409aa2001c2c00080100782c09500310050025040100180500000b1000705500758020f06009d909075503c400c042c0d502c4843c58000ca40880c4409803d440b221101c80c03040401c03581c80755400108628001c03515480c080d41901c02420020140180480003180800c443e4041d0138000482c0342c2e05150203850240b40d45c400079500d0107405a19149181d002010804202001300b4070b0001d40d911a078103005003150703420301d2001900081d40c031680c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 393040611 1250 393039361 393039389
    0x160e1017010f060c030c0c0e0124110d120b06130e0105030118080c01060b04080a03020106091a09150a090f0c020109120c08040e010e16020102040e060f04091a01 71
    0x10400640701c55003511030540da0034001d034546450403180c1d03000d05001500c5211007041f0200ba0745102c259014007030100d0030008204480c41f800003145c454003950070401040700f28090528512800715032100d101425103401900300c61035021500003800c0c1e411206501000005a6102070503410703c0104c00c80d9140c0c80414030503a81e85040c0360907120310750320300e01d840c0f50f034417803c0b40010381038002a00d01c0151050002a110744c403003686a889a0040e04101c255601001419082640c24001c20001e00314400c1c050000d01f03514007081515100a8400c940304000400000c0d040c1000c0305012102110f008140034000d0f9611101031004000048503041040e05080900003210300500a01e40220340c040c110700c841c0c40201c0021a0042ca4440e011501c0080800002540e100c84440f0a1b0207002c0814555040d030030601c0340c0707c1442900c1c12061055900611007003040c850f80c101e90725481042562100000c0c21241c000400810580000500240c10780e0343c0d40c0214804086114180d620081003465 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 393041861 1250 393040611 393040619
    0x10f020316080f0915090312150f04090804050d03120c0f030e061315091b0603060608130602070204090b13020a080102121605040f14040b0f0108160e101701 69
    0x1d003c1d40403282403800764030205038500c0c2014518401c1d0340c00441c0c1420341c0d0030162540b496041828055801d4001d18410500280851525544115040108031010443c4500d1952505c07898007541c840c070b40c07085540c006044103140c00390f1000300d42041811030401141a0202003c0c004d02c0140c07202030006440c08403580c82e0300000180b080c2c004c110081107140740419503a0342e442e8048443c5441c2d5201a110304141000a4801d40c15082000189511900c0e10382000b000404a8000e584500c007082284801d00c420b8040d8803010708081c03a0000c40250351003440d8000300c0c0140600c030ba001000c4400c41c0040024050000d000441042d1080710b010031410b640d44003071403e038054813250038102541070ac040352a01082c4ea1680303003564854144203017410782e200c18150b100a4542c1c02081c8108240b40d29940c589001d2184c07090300c43d01250040700d15141d14000920a1500030030000100f455400c0d01301d81a07024412000f00d06d4001031041141c3c0551480040c440086480c04007141542c0200104e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 393043111 1250 393041861 393041881
    0xa171002121603060b07050321100b0f0f0d09111002100506030a0807030221040308070807060e010203090c040b0406030201020604080703050706110c0c040902150705010f02031608 79
    0x50495021810080e074141c50300c04102146070391510081c014195200340c00618000500c024040c3c09000c0c074007868444240c0c0c0e40303203200d2407030314841e441c8942c003c00d04200420b51101c11035002d0391a2210102d854032510700c0c405407540b0540103482d02d01305c40420750100280494005080c950303c282022509040c070f000520407281d10341c020303c40268000c4920741a404070703da4021540441c006040b554542c0003601d130010319522030201500148c0122500042c8080c01504c8442c40081111320305141c00d107541c1f6a42c4040c00380e42001454040002503400500c0900d0704042d5903240321714000c541d6402c1051010343d545a410740030303c2c020b50811175510a540741920803035085a4068000d8165940c559a546009034042181201400020300c80c06005c01c4c403e00c290120462000146940e86038000441c920f00030081c9000e52049003061082001a110134800204100800580940721403162404034003502d292001c0d4400740748040200489141070490300041c2045684842c1c0c0305845c0c5110350 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 393044361 1250 393043111 393043117
    0x2010e1801090c050d050a1d07030819050c0f0105100b07120503040312060609031e2109030f050303100815010b030709080a030206010810060f050411090a171002 71
    0x1240031050840c004000451070380e005162151182d10785a40340c4804001c1e5502280d005407411016540c3d00c0d4500b61038401105481034011a407080100700c07051460751040c04134400c0440c00d54100c5c0d44c03100700154080c003231401d03541c00b0381d0b07080251103640c0c1e6011005402800300f1104195010b00d100c000050000b40002100c03c003036000841c0c001101e460711410f5030a82d0001d0000c8003006150b501c03144103204244a40702c080c2a5135925000786038690b0070701e445402180030000c598440d070b00d071044000841c0c00351007101820345036003020206200900142d410710381d103600141078940445085410841c001c402148192a01c000041416840b41c118540e942d1390319500e00e6800506c440144204041040a564820160320f03142d24100d0b00c6802007810018600c00440159000600502c20010140904140800351001c10018280303000300302c08030800f45110b840c0c01240d40e040d240195007030400c125641100b01600400525035206008050030240d910040d85a000d19046144030400c18021 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 393045611 1250 393044361 393044389
    0xc03080c01052e0504020c0705120607020d030209090723070602040f080307050a1104060302270604021819080f100e06040b0a150f06170906090a03050f131202010e 72
    0x329503c9410315050000035480411541d8203071198240c000385070360310b142e094100031b41c140004d08603500700800003a04c1c0c2502144a0410300d070051240004640307a80402c0780c0e1146880c0b402d02000c00018127110740d03940b50484240c010f03820002e0f9070014043e96400800032614040c456800c499520b00c3c1180d01c0b8043e011000300990003403070820012030190b50242c0702a81c40144002499070f600d500081400301540090080203c83e8018005c4d029041186181e100c0d00c2034800b503203840c940000ca18410b0681d1114540f007150f400c0c0710094a198090341c41d0f00030300180b0f000c50b54001c040750340030b613641d50610862a60003810044846081003011074928015980164801c120340c540e81242c1e8050b00e11031003525803801c54983c000030003940101500300189400d8580c450400c40070030541030050380061240060794001020300070ba2010000340f0522941e050318100c0d48038142c0c0140607010b07100c0c11103c04201d000c140c0011a00340d480500030300515200340c8a0340e1710104950148a25002014a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 393046861 1250 393045611 393045691
    0xa1103030622110d0c270611010e1b03060703060b0d090317040305041404090c03020f030a12080601030c0815100207050d08220b160c03080c0105 64
    0x1480044182d0310260034801054468042180a0030342e88020040e081890070414258550035581c00907900100418044410401e1383c4400c4c611007010348003004035a20440b0b0411041460b0070076401001e5001ca1400983c0300265110740c0440d1424088010206412a100c4d0007820046040203002e40310300c0040310000b10245040c21103031008500201324200050307085c000303030546121000c500e52000307a21032071081d2126178440d03091040e401c81900420301d50300d02640c5410180c00103d11044503800c100c4e907044409034206207544001c81e003040c4041720018003400000b281d0f44001074014801071700c102c20a076010002d0f10900f050441d4142d80955000740f03220490b083d600d40c00d00706428420f44080f81030044403c1c45a882001c151100702c003060651300d00c034022440e1513200a0440040104a0007582613100ea28104120700e85184503940744000040d00202c2000100f00310340640d02c0c0110380003864940c503442580c0006003e40401c032244481544440c3e080c401d0301e0324100c881001c29082034 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 393048111 1250 393046861 393046879
    0x4060609231b0f03040605010f090e070306050403090302130204051008070f0809030f0409050412020a03021f14010e0411100512150d05070e060312190e090c0a11030306 74
    0x41c442070000c2c0444005040e001d004020350401e05003410011402540300703030710019107589403114542c11511182c1007444110700f00651480c40800c0015098142c940060000548c1d45403442c06890003011035100940001940030306030600760132540507008850b415030f88030f0b0024034144402c40350250110b8a650126254000d0b00000c0d03440b81224580c4aa404c40807a0700c1c0064442e10086d458025074440b4401503200d2040100308100010099005451400140200d00c1c1c15078001e034645d019a00901d0007280c21a000000c64805c0b504041d81c3c07103001c5d044404155031a14182d60f141a8116015610a20b03845120240c90600c2401140741722034581d211424844a840c1e01c10b04140e02414110b000b84070403901c14403541e6009600c0141c984a0310007429200d20f4002c0e21404400e008018504c0b030b422500903a1000003401d4215120392515a04019046040c100c09481e01086e000c01d40d81c2291001003004107050705040103141992181e220600c8603030050341000d070369100458045030007035040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 393049361 1250 393048111 393048121
    0x14040632270c030f01020f03160c02060f03180705090a1806060e1006020309060301090902030307150e0c040612020f1c0501060303080c070c060e060906030406060923 73
    0x800403203904200c481c01003400085012160710007003040c14485040c15001001c40c80424901002007042102c8088025810552035290106080c00010030401203000c1c0000981c0b4003034440d04101540c603900500f0716482d699650141a11500115141c1000d03007018440c52100341000143c1804440c401480400c095880e0800100941141488800b1510342c1d8118000045d00a0040340c0c003408646514403900d2400041d00b03c00403038158020700554004005400c96512428212030540d0080540401e4840c01d42c4003207440d40c49890380180001590544069022105401489459400c0e02c102d801105001d4104411110355102d9105044440c081c05001810312481c81e0380a0340004000071032b016945620002c080e04020740465450b507440c00140304040d00b02c4800d0341c01c49900c0c00043c3c11b0003c0c0f0360340da11b0f40e13036158021a014017a200e040060140da6550864100b000b01030310b84d54489c2032a28040300580079030b004410301345041443c18460b12110020f072401820001ca070b4a1069158 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 393050611 1250 393049361 393049451
    0xe030c0706051b01050f06040b0603010303020c061e0a11120903070e1015020d080a0b0d032a0311071a030a0504020303160503091806060f091201140406 67
    0x118001c00c1650b030350403544120302500e0a00c41c00344249038460010f10103247c070b6801c20080300d0005080c0c5108000500c01400482d0740007891408043d401d46855546031100c2410000c2540005688500c50400043c01c0c1c0c00d80d5801a01429203c0910044a000c002da090142c0c1e0f40380180502260180d2201c0380400072a90b40840c0d881c4c00c001a0340d0480d00168898840360304903110544068050303800701c1c4a2207059640080440d5020480d00d80801c5401949000141301c00300c1c1000117420403e400040d181000c411034002c0c452401100454403100040c1e2030f0240c50340c0070b80c80d01c04d022030182d0103000900341d5040a130130300d00b04000407143e4990b5840000c45001400050800d030380503c8284490508150682928401f003805040216241d0b001c95080000c601c04080c2040560481c403428401680c0f40c0c00c0c03c1d200d00004075005a51201190008a840032100d002400e12070b40c202103000c007524401d200c50a0240e402164240031055016101c0824044101503c2c185070840d41410009102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 393051861 1250 393050611 393050617
    0xc010212030c090f1f170609060d032727180f08120106030e0105090703020637030504031d1804020d17030109061e030b04030203130303120e030c070605 67
    0x60f0041070500c0c851000103170141240b07601406480894508840303804d03035143d01c4450652003903080300c8491203071624102280c250000390300c004060024180f81c1d1000500b90003140c210600305e07600741001d8a40c0d00c0d189083e038a0517108050501004070b05c1540310880c2c1c6805022481030080040700d400050542e6000e20b42603084106507200035040c0030703812040c8081e55160f03000f04059640441c022480e106820300b110000727008203000381e200b103c041005031641c40940300c01800350198056000d444101e00c0030100480c1c0e102181c04007480b8400219141c040d80300d64000c1c7e00030707954085c101d08000111200144440d003a01d601000000c0c0303801e003400608100710780c0103201901003030900380c080e6220b44081e0000c40d002030b24504040b0040c080c09030b0318031401008040405820408400700e110b16100461240000303004107541c4000501414020011109000c6e4107c02940f6416624100280302c142d064450136074160800784050785000000080d0b070300c0303d00e03007601804c841d038a800402e403140d80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 393053111 1250 393051861 393051889
    0x1a03060f09090a0503030f06011103090109090209060702040501080d030b010801290f1b0c0d020d020402030604020c0f03120c04060203030a0f0b03011e050a05010e0a0c0e0d050c010212030c09 84
    0x40f00710494000068028009940160b0008000003d81c0c00d0900000d04060f0045440881d568424005964a80e92101c0c9944c01c45913100001a070710703030b00d140104815104d00c0c04003a40041c1405c00000b50003000280f41c0550000d2aa800c00a541e50a401151030310002e01c54150344000101c0034520084120f1aa11040b200b03c8040c14600000b100d6008142d40100360003804505444400021406080c440c070103003614212003a0301d824481c0d500042c2801034210300640116404400500c0c0740c1c94170790440e10b00a050100319440284000c014070b550b5032085054000d07000220010409141c803403402d450039036070160080d505695468003081c006009140481c41d40750380b074480e003a025403028810703c6100c40c0c415030042065030644848600362a400f42850701906e1406c40100208a1900c0c9030039045000c081d400f0a08100703640045981500054110b90b200f410000c1d081c0400c4400a5150404030082c1c0030307030740d00e101c071b44d030325a02d40d80012100440d010a0130440d0901c50720380400124580 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 393054361 1250 393053111 393053113
    0x30106050a300c03020c1009050316140f0102041802031b0a0903061803090b0a050f18030606100806010f11060703050f160e01030f091202071a03060f0909 68
    0x3105099001203940d10b4006000c1c542520910540404040c2a014407414441c0c2d80c14254a00010810126075035201c40484d8441240d1320540c51080040620494a050300100341fa8403140159080000020360003810f6508103106000007129840018001d4400b201c500013075040b42c1564692505002c2d41c401807d6000402c103951010210300c0b41e00000c0e00c0000c1d190394815600d581986006002c40c0c03160141e0104840c01559980c0000b41d2190810f0305036504c040b83c0c691112101a000d0340c09016401941e03540c1c1102081000917000980004000c5400131800c1f203440d5211081413229096040000d0070000f44070f4000900d0950040030340c1001d4071040d2900d9483c01000c03080103410158142c0740b4a002035200d406001c4c0100410000a03000f1a81d55070361202c014180d5005010407012000c0305041c59142c0711a03003403480c6982e0200c000745401224511350303100b84da44001e41301c0c07180c0d0091410150071943d051108854860a40788915005021110100742c0c1900304415407000030a060a5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 393055611 1250 393054361 393054377
    0xf030809010209040921030e070510110a050a0605010b090a291303060507050c0a030f03060504140106180b0706020d110c06060a0501050a08070f03180807020405010f0b030106050a 79
    0x40e51102e202d154400381c0103c0380c1120003001c2000030f050200d18141b4540805081250545100d0782c0880c0010071184200c481e900300c003082800c160380341c0d185008000154000c00c28030303100f4010081105500540b16500402044c3e8984041070401c0c00b551080c550490f5542a003801081030f814068403c44041554551000846542c0300c4107a9002c0c4c505219030007000349040080145a008245d00145681071a5041840c142c6485a0342c0303c5a08000c1c0c1000b003417052a00486009038000340151070007600c03d101d4605201c01e0704005900030700c650780004004401c07046d2039180b00000c4805949010381c0c92442e0100a4860340c01a400550075203c0310b40c1c0d1042440040645100102846581c2001400b6549003403401c005c0010307001d620181c10b10008206084603c1e45c010455640603105080012140e0880b15040b801031030507200a01032258112000d0b004e004148000e011114803c642c244460b80c0c0f10b54170000701400ca88100c045580007071005121481c000d07405000069554580404 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 393056861 1250 393055611 393055627
    0x150b0307120209041d0106240807090b0f070c0e06010509040b1c1b060c0206031611010501060e1e010503070c06091703071d1e0301140a0203090f06040f0308090102 72
    0x40b6400c00412014441c58203801c103c00325020f001f5040100520b24164070080394881d2403150400e403980450702088a901c00180c0d5440c0101289409006a91100c40d114520343c408515a503010403002c4e141c120351540c00064500011002c184900c40603540c0310300380100c54003440042d02c00248156801103100c0111760203505003c601120040c000d49803071314801e5118080704002541d60300a242000400d00102c1c0140c2c03100703005c0320740081e082ca44444400240190803140f50b050300b085c40005500b0503000017079040e402041c813201020121350780f2541041d04159694020b50725122035011800c00e10001b542a4028515584201c1c040d5a010681302c0c051342c1da044003040c0410154201000105c20f001d54541c1c0803d00040e851092020300c8031000d02c107000200269040103110800a014803044262500c00307420080d0402d00c41c1045035028104013004001075082280c0c0301c3c0350f500c80c41c40491181400020054010750b00880306021164560702c084600000c010140d50056408009443c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 393058111 1250 393056861 393056869
    0xe040c120f060e0c071a060d050a060204051008160806031e0d170906180c0901030b0f07050703080c0f0403150507230409020a03060503060910150b0307120209 70
    0xd20440c1ca15400103100da0400840d0302e48524041c0c0401d031040c1c81841500300082030703102076200014400c1641e41d2281d90345800070300b01100a48000b41a030007481d401c6402c010701078000d030064483c1140d001240c0307842e1100031140c5040803114103d46034182d00320340d00118010103040d90000c4c0c01030305499000e828a1000d030a440b405520241040d4442c40840c820743d640400d045245c041241c550307400758141002e1040d96944060101c4650564507030541c1e0315040100200c5840d0301000e08041143d40e501d0070008000c132000c0700d22210300c2c003401d0f00203284c43c1d10030403c95880c55415110502d854071140d010514580201e030214003109020040031020560580514401501001010815142150340123010740a1103641c1c002e1a4941030402c0e8004148509403419981821801a186c100e060b004401500c410343c40142c0600031441400001d01e00800c0054200c00600b000b4080010224041c440c010000e12906103000c0d41880400c2c00355104100170081d5207510200503042881e803500107 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 393059361 1250 393058111 393058121
    0xb221b231602151801090302030d030b1c0c08010515060a0e030c040e030a030b030c010c062c0f010b0118120c24030f020405031f200903060f070e040c12 67
    0x8001003030f6010402000381848241c00b040404420701e40304281c81d10710382c042039440544801c000305044d01c840144005844003000440864086038051962220701d08020b0302c200514000e1568079401d01000039440c0d002c1e5105818a0a4003808040c0381c65811202111501e1014411562501854004c01403584e5140201100c2d0809000a503035501c1020401404070342d200002540250401c0c09002c0f000da820504181c1001d030440408075105041c124900e4440840031011407640c03e0501d000c2181080002e500c05030491044002c21440ca240d50042d503078810031a1076240c44180e1403a0501150074085148550503114805c1a00004d840341812569400c4904000414891024040c941554540201c02c0d98950b8107800710720b450300f444082a110010840390000031748110005814007a041d5000018000c04903032843d00412020b403000081d0b0b840b6006561003803140b040840d0518043c141402d0148980c0d8a03402e03400c0c1c0c084c40501c00070f40040441d01e020700181c4030007284c814842d8094 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 393060611 1250 393059361 393059389
    0x2091801090812100302030303070311040b0703210908090f18010e1914010e0408120a05070e03010e150901020c070806060a0e010608040201030b221b231602 69
    0xc50307203e09410010718481c01c0000d0004054030881c80301040540c40100840303400c220203140200740e85c2c2040101030300c148250742c0b181c91800c4000a9510500d64850080c03888485111390400282c0380c4411004140c40004002615a80c030400c100c4216203802504200010006032100100503c031a2276019506800d9000c1c070a00d020890070407000c00101c2d40300b065408404201008108440120700c60052814003a17450683c0c0d92101050034002c10005644040400c503c50700c081e8542046000082c1405490000120f240740c03161745034031325040c08ac5050200c0200000e007140c846040242c07041aa000d0510400c9540c20060312001c00400e020b100041c0c0704183c0100020b0030903c05014064005500004000c81554014040268801007242d08643c0918020409105900000300300b0001c0101400654a01c0818400100002e421910b010a400b1440f03000381481500c0a541e9203101241403644000c84003e10503490034001d0280808000d480e210983c0f000303040d0f001c5488100d80c0e030780c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 393061861 1250 393060611 393060623
    0x30903090915060806010f0c111503090d1b150b0406150804150c0807210f09060c030e03070b15060301030f0b0106090b03010b0a12050a020a0905040b0d0209180109 72
    0x140415074000104c42c2c3c10000a00e450780b10710490490003400304005010043c4012070250f80c003803581e500d141d140c6464100101c80b281c0c1d00e0401150040c0d9610404591a020540040001c00928007002d020781905030001444e2180c03665440400c00180350405100c4c1d40261340340c0c070200c0c007210300c1a20074032091201d4982211a061605165446d10b80c83d41c0215141424400d8030f100540d84400c15940040f100d050588540d4540e601005141d0142c881c522a068076010460169019940052051030b008080030000c002c101c9008805a9800040e041c560344d0007040854002569980103036400007134a04286c80e2028080c00040c0503074003c1c2d0066604a101d52003140c00d021014610310300610150820803040c9103098681180c50005103d070514500012405902c05400ba80012507800201102040309261500040d4002c1d0011404400007508454002c1040d00f414810300c81c0e1071038000c1c544c0045040c00d17401c0144180b4002d0001e01c0074010f40c004d540b030642c0c09004111500d8411a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 393063111 1250 393061861 393061901
    0xe01060f03030810030809100509060d14100f12050f010507080414060115030b0102010b090907091103010f09020f04120f17120a18020604031202060c190309030909 72
    0x109005258550140c003407103084e0300241081001071102c0c42100c2d4290000c1c1e03001842220a800180c925001d051406900490f0003c0c0140034040f081e0321142e0100c0000d2001d44890b22001315002d112401c0780585555142404424015030031200c0091410070310500441e00720b8001c02441600755601580c02c403022400d01c505100411500420035022000207000800117036160910a1210005d6090070030207140e44c905010002d81d1003034100005240c0042c09640d064248103110f656540100d00ca0030010b240381400343d11403800420102ca040b109030200c50034402e070074468500b00030b40c859440c4da40c450b40200800039140e8024103e20754024020380300c2c0d003150030443c00c00034070030100749604e402e1450702003003100850880f4011090f04244842c3e400900e403500701c50789082249502c880a540890701250000070070841e07004c25944d41c040c9509030b45140e100c003000c684160080204031040c1600303a211403003040d8400d900854403e0701924203420910340d20440d02d02101c05510154055159072 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 393064361 1250 393063111 393063113
    0xa05060f0624090901170606090a020705010c1706040204030209061215250e06032806170d09030519110904060207052512050a05030c06010f05010c030c1202010e01060f03 75
    0x114400390040018841b088403005000c01c0d1140c40da24000c1070944185c44200c04a80018081e0341030342c5030540d000e03008101c01c2c040c040001e07000d803071280090401c00c20301c400016030034141402a6402c40380e02900d44022600ca0720704004201e16691034580301c0344562212811030303072540a200d40c05040038400290350906003444d101c1d156001d0007221070511071011901600c5898040841c0c0c1d00244050718144d86115440401c1c50404081c0c1c103041c0e00034180744001c141303070b018040c009203441d40410465a6a841d807a000362002900d511000d0090b0304110610700c3c807900c22040f82c4080c50f100364052a05d8549441c0000c02c090b1041c0c41c1176076070030760119030300e81005010040400c60001c0304456070019038400100200d41da03c28050076510800000000303007048001c002400c803065005064035191822000c0e01c95031244244184102460366240005640d400343c0030421105d505695244110001e507140c01d0b0102403e007190808540d680e002d040305509080c0b00e15805081912a842c41280c55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 393065611 1250 393064361 393064369
    0x30312061926010203070509040b0a0801060f06030b030f120a050909100e0f060603071b020402040e090706030e0622230111030112020103050c1612110a05060f062409 73
    0x95810202143e0f01c10001d1004168106094030b0504204907804148490f030320011400405040c0c1c420361f865800d104010038000040304285054803020303a8100810000c210400d81c0c0c9003d001c0d40440c15402c200003a00624003201d0041640101c0380c01c4c05031034120300c2400700d941d00c00d04890103020219401424407591035440181c68200701000740a40403420304000107146840003411060a01a004031078101e900110280ca0402a400520031034403140d4494503900c84400444550b5018040c20102103081400307481000d02440850009200a80d1030201400c1c1800c1d42c0550503d810340c042c0a084000382642d5006009500a2004400c0582c4140740050940320392608009108400780b005101c0d071204603400280c1c1640920300410345c0e89489080303001c83d110f02001d010f146107100302c1c041c1c24804202001c480f40c5034540d545c01d610b8588001c020380c54008203100104903070090404103030020064410181c000c0300007800040e01140710a90802d60b00a0400310b00440200460340642d1490 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 393066861 1250 393065611 393065669
    0x101115040b151e010306030804080303040318181509020313060f060311091e040503041d06130515100e09070905010909020310030804181a0303120619 66
    0x1072804161110719207000004010b210072880f10020081005030015880e84682c020b4001035402808042d80c03940c9444107580c07264001c603000d6010a40c10745021a000741445189011151103145a4070340f42e0032010190090107040100f10042d844d84400030604030480c1c802140504600b18540c1b1403000b0030b1515106881100290f5a0158680131003040801c5031440c820444510480b2201c80c00e55502591f24a03112621103601d0404d0b031010100010410000001c0090b940d1400c03146600c4503401611a481c0c9404407512600030300c10415003004c01005400031508201405080c2030110261400b040712207080e07134240341c00141c1e00080ad0718203007840e07038259402c40d400b4a4515031403400c10303001070b04039800c6100301520380b6400030018400d804403c10304030280d584040301075603540c0d490f03001d000c401d011245441030442c0740100e0441c00d005103044035035105001402440c1003280400c0803007509540148980c1d0055105e40c0d407420720032004400f01001d40400e00c031569501040e0030f110043c1c54 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 393068111 1250 393066861 393066871
    0x3070908010e121315020610081b060c0a050102030a0b1305010b09100c0b01030303050106030e0604050d051c0203010b0705060a09020a05040c050d051602121305101115040b 76
    0x6450b01c9001020350707502282c1d4400a00340080c0d81951030440941c84813104440740c0c448100883e443d0000c0040b00d41c0440c0982c0038500c107a260f94007054444207442c0d2217aa441004640700456010044003608005000d80b40718003040042d90107500030794943c6420faa00868403202c645a031022131200a01c0c103288012207068a100c001c020960614900004900c42c0a070001e02c2105a2103c0180a5200d02203d4040607400081f040c5256500d140c0500602070a01403400400d0404905402280d000a4542e02c80d9802031b0042c9600d004800c425200ca80c0550001c002c401d5908010500c0b0507441d00045d4000c1802c0e064050303a81001e07091480c1000400360131194518109500e11006da035030b1402e20821b8640860300003e100d5000c00b0242d40910a1201c030345d07a0503041c030b01004850810703940202d1910b480382d02500c01c502d9041e050242c10307209e012605010352203a00800c3c015803c19141c03140c2882d14030b080c600b100e00e0b907078201985881c4040e2140100c00807801c0030001000740e821211034200c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 393069361 1250 393068111 393068113
    0x51c0b040e190807021306030602030709080c0d030f03061e0527151807020105040c080706051804021b010e0d0503090a02012f0106030b070804260f0a030203070908 72
    0x4040d0801200c40b5404414102609118020a2403c103641d5030558090580710201c00800c101c942c0ca00d00000690400c80e00403020500b040d100007244c0030045001c8404400c0180000c03402d80c0a5170302540c5d8400304031561001c065039824085407004200705441203543c00c01519081403803130300c0c041019441e10540d21744034941c40440c0e50740420101d01c0156811046005003050080c03083c0000c101a916207803200c0032a00355034000e20450540650240e80030720b02a03d0f01d80415a11484200d503100004e10840c0d000900810400d401800c01c2000c207500040001d00140c50031280e90004a03945440c07608941c403995540e0443c0e24201d2041001c0c0d6284d56145c2402c41c11890546401030302c440d0783c0701c0c2c084d0504c80e02950050306400500500c21102040c0e4000319080241011b180b4000c0c83c040c0400c48610743e019004c1000c0354040c1600500c41e6611010019000d0f00441d0350782500d02455a28000c402014444040d81c008000040c040e1000c9580c3c0044e10307071031301107801004484258081c03039031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 393070611 1250 393069361 393069373
    0x1b0f120f0301062102030c0c0c010504080a1b0e040b070909050402010c020409030201110d02120c03040b0601230f0a0305070905031c09080105070201060503102901051c0b040e 77
    0x51099900550b41100c070b0078240041e4062011403610400b001440303007130415510010030428203085c00009005043c00b208103c03010510b0103401540c0502c03590080e05001e40c040000720000031907850503000021310411071451807585cac4200113011365409803401c880f00e007604001c00c1010755101d0001002001519000d200034141500041c01091030b40101034015510b60a2120926000b5000310b144244503420030b0396550b02ca0f106000c025000410310201d218900c2c00032801d500c1c620401da03801160810202e1160b5210782006403a0217040303107444042007201001001d0015100006006a02551150075649101d010001011200020a014103000300707120140b00b175407800614410203403012011458941d2100005071050800d95205c9109507013080c0402c110f00354190480c10444105a044808025500c00c0f0907007625000d11020030040f4480003600429505400a0120750f4018113020346400007043c18065603035511030510f080b540c1c0320740300c88101c2d041c80d202d0b41000c0d074400300203480 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 393071861 1250 393070611 393070627
    0x80402090106050304050c0a32210712051536030903070906030c231003020702030d091a1806070303150303170c03070e090c1b0f12 58
    0x314080600880781001000b10014042180801030b0128181d070040c5902000f664642c2c0310f212040c10070f218011103110801c08480111841c07030f0561a48000202550380c1071582c062506001d45030014901e106100303201c0001103612000005c0728050780104060300c0c8070ba044d00000c0c20000000303060b080c0000740d081811044069803910803259845158011410303900c000002c0c500c0d43c001d0b410b103198540503541c1c0002e10803040e0760150049900c11200c1c0d4550541e11200400c243d01c80d894400544a0321034880c46003840c0008032104214410b003001800d01303c1d6500440d2800c954114228042a0048028000c40864105130b10b400340704002a145018414845000240a031081d064082c1201040750020180250007049000c01560004080180c1c0c9023002841541043d03448100d03981c14002281e082100407048a204540d1625403226800040d13040c040412002408c03460505014484005241540840300f601c10740e11070000c0003101415041c00307007016025102c4110100c420803c103c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 393073111 1250 393071861 393071869
    0xe04110405150319030201230406050705090604090b130906020715023604020307051902190809150a050703030b06030709030b190219030b091009091e030203090907080402 75
    0x3c81d480f02074110b281e1694000c5c60281e01616940c850101e42803072900b40d860543c05401c49240c800e5000f030500b44400e032144001511a40320700e280d03242d00124204802d11001540350051000c2a901800c080100b1310320355005c10464282c41c47c100c4101d50000380042c180600e0715102c51852681000071442c0240e020704070361410f00d656000d10500e016211080034001c1221250031000d0340054001d40d600c0c941100c0041c4546e006010054900b044083c040000a1002942000c902c08403200840725a00c1034407209410b4102003d070580c85280c9480c8410344142d0600a000030341c40c00d46442c2d46840e1981307405825601469503140c01500e003841000350007a4031942c403a00b20b070b030017a10038685500c4000301903541007201d6a40c0031240c0e000040c0408003120000c04207000c100c441e03500f00801d040407010807050b100161032255003d00318550074841038100b54010900e9a10411401c013040c0c26605d841e0b001001000d000340d000da0008107005c0d03000d0405405075076001529103440541890f280c1d0003e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 393074361 1250 393073111 393073123
    0x70b0601030c0e0d02060f030f0402150c07260109150605061204020409020d210e030d0909020a020a020301180b010e010303020619020d15230a0902130e041104051503 73
    0x56100d0011450010f0a41d15403000f1947c1400c445040c003907891074003c0b050348000c14141c5040b40a42c00b0307240d2080b540c0003244180e803c19030028001d041c003686012600d140505070503904031400641e0050504c030a810920800110a100f060b0800604107821080400c40b5042e0740064021035040000340d119a03c800e0040d40e2103981110001500286400812038000c4a1103008058603940b556650500042c4c03100c40c910446256241751406460500349501c0c0d035900c04100c004203040110501c0303445c00d145c014000c982c807644100d800c40d003a0750300001d09540d613543d0b0108414103407113601c20901803a919498050030003d0706003903465145940003952001c0c0142140c040304264015680c1c030140d95012107a04620700c2000f400740704062280c0c00d41e001c949206520030090441000340c1040c820036010b21240000034002805e0501e041e4000700698010a54002c7d103d41c0301c4800f04812115659040c002e9004134400505169200c00384030032950301400480e0040c43c001c0b40d0b640035603000908 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 393075611 1250 393074361 393074387
    0x6030c0c02060304050a0c12051c20120a0315050604060504090c0516060b030607260a0f0c08222f040e0d091401050316091208070b0601030c 62
    0x34840d541c2d03072a81002800c180b9500002032050520000015031120041d20303c5250342c1c041d1040d0ae099000c10010f62032100c9500b00c500340401c0c0b010000454001100400c4416104510b0a07036000c200d640030b030b40780c81e0b51000380c101c008207540354581855001042c50020141c00e007030314124070b89030400d4800391582c0218401c46004a48400d5085960b03445082624440e0702c0b0000800419801e904c2e0420140548680c01c6020748a181d00141d0708074421544002010368403410701400c1421401000d80ca0340d0000c0044651030780362200c00c03007110310381e1044d550000550b5031034800f03605204442030316990340c0b114468176403140c070944030006c151b0482669101d04441940c503000110b580c4641c201d0701004410642c1d000303240c4103100c6076034400840c02c5482440e41c0d580d0b100080c1e032504801510440000000d83c000b440a01c001407003402203107102c20b1108094101401402c0e9645607000507180c6003107040741e80d00b801003524010041d0403000c594020100342030501c0081d8948400410f41d40c044c86c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 393076861 1250 393075611 393075619
    0xf0b071703090a0519110f060406110307020604061e050a02031b0f010c0302090f0d0507060e01020f0601060507020a0e13021c0506040c170a1e060b0612040c06030c0c02 74
    0x45400000c04000f500721140d8481c0903189141c100200b031240ca40205c8600b99082810b90603c000b00c2d10b40601600d4070301c4c90040840341024105802100d400006c01090000c0384010040c4401580e500f0300900024075844c1e58640034015607a0310100c3c88003150300a5000e00c8030502a07045010b4000c0140c0c1c2880c2c5101c840602c0141d03d0441141c944406e04501c82d1442d440c01e0324030350a01e54160000e080080003965166004540d0300244140c2d4422480050034076008400c045c008148160080d2018000520486845500b074402c0c40703003071400c01e900401c00706500040c074030210304002004500801c80a46040b04c00e1030000303001140c070001200c0081c03041c654080100903400c40b01210003200ca42010844860345014034040030191850300a04d039440c003104044082c0400006141e017142544846515800d000154100c0032040c400c52044036401d40700c90001c0da440d220075010303200f80c0501510203001810f05062103001c82030075820040c20541031200c044456600300c841c40480641c189c6d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 393078111 1250 393076861 393076867
    0x81003121407050609010c0c0506040f03030b061201150f300e0303090f0f330903030612060606091302220314070509040b09010e160f0b0717 62
    0x4104899075180280300c801d4440740032034050144600054041d104081c00c0c4e00030806415180130035140f05003820b0307000f001ea902030f10004000426091140380824404d041c00711b06001d200c00010810b41140000d040e21004000c01003100c3c0410464080050034603040c52829100040e00060101185111042513074004681098800505002903148034200003404c0040303c0180710495280d41c002d80b4101503920804802e580444000b28246015205200003440d0a240101c50b002c101010b9030310341c0c48000b008000303007408025800c001c45d01c40c0340034101031940d900d0940c08004081c8a01410014568494000c0100b1a01c1d0402251104002281c000d0300c030300c0c0c2010800000e40f0808003011230700780e0341d00681e0f2071007a00c0d4240310060b24403c001d00c24107001d400013099580c0000d44580340e4494400400302c1c01003005400051740041a503800440c0d24900307200010f00d002c8000816015607110340708104400982c0202c1c00b80504240b0314040c0c5040490b03103c0011413009009000ca000e1400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 393079361 1250 393078111 393078143
    0x608100b2e12151e26191203150e061c0227011e0b0a050c0105040c080d02060112110a0314010207110103051306020c0109170d0c081003 60
    0x110045011010365180c28030040c0c841d00010003041c0824420701d00c10440c400b80d81404c1070400d4581e48160b0b40043c04c2c0700d114924200d43c0802030a24030715000c2040c010140101c24103c1007003820f1030020300680303c0503090782c04c5031402022910a2184051800c642c100180091400601d0842d00210b0480f0000015503031754070381400c40301842c3c4000303500500e1400300070703500962106c111411070500e0084281681e070761142000e80e20800760204102921548051000c80064809812103052a1500d1070503d210b43c1c5078142110015141a510050000d80400203918200300a0140ca04d0910181c0032951410000c06031040c040c1c500100641c600e00b044d14256101d810840f4004d5400c032045103050344103001030303d000758401c0708241c070100c0a41ca588259035009000e0b660003040f8484440c10801c4050311040001d4102d600c1c4c0503065505e80030700001080240c801100f46142d21881700c1c3e03464403a80c1c131070000c481c1c80075003000c18442410104001512104404002c694101c400c03105450f1710 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 393080611 1250 393079361 393079367
    0x10f090e060604080604201206131515080c040212011202030c031015090c0f03150b0d0b03010c0201050c04090f020405090f040308010f05030a1103010b040608100b2e 73
    0xf580c1203813429201c0d0104110a005100100c0403d0310150034842c0b0f0350702c0c0c504051201c0512452110022030b481800803d00419007c54000c0d0a14020b001d60b55905d1884948081501c10301202000e20406200c0113000d44c0c2e070188007905110380101c3d030841c40d100013040d50b5050f0340d00c1442040e80041c0040f41d010709544092101e060680001004c7d82c81c40300110381101d00030612081d091104051002c00802c8950f66031107694583d1070b013621446640040054220003425405880c110200c0004e1030000341060180b01405221083e90320226000c4d44040038036003182e00c0e10303602404581c14a002e0054200c2d000086805503007110001081c02d24005c2c0c03a10010b842180c2c400750700202184100000c8032584540315003c0d501c299110142641c2e01d4200202d0000306025040e41504601e442c030700002d60011851460f040041c00103e40c6a505400007000c03501c03181e110302402c2d00000e8400048107103e21400d448280106c0b1200c89815040a85101d1000c400c401d1030038007030082881d0702d48a40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 393081861 1250 393080611 393080617
    0x91005040204060b1201060815011d011e050703080a0b06071209050a0308091e06030703090f0503130315060b0703050c010212150a06050f0d1805010509010c0806010f090e0606 77
    0x904c042c80f9900e070100f0305407500035903007403180c400010103210110710143c050180f9141e00702c3c1c0507552204c1d6074084141c00d944aa0030400842d05000403903072306000b0301280111481501da40d0381c852a88507205030a0241441c9402000804038625002008195a81c0c5200307403001d403900080300301c1038040e150b2010741302c00703020b0b8100c1030344054500400820040c00300c3c01403d05070707000e403000c00c0304181003a000450b0031011040190710520501c00a01150b120b5400154414025145a41a01c4583e00ca103400c40e4030a0b441a407000101d80c40c184140300700c0911060b80d282000c40f08000b91840c003604a01d1038080c07400000c08010000918000000e001d40641c1c0c0d442c212b00810181c90b00700084140c949090415030f1500410402900103503481c088c00035900a00c294000161130514121450360040c00b5441042d01c1c040100c20b0705402081003403288500c5220107000000d080c0c488548003400f4603900405180c100a1812603030403885a003c02c0711011100908491403254503001c0025902d80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 393083111 1250 393081861 393081869
    0xa060e0102161215020a0905010e0307090e0105091603080a141b0a03031a0f0909070b0c030307020115080a03180b161b050d120c021809120309100504020406 69
    0x819845011030f1074082d404148110341c1c4100000c0326022180c0d400d40059018001461001c2030b0021b07420003142d400360680829042c002410b0710030158882107101c08403105020a042d40b44e55400400050640402455050090001582d4001d03450b56030b5040b1940300300070b4814204103107100e0260b861030565007a101c20b424000c840b040c0301c84088107a540d88600c544000d90001e4200030012190000000d100781c0e403400003030301005080440703109100d00c1807006400400399204200380010041c000d0750240107600c0509010710390b01e013840c56009003034804129a107482c0b8080604204140c0c0320029512104c82d6150418258021030030303210100c0c034400391b031240c1410722001540713456024418400c441c1d034500c038565040c031000c0c0706600b420fa02040d901910340c02c4400c0c8810400803503910020024100c06505c1d2001410916a000c03440f80061041085911180401404080c07042486800560103200360480c1c210324240e0070381a030310001e10b600c80080715581c2000c1400d544079900224050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 393084361 1250 393083111 393083143
    0x61e030a21024b010213090b04060b0d0504060b0316090f06081218062b0b0310150306060e09060c07030e010f1b03050301080c0f0a060e0102 62
    0x10800201c24440e091400000900050245034803050f01c03000825810950210b0031400c0c81e151020000ca0711241981882daa4605103001e855102e040500c240018a0024841d5040d00c0a044c5010100015101107048462196041400030702180c000ca60a59001e1400f418010805031181e08000c4000e01c00c00b03e0803605401214070a4016544410a942c01c0311280e81c010040c006d000c0580c00120b5040d0702130707070450f034000d2040011400942c0010300300300b582031000207060400d550009062540002802c2c01c140910522600c6080241070041801860540e03040c410480c800001070303110b916210070031180c030350780c1c0d00b0016030101e5900f1705601031648010208440c64941141c80d0000e07400320b540e0700440c8a182c3c001034082c3c00c03400641d13403219419190004d0718401e100c01520346004502200b801c0002818049068a5031590380415050003a21055600c0d4100f00c6503034207003142040424025050710804042c16200c8140c90022038600e85000c55152070301d100102d091085070362400d2a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 393085611 1250 393084361 393084383
    0x904060902031009050402030a060c09080d031512030819111225050409050c0904021306140f04050d0809181f2403060b04031118061e030a 61
    0x5448660300030750080f0050403010031007554070704013603050354801c50b0001d4040d003100c1c580100145c000c2e0040303c0212060b0402d06a155103079a20580317800e4a40c5040000a43c4440034001e04c0f44102e03a82030007500c42502e0103c05050207840203400248041e050102030118040c200744911030b0341c0d120b180c034514080b071150340c1c0740c0344050510101d5000b51111241d81455405500d0035862505002c0d0303095100e51501c500300f5152075000d800030100100108125102005403c0c40c0781d03201d01c0100048200c00054080c41400d020380180203000c5000c01604c041020080c6100080b4020705903030403640200d0f0003c40c043d20303500c2c210445028010440d90011011300d04420448243c10005100700980d0f2003096502607400039080f032020b4035105443d4000403541c2c1d0103c5101c006215a0b9900c5003a05001c1078480c0d640c0c40011607a40030ba8001d41780101c3c4110003d116152104136001c45603000c1d42c05c1a1a42010780000301e00b20545240d81440e24050b1382506625201401100d00f965004150185 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 393086861 1250 393085611 393085619
    0x9030102070f0c06170c030411120610050613030206130914010e1303050301120318180f094e0f0309051e0f010213060215010501080417090406 63
    0xd090b5103071800498503c02800030120b5018499200c0c10003a0010a814001941302d61507080348a500140058521200003180c0c40d00740c1c4c9446120140300d82c1140020500c2c2d2402c030500c405484229082140b01d00010042209100c0e000316a92050325012548242d0f2000c0702041d0360032004031680715441140c1000c0b0003400750b100c41e280b0a412074041000c01c0e10b8540e5002c961034421200180700502240e02030006005440c611859410074512030300340b2030580c560710203080076910110340c440316042c41702d41c981078078440450290201d080e090010900407101d1a644102d400200103450aa0141500e4201e03c000103002550040700b00c2c94590300c05080e0220b42c41501d05a401303800140101d00da46a8401401344a07105252100b0f0300b0401070000f088040706a20500070790b242c40708032244100c0140d807080403020300c0140581c04911400441f120301d01400607080209840b5070301c04858440d0010805642c200c0003847d80710380d01000e1002100c50181742c940890084192103500b1920b041c034046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 393088111 1250 393086861 393086873
    0x60a050408030a420b032502010b130e0d090510030b031c0c06140f060108070e090108242206060b030a0501030204060b0703021515091306051006020c0d02060903010207 74
    0x1d001e80b070b10b413403140b109a8030b8002d40902c0b40300c29101154110386040c82d06c041300304108030040c05d21003544000700f00e07049030b0b40c0081c400c4008034121820351760b50b42c0c031200ac0703043c41040072080c8401541000d00307829241800055140002440b00c00915496501c00c071a80c1d0f0342481846900f40c41003140c1c0340000800c0c0b800403c580a0400d00b02d68103842c01000642604038504040d1150703500015102856890900445004501605440501401101481041d03503400c0d0401c2c040c2401000602c5022141941c01c2117458400300e82c81158819201030280304c1d040c1c1501c1c00b1505113040300f050b08a803103a19204000300b00942c0440340500d400300038040c80484d80e030480381c100da0003141c0c00e000043c0c0b25901c2d0b003054456010000c0243e4003000100d9120790304000300c141d0190315107000c28101820000800d40c0c01d0002c49045022400001d82007080000760710070580c00840d00381c0f02e0303094203040c180003941c0d0f0030364001094820780f8812018400c40d40c03110200c440100b805002035442d01d101d8a092 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 393089361 1250 393088111 393088211
    0x509040b1813050706030e100902040b0604030b06030d140a0c021507080d0e01060f1809061d100b0d02061605010c0f17071704080f0a11060a050408030a 67
    0x8440f540260000002c3c260f10901510090300700039805080c44050384020f24009000c105801c980054032081e2806c41a40d4810180c002140a452a14414074002e03040605090495071040244003603001d02d988050a2802603d43d0600300e41080500c1078032500005c0c546100c080071a400c80e0800140f80c5040140010240c040b02c0d0080e001440720400a0302418241c99007801210100d0b10448400c00c240300070420a0001c00b00007e00c00102940c55448180565502d0300300c1074244800540d03208480f20080050704036400d101541040050b01800000342030780c8030498041e20a400100700921b88a641c4aa204600b951000017000703188105080604521300100003a400b041500040c44c14210325510950300c035080d2682c4840010141c1c80c03c1d00c02e4104090812340306c10304240b15090780107501c140242011b04103922844005121918400c2c80c00340000c00c0903007450300700001e00000920260aa941002050101040200f580c01030300d150303002d500210304150301010042c0203150803e0080c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 393090611 1250 393089361 393089363
    0x30d2a080d0e21340501090203120304110f060d06030b150d151107051b1215040303180204110c060f191104030b150418030509040b1813 60
    0x9075083c40e12480c0a001d00f0360352100144120711402c102132081d4407802d440c3c2c100340e5010f080e4818800300b0800142d0039982d908040440780d40e95200c4d02682580307420020880c0d5110035540592943c1f8044d074501d12400d542da04000d010b40c50144021840e651000c054988650582e18100551660b0307003840141e80030107640c0d00200444a60704042a030a088186400c07054210404a12001668000000502c11840b01c19400c4030305010200021340180b0003034581c02e014150060049800303004005141d2200c1030044402d41c4002090442400c50601603070703200d030f01420000741c0c00c0c03050451400e80c810b024030021751207440d040c100355055000c0b1014000c054400403c4442e2540c420900304d09170401511604410142c40d0500400660b80c0d40080440441c17a010b52420310b5603e6541d0300030340c44259920984081106810080b030304091090082c0780c028010150f00100700c41e1409085486081c40d41401281c0361483c40d1455124160900360700081c1e814440081c0c6021050425a1042900 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 393091861 1250 393090611 393090613
    0x81204181d16050301020c06130318080705040b0f10120b0a0801050a0c080702190c1508180714040216050a050a03030f0501181d0d0f0e030d2a080d0e 66
    0x5000710f118141403003a40c048040500081c81c190f107a030b544c5a0040c84034800e0890810400182c40c015036600e5501090040c8403500007090002d050504200503517070300c1241307a4004c89070803c1d07007034042d80d5000c105484641c0034140719146403801c107191300c06400c210b10b1450b0044940b480000e9600e10542c40300c0d1152034203003810003052102e401300322042d02094900500681c0000d40301100340c03052012161420744075032540c03507005999240501c0d0f025880e07003617040491000d5003088404050080310403000030040e40078092190503c000038045441d40d100725806654049840c1c41c038100142c0e00d40c0350300d580180807030380c0c115050700e0882c0c0d441038400c4007100043e04104001c0c610b02200e000d8181680c0300c0712854181e01d00c118401d00700800c54061020f15425140340c50a14800c0140203104c0a428981c1c0c0e40090010300c0070b0007078250f00362469194003951000b51186041075100f5210a110740015044070b0140401d034502408001e45c507000603001d80300005400a444001c0e0b4005020200084 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 393093111 1250 393091861 393091903
    0x1911040515070b0408031906030f111210020a030b0a082407052b060b040f08070f14120303011413090201080a05130803040c0609081204181d 62
    0x48441e0045020345040104150b00d044040f400288000c00076591024110b134903254011607207140c600607200d4590080e141c000c524110b9400307210f40240c7c0c1c007078480c10544154481c0e8440c4c0c84e090f5a940168051400415804501424803070301c02e400003562540018402168240c440c82c10301d4840050340040030a84000480480f05101c408070098807812494586506040704500c1c4040c103031104000e03441070300c0010200005900d03541e118000141c8018514680c569080001d0081c406680b40c224141e00c0e070204004000d03000351032040b1810743e41c00d1b0208885a469032400300b102d0903081481944540004000440c141c0d200791200a01050200c1c2c450100e9104111034000b00c1e40742d010042d001600b003000103180e482c101d410a6070030002124280007c0c4601d40c440401540094500301d0300e401003410100b04060340000d0381d002500d10070000d04400e420006c102c106901c5240b00b548413000d44103150107601c1e08541e2015100c2500e1100c0b4009800503810007503102c040c43c055000000b180c031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 393094361 1250 393093111 393093139
    0x27150f1914190b0901090801050f0103060c030218060c0f030d0f060f03050c0409080c0307060209090a0501050d0f0510180302011118060c03190c1106030705040e19110405 75
    0x124070351992420105124000050800030081c900f6403000404c50f062280c2a580010007400900c1098451102603044d80300a50442c03070f190098482112003181010700610001c802c40d00c194440c00303041303442298a60341d9124021034003030503c01c04020040310380c000819400c01283c41500030000220035003600304022604c41580c0b0340256841c0c0005011030344001d1601030175040c070703a0010031881e025415441c20b2601c10b070280d900e15842103804903201a0081601c80e520305110010940049082c401404598142400705614801da42400340c0844000c100c61001d000041c421508071030000842440980c402211001806004003c01c170019843c000301c1c0000303110b040c0196031200c01c51171003249280d29000100b010a0300000211703032843c0010481c0d8043c1e0081d07900034024541c10b948542d00300074074038103009029295a0300f01e0341c0a80c00c20400c1000c03540d0b01c90116016510460740100071503c5000d0305c180800420f1507508820740c50312107051103688001002c1c1080740c104480500c544100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 393095611 1250 393094361 393094369
    0x7080c01021203060103020a0c1e060b1206160c0c2d060e24040906080d210e0a021305090c03070b0717070c030f0227150f1914 56
    0x42500b0b00c040d4000500c00300f44290300c02d80003400c40d1655032601040700b12540d2a4800c910188990b00401e0400b1440c1c2601044071034050300c81807940c2105c07824032400a0802039030703c3d040010824540d0f054081c102180d02c50184d0a0400c1180e04102e10781c070120303104c40002c4a000940300500d0000305da11079400b89054040259401646c00c2036513001741c071040c40001d00030302109050845c030046808445010b0880d8030000508010000b604012542d0fa10b441074842c100811103050b10b080110030940448021001120080040800e08000590f840b00501541c01c01000940095004000d804070303a181d001d243d005a80541d24031003d07200d00e050b00000b0150f41d05035901c06d055040e00d05110000104212a5100d001c0c03046890726146003010030351302c8400e14040ba030401c50f86104503804071410742c00c121030701003100c2c3c0c410f030303c40c40c0b0604015403250300356080141960b404250500c41d001e0030761074803400c502ca0b880300034010a04d03c511a10b00c000c0d0040c4c6d940140d001c0812208900889450 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 393096861 1250 393095611 393095623
    0x30c0e010e090d140c0703060e061006050f04060516050a0b1501110a1403040e0103151406130f02160305030f07050f0417010902060406020109030f0809101d010e07080c0102 76
    0x801d90302c0b4101000c00d02d80032007885170001c0020501e80d0091400004c0030600d10301414090300110409014a4640f01c0d00d0002e898040e80c008404102082c407132075030b060400004403026110103040c8a920744964000320025240e500500400750f000c0c0a602d0400c220340003800340d0040ba40c1d0005070f404490884011556010300391b0401c0d43c1940325101000224003c03041c030b40007950000090b28a0700c1c1d16813041d02007810081e80101c40d200301608030504030700218401d19070210b8130626202610b00b0003100040103107403008034507550185d43c0d2030800101d020039411182081c00203041d043c485112824054550b800454080d4204080b600006156030f10980450750880c405007501c600f07041c00c0408040441002c00802c11141d9601e440440240c2e0310b0b040900000d0800d5030011955980d07901c0d0061003490003610501c14009000184a4903180104410250920320f010000740d56006c031440903220000d00d40c4071740840d407900c186280d81210100f50402920400403c44043d6542e04004907645d070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 393098111 1250 393096861 393096883
    0x307060e1e120d0207020303130312021c08150409061d07080a08121b03100303110715030c050918061f080112020d0501140a0c0311030c030709030c0e010e09 69
    0x100300300400341c3c0300241d409400c4280c00078040f6820291001c1805020402c0c5420603160460410602c01600e58100700078042d109454010800c002e400f1701010700001000b6222500740c88561481c8140c0f900c803503000450041e0820810302280b4800030305414207030b02035402a0505e005a94011450790000161720320000e9010549500d08200d000c200b03540410013a1a107072280d90700072004440c1040c40406540610111220290f6092a514002d0006032041050712107580001d40104102495401940c4000005040102d403030001050107c03800e01c034111a580d80000d14000d0045540e0400c000a88658029580e190314003410b0040d41d07428121852180001071240ca0042c06005040d0159041d10b40c4050044088001c5035038a2600f560710441c030203d440d009200030400203003031703e004480314003d09040400131141c03c040c060b4224803008040404001c000000308020300e02c9032940b00000c68102c02d410035000d8503034480600000081c803070700c42c0034400040410720358440070460188407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 393099361 1250 393098111 393098143
    0x315010314040b18010c020c0a2309180f07150507080d1a0d0501050f1503070320120706140313060504030e03010e071d010b040b03090307060e1e 64
    0x141d95160b540d0307003c10200070001c0c1c0142c1c504103d9641d400c0c4090250000b001100d4003e0b210480486050001c001548e502c00810306100801742e58408000341d2450880078400d80d074002050351007541c4040106645180109079204500003c02e1300d0350041400c2c0203483e80b401e10016940d070703864400c40c0c0d10b00410502034005403040040c00c050081940c020f01c3c0300c00c0c4030f01c1030380c01144841e0002014800c0c0c0c2c00c42614039035152001c000066001c601c8460f40048500c02412080d06074002081c2d5400c01e40c040101400882d8179100b00102800d42e41090300312009204a0702003516180003034941d1547c0c4100804074400c040a02c00c0842042c098031301c01e158264054010f05c036643c03101c201a1030064801d03030070b02084441807a07460305e0070b001d0440c45424100042c52035604e0090100e400c0d1100d4110485000010740052180c03803c0c11044030121295a810140c490b15824501070a5207c0c000c00104598a045c486145044001c07654950340a070720034100c42d07441b0b01f0b01c0c1080c0e1191404ca80c81008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 393100611 1250 393099361 393099401
    0x20903190b0f0c04090915060b03090c090112030c02030a0804032402040303051206011413030c090e0307140c030a060b100315090c0905041103060306100e04020607020103090606090203150103 84
    0x541d40b81350f440004132900071040001d107d508105036804844464001078810800002000700382e040400c031140302c4a0013900c605c4100d40c545204008800c546400003010030400342d0000041d55410014013040c01c0d040560389075111365a14010001c03010b0110f0419132698010920030111029100303480450750507031507003032920100d00c01316034111400034000c0e8184a44461400004519080581030407540600c002c03c0d09030850170030245681c1d03168041040306051101006180b0400300540d080994080003903003002d40c01588880c2400303005141960540700310302164080c488180c00a00401c2000d440c1188007480e1003c04800b5941510403d692080080c0000c21a0400c1c0d5800302c0c000813114034004454680f1500040c0c01e5505240500b04000408401d01c1210719082c40060b4008600c58400703a071183c6046200540340900a0010f4490000403c4182c1507900a41003c880254403000400c203440d01c901d0a0340094000751402e95040034000320705d1404d94004c0c80341c1c0001500e801e0314624 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 393101861 1250 393100611 393100619
    0x402090118021306030204060909020325050415090311060309060c0901020c0301150801060e1003030309031707020f0601081b0402090d05030c030d200a03090204020903190b0f0c04 79
    0x110708104442039000c0c2642040244644031031060840301411180c0c3c3c01590b51850050014160300c000d8200000a0f4410000d00010b01d8100071145002d00a404462080c820059410399550080b40e0000d040d081d240041d004026030310640c0501682d20500300c1c00c00202c40700003407005174041110b1540320740d44001c0c00719000318044006804010014411a04240c1c0000c02180c03d541d0f2a4124400569a402040c000714074207000c1e11001e0500e029011190f4a010980486040c1d401e200c00360605544d155007406044c881c409001031404011154441c81c104090029990084990480c2403800b0707100000c2134212000c55041a251b8030b001c1034928010f988020407000754442d01e4119449510000c2a200142c0240041e0014420b944003441e2201c68220321142611504a42a5003d00c040b113025000b039020003098601001503803900290b400c03203a20200c0d000303103d140f03250341d411300c58003200c48a0083e500c0f808000541c81007400a2264a90400d09060300300b0940b40481194010f00081c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 393103111 1250 393101861 393101879
    0x60804200f0307181a0a0e04030c0609050607031103060f011115091c1b15060302031002040915030f080708070804060906030b03060601080a0e030d11030f070804020901 74
    0x3082018010900000c80ca40603002074034048040d4001d500071501c82d10203001c464001e200360002c3d42580b54800520154140001e03c2001d06800760789090004003010809040c4508101044258043c00402c24003469003403695480c201240c04500080c02c14059290801d0280280d80c00fa44014101e100202070100040d03400003810b0040b440301c0d10134500800401c0038030703100f05401821050040c040122012400d400d029030150111424070003e900704c655944403c06020007620307001050301402840090701d41014249990000c3c2d8580324000c3c2c0d42d030405c001c513801042103841402c02004492010828100b0811aa100c09031031000c0d00e6030000d001c2140f030801050b50030b120f101011315000c07180e950041c164120760003071400104085028082c45405110300e8042410440c010702c2d452034103500081c20180c2c0103090180f06511401c52a0303c80744100240c2d003000300d00304000d05ca00c80143c02490b405030800c0b18521840c1580e4804681840e000c0c1c0140c601668000c1d000d903641c6ea082c0100f807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 393104361 1250 393103111 393103163
    0x60e0d0203030706090c24021005090a05010e1b12030304020d080708030a0515041407051308070801090201090f080d0c2d06150807120534060804 64
    0xd0741c140c00104000800601c26103e0000381500c81c114000540d4103050540844802e10440884603001c0c04407030340c0c00c80d5000905d944050001c410089160b50f2202c0040d811b0003c5060010502c2d030804007190780465000c54103140340105000020304c40440f650411041075061207921f00725400030070111700542000100d1441c0140a034911510780203483e521003015030f01c1164850741d803c3d545c0c024000000704c492003c0940610031502802040032072041c8541486001d0011028040c1c0010916500721a004640c0700602c40c103029600c5280c1d5136480b45018201041c4d04074001041c01c0404101485510f0211040e1703406e4000400c058041180c09558024050009642200f4040d404c2c16000151400041003542c25640d40f0400b0004e914110342610009a103103160803040d801d050021071400102c1004032005c00806040b08aa1424103a0408641c0d04011502a240b547c0c1421100510282030461b1550320310070a032000e0351000100e407401000e40e0b00070401c40990000700500f41c0d40941c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 393105611 1250 393104361 393104363
    0xb070b06010c0f050304052409010e0312130510050f27060403030c0203060a022113061b0f0302180d020f090106021506030705010c0f03021002042d060e0d 68
    0x48450082c2c42030300c80e908025481c0808541d2070384000313010310a0b400c0610040b03196100710700c0140514980340c10039840c2c90080d08085410040e8070a1603010541e01040200781050409032500c0d551109442c0492802205000742401645203808400007944108202d50701040d811070b040d418210858008100502402c480803010075130b02d05100c4103590303021f00801c011840303030311800d00701140bd1042c1810301d41d00900040703980307106001d000d0111806403858a280014a42d0301aa20f9907140e00c1c41141001c4c00c103024102d10301e45450509108150491000c01c04200e0300c0d400740d13048001c0c001728103912840e140301c1c50343d180300f02585569041c07541c40301d052030784003c3c0884800004e40d4082816154240e01c000010b80c00300c050070000e025450113140d0041c1c2c003074000e000643d0074800082d090361001d90300180203040c0c00f01001e080c98800c1c0035512807009892410365545039078070000300440d200c04a03406c0c4e00c03259000701004122540c00419003181c050340c444401c1e1164241c1040740d0441c400e64 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 393106861 1250 393105611 393105617
    0x8060f0a020c030f0a03140108030405130e07030f05100507051207030f1e06090218210a0b0601090e07080c0a0309052b0503070e1e0910060809070b070b0601 69
    0x42c2c8107000074107101401c06040303036840c3d5540744c00440d0340050a55030b0b403c1418851104410040c49110004011902a1201554420f07104203807501014010281034000380d0301801400004410454001898500c0c240110119144180c2000c01001103410076600072010600411000e030414442000713042c1d01030321038100001d41c0703000b0480d01c2003980c024070030510301554901e40a03072100c441e0348165406031103128421070411501c0d03280034410b428408c0205114440c02403c15461000168242e101501c600d03090703030a0700240f4079204002a50548280340844c62610000c41c000c1e1151218038862040c60381c44030031540345c1c446c3c2c5c1402548400c40c06000c041d151070307912010680c10490824034500c1110000303507002c0ba504030b540308a10204112010001c0c00c1051102d20b941c855002010320b0381c03c40f40f091901501a03005d002d01030100f140d846e0410034090401841c001c0d6409064102c03101038039448002c0d51180c682546410b2680604810b9460a2105401050b02d52440c0c0358000c0c0181 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 393108111 1250 393106861 393106867
    0xf12180609030320040b04090f0605030706020c0906040203040b1f090c02060402030f0c030d0809100507050d0501060908031b10020f04030c050a03020d0b0709050402031305011508060f0a02 83
    0x62503a406848121034240d000c84d84800c600c0401602c0e151510004960022403141040c0c204103121000d88540d104440714580c44003080310b0711607050703400b960041c01c000f02160f100343ea81d8030300a5100e04209038007504c0383c030f07481c40060503c1c00c3c1070086078400d0f51701078500303582c1307980c0c1038020b00d80c04000b80c9610341c80c802c140001203108a8680b1880d0514000c03500105600d02d024410103207804002a90418190400f002c211001e40700056100e29044440c2007101e11652601041880e0440d1b003900c0301031040c05e12050014a9401c080280160713440b42c2410b124982e2103d00546294266103e1442194070401403c00a10b5680c000c801c0c1442600060b1a0a0002d195007181030380c2103221034500400c00003600704200100030030740300c00400054a02801451541d00090b880300095840605041e85402c0000d10f000e00c12403e0b18042c2c24010001c648038109030b031303054111540080040b0740035071038a120403001950000c0a00b0031120314030014209643c441070010040740002c0c2007880079903028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 393109361 1250 393108111 393108113
    0x3080c010b041d0606060c030a1b0206030a090614060a09020c33070e03060106050c0a02130b03010b040b060a0e180c130501080402011205220809100f1218 68
    0x1e40250010005034901201001c40f003600d0182c01e040c2c0240c0600c0c802d400410505440307100100580d480300c282420503040040140c0c0380843c0d14844004029403046001040191401c0e07541e2003d20541e01400c4100805084103407240c0010f0010fa07041a0b000124103400c0200200d6a00102040c01c4000240c8502031b42224507050031a000300035104560600028039002014034030107259112085107001c07074840008101080d2108018062501000400115041010710411880880c0d40d4041c1840070306840c50946080203041a40107588654209441100075140c14001d00c03102c600c0050501d4070f1305907130b59026038007039180c14455178100c0840e14420041c44142c003080b41c420310080d120107030380d5061004008045013558104505106401c1d080c000541d80c0070a42c0e10f519031a9143c00a07060f00e071280e034030400b1000910035512903041c0402c60010410400c014200c00c00381602d8039001c01c04480340940d0691096006900095030788040d080030703009250084c0701c8d1500a0002d1603114080d03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 393110611 1250 393109361 393109369
    0x1b0702090124091a0904110a020709110406020c12010608061303080a0c05030609250207080d0309151112180708120a1d03031c05010b040b0403080c010b 67
    0x341e0114500d03030ba03008180e0b2400708500c1040d03240c1180394a000c0484508010540b881884003960040c240303040443c2a603c2c84d05d0301e5000c007c0e08901030741116112070041c203000b2340d592964010116200e0803c840f40c2105120081500c0640f031442c1c002d40700c0940c40c84e050010034518200b0740c0079a5904c8040001c0c1c1c02c00e080c40303254003446180d00d9506680e1290704028041c00f001038100d213030161a01e0500180b080e4440c0581b80c000304110b9500c07503a5110001100301c410f420761000e40014003800903c2e031403a030b000220b500840e54224141c2d43c0c001c40058080d07044828840c8050aa0030341c1380301c0980e24500c00ea2020f5600c0e010015030703c0c01c00342004070300107a004084810015201c80002d01210700001005840000d0403071b08003c0c4070000820000705458016800c1c40c41c24804400d83e440703034104000c04229010311014040f20380b0340f000b444416880c0800c07031060701072007031030704002180040c1880111030544403d428110f142510359036581c075103503000104810141d540c940f040003642e56 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 393111861 1250 393110611 393110629
    0xb0d020c011508060f010e0f070e030c040c05040801050f07140d11040b0909090106083309070e090a05070e09010915050108010b061908061503040303020a08090c03061b0702 76
    0x168040244518607005160001001042e00030040c001c10210800507030b03040d28032010703a100942d441d044601d80e062b140402c0c58070100c030b000c1035405800c06c1a0031001c29807101c003900407180030354000d00481c1c03180210f42080720070507600a00000c502180c070300b25a042142c014502c01c1c044035800500d0302602c0e00c4452182d005600011050000080d03c4c505a240800100303400140000003042418940400150b42e484c4c3d000c1c11882002840d000c10054002c041e02c00d003070030031010b8500c0f484cd1a10200c0e964950708030703001d110040c44007030000c103900c624000303912129158402c00801442d401c001d4107101100005008807150b6485000380c2c0d001652518080311a0300920a02040300d504051441d800c0d103494030b08a030300a06040c8900c10200181b0a0f40002913800327801d05074410b4582001080a004800000c5a60718800105110815515a001342400340c1c40d551480c07842d845500c07489445001008000d685940002c000c14549124045450300100c2010703d81480e0552550208607851 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 393113111 1250 393111861 393111869
    0x4030606080a060609050702280203010e0f061803041e080109060902010e010302070b010e06010c080f090a0e0f07080a02160507030b070c080d09020310061202100305010b0d020c0115 80
    0x5080b802e040002c014081c0103080213000e2001c002d028034601228000c2d81c50205031406001100c0c1894450040d04080400710b0f001a0042d00a0060420300c43e8001e80d51482c150315050700e8407810300020309040900c604910f06c40d0714000550300e020701c1d010034500300340102e10300300306801511040011300a00900c01c03590080d20441c00410140304500014011200e000c19060500d8010854403001403204402c0300c2c15a8204240b5400e5603c1d4000129000031010350000c202c40390000b02685194140700151003414002c0b0303940784c0e150340c881613041b0344000181d030040542e11408010400c0b4902400c0e6440d4071505019006003401c0c010000d0180b0100328203401c0d14145c0000a042c004d0000c058149581720402e800c012500844a5035411220b115828501c09804c1d5100d86001c1155030034400d085541083c240140145902d40500310505000417000301d2042540040a4505a001c0d002d0796049400705a4441d05001c0003a0007040654001842ea5101c3d5680e00c50f022594052400800050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 393114361 1250 393113111 393113113
    0x50d151b0807200d14070b07080405060705070305090f01021c0f0201060b1303031121030f060409150b060408150907090e030409020711040e030c010b0f09060906060403060608 77
    0x2e05006102902c0b01c03458500c180c11410380d5024000c04810001103c2c01348480501d000210314600a0751042c09000700d140040c07444030f801041c00882a40151701d140154050300540d11151190282a1054030490344010042041440140034502c0c0c50041c0c101000018015a0b01880201c142c10201a00300d105c0180855201210901104c1c0c2c24802e20000d00740c90004940390880c16000030820030101e20008080000c01504450509401d010b1940124080040303180e009500c14144907150300f044540c00300080c081000607102d071401d4020341c80d07400d4100b001c6102d07010b11003c4100c05002d080300f43d107400c03007810000080e803001c04000321506400504c41c08601800c08804190500c80140d0007401c8090500f81ca15289170008000c440446403504001a5190014070313100d2554940c51034520751051611000120072034000c001440d01c40c424400805c03185e61034030100a080f07120380c0c20141e002032031800028800d040c2402c1c0076070401801000f0134100307a540ea4070f2406541c071580010030700f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 393115611 1250 393114361 393114377
    0xc06070f030e07140904030210151d0f01210f06020301050a120312051305010207030e090601033809090d1e05181507030203040f0906050d151b 63
    0x255252040da0001c1d080d9001804080349405500303506944131403451031081c140e80d0b01050030075000700403d00b905000361070140305056085481462404407403144031404089156420341d60f9102c0b01c0074611a8001a018041503420018404503d4000d40d09401801000d40c0140020401550f0b42d1905103201d010050ba8030b6040c80144513000003641c1c80001e200c807806111000180c0c0200c0c00e01400e030501500011130b80e0729081d180c1d10008028030050610b500c005150000d0560181e000455800c05580e54001610f40310011411540e051380868050035885101d00c0c41c04e00c0a002c40c13101c0d00c11420f2040709014001c2c0006800101c00d903440041c2c0c1c2d009401514100e900102000d000601c80d0540310300c1946030322005001807040600440358041d8255901410350b4076158550909500301c2501503c50030310345006944c9611034050081d0007495404000381100881c002c541c165400542001c00030750199482001c605138050348286107071303103440360020680903c804e9200c2a00450765410300c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 393116861 1250 393115611 393115637
    0x11030f0c010b030a030807050307090f0b0a08010503030a090314012c07060e01080112020a090507090e09010603050a12030b040f0902180f190608071202011103070b06040b04020c0607 80
    0x3003150b420741e4640380681c200301c0c0c0074000700e9042424541d00c200c05d400c040d980ca54861000b1141d0403250f40201c620300d003902c5408240c019154000e402c005003540c4400c81107981303072001c0603900d000f0a0907080001d44161300500004000400c0181c003510104008200d0781c0103000200d05000c1200c141044084140c017107102044802c10020b0010002401d00d0320a03810140c0c00244500414041d46100341140d00a0030110345582e00681c0040c00304035001c20640c28036060040282d140c9200b1004024400400b044141c4418490201140d5000c03000344021220759031001c085260024500082c5a641d10000c190f58840e8010403180c5000e5110020750301c5054410481c5070070014070308040d007200b4501000000c03d014092550480e421000807940d0745014000b0101401c40c40d0488c19040c05060300000f40f90921103821005c282c402d80b84ca002e81000d01009998900a00300e024104450210201c0ea06040907408800c0c02a40640091b20380186401118640002a10150000b035906034101d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 393118111 1250 393116861 393116863
    0xf0d020f120a060b03010b1b010905011b09080706030e03071e1a09120c0c040f051b0c0303010b07020f0d1b12020a0302091e0c0a0f0906020d0c0311030f0c 68
    0x1da0b00101d03900041000900b000c4030708089010500501098000c0001c2041c02c0e8440b0004020288404400038802441c8500d0000d029100b000200c14000108920b80420303540a21090425501c00c4001011000d2a0100490207407042d2440c030407040c0420081d60000c10783c0740d50404c090b01c00041c1941c1d2440028a0825130342d208421401002c0c41c00c0c4802d0142020380410303504981c100324a00c940d110308690100c40d04000f420305030250f115250100c401d01c03980d296080680308141009011042d402a41d84a490511a0304484c00c03ca400800040c440b80500780060310f43110b4005410003c060303070031201198402c001034006498048001c82102400074004c00710761301402003181750245d6800543d011940100e0240030091003031074900d0024941510005c150065100d80b8602d054603401c24a45030141ca0340076511040006940031042c4500328000c02c1094201c0b0183c8c0e00400c00c1c103505550880b04880715510481c200810000301488240c0c042002d029030001c10341c42255544030303130003081d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 393119361 1250 393118111 393118147
    0x309030e060f070201180b220803070f03030c02120307021c020c010e01030b04020d050c0a110c2209080408010204091b090b280e01022509020f0d020f 66
    0x418032034541000818580b100311000d40300315680c28202941d006100104070300d250b043c1900070050024011812500307030980f80145443c030805407040d5144a9444c2c0381120348030700c18407601a08400c402007010000134400c1d8003545040045105a541285941c00d80f200c3d2a8010303204100181e01c04d003410303448a141c5150350070342d04900340000c15100f902a000603040350307607598200741455600d0740541c07641e40b600d804481c5420306c50002048280340c02030f2000f00320341004c0c0c04580041c000d61402c003900300000034821515036008150072605107002c040d1502020307501c5c840300207213a100c6600b400041c0292021780041c00c01c000015071100d092034111b904071000410940220740c2010880900941c000c5010819520103181c5140d807180308400e0107039481130301c40280000000041502407101d500c141c004070040001d90a40300c0320b40300141e8803001c00b01c540c0440c4552002d0309070208201001a070040510103100c040c0d46d41415400d450394012a001110445e0382e5080004d4a07c01e5a1103950030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 393120611 1250 393119361 393119387
    0xa0b2715071a06090c0a0c0f1a010905091f090b042001020115060e12030a020109060f0e2a0306090604021801080714040b031e0c0f1e01030b060307030903 68
    0x41c000da50f10f00300001480003030000c3d0950381d802c2000908917507101e11861405246a82003420a444901c052a140d23441070040181c070a0701415110004c52140e02c1802150b0203054840010842072400508a45004041007210030340a551a0314001c00550410381044c4030b58028220b410700c580c000e0511540c02c0040c0710b04a411079150028100c0c10711703503030030101065580f00e1402c8500020800082011622208260ba40c54031010510032035a50b4150030805a9905c50541400900e030001481003c1d03460b0340104840980203030411b1645413821b4064180900250800f124002c0741980219040a0042c0c031048040d0b0000c2c0104030943c00c00444940d5207246403001594150700d48262a038852255000e0500c07031004034031380380801c0c1e80c403500601440000142a20342c162104502c000c92250075001800740c601441c156031100349408082007840d07410150000c0d40c40c00b04400540c0c1d1049446d020f040c189659aa414005a180c49020314441d980644001410418070304002d0030850341d00034 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 393121861 1250 393120611 393120653
    0x13020915130522050613080f030a0e010b0607020d0605270703051504021005070c0b040b031905060102100504060608071e08011802090a11030903090f0a0b271507 71
    0xf400001420004020b40d0220010fa0390101180d400e18203207003035104014803039045050100c18010301003d2507102c2060282c3c420000c20078004141e003400941e0046a070003a5010403003c01040c0400c4d4a0f40005501000441c0044034a090081c0842c2c131061012420b2092540039100074820000304200000c0c0c041e101426090307d92429500184440842d030314110100300c1c010940404006c1c241c01c40324050120816504c2e01d44c0d07101c044040351500b00702c0d1241d40f00d400c11114000c1c42c140c2e510a041c015401a4090002480d01c80903507000b420024200b162515580c980c0054a00d500f801000702402514420003803c84030145429604651a00f15204076403515444070050103c121050040c02d60564290646a56042c403900040c0491320415a05460000420142c03060110003040400782c2203079200c04004c1a0800c1c424100b541c4d006180780101c0030000c0e4429280e081d02c1544507158030681d4144800c00301008110600b230b60501108600002140010400c2001400e031211884044 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 393123111 1250 393121861 393121921
    0x40e07080c0a0b040317090a06030c0e2e02150a02030f1005030a0201110c090f010602120412020609130c03051b030402100809070f0e040606050306130209151305 71
    0x503528540d548181d100003802c840c000c00c201c03850b11041b4070030354914060007008a004581d5688015025154a82c9040002501085900440d10b4221a0b82e440002c4941c801d2400e5401015150002542400b4110a5104107102d13500100c040049461140c0f840c81c50250b103e04044010144060001d8030046600a10a80a00c0302e5100015072880e02c41d02460601c6000220314000d03400c3c0804010001e0700a804001001084c5440c00b003100c0c106c4255508640407c00140c40d0082e03607010300c0c010f8200d243c0d0180840ea002d0314094010303118082e03004040813054026001030000f110340c0d00d6101408a6110301c100012500000000c0c480c01212000c40e518500c0d29074005400c0455118210042c46400004a68952010402d41001e4415199030f0380c2455101d84059a44200c111401ca49980c1420408645814041080ca0190340e2010302070041e03202c01c0d802c100d8079510007032001c0209010050f0180030395980020000440301e104500148030300700b4540c01d000c107102c01c5003040041e8000d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 393124361 1250 393123111 393123119
    0x109050a080604061d0f010e10090203060f07021606020706200c0909032106101b03052217060a0c0c060504060b10090806060102061605090f040e07080c0a 68
    0x100b4540c0d4801d9001e0700008048018030400189036000c142c2c041c5242c8a500d21840d842c0005612150b40040c150040792440f20030350b9041e0f42500e81002d070086d01500440081241d045100302965048a20750064800c809a15061007102c80b080ea8480ca0050b44070440400c00b4039000034035541224a0040c011211039000745a890365808a4000540612605c00014a00342014420f441212070042c8101c00306603500301c02d81c240b1071000c1d0f418511408a2041e44020136014294401d50000301d20b9168811508988042d5280d8119005414210b2507802ca0382120054801d105009007164100d844107685110814a02d0100010300c1c198003d0b2500c00030090309600300c0d2060700c4d2551701c01c5003c243d81c5c4c2c0714603000000d4010103030516041282540c03128403050704500a042070321203400450309107a0f85d200c012a5031b01d50035140301d03403118540029031000c24801c900500310900c010704414030030403504000c101150000741c80d04410b82c0003114144421603051200c000c5440c000c40d80c0000307507420 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 393125611 1250 393124361 393124363
    0x30c0301090f21090e041a0901140604090302070501050d0f05010b030103050d020d020619020f0a0306030b0901050402010c02270a150902071203240305010f05130b0103120e0607050c0109050a08 85
    0x80c0d0045c1d52440304010006410044560107090b202c03214039040c5610b80c20b00440d1540070707000718212404407100c0c4100040c52030170a84241102503805600a0014074a440015512a40701c41302403e807881c0c035118580c40180b4203000e0680280440444ac9a0b2503145003840360030045080203090441d0410f200c90070200b0390000b580c0e6000601d4500341a0700c0d203c40d00302c2c64024403641404840c0c0610100300704250325055400038045901a1103c0c58040d03895404041c00c8a808440080c04140c5c901541005030401c0c9101e00042071191030389500d882c107000c032038081030141101c3c0d205a198448000302c0790300030140c010385e0040c00280000d43c00c286c110394445044000b00141d400c1015540d148462540740c15003100d04030840401892000309813617042c070303038060040c42075031040c44c074202408500045034448200e104a074122110840316400c4d561402ca80002d2550f248040020f52252042c0c0c3d03030780d4030307001380a0148510b00070419817032220700150183c01039910891003508400410446c10380 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 393126861 1250 393125611 393125627
    0x313030201140705010e0f070e19020f0f030a0923100905010b1011010c0518130609020c060103020a0b03090a080d110414010815100e030c0301090f21 66
    0x80d090911691282c9030000641d0140200300c0050810342c24480c0350144039002042c4000b00707901020907200b0b050340f0303040f50b041d00c14007d8440c5012184000c00060318504151301528819403840100361505034164800900c5410644654030803070f650700c0320fa40411100752080c00c6503502051450644038181e18109449a5114000f09001625001607604204081d07203c019548002000500b03100045d900c002e0105c1c0d0380b000c0f0030160350310340848602c1c124001c03000d5402d206580060040d6841c40101031010240b0b003050340090b07040e00d0700342c0032a00e40000c0c0040c0c12179540400003494030b5803440c010040025160390008036100740c20020301c02c80080108500722025004040302c0e80d1072000703902c0000105030381c3c0301169040101060126900e2901d81d011403c0304800d1b80e880b0b800e902c840300011054078442410a82c00324444020040f440d0203904010340020009041c0c0311101140d001003400e46111900441d01d80010704699400c00c9110150420010f82920340642c241b03c0a52001e00009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 393128111 1250 393126861 393126863
    0x50604030b1305010c020a06060f0e0103062406032004210c03120507032c0f0d0206040b0301030b010b070302071205031c021c15050118080303070c030e03031303 71
    0x18071a800211000302c1c0041034090a07901c90001c10200d4502007000b9119140c804e001c9640d6810604000f81780c401e0066000140c8115101c0c80708940d1841d80c6020040540030304098000c541152032017a41d0032201040001004039440208500207042412480c2004040962107452414441481080f03000c2c591003154000200b5455203a6889003409814440242d00040c03812102600030328041e5032040140801c40d11036120000c00076240100c0e8845a850403a948000b03a0303c60725035040c18644140007518041001d0481e22003080181c0114905a0040d0403040032184c00000400030452004107040c010220b10703480f28107220b81964025164070aa100d1003803007101011030002807020502c101c682e05d182c080480101e41c8800f540c1c2c00e010f0341011031101854880f090501d482c40c0c501e800342079458018090500305080c10203005580c3c0343c0809481d894255118000410141d41c100010f600402c000e440d654480f800d0b9140052100562082903402500240044103c41c041c0700a1801a2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 393129361 1250 393128111 393128123
    0x10e1f030207140109081206040e0c09071b060b1507030804081804090605011406070804210515063a05032505070e040b0114041427060105060403 64
    0x1040c0c14180742e07040c2c840c50f00209203103510b0070400e4003c0104031401040c0c50f0202100100c9540c2c0c42c1c004020840700f00790308002c4690001d451105051030040e0703085502202d00d0078000f50b1100761600b0224403014000045486903510001d9040c18903005405074030000d901d03c2c10f17624080303c1d503500811910014000401600010950100c0c010925070503000c8500058410403140c4200c1c1440c4010342000c1c80f45501a121034000100141001e200b1162603e07040400a4503040c50706e4228401d4030a4104901e0584040d5412480040d90501c4030302508503621101000d141024000c200300344103003e02035144494290040e0005240e418012000300a08140b400d110254600f4032504601c1400b074218071030321883e400e1001401401c40c0944905000c0c1003211a0749071140c1e8180b12242040e940580003003a043c0041128503c800e04948003408058408078419800d2004042e00c000241d43c1c0700100c02c2d0310001d040d041c00c09080d64a0014026038010103507035242402060061080b0301018240c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 393130611 1250 393129361 393129367
    0x10e03030c0a0c0203010609020a2c0303070206090f03030c0f01110301050a0905070212130f082b18030305040503012a030c0e0a0603021e07232109010e1f0302 70
    0x555501f0350040c402419031040a5550300001e0600401e46000442c03c0d0b6082c440b07907100d81d0350801080d0040c0b0700542024004600c0c28002e07408200b469002030000c42d034400601070104a403a20148003500207101400002c14003510b02c0f103d072070700b5500f079540381017050711091004001c0342e074030722151000b1192210700020b4a44c4560388121304140c1d414260702d40d007000c00500c84003410501501c007001c4601d0014050006526020121b44030507110400c546901c889103480321400c2c00d10304c4c4170b01e2020280d0038448241001801c43c8605102c565005070003003007012408022904082c01445600301c01e0554841d04204607900403d00758a1407104102016902c110751203081d8003e098010219030018240c00042d0754801c0020080c1d480642070340b000c0241c00da80b19207100808400c2d5100da952140c0c00ca002128035441c20800039584591808040c40b45003a03100e03200b6813440401542c103054100d039650328640d00002401804038284064040d0003880b840d040c0982c401003060700140c0c03680c0b03009aa = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 393131861 1250 393130611 393130613
    0x7060b09012403092109060912020622090e03120f04020102150c2b1401080d051606020c0705100207032001030e06280513020d141e010e03030c0a0c 65
    0x1004010048016a16452170800c0c21005030001d400c50121511036a480c24070300d85034803034420100c0301407600a411107018400703034061410720f05d00710707100c03c034035004040b0201c1da0744007a0810380b00c90100000d034641001030f10907521007882480c0c550000264038141f11500b13003540000d540b00d40f83c1d40c40403600039080c004600241c1c000400c55003800c240d000000c0e40700c1182d28604409414030440311064610301aa541c4400b022402658126020400580300d400d646c100c05942c241d001134040302495406072486070019001f4809498000c4500d001800a18101414820001684400380d0103661084e20100300096010070b55443c00e40c0410f1040800711b842c030b0f00583c05410281c100c0841030240c1001c00007803241d03018103103903841c07455410306000701c043c4001a17040315001d5860300d0888002001c14005802d040d0003403450207100d80700c0100610720039490700341405c10b40754150f036502c00ca10301404500c4009005581c10707503410001440c5076040c010f60303601891040014107803c1c0b02806400708 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 393133111 1250 393131861 393131873
    0xa17070324080625030e03091e0f041104140604030b0403120c1701140d150603051e06010519030503030a0b100309020306060f040e0307060b0901240309 67
    0xa000402003010484400700c00100e10814004503008140c2d4520500c00020021452208004034411502c0700a0b2003000b01910b048014107a038055481c1207100401c002e2080d51a116203803030070603000207c101c4009625a082284580712178010a210f64201010a4100131040c4204d4048032900b44401c105d4400300c1d07001c01c905000e140d10140c0795814410400042c5034016a05d40003000d003070308042111007240706050741c100c00040d00d052404800600144421000841e0045020300020985140c80b505070380c95144003494000c04e600c01c9172310b8403020400c200d02000240314407100341c021029060309010019540710310502c103503071041c0d01326003810700d003145c103440031801545c0c0003003c0e00d030b4034a00b41034154041e0400b18a03560103031404c40021a03010f8420322031002601c0c0d00801402d03098940301c04015074141c100901c83d5000790b981c94030a415050400080408620406e4041740c6c0d41c00715020400c1c0c51005920400f004243c3d401c9244a01800c092903031a85a41c600300015001500e040074 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 393134361 1250 393133111 393133121
    0x60f1512050c030103030f090305030d0c0c0611091008010b03060607021519081806151512040b06060a050a0c0c03120c020a0b04080a02060f21010302150a170703 71
    0x109503601e00002e10840402ca00000c40c1641d000303071102c20b64a00d200e0380c00c42d403001c0140b201070150342051207445c2c0c441e031140e0888004a83d180c0f81c0400c6ca03405a80f2030300201d561313607411a2000d1000145401c007a0030096a41500b485035820544031a6161400c2d8680601c4002d01491007400c00286000441d41d909051182014030081d00d16110800b0740c514402c414a0906502e000c0f03442d003000100f00c403255040540b0000c00c0d00004d880c00b40c45012803180010355411901e9030086020508030030b844100d03030192072118000224101d050815060100300e401340685501d00a01003040801d0840c2e8114089988221441ca0000c0502070141030210601c1c0c0c20340c200410442030660200807295110345c10390070160089681c10035955030303940382d001c041c03045110f00c0e45183c2000012034090700d042000390500000301070540d45840c0403444c1103681007482070400c00f80203040304014010350074480402c040d4070350075071826440c000700314070090800c03e0420b10710010f1003128400222843e00c03079001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 393135611 1250 393134361 393134387
    0x609050604090b0607080310080c0f010e040504081603030501090c02010c08040305160609030507140303010f0308030c0415110d020c090a18060c2a0f02090405030f0706061404060f15 80
    0x180c0e200e040c00b80c0341c08c941d04054440c802c0e0381d02c220442012075282500c043c0c00b0740c2005841d0882c2c505889010b000c00380200403c151420001400714051240d81c3d03040080d50b02d4400d640c0042c4960604180710304503401090ba4508682c034040b0040c09080d0024030b5203401581504040d51908a2780440d40ba9651107801c2c02007119040c1946c2e201059000000752140e50f203d0002b5a0308119071046c856503a000074800c07820f180310403000401c00714507408021500001c06411a074030b8540c56266450f29070030840c0c41c1d0400100e508000c10340c4607406200000c1d0a941900c09404102111000582c80b1200034048000441d039400740e40b12050170203c062040c4540c00007080c44540c2c0c43d801c02030720a100c031941c001000c45000042d150742e142003100304134030158848200d40710304246400b03020f000d4000510885051104100c02c5442500e40c401511001c2d00c00d034000b15800b401c1484005500601b0140580124105001440381c3d0740c259040c04161000c043d0329404c0982d001008803440d20b10707091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 393136861 1250 393135611 393135623
    0x50315030304031101020607111c020f01140708010b0a0e0111011509020418060305070608040c080f0706030c0e01020d0e041401030602030f060604030b060103021b030309010e06010609050604090b0607 88
    0x1e0b0010401c03040a25400821100b40c081e108075903680030040e070b604408611903092503003001520007007002d0f04580c03100d101034061044071748995400c0c2c07480d421503a0382c907280201000c40034104401e0302d83c00b188035405468201040c9080c01c4481001034001920007040a0500128140b41002c2003402d40c003031070031400c500c071800030340c030f9505d54200c4008c1d803040c0a80802c040c986a0751101c0c90b612070180300102d130760001c01080b48500d0070704210b9041401a000716030075401983c0005444030308002c41e50100c550a0040c0c0681303440e01a015003240d107214903040c240142130380b1102480c1c0e000f00300f04100306406d04102200710360b0074000034014202000d12042c0812040008000e20071583e0255108080011041e01203031902070402805020f14032000b41840701403800601e043d40320b60041c1a8114888030250f0070303000b4001707c00d0300f1504100d030506400da644000b8844411820842540180503d003808070b20f01d42060042641485a4045c2c6410300351a07650715805030b100d5904403a51690450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 393138111 1250 393136861 393136867
    0x121e0703090212012409060501120902040207080408030d1505090609070519120f0b150f0d0f0c080114030a03030e070506160b0604020a120c11100b190302010f0503150303 75
    0x2503030301540e10140c50307451385c00c80f10202c801099111140c4111000e903a8140c4403159007551951415000d08907222040b600940c00303000520001d1160701c0644007400069001d9900e41c45141c1c0d0315401c0301c01003060350041149030141081151648020149c1007803050712280070039683d071001a141361180c90003c203400d40c0700c950a0309840750301000005880f8110038062010585420f0380109454844ca82c0c1c9a0043c01c601c5040b03a80340b084401011264815266281010248507014080700d42d07034503032a52901d031030b00d81d14440c40c0c0c4c0c02042540580030740c0200079000c00c0b0307520110380d0b94065010010140b540c0c94030290304102c020044c10006010080c4296603a00102c01c1d440b00754800c400048526a094001260031494140280d850698041e0303150302c2c0c8480c41d03580c0e035005042211400380070700181c541c190103520020b008060b040728500002007011100b46052000050302d0700c01070000d0711000c2e642800180c0c0d00903031003076040c11b0b240307899030702c0381c07120100d901c05a8012000198548400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 393139361 1250 393138111 393138131
    0xb1b030106020a1104060e0105010807090b04030606030b060904150b0a05100f110c0f01050a0c151a060909040602091225090b0a060302030a0f0908121e070309021201 73
    0x808500c8031380318000700500712039a401444113640c1e060141480c44112000140003a512030000e00380c0c03003003447c41c003607080f155140c04058659116420503038103680c94074002c1c0240703e0480f4102e50064000d07581e03060300d4035080d2603d2203890196010300e0311a9450751580010360351102d221802030100103116200e501c4040c24007410005003d1301000101d0700714031846154200200d0508412000074100c9941c04a41c41c0045445610807003031402404003000d003035000b1070008025076801e9070011a0010b0b840c6c40a030004c51004154100a611a5404106110982d1070303604030260080d5102d5000758564040100150940c600107280300c8641c8610418001c0e0460384500311142000c036400400d104944618100b420380f82044103a54001814003020041d0b544294000e40d07201162180004004002010080c20b4544258003560f1010340400c0741c01d103200c106c642045d040500d400b5041218006101c0701e000d4148000c0605090640d5403500700150340b50300c20140640b50409000700020106 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 393140611 1250 393139361 393139363
    0x70312180b010e04021005040f05090402040204090c0206040c120213110f0f070b0a0504031b110604060309151814070e1801050c09060409020f04050a0e0411040908070b1b03010602 79
    0x485045c2c0c4200e03402c42d41140124015011035003030740c1082168030140e5080400b40918508090300032a0800d50802001030042918451404a064542e010708458241030400340554241078008207002d05501801100503a1080c0861a20080c51000490200d20203002064540600d002c520701503000056036803502619140140f45042c410b0b034049139191140001b55003180c0040390014049103181b0641c040f02031810280040c450b05c660101ca0183c01c02c08082034440d04594400e01c0803d031542c1807a4100901c3d440016582078443c2d104000411f51044180307201e1480480191008644c0c0340304616010040c0014006000d2005425015040680342071051155400d030000d190752030003001c01c3d008113906040b2908082c001700250b0406050810f11002540300d54014003801c0001c000001d259200e0080c844000d18103010703404c00502d8070b401e008416495418015100d2380c90524008006010380c03041d12610368012865243e41d43d1000c2d03050312402d18100210404610210000075410344c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 393141861 1250 393140611 393140639
    0x102070212030a030e01050105090f060409020a0b07201c08070204060f03140c130f0e1e1015120f20130e0604030311121515070312180b01 61
    0x4410342d020040408440c85d45401c80303000780a090b074030240000c00714002500751003803a90800b500030000508100160700203400c0750407540c04030140240200321002400400c09411070300003005804403101c0e12030707400041c00500e400302ea68010b007940c4501000c14001a241a204010b82c060010000e280d203513008005503481c42d1004403101c040425200d00788103070201d049503820f0b40c043d16410a0700903a01918000d48040758250311050b94602001c04c4610b41000323216219000224038240801c5c1030740305c060a244020095001c5039050031030750b0071540c200940000c202e942400c1040100811440c01410f5503e0890000d04420000c038040c3c0099885000e8942c00359604407656000191b18043c0c070030540b0038a09544405030807940c00200400d000340c002c0842c568164006030300d846c18580b00060b044006446078411b030401d802c1440010300300200701c00c42c0034903c0d0051900740041540c00500d03032008003500010240c0c69405852281c0112030a03038400951010f00040c0541e16150726600c549 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 393143111 1250 393141861 393141877
    0x20c0d0b3d0f0504150603051e040f0210090f05100504050310270c030b060301060b07030e010216080615031c0305040507060503010503030f1c05010e09070b0a0e0909010207021203 79
    0x140e01c2c80001d0520380303482908100b034030140c01c070707000702d03240640613801084024051010441c90080311070801c8822400381d803007188510702c08101d541703250051083c2e0040403402c040c103008003a44280904d03511032284c5811554202c41c1213400c0c3d004603100700d0f01401180c0c4241c0d0103104903a0780c8407010030180c000451094800c00c10038403c0c804a22a803580904804c400b5041185400b4140007203803d5000380356000c00047d0004c144103070f464a10441d990300c8400290001130100b41a41070b150f9041c444c201544080c1c01d8181d2500d42440c0c0310545882000d0981118001c14400d48521034800340640000358030102d45420f00d941c032004010300030f00012181183e260046101c0800c01a00400a49068410180085080203040007090350154005846144003030100d9107410511350084c06814003030100003e69071090308180d0f20807890807241da0483d498000d001d0020350b000c4ca034041c168140080085805814a480748444180203104500021f504000c06010b002001031002000300700803 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 393144361 1250 393143111 393143129
    0x315040f03020f0115211b15020a030e040c020115062303221109040f0501050f06060306010f0c050f1f0e060a051e0106090501020c0d0b3d 61
    0x703280f8281c1d4540c200d601c202100d00312420030760010700c0307071514800800641c520003007801003400704291585200715010060b240b00c0320141d80300c02d000c1c2c45051401840b0260b0b0034001013500040656000c4c000e000b1991003540103941da509171030b100d80d2007500006111003007112a95105031302c6e9030b8020403075800a604511300d801e0b40c6500100e102e00b0801240e1103504001c2c0c0010040c003a102142001070414142030f200c560b00301c00b03c1c0c0300aa540107181402207200305c4000e0700140c0d4902d040c0b401c5d94001000140110b8200042140304e898042c101c0e07034445401d18105089a001090a03280c1c201011400313440c5105600b6050b110000000b0395540300382840e1941c1003800d0b501507850040d00d20801071045030b03400142c08644012000e8004070b4010042e5910f0020b00001072103841c405034403d9104e1000650700502c10051560107005120780c42e40300340e0382c02c054540c4645031b0351048000504045980325070381c9030000504a811310f6000190080c80c00218802c040e6103507074010b01040740591241c3d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 393145611 1250 393144361 393144373
    0x302150909070f17271c1706030d120b0a120b01051f02300c0109380c070f0c030b0606180d0519030507110402031909020315040f0302 59
    0x5440900544595412035950914510313100501d03c10981c54062045030b03104001506c0001c0c0012244014140266650614100d4603500c000c2110344000e0869400303500440e03c1d0031100f0b42d20520080783d0004c1c509012421a15a0010034031003043c543c402001149010706c184100200068001c1c101d5200b100e401980d011804100c1d804c9408024100c805039101c01e41100751245045448108003072040045454134a021986620030340c0300c031120301c217580d540304800810810781041e00790140c1d4104100c02420148054002084068505c1c403203504103140c0000380c02c2001c000c00710381c0ca181d44001052900b002c036142914040c05a40411102d00007030398002141402c01c02c00f6180500701000c901c0d01030b00756000a0021000c00b045090f1494006d04400030140c1d0448460607864a200b6034629945040d1414214041c0040804040c416030040042c81403044a0088503010468002c00004403d43e403840080d19020190b0300c40710342c20314107208020511010a0a41103054080d40949074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 393146861 1250 393145611 393145637
    0x40212010b0d06051f060315060e030c3d0f080f040201031a120309030c0402070309062a080d050a090b1302040e2b0314010302150909070f 61
    0x200740c8540368500c540145000d00450003042c21500a50703080001c41d085c10103c80658040d003603e02d0b18030f42112005c03949401c5001500030056540c03200801d40e84c074012404017480d00019031200700e164000ea00c9000401c1019625030110480f01c81c40346904100c102000170600e0300902c240f100c85000001107810101180007081c02410704d240f050710031944002c8240d0300c941c0103500400e003107480109406144680301144e503e42e0101ea18280741c02100940e200c0810b80e0800d4a040c46107a078850055005120038070010307801001510035183c42d400d040d401c1d046d0000b0000b60542c070345900104a44003003055401400369030001007400c02c61501c000c2c480f5030340b010303803034020340c1c0c18502c00400310402ca10004010f0490b07a48410001840204003041030007480c028a071608882c21035031400034040c902030308802854805101c685040c40d045c1404a00c441030940540e251051002901400c0c1541a01001c00c80d80403c403075500f54002d10580250400170710017410402d14002410100702c60103c000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 393148111 1250 393146861 393146863
    0x6030c0d020f03071e18120525050a050315010b030711070b07030e061c0b030f060906010f06020a03080a0203130f03080106110312160c14030903010c050a05180a05030d0305040212 79
    0x311245480c50710081840745044907e40080314007400558042c0905003440222045141000c80700d1482c01e060703140f090f410302081114201c4260700c00c13840b07540150050f04000682214030760441e1701c038007003054803a903c01005070f0342404100c0441106005828008c6605611031000d481c1c01c901a5130313400c400d11521000d2048521601201c00c108034162501c182052075a41c000724903a1001405903409039010b4a041440e00d0001e951010307090300701500602004580d0324170f00000704540e04c001c10109400b9240902050304c0580007007101600080091020f950120382480c0f1250301a1121804100300d0400030981e800a0003000b000888120b2200080e610010a842c156070301c0d50b01e840c0e0b0b5038440d90001c450448280c91218203200607001d221010034154501e0b090b01104101c05169a1080c1004050031075011010750000d2040900c600c0b054680d1080c2030780c070444483c10582130a1940600014040e1038a0b90205070300d445180310035007800d80d05400080c01503209a40345100030710620200307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 393149361 1250 393148111 393148127
    0xb030403020c0d03090b0f03090c030307151107080403111908030901050913090c0905070507170a0915180806060919091203270206030c0d020f03071e 66
    0x80e00681c422440140d40d0710300010305651803486800d0109605555500118141d040362282c0e141034003002c410400d0128082c400652540e5040f07000e07616001007a80c6100d403808148003201d17400d40d910389125212019010840320001e80081805454950700d02c2c2c44490351110b00300c241e0058510030740081c10b00017a40500404e5a108802031800c1054040044071542c01400803075910a1207420346000e031043c140b10f101c2d0424000e001295400e4188407803107065401c040c010f1020032404000c90008201100c0c2c4612180c1d91501020799554416003003140c03120025044a18a10340349231008150581200c181407018010b40701c904020b580d203031045a154281101c405400c040c080c030011700f00a0700e14101603514026090009404280e60320740813402030240120501281e42d60381c091aa00c0191100b000b103441da00d51000c408030049601150301800007030003219811002088200d07084425070195826142d210564036100d1814200c0100942c14644920b40000c1d8910030000e8101d00c10060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 393150611 1250 393149361 393149363
    0x7020d060f1d100b010c06110a0f05160201030b041d161211060306060d14040308280e01020408161a0406141b031201090513031b0f0b070201020c01060b0304 69
    0x2d4140c600c0c1ea50400000341c44d10401c181d0410030401c0504d400550644100e800c5565410116612455a6003000d4003403000300104c0001c1c04820302500106543c00c1e010580016420320380404e00355807007400b04000c0d2414591081c06618400402d9110090010300340c600c0c0b2180581c1550401e130b0300c0821115407541d0300d601400324440408000707041d080c451f005640040c8003905c520300d41260040c0034811908961002105c841d00c0c0c9007800b0515900c00200c0d41c0155500c1c00d05400310039440007400340750521001140c40340362100620294200203606a80007003001c142a43d5080e00700c41012250150b141c002c16a1094020410f025242406400d039030a8494541302d41260034030035071030050310303401c1618002d0121061086503125090280080e14815241a80314112035040c400814103443c4001c2066042960340e18009010903484020141d47c8c84c40300b02c0045141410b800d0150381300c0c10600300584039084200510a0f40c941c15801820520b402d43e000300541610b0f003900d4070703152000307a030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 393151861 1250 393150611 393150613
    0x7050309090405070f0f08060705040b031504060f3b040305090d1e2607030e0a0e0408030f160c061a120a0201080603010c140f07020d060f1d 62
    0x403042410081100798200f401001241d072803c1da0b40700244100c00060708141145c8041c2e260402806134104281a000f134040d0034040c1c1018145101105280001001d800c1111503c00710145251501d500c1038010382000c0d00c1400c40b02e40c0303030342d0003030354000f00c142e003116200c0700c072441008100c0b8141c152800300090304444031031140c0351614225800d8000e04600c80c1d00007007004044000070669a0800211403204000418420300d03070812031203000f841c485d581941040300f66411b24003d200d0040360380350b592506001c405542c0203404207420500c01c0d040420084100003d010a12110002035441038403584040103451780c0e40321485030040300004150340441d03031100325480002c466400c001c030161882c7c951081c4c049140c00025100071038541d101100c80c0c1000c0350705415964412015a48004150b000788100414031000034100c0280000000325180701213145000c0d40c800000b140c6030142c00620030320107041030341010401405540060058649400d00001082804495014404400300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 393153111 1250 393151861 393151867
    0x60504240e040b0610030e01051815090304051507051006050a1202100804050312011715010b2a0102070c14010c05060403180e010b070303050105011103041a12131205070503 76
    0x400707000b50020440d070120145900d1f5043d030030180d0424030030948100c51200700c040d01d008015600302e040000020f170441105452508006801300004122001c0304e8054440c031144401c805000205801614002821030290050b10149a10303075070403603015204103d41e0810925076804600c1a042c00c400310094014409403003d503a800c1c015101d45900c180940d0540346004500442201c81180980215018500b50380306101d05101c00c0203608541c4c900421082410b5040000c080e41501038000c40584040e03481c21201c4c100b501001c19090040ca080000307645070002031819820200140c06072285100e001c01d03100400391320400d500e0303200c9038100c0d024042d15122a00e00302e500075011031a0b0400003181c1d00d80081c051a034002c81600070300c20b801c0f9290302c0d95110300d4010259903045e80a98100f2101007610b120000d004411141203c100e40b155100b1900043c50200b0103015801d80b00e401a60080204001c1c1781c01e148060041c0c500c5088603551032820744009407094021000d01078019403080c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 393154361 1250 393153111 393153121
    0x12071710210606181b08010e0601090305010c1e1b121e0906020c102309060a021e1507050d1506031a0102070b1204020d050105040c0e010b04121104060504240e040b 72
    0x9908d90a4000c0d1040c07400400e4584c59840b2242074640300e19010300041d060407100c4e050350390070718104c00808803140fa2040d0040c0c42100418003000b072003000a00404011111f410405001c0d0781407012003490102055401d8560301c2024020880034071529016000c0d000c016601071401355a5001d8040054680c41da559110880c0072141c01715542c010b00800c0d03070030003124059554103405028016040e50040400c4c441d60b0100010b00304400488000590020650032464035070992055840ba4a500d45103417280c1c01d68403220064138618030b0f0203421489a0002041440c0d05400021803104401c071a402690040340049035104200c1c8160113020405000c3c0c0b11001740c0320801d2a030800c0c0001e041c4d1210400940710b260031608155811035140d001601c04012144484111600400c01c080d01141050702d810142c801d1040b00e0600100700c0080038007150115078403684003802401c0c000e003041222203845520810b2030b01d04068002d00d03590281c00d0006803846d00f1031441d40710350751103004180b4649071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 393155611 1250 393154361 393154379
    0xa0b180601270903020f010e0d09240f0207050409290f070509010c05160806010e0402030a02010323040c061103030c040e0606040b12071710210606181b0801 69
    0x3c002403ca086000c1d0020760f1205107000d004e0103280044200280071000030800e00a8210304051340000c06451602000b82c001c2450300500121411050404003060300100d44102e0802010790000c6034450310380a00d01b030600c180081e400c0c08190300340311040c0c080740c078200805a049108540c9050440c0b01c0500048009204001400b0707172a1060404000781c554075590541481800007001f2108184410100507451080111500500c0508070b41649070425801003900c4000304c4101034181905c62589058a0014000c1c151240144000d548220308184ca4020013103030709407046c08000355158565040e5800b0200c100c80c0501000b4500f5840c04c3d01d003043c0c80d44170301c074000c0c002640070320184000101903030064000c00c42c50002401e00030044c50f010102515010000c0d541986681600040141451031100b000090722000400e1110344034003400a040c1d007004200009000d81d09184001840340b0010010161210300b070b520604c00080f580d80782c1e070415240701680c03d0015a80c10010071501c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 393156861 1250 393155611 393155621
    0x4050a0b0d0320100b150711010815030a050105091c080109150503060109150902040315090503041a0405090c0a17070e0d080d05061e120a0b18060127 66
    0x12030818100c201d46031892003e8244009030448008060f101c109540c110b15101849464480c0c0d40307100142003840d1621a0004100c0c0a20024140308000c0041828000740e11569030f00d0300402811070701c43d0091031030107a0103808241c07503070005d51042c0207144070003000c500f040e4a10a20035a40703006a9a2a05090344090864002c0e1a074034501c8010307001c00c20792018402c443c040c252100c4003040008110814041e0b2615a900601c0c43d20701c14001440002c1e501c0c500d05071100c903d00c4010500e2003080c2089800c51046900551500d402c2c000700101c9000f135079028104840e0200c0b00640d15981d02031002071203228402c000300c00141c0181d4107110120b01c8840c40c03900640f40780360420000c1200e00c00300351401d080480688002201081c40680e022042c0501d9901034000e0382c8207403101590920900000c41e010710011320481c110013005004030420002c100005410074100d44450502b001e030f61103801e21704040280785008803400801c405070605240d80012103528207079809001101e021000400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 393158111 1250 393156861 393156887
    0x10f0f0b0925030f0e070626250e032a030f15090f10050103050607020106060906031107060204031a0a0e03070210180605030907060c020d12050f07030305010504050a0b0d03 76
    0x1e640304803c4411780010065800685201d80340c124258a000c0d01006e00903004e450055002501c031000c001c0c030910040b035041544480c0d495103003d41c11010f00207840030725a0b000f0898151040c40220211003882a4101920381c403840440d0184411030414182c45184501000301c0951120580d60280c41070455141d40c0300c2c90700019034010b5514100b015090003c0343d4100712045440701d0040c030a02005010003a0040010300003007001503d0010080c080071003900c544c40501d96941080e81175010701404030340e0302c26440b10b0210742e0313980c6918000d0b403491051030300200700f100c1d0072000070990600703449a103c0b14050000114200349003039007084032041002c1208820004910399803d80110f6241c1d0b502c0c003a29450700c50646030300d040600103262007100ea100c10100100c0844c0c03180541c540c0044580140d40103040c0d005030311060f0320186ca4034844ca802444541d2400943d00080c5079140d070025060704d00840e03040c0880c0d112002080292404400a65802084405808000b900038249807101c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 393159361 1250 393158111 393158141
    0x60e0402030d050721031407020609060415021605010905011104030f020f0a08030a0309020102010b01090b031807050a0303030906110c0309010305040516140a0806070203040b030405010f0f0b092503 87
    0x1e03172180c81c410030304500d4103c00303001c40d8490820301d4440307002051455000010744014941c900c0c1500523107603a0712014201418a058105d060240300d066a0101c82c0c5900d809505215484030b249000e0340285051901a1000c2d4644102c1005107020a800c0f102280d4004580c119601416000c002d00b0300380e40e0745c42c0c0c5da00614656000404032800d001826480407603440000d01071500780006800d450703003078240604025407448144030340300c416810f482d0080240c602103c01813081d480483d1500200350442c691040c00024004200741e4550000c0c1c50192107400240071032001281d11090710b00840710f0707480c041c0d007080c4814000c0394460380c810340d4098000c60455546079242211602e0741055034020f002c2e00701660714002d100d030800c01c4500c4020103400c001000603180c8110b000351030b80114081ca03e007000c0000042010711100350010f04408189071810400c3c40e90f0601100e0080c13000d05003240c0106001000190384509080741c0f00d0880b000611a104000c0481500700c00400050003c05030f9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 393160611 1250 393159361 393159383
    0x6120c020705091f060f0507061808040f08160b0f0306040f0227030f0a0b070e060d021c09021c081b0703051b150307031d060109060e0402030d0507 65
    0x1681c0d42d406250313405000d40c0090143e403150880c40c4c0c5030520049401072401c0c8001000c00c140711030750000131640d41c01e800101c009048a030410469020341061070f00682000800305003c50848111500c00086600d0002125801400c81c0d484000d41a110b10600c09003400074000c0816544c0040e0086521840040000030080a480314480403a0005410441002422210010000c0411070807031001002240101420008820010341c5d8500701316005244c4030405001c50030040c02880400c0103804010701860300c40c48044076103402901b08452000c1035004241c4289001440b91040c04603041d000743c1000000e441c1e40560022502200d00201c44441c4100301d040c2000050048201c410781c0300c400580b04107403450401c0c6143c48030010910302d0002c2e80e40d003541119602e18043c03950350035544049948a544040d0309038000e200184c40050200303940a929803810780c0100d0b000e41603514a43d010001c040d16520343c1e18294504480003909580251188417070580100040d29409116090b01a5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 393161861 1250 393160611 393160619
    0x90506091302280f0206041e0201051608070b0f0601081f050315100b040e06040b13050a09022107050609040204170303040308012103030c020106090e070e09010606120c0207 76
    0xc01c09041611200201e190980c0c20700c3c1040d840385a280070700445100402441c00e040e16141c1c202484000d0240c1100300541102085900400560703141c184084051180c030320f00c9040913145944800800ca9012002c20001901e00c901c141c0c5250081c40183d5400c40c656a0b6000000140304240b83e0105060204c0300000509540c2048030310007036445d2580b5645142400c05414421074510f80082c0072203101403200344982680010032a900c0181142e01081c400c222401144c0802c0640c24092000360a110400c1001b03183c54008894061080d0341d0103986c0491314100d2841000421415400f84d04140410451850100050419000000d00c010310f8203513540c079000c006800c000300c0d84215400120400c410316420900c8240180703591400d00000e0503490260039640180503000805140ea26124019054403d511000203401c0d03841040000700071030810f140c1d4400311449010318410b098800074000c40018000d0360304580003074940c08001c0d03820851143c054441c6030242c600714410008001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 393163111 1250 393161861 393161887
    0x30507020f010219051b030105070f03022a010c020c010f051b0304051909200702010f0c15020913150308070311061005041b0f0c0606080102041d07090506091302 71
    0x800d005d101e0402000d01c007014042119169901155840c40303640740c00c041006054000b608280d15110300d00c0c0042e070700d41e441c2d01d0340f03911140d000f07000346950031003010035014031801544600b80e8419a5007c60358902c94120046500c01d41200c07408001440c20f01848000300c48110800050131614010303603051a440b00007284013103010303440d045950180040100042d12203840b807101c003c4010544911084400d220303c8201c0d10401800034100501131164640d258810002c84d80583d9103c280c8400d00d44808030000301940080d66254841c807400d04240150003143e00c500c2c070004004c0000010028038548030740415402132003066090000c0d107076800c8280802805041c2c4507080c514a501e2400b828582448104c0310710a521140702a11803c074941116007007214403000b20200d240c003107040e648510340700c0c0c094034a603840124950700201f1301159102d43c4001c01070551250b18510081c96903900412100c03403440744500c90f04000304000200a50904043d24454001d9514000d468410341015030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 393164361 1250 393163111 393163153
    0x303031e0926190c0201092c06120a03110d05040807050d02030f07030309150203072a0803030405010f2003150f0913060c020106060509060a0903021801030204060f03030507020f0102 80
    0x181c00044444d4542c2c41103681001c8a07401521044288094108503491b80140d2050841c05070b21039203602600040c0d00d5501d00d18116140341c0c0c05400d80da200c90003450050b02c58141150340003500d001e80845200c40328442c0042d0307011601084000c045144c680170034001d490050000c10390b054000c00c0e00030021020100211002144030f42c0d03070281111b203044c000210004100b0710750403c41d00100164000b0803400035214600c03454100f4041c940440351824800030300c03215446900039000c00f104020071f1100c19400f80c8403444240b001400180b48400040f0481c18a5280741900c00300f050010520040400c030880070016000340c0344140008900e400102e41e11421520f410b902580314115104100703041c0919036104903607000901046041400c054001d02407500011301640002c07518072451489110120019900a46120b6254014155601065209000c16030041c0e043c038800141c118400c03008241100d801d55a41810a0140d03401c0001040044600340d045110305e80885000d04024155 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 393165467 1106 393164361 393164407
    0x7120206010504021927030c1a042102040b0616060b03010b0d0b040206040b040602330f060a0504050901020d0b030c090106050c10060303031e0926 65
    0x1211b610000f020f000d240071031300140b1000052011000d0260282c03000600903100f0f5100400080010b440740f0300c80d001c0d0036808400c03030903040080a660b0703604461000b007011428440400000e01c09802c00000603080701c0d1032041c3c0004001d414801c442c003105040d0002e010ba00c14403000a83d045101c8540549136142900c001411550341c08100d82c00742044111007601c1e2603c9500007552002c000c44c80b50f00118842a9104c3d00403030485011b0f8003201107011888c02692405141103e50b8009800c0a40000c2c01890104042c5d85600405101e00c4094000507158000c1a01c80300586080c0103506000744c1080714040300300e0319024400b03415500f8500780559509800199507141c103410341c864080182c51305001004040c0d043d0001c03c2e50042e008012450388451211080c2101c0a0010040a010790000d030000c03d078203003003000080f0051403240782c0e081c81d0040c2d8005401c440c90f2b00c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 392985611 393165467 := by
  have h0 := BRFrame.cov_init 392985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 392985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 392985611 ≤ n) (h2 : n < 393165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
