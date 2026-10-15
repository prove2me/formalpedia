-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4890
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:04:16.278929+00:00
-- url     : https://prove2.me/submissions/930132da-e572-426c-b3c2-921b5b1d96da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 879316546 ≤ n < 879496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 879317796 1250 879316546 879316549
    0x80f061026030a022404020d02040f3b0102071106030912031905010b03040512030702010e0f010b0306130803070e06090616021309030806060a05091002070e0c0304030e 74
    0x40d040010703000c0a00120085540400d001d0a40e00024001005600030a4500404200c80143c4841c182084800501c40d850b19a00141c40040c6400020380240c0e61075a000c440344030194002020004144201e11410039501171241c5c00d00e0003110010742c44862600c505100c40414029641140e43c4203241c80351006034a0140301301ca4200038080445071181c1c5c0c0604c000307122081d00541c022454040650074a01d01000308905481c8103a006290b803032420010003021400200b000d035060740501c9400d99494640c1c282c100e0141c4000c00c06e5070b1290082c104907101ca4901540003d00d0b6403c103030142c034543e03a100b0400d45a45100d601d00503086400400001d6292481000004e411250060000341804491004180c41c1d40190fa140c0c0c06041c100c40c009c0301580340c0716150a00c0c06c58104001d00050049681c010403059018200354020900400c4445096001e0b074217603005d031203001d800b01c6200045200000c1d940c480c40d21400d8031a016000c04a42c00c0003054084038840e582648846180e944400c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 879319046 1250 879317796 879317819
    0x908060c0906190302040801110406272d09021e0304080f0c03090406140d031407141006090b0604060810093303020a060c080d0f06080f0610 62
    0x2407200b54050800c03c07140700070101c0d41e0207802e601c0140b07960068803141010442421100c018910004400081c04104483c0b46e110702d00c800a44440d0901d201030103551890b1043d520721540110f0314640d404460141385a0050320940707510006111580681c981d148110002c07482003048001ca2102c1c08a214415610900300441d00248509021807800c4407024016460750070130880120036420000c0d580307003076280a0052074094075102d1510725041052600140c4610049000242481100c0082d001707254102025102e0280d00a02500c01d038500c6031900c03076140d0040d160240e0550b85020008a1414040c0c814404400c038060991031815003080030903642003000410484040800910205100700b43d07008401c8d01c2c490301e41118090158070482c04042c4851544c140ca0344201d040700030005a51120005000c0f1012424901602c80d62410001d000e0f2041158074942c2604005c0c061885184951240c0112140c14003540d840b848104c40c07040c1c032808160b400c100a055041d000340001203c00c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 879320296 1250 879319046 879319057
    0x5100803031f05090403110c030c090a1509020a0201240b03040b2706010501090e0c16150203041b12030909110c07031214270a08061609060908060c 65
    0x1c1240b01d859441c0000f41c84004211022030020f0580a9207007640c0c0c00400081c409410304030058001038034200085070b8624001881c2c100300356204d110141030f40d9030442e850009805a424250741d2400001e90207800790410380300088205420940d0350200416a0182505841c2c00040f0300d869616141c0710700401f8400601070000180603086c4042034005140d8000006482ca82e0160440d0361602d00090180c01003984401c00f071000d03e000b004201c110761011070300802a200340701400040e050803c0c0780926580507821301001d100000384014000d1201c00c4800c030211882e13080505649035480440424a80c400040c080f0369103a100f4820030003d034000314034044951705400e007810380c205240f41c60034165034070960b4260003490b101c40c4000d5000d516400070541d401e180d2881d00e0808c20340d0766604d4004400c2800c000c10311558481e010707680c4c0100300c002040080225982c60808000307840d480c0c1101484400854140c43d800900c46000310101e10840c0c120b140035109613541d07101c8503440380c0c1c0807 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 879321546 1250 879320296 879320341
    0x405090108241e1e09012a020106030818102f1f020408060a06030f1101090f0e09010c1d010507050a050607020307150b130f0b03010c0f030510080303 66
    0x4031881110b800d908400e034035114013829559010000504442e030200c582c0064121015641000001d030900b0340741640049603030600e1104009060f000781c10032401010550802049884006181110040340390754016034258100e40030724400c80c0700c1c90140d032491a01c001421181407500c981039100c01885400045164101007076407650071200c465500d400e0324000701c1d410004d6012505001c0340f00200b2249070310860803481004002d0542d00d841c48180b50444009143c1004000c82c900580d11402041004011000c1c0c1881c000362140300c0324a14420455a5903115860714159041e15481600b00103c05003920280d0000b403c10300004450030340c05140e00f035a40d4403d000e040000582d040040318402c0107030f503002e56100e286500d400014415400d00040405040090404060b502e822010181c10041000003580317544031201000500300e0400825419441c099a85176190b07006240640e11404958041200d56203200c00c4100820040c09064155030007400001d0110751001c5203c00d00104 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 879322796 1250 879321546 879321571
    0x120f020d0c08192003120310030206040b0a020d0e0f040c0201020f1303021f02060703022208030a230405060a02070e271504020418020306040602040509010824 70
    0x860310780b40ba25001c5480500721040c6414062a814003100046854503180008120320448101d01c00103a81c500501c124801d801c5000404602c0b030901404044004550241605458039542c000d0f46015030800714103000076020311590103c0940c4a0400306c15000700013003142801a07103c10a0000900820028006566081040c03154103540e40019000744940c0820852100d4110703c10301008000b090440c2c1008290b0383e01035488981c002c110154440c9076407030b0058031407142c450105c8101d90b1000346c0b03e4801102860202c0da40320040b004104080c82074442a02950480b20b0400d80c1c410200090301d190a801d00c418062840d00300300030000340e01c2501c1115417040d2180c0280c212603c05031421842c90b814100030719040c50001086901c103080303403805030500d082c0c91000ca001604c030090001b4400d50380c500c01802d21214480d1219400d50b000f504a860610f00f80c6041002580240601c500c9150840c0c00080c4810001801590081e10918802628002062079088012014000601240 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 879324046 1250 879322796 879322799
    0x60a09020c0a0204060f080f060c07060c0e12010606200307172206180503060f0603071a04180510030609050102070b070305061009060c03140f0f0c07120f020d0c 71
    0x1c1e2a03005e003201070404481c00880151510803600e14125100c415290181c100c3d108010020407800291840b158005a012a4100441404807080480310041da94084d060b6100d52415800541c050b50942c1c1094540c24901071242300480e203110100c0350340003100e0340100001c000064401600c184426080c6d44a40e040080c1e4124048005028030180039400340d000310b040040590142c00d40c2c40c0f11440c0d240d1030b60001c0c10440425120070006129100d98010500880c05a4404100d40310003400c1c480c00007111b03034000740207140321035215100d80c50406030064404541d006441c82550b01541e40040200d90551969850001402c1e141005442c5c5550038003650300481e042e03d6040c0e1241c0010f60340080c8030325098082100c42281544441c0c02c101501d81d05105140c0c01065079a4000d800d41000c1303c04d1004483c88000e503100700755070340d00c8400000c0703001520002030f0320103420340c10107e005503001d49895005141d003a405840740580959950ba182c0809070421409082d11b09014050054009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 879325296 1250 879324046 879324049
    0x1202010b1c1403093d2a0b04141f06080c031c0c030201140a0b1809062809110a1403331008010e03090d0204020918090304060e09060a09020c0a02 64
    0x49100c1ea00c40d001c1100079115206d00205000ca94000325200002011034019a84504025090090004041c414108030300320691604009920740c80590540509044a105080c403003d0012072080319414818600d09444a16000c9149005041d4498074052942c01102c8201c0b22030b11606426015550b82d00d180c91104005800c5180c4940518480418100604002c3c42a20b443d50000007680e20700c04418031007001e00100341d040d049000b40c1d12400380c2a1301088000410314480382d00303902c85031400040b04208844040550000b9000312055101d00780c2c0c801240f180303040e101600b20f905400c02c0ea030036841c04c01c0d00d00688083c10388000031803501031188000c040039900155901c083c1122400c3c400c0003011070902a00402c010350402460501341c170240800c40c109a07180009100ba0740115600701c06480f0040048203070b1000040d072120609002d030540d80c480d440b81c0504800603806040c1d210150901499803030013880c000d0005260300d41f808801600035001042d080301c4900541384c108016 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 879326546 1250 879325296 879325399
    0x70807060b010903080c0102090a060309020325240e06180d08040e0906060307092717031312090303020606090a020d061e050117041202010b1c140309 66
    0x101b028000042c0d41d64016810400401c026a100e4002c140c02c2814400c01030318041040303407844001c082d128200c0700c4040900c11001000b6009100d0041018081c8840300f5040403104031f006145860b41d1411901c0c000600c44144202c2d113482001c00021038445480741042d80040c81100c0c0160307001030070175454100034a0001c0c01644c02d0f468940c01081484818501440100014038010320200450070b00e02c16032031018610740c280c2c1d40340b001020445c0d40511040c0c0a0382414580700c1c032071080d81c034604a4640c9040c02c4e01381ca4191580e046071b800c0e28410368061030010041da038050700200581da40d40d1302089900701006080e5100c0503028004d01c03c0e50905400362030060140c051050903101000c03094805440b4a540c00f090401c1101c1c0701005121401ca030300142c120b5080030798429031101e03662061f405494032100445d04001b00c00c040c07040318240d6040101c81d00340310313408024194002164140d540d0054a251507800000128020184000c1c1e805010050045100004000502c1d482c80d062 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 879327796 1250 879326546 879326557
    0x2030a08030a0c080609010627030f031701290702131109010206090c09070507050c090a0f0e010b01020d18030c06170f010b04030623040501060911070807060b01090308 74
    0xc1591900d20407401e16800091442c5e010905603000244c940c5400d40003400c000740c02d841c40720120b2074901800703201c1d140300400300c1c0a1500500300310f0007007000d85801845840040c246084000b03040d13001080c2214000c3e8503099599508110409131080d0b100d1480da43c0c1d2061b801240d1140100340f640d039401120b8010300c00142c00ca5004a520380001200281c02c00400420940580c0c0040030225215501d00c031545401c0490f1341b81203500c980640c81c8c224030784101c40c049140e100c41542e00b00481102d82c0d410464413400c29000c00c0c441c507120310442d64203903080d4042c60703805a041040c421910742c0c491010900f414884005071104030790b8a031107003035044507103802c00c20002e0101601003500c01180e0241c2c607004151380010580640c03402c03850281600450100410840d16902c0245154419403855017040a400300b5000d00d50605180c0b86000740528072840400d40d0030404418050301200041d0790304070f60803031286440c0c0186591103600500612942c5414010040000f001261003c0c003d0320 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 879329046 1250 879327796 879327811
    0x51f0c050106060f020d02011811130212010f2c06030a081c0506011809051b13090b0f1509060408120a03050606190e0112140411011b0f02030a0803 65
    0x1301c00340c1c0c2000b400e000726106c04409580c18001c288003500e104840017030045800012800e40030004100040c0030078078840b02124020b00100b1680103048100300054100d0744400c80c941645643c0328411002e010300c2142464401c501c51020341c424000441e0542d90121005080d20440101a658040c0a4208140110300904806022600300e4028400c0d1500700d0000d0915051141070341860490305805801040c5041d0707182c0380415240c40d50a014128441e44000031039032903c40300302d0001205c0089202c2d0440d91170600e05522800d042909884003010405022020456003600c03164189511001015420440402002804580522100b2450302030a0201681d8079404000102910307006002d5501c19141000b08050f524002082c001f2480560700b0074988195541d4010303180610700001c1c8a604a04080200440c41c000400c075510a0b0710415400081108080c01107841607600740030010200d013a00b0540010407014007188182c14402011222003405070f40c0c44103d550816540c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 879330296 1250 879329046 879329057
    0x308040504060b0708180d0b07020d0201060e070f231b16060c0b1f15120b0337080d0f0b090a0c0e03121b0304051f0c05010606 56
    0x103008514050040000400071076070303400e080c00340d00c1c3c07a0748086204d4072a400c00184240881503031551114594900c4080c1c2040d80031805150030030020b5250110009880019460105d010a83c2c03800151841d000c0c00b41a5a0980d4142e0340110070303981140c040d0601c15007038000c40c4aa030f8011400c00010040301202861070042590741c0c19650b45000848682c00440d9401c001090001c282d000000349d1450b6004900c0f281c2c0da0321550b0600410b840702308000f1521120400e0085010401401d41c00d1161226588a0354000442c2204e0401c4810154035580d264200506c99142d0030445100c0c040076060040c0304d000102406800c400b1203020200007290410004180d0301c086480500c81c014a402d0310103018041880b085001400700200201a9076401e6600c0d0500f030895445189096040c0e10050110349210192080e150b01302d80004144c0300100c0410b1001954502d80441650216a0040c1c0010300040510858807600d4030100c1500301000541400e450108500340240401800f054440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 879331546 1250 879330296 879330299
    0xc0b0c03040501021e060a050a0f1127090103060c09080102070c050913150c0e090f0105280b251a06041104090c18030c1d011d07030e07030804 63
    0x19052002c00700c9031490481005803840004100401d03a0381e1f111100c00740005036943c511200000400d1840c0d440c00c01d903840e10210014040900300140010400748007044610b28061f504406403d0b090f000160b0007103091001007000440d1a001110314044a05000b50011b0b10303130b45803074220380244c1e005640d0806d00020030061401d1a1041a4106800092541d075100c0c20740c550384200c041481c00880c01d59581c0da8006400c2d44244030141d0307030315002010b00c1c40b0781c280900d1218880070f0a01a180c401c19041c007102c01e110407640c2c92005485c600141c11203244d40740010100380303600041c24034144180c00e84100d8108070001800c201c4503d00c90f6600c01c4403031000d255000d8520310020000d5004600d0700140038244000c580544045403a0450045070405402f002164099003166036000b0b0004c1c940303404002c02440381c1800d82610b41c26005423400111200c101401080300313200308084d18403104140da022038002c981441d404442d42c00c001c200b6141a12810703203045000c1d0700a8a003400013090 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 879332796 1250 879331546 879331549
    0x180e071a0301090f05010803032404140a0f050403021c090e042108010b070213090206040b0a0e0906060315011403010f2c0112060b060307030603050c0108071b0c0b0c030405 76
    0x22589010604c00041010b507050022042d524403010302031500d145060300201e4a00c083c000642c070651200980184540010000440c4500340e05940d405460741c1050510601e0a03e1841410321481c0c03d503004200301510301c4420403206012800369800c115864002140515800b46001d00492051030b02e1800c000426400c48000c03010102104100103401004004004541d41500c00a9030112401e04440e144405080e000b030405a000035084a004a80010340c1c00500c8094041c001c55901c9900b00101c0b40010425110800c40d8005da201e102403004c01d411a0003211038200181040c100600c00c090a181100b0310794009038490307804c080310008140070914403102c2880224104c0300340c4009015000d46143e54117007050013000da00000c24200c440c01d00040360000c0d20059006403c0a58a00301650010080c00302d03404165142d11400c001d440d565481080d030503200e0f01003960b03015000411120007406202d1142c4090314428a55900445c250080100074007103260040e000719a203510700030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 879334046 1250 879332796 879332801
    0x3080a0e030111190e0d0c0e0106030b060f0304020d14030a020f0c030325061e0606052d09280f080606460f180e071a030109 55
    0xc80c19000364181190f0141c06011181500c00407200045003202800c001d000c11101c1e103400d8401254002042c01615050007003107000e804c182e03180381441e0406a0f80315582541542c0302c1c05041d0703410441c200b142d43d21102525000e960403e00c000c0407240004d429490302c0e5510740c110400031003181c1000a000c02c0c00c0741c04001c40d503499441039018214080320900001c3c0c89000d00c441d00c00924100c84034145621005500d1003044583c070550070490000301d42915200c03070b0242e0044e013423200d00d00800811540e014030243d5090020602c02c014006040c070180e8a6401c180601c10b00030f1480c00c0c0400701181d82ca000259480d0319000c8240c00d0005240316101c14040311076405079200c2c0040901c148642080810480d42c040816140180c221450402680d02860341c84501210522050002400400340c80c6a081d0007602e61440a203910341c9905404e80003041c0e0380f10301400131480140d030345c1015001e60003d4800400d2082551084c41c1d60b0601646002c06062a4011034040000188000360051 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 879335296 1250 879334046 879334067
    0x2030d080f1008120309011814071215240b0306031b060a0e031c03021c1107110d06060303121104050f06160c080120070305040b0c031303080a 63
    0x11102d5040c4619201c60561038480044007000410000030000e1800f10b42500146a101c0075021120011481800c00c8031513445c13146241380c110700420000040b080c103001042d40846400914415042a180d40c08000030142660305044440c61840c04241d5184d42c1400580101140c0400b140d50b032518030201414400300c8400354602898980d21201c407615174000f90b40414803182820960800100002480c02c440c43c000b40280c04500b12601c0082603040d009814141480e801400041c0b0700034800c44151034100e141c200003010180000780204003107090300415500e024100e9030381040d242e10747e842918150307042034011681100903103244d0a000d20a5408100e51b4800031801c0c9410440040c0c0d6040850030b805110710303808502411000c1d00c0b400e844910540c0410280c42207a40c036400c2e14068454107110748a15251550318244200b2306d0412121301c280c1c182e44061600741020f0404e80f141d04800c0d42d00d2520320080c0040f4132030755a2810140c02460044141c10703114a1103003002403c01000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 879336546 1250 879335296 879335311
    0x11070e0910060f1d0a0f0219202505061b060f090309011214040b070e0105030c09040c090305100f1a031b030123090607170406020a050702030d080f 65
    0x80c103410440f040004007080c503130703103520003904000c1d450b45042c1c0c02c09490700ba403406c3d001c64400142801c48580001c1c1480703002070281c88601d0f24100301c0403958850300f01050300c506241c0107580075032074946580215850202242c00c207400000d858101040081d04070260405904103012040c1503080d00800089520400540030006646051942c41d9141d00405200605001d54a03409040b032082c180c020b54402c0703542509803461032401e03041c1030a801d0302c2a5507060220303021402c0002c96501c110110303840303054042c86984c07900c400001400020150070503001b0801c040b00c400400094014492001c41c01d0220401083d82880340c412001100c00c4c0910030701c0d0522034081c0d10310090700c0101c1c6001c6907082001c0c0904182c072030035010a0244c00e070100400003e200301c0c40040542c24103102c280f03000748100c0040358110340c1c0d0b0400568600b40145c40b20002d010f070361030001d00015041c0e00245020030003480d03e40d00701112680480d15000105003510b001c01e03154010481c00c1d404854840d98024030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 879337796 1250 879336546 879336569
    0x30901021b0703080d050c0d151403010c08060f0d02030a03090906060f0e0d211e0305010e011401030914010f0e0c010e04051302060a02030a180e0711070e091006 71
    0xe1a07468648501c1003241c05040d4031b88510004071240001429540203154110007446030084028260050380d4441c0100465a44461605000da05051094030440101511281c0b007540761041041520b1103504122944a4602c1142c10010785040c0000b801311032007038446000313450178298404c003a2030385a000340b000c000c0c003014421b00c03440c0c2c0b080d5599041203054444c1000210642440525101c1d030071030301c0d000c5808451485581d6039000541c12000d440c0f039140d41d5810042c03d1011400e9404c00c0c0305c3c10310b421080600500c2104162130300c0320a5070f04141030005115105581d055143c2030303080d0020500344d42d20065000702ea01075002c1c0c2d00b40418004058586d02e50400d00292419264082c198055940c50001540d02803654080302e4499400410b4246c0340d00303450f40001e580340c0c414100b050001d48039007440d008403910a2014401d07520084c1e000103855481300c500302c60740100584d85c5500752061032400181002040101030043d02c07902c011b00484001595050184d90090344071050240 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 879339046 1250 879337796 879337799
    0x1504080403030e1f0f14070503040303051803060a050402030d230702040b0402070503040611060c090405090c04091b0602030f0d090206040305060114040c02010515040e01060b030901021b07 83
    0x104480115000d0700d5240c14462040e0500001090080071142c05002c5852650440240f085030410340c1701141c2c9505541d060102180c90501c06400d0150304801800750b44148014800240140e0147c03d11880100310030044d86072070000a4540360b0291a400b8203942d480040c0300560030184900310080255050030030700c2c0b100040c1c00c00f204050942e481c840100000c0b0381c0c01c00f15a2160007100844400900a54455445041240d02da81c001d2040b0070104451100c550b01d0008045a1144900c0702d007070185003000c803110140001b0303140007000c11305c050003014100c0440741c1c1e45104454241d8000c09041580070603000901e03444d91442c4d0018415580140100c250f81803101d01195960001c610001c1503001c00c81c80403c1040c01a50002040c84c040c1000226800d08160044a015801103600f030104900507081642241c1003070750080c110b050300c20181405414260400ca5a5041043c000601c0e10798030301480b42c042d04195000c041c1c1e42d40000c0c281e00f041582a031524004001d1001504020717 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 879340296 1250 879339046 879339053
    0x602070f110904020f1c0203030f13061403191409010f0f0b0f131b230403050d0809030f07050606090105030f031603031b0e04050a06060c150209030d0c03021504 71
    0x1610b001720300d030320500410641d0031181b076035802e100014545c050200e80e10740884407201c4c0702e190459a07000c51465170410000503460320070268000c440c021800c141b417554440c40b2110320480c00c0d00c000d0301032a40e00c811100b0341c03400d0f12020305480f50908000000c0d47c40030261310030065440780d0103038040d502d0030031442d90310340d65610184c030070500401c07140403005100036117410300030780100c0600c1000968520003240306590030407207035440c0503619905120b81900c5176420707a0050003a030002525640c400b52105454074060840307241c200c108a000c03a03091224030000070159501406040703070113800c100e080c4005400c0c10400e4501404085000d0072900c4245e46a4030307528000c007000c500030803240c140c81c1d509040c007a51103d44d018000700907100b540040c030311000e0221010b01221500a41c42d0a00142078a0007031b110300d40641e030f000c0e902d0201800598940e00c00e0211845804184d09600308800e62040c0c0e03081000c1040c001c002d894080407920341e800c000c1d00301445130201c400540c40502c00c000c0003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 879341546 1250 879340296 879340309
    0x51203010803040504050406150e2a090925020d1101180233030613060608060d0809091509070c1e031803080c1b0d0602030606070602070f11090402 65
    0x1521001e4170b00080a544130305050b0090302600030310521921070a42c3c0420010b6010004074400c00c00034040e9120382812901400180c10203101400c400300d81801040f100b454042a401d41100c0c10f214141011618440ca030400c25a40d001c601000d6486a01d603c43d038a600000c40580340229070300200240401c0f80c1c04005804100c12000b446038036181d01400c01c8024022400070b81010003114450401301d03800900034698001d131000783c8030f0303a83d0548100240d10140900000d94103503942c0c05100303868070001e00820032440581164030300ca083c0844021522180c08051041d070101c00ca003100043d40400340000c4c101c0160490301000290007903c000319030042d11340e6140e000444801800081182011039000440001070f6000040414000082c010040c020b0803030400110b090729164600c0102c0c4100c40d40c1800317645034010240c1d10423180030070690350195501c050003401d414074144003580e440302240e00054003112300505c0c200c078080c2031101c4d40e01107a800c0413080e03981e580c5a04164002600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 879342796 1250 879341546 879341549
    0x1b0604030303111c06060e0409030212030a290a0b04080316080f0d05070305130201020c0d240e0c180a0c1110091101092d050a0b0705120301080304 65
    0xa058460100f00b8041110781c04440d041d43c80b4005980c206400e403039040002c0c0c0b001e0310521002428030900441a0700c1c05108880040380c0c5a001021625414165508107810041c80c1c1e40c10b0035500d16802340301c0302188030000495890b5040455448440e14100800358183e90819640d180041c0018030401c00c00100711164600707580c00e0b08403001c8140c80c1844a92140744ca01203040b00002c54003003170030001a049540074640684042c8000d60743c581c50742d92580c96541000e401a8051018140b039820000d102e40d0f102d03402a600c0010080010703440b1444605c5000048c6050b695446111200034014407a141075900d0481e00c60a090440700a0510022070203031100381c0e000e0751407104ac114513001e485840c05020003101036070754003034003940400c0c014480058241d6908a0451905100e51710401c4290141c865507280510080340300b49040301d16000103c803152042d1a00c600c0450566540b00d42e0b0401040341e8445540e944149141c0a0f003488882030702d0030400035042c03005108201c0c01106480 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 879344046 1250 879342796 879342803
    0x40c0b12241c020f040506060d0203180d021f0c0c230105100e010f03020330040e1e0103030f030e070518060306010b07150b030f0715021b060403 64
    0x101040702011140c07462a10300d2041688840400e000001040e040c080805007203008440c42e49803000000b0034041030710f0040310942d5201c40100400402a146907002c0c64001881034900c035a0b550b43d00c4155441d042c0507840400140e80b02c0103460524015501055000c030a40c000306100c0c401606401034002059400e00814000c040b030101e01e803910a0325001b1191400707020080c0418184501014542050b0f40525035801c03101764000300f101d242610f400c03021207a0290041c5031070079101210310826110500b1420a145914440602018a503406000904118940900c09007014003164400e51041600e440b064000d400c01000800c1d000480a0000e0f03900f0700300455a015080789183c20050030740c0125034412004003013120000c0c8041001440743d8001c0e41252403a03602e17808000fa150007280c5c4010490303110448140d0401d68070f6080b1a076007210140865140200311441e80d4180540c0f40c2209464005070008902c445604001080c095071000c00001d900e00c84940100760544240d00018 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 879345296 1250 879344046 879344071
    0x203041e051509030c150105040b01030e0303040f0c0b0f270d06111b010606090806042004020d020304050606090709080703060b0a1203020f16150807180806040c0b12 73
    0x2c3c55a00c010b108a0f42c044201c202950a034222008000f80c1d024000e000c3c0301e0045290000d06034580d40240b151942c0707000c1c00300045003141d4070340e6901c003543c0b00c0311001141c1401010310f0000307104031082e0140824451080320b07142c5428002e4030748200c9071008641d81c01d0202d0305140310006502e5091403141d8850f00410086400f010030b05150165203e00c1e000401c213200401e004400f100c80c10740c051403d440e4180d80302020250750700c58003070343c841043c0c40c0a01042d0f0400800b8020035042600c5107075000c030161015092a40340302c00e02c42240c004640a40e00c81e0000c01c1080000e2500355032080e80442c89044c1b201e0001d0509e031242e40d803585180002440b107035880e004034070240c0d544841036000701142501e400ba805110710300251100100007141d0344910800c4401c41000c42d40e84121829203441000c400030428451030111081503024152100748482d5100f40c14510101c40342c0b02c8080c200d200e004024071b0405140c41e4619840e242d000321201202800942d0054810851b00d603000703489035212 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 879346546 1250 879345296 879345301
    0x7050901120209060a1206120309030b0a0203011a07030e090f0603060603010c1d1807050a110303060607060504060f0216050c10020606120f010510080616121109060c010203041e0515 80
    0x40034010070092301301c0a20510040c0d100307030402d0b034421020340503640324103400d10303094840724440000c1e80000e01601d69145024480d40e00c80d0f88a0b5005040403c1c000d16029440d0320100000c0b82c003541e8182c1c0e103448110031050030030100f03003010050a908071000340d000300401007036014010003d41101645085031500c017415541c1c1075588505854001d92070204c181c40d90f080c03140018180c1d51024880b032012031508940c00400c01c00110036680704280282440d843d203030381591514010040144210b9110780e443c00da011500c00c01d8400341042205154081d100c0c410b45042c801d140c5090503104611030f07080c02800f030100d03682c0450a6134110800f81c4241c4402c0308034582142c18003110001d0f40d00d264ec40e00c41000422841000c2c900229045507066840da6200e9407414460062035200132804104160b965002d018419400000c0b80340c18040050700b441c0b090000980c030399009016203d801e80d0084113220070302000841c07114225503000040594204103603250f64640f25001104406141c10000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 879347796 1250 879346546 879346577
    0x20d0815010c050c0907020a031b05030702090406140403020f0f0307020609062d03071d01020d050c072304050f01150309141005040c08010c0207140406080607050901120209060a 78
    0x900384d05000901705c500314030300034034020364400104c041070300001c10244000140e0111100b02507851900840914603013070300c0703809000f803245001e40304171980e950310320318035499041100d240c90243d4420f501500781d40400c912441d00c0d100701c0241030301c0c407900304100a10047e6181c0742192002d10040e07600300e0322000040c0d40c099014083c94092454069202c1002181808010040d8030491703d82d1540c1c81910000c00010300e060340450212800f40e03000152040c2524010009441d0020001c0104c8000d107446501c0344511001c0c3d0a03d15190b030790080e041c8406441c0501680380e010080756012082985480f000000d0f43c054081200d082c142c1c4d40988000303200e0700360702e401c64113201503044455480702e0741d10007001820304584c281c9000340002c0d001b04001806000300303058850b0340c2d401822411704145041c002c4480e134040d41a402660303541c0c0018940b00034066a0303c110b102e07031200b41c0c4540c084000588685c3c04107001500702031041180b10f2680d41c03028181c591445c060700d0320b080c0039408800f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 879349046 1250 879347796 879347803
    0xf0d09050f070b0706140405030d05150a06050d0b060a0c0308060a120b06040e0d05040e060d051c11011b0507020103060504020c011a0604030507050d0510061401020d0815010c05 78
    0x500c0400c2801081030108510f041000203084245c810310042214010315240c40705101c1c42078400070030301d030400c10021103081c106803c050f400103074841e82d64007801e49002c00500d6518455101034007040d4003244224103820a44a1110702c61420740d291850440c8503c00145200c0420074010240b09054020903820746030521504040e204110b180b50880359036081c120110102241d440d4803403400d003608021030380707404211001c0303c2e18903072556800d240c24500341c0d1000080040815400c4a01c1c8001d08002c13400400c9115030702c5000d003518120741c07040d0040041c010a4910003114080c0e04028000050a401800001001c682c2d07140036030700c0b0091032004801801da40c1d030003950f2260002c1014100c07a80d040d13000c200240003035643da0a032800e51106102c0745000b00d01c0081c3c034a800000080015082010016041a100341e003035030389840c690901c1c4000c568454000380f02c40300c9010901c103a0380d40c04000d041440030303040c201207000380307443d0600c040301c80381c2c0c03554444c10040c0040d41d0904021081 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 879350296 1250 879349046 879349063
    0x19110d03050d11250206191b0f0b070f08040b060d2a05010305060a0501031e0f0b0f0102032803020c010e030304060b09010608060607080705061501090b0f0d0905 71
    0x140520000a1101070303824650044490360b003031104000e1010122071307070040c0c0030400c2c5580540310900f03002401c01d2603181060701c0802101400715842000307054848103440c91007070705c1c891300b40c01d060702c0f9850400140da100028a00d03c10b20500b045510005908031450550081e1b02c52201041c0e50f4034800881c1c0704120041e0020001d401200100b000e0000020f041802003030424002c1604582e18001101507410a440302e54202e03d40410031320007548603801c1883c04101d100780840802c007604022008072480010903c02e01d59650710400001d28004001140d405001d2004504202d08900b1200800026001c880310300181d07040c003660100e0094051395400b0480304000c100c184030101e103060702e0b50310403602181d0292801c1c909081c60b01e09142414143e81c001e60fa855403603558401800520307401700c68107540001090204c540000c00400c0064800c00300711000303070301a03031800002402c43c00880d00000c0740c4050074031102c00e510300110103481c0c07003001c01c0310042050103407070900c6410004076 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 879351546 1250 879350296 879350317
    0x18010c0807050609011a010c020607051204031110030902030c24040b1b0703030906050a17090f1018020d02060c061311150414150307030c0219110d0305 67
    0x1c601501440342c041001c500c903d140300c000340502c030311854100307035064420f5902c01e0101d40740418507030140c10b10340301074403071300c0c3c07258045904a41d0540240d84041d0002c1d4801c680781c1c582188500380f141000791081201c121181000d019038100340d8002501d4204100030140608028003004600c845038004140a108040d54181d6480e030300d03070100248a0388180840c8208059041c8100195840040c0e84000c03203426030381d0180824200907003281d81d98402454502002000240340d20a281140803c0f13004140d210020060030b0030800c00141020001c4400801c000d240c4410280d0000d1290101c10f102d550440341100e00d01000d100040c0d1030301032241d03c07411901c00e01741044505500060404100c0d409540342e840229094400c000300c41e40d521030041c0880703a080c04100042c43d919a4013900c0050018003005204004600c4081c15400444030200001e449109848100d5014490402100c06450313007441100050740b2100203c11581c004c0b2030240c10480500d1050520640645807203208 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 879352796 1250 879351546 879351563
    0x1021612174b010b120721020409022104080a0f022407021504050709090501021c05240303071127190c02070902090310090803010305070b070818010c 66
    0x90580070200210303161a801c2d550204a50020030f900305603000f900c40b845112041101d0b20b070707160081210349624000d180011501c016244c205401c03610300141004d4251010016190715a41240498500c0700514008241e0400d0b170034000498480800c0b20200186410b107030715287c0408004903d840410145d003400042101001d4102031125028a40101410fa00321083d210100c036151040c1d0300e054a0081032507000113402c018913100c6401482c0e8850140d0001400d00700c6010019103c03c141c1e44141c40744070354032070820443c9400c481011510341441c2c18401d08030b00d600e0010075034134440c1000c06010300c880300500781070903925a510301f0907040701c000200c104458011545410b001d0155011200d000418243e091000d0691241e4a20b024142d4001c0100310301d400f02c0e8500030b5010340607a541500868941e00020701c541d00900c010540b1031203200f9034940c514101603082c0404c0303811404110400f0001b81d00412110000e4809440c4d90340c2c1d4101140c05c0d841d0060300d1240d02d65400920848 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 879354046 1250 879352796 879352891
    0x3060501170c1504230405071e0507020d080f090604140315554515050a0608010b100513080102161217 46
    0xc01000d40c6084070004001280d9800403003408120183c0210b00c80c00003100c409000420040300158511841e5200300101584a14080d00100d019590b0455200010841010310005601038500c0c1e00950442a460560b04242d80360b0300061740c25a40543c0542080e0f80170962042c0c5a80e010121649428010050381c1d071540d540052030004014800724a00c2801486610144011a407020740d10034140c100440300c162442014015403484034480903840520703e280030030b404842d481d0012000841080c103a9015200f0452203130b0644400b111480481d0141c2002c201c000007c1c940d00c001c5102070440e1825030984400000a80b55402c20001341550700c1e0a44024000c1d45244d0000b030040007050310610070581c580424600f030f80d002c9038485030440380ba8001500e000b44188082c21000f40d009031f10f4182a0f950304183c50036a04500d143c1c5055004203041d1400700441030f480f5290041190a01280703070240910303690f14044d00188100000580407180702c07428801c2603c01010140320301000b030317591b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 879355296 1250 879354046 879354059
    0x2121e04061205070c020f04020d0b090a06050a1e0e090c040504031d0904050601050f01090f150909110d020d020705060103080c0f12070602090307081009060605060a230403060501 79
    0x14040340744460b41092402001c02d000e144198140010250050441a000301d1244103220080d48200d84065480c3d030f65151001543e500c4208060240701d4108010603428201400c003d19826650700c450b00301901c1031200320b14082000b401c0c00c102e9542510540c2541d0700d0740012410a00c00101d4250311510742401c000030190030903100680b06101e0b0809036094403980e81880072840040c0c07000751266104600410043c50002d090422070300c07041c908403640075617031b4149101c000d000c0d030441c1c508000040e0f1410307280303079100c207100c4010b18a20f00e0510100342160781401041c0f0840740000700c640e800007001154055907404031114158090126480e035030396802c1030200c3d500304d071401070b4203401049402c0000d11800544565900e060401603440e100342940e0f084002d50124240c2134040c041d1480000d8441e0043c820801044100d98001c43c681049240410844149421480c4100d00070302c0307503400b081c0d8440307000300c1c04500702048030f41c3d00011110040c40900496000919841c14440042140b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 879356546 1250 879355296 879355307
    0x102211017150c0717030a0b030102070b04031107030b04082a010e010632030a051b010e09070203222601061208030a18060504050f07050a0602121e0406 67
    0xa03080b0340d440340c400ca0700c0d554040d6442d44140b041c06403d11070450b021103085080e0700001c64000d0751015001925800040c0820700f660442c41382915040045000c0106243c2c115511041c0743c20800080d040503030440e5600c258011015002600040c0301044007802d501c1940301300c880001b0040305190380800007100880c040c0c141c1c0440d52800e9401e000000501c9805105d150102d4810111623903405140307000300490000192061650522800308040d000c1503050051603001d200c40001c610034400b001001400d0346d081c040106d0f000b448040c0401c10026404420f5a01c054800f00300c4811007100b000c44a1501c800c140c10041125502403d003400710701c0c60040c00d0b03051402c044020710107150b0742c10f281000c0c411480000380c1003c1003080007820300c0080b6406a40740003808291103105600544030401242e070202d6046440c2e40c8900c01c0c0700d18191040100000070603044808204050030800002e456070403a0240303c0305654041b0b07180303002500d210702c1000c807a40700c0e0b2120740d2150b6a60701b00605 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 879357796 1250 879356546 879356563
    0x91e1504150804030507080304050d110d1d0310020c0a030311090a050d0311010c0207030c17030a05160c0314010b0901080d111203070903120f0c020603090a020d060209040e0102211017 81
    0x40380c490a03307040108070110701c201c07844c610b13522061902c0480c21070140440e01208074959060050444070307004021648003918000e40010300030014154580f801908442e40440440e54a0b502440030161070342e91200302005554054030841e200701d0040c5416100600d040c2000070155080c4024800340c96400101581141e0080c10310400080d91040c200c1d540200c06088002d00340c00401c05c1e2800c980c0078134020000e03a05883c2c121202803045498100e01c2c1e03d403640044400b51941121403680c04c200340918242043c08031080e078a030794940b801069440e05c00000303150500088640c007821002013841040d40001c10984000d58032703d07210400402d940498001114009a2003003107a900318031039444180c240c1d4003501c42d924003092030b400b00102c54000506841083c41130003021001603ca100240d02c00b584542005a241e244c040204000c4d1a84d4154a2055078414818180161100780c2c0c611504540c000b40e800706900ca07034081403040c0200b0342080a242c0818a2416001c0100203490b90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 879359046 1250 879357796 879357823
    0x513060302090315040507170a0b09160510080a1509050901050601020d0f0e0910050616050f1603080304330b01050a05031803091e150415080403050708030405 70
    0x410724140d0b400504e88042044c0c802a0172684008010320843c0040103404a544000400b00c070100c0509d40d84440d0003074000c845009258200080380031002c0055868040503000823140c5158008070000c00601450b0001e00c030081d403640704c0031b05089904040c40200d000d090150000e010a107842d41030180a07090584071180184200058400709505c9090b1024605840b6918000285251800c0144109020f0b00d05103810f048040300081715914800140009421a0070103d0490703020b0500c982050800f5110180542003200b000103036401544410701541c0d80050360584070f840f1400d142514410710070540020103200c030510a60700c9144110030003240700044007809406542e00045410340205001e0601180040c808a0030300c130f41c0c41040000010072070b000c40307041c2400180002c0350a80c2d000c120010082d800f10103400c10b410260310030f8584001c0c0d4500907280c0b502d08900c1008480f4003e0030700041104090218013014403441c201c4135500d410010b0b103500c038105070a0444c0c4401e420440e42 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 879360296 1250 879359046 879359053
    0x1f082805150301110f0906040e04150e1612211809110a110a05030d20030403051204030903170c01050612060109151814090a0507050f0105130603020903 67
    0x4103481c0c58140600300071000013034103050424003000c903824215000b4032141e540c080f20901012541e01c5450013514450380c040c1d0701000886000307015060842e001002c1c07440c6c10341c01955007035140c10086040c000c100d41d0704031103000484a042c14201c10759981c100104200d480c003092003001c1c0c944d00107070baa0080100491000b40e450f5489240c1c1e012250303500414030400c0028040841071320301803851030740179074a03d0050b1130b80c8840c5681c519003940d00007040d801d10b26135141c0b114807040031003200400609840440b0a0701d1401c2585015001d800740d00381000c4949800c0000404151052140500035a07000b0070352120036007800800c0c10140c0025030109525881c04000480900d0300f11801840900321002030407580c0d00380710592000e025a084012031016040600007015150803800c040014910750780003c3c1000124404041e02d100508403c0c0613070b00c4000500082003021a25600b12101210f480c034001d143c03640141e9840c001c060000040d0007800900007212070305500105403071074044040d0b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 879361546 1250 879360296 879360331
    0x30705130f1d04020d0c0b031801090503041a390c0a030210030b031203010303020606030a240605040f0b0312130b0702010e0901090b0901051f082805 66
    0x15180c441051144810b08018420005411500c0a440c10340160001e00301d400c40c202c0549a8440782d51460780078425185000080141e0b00c00c1c6c8400c803a41d002d000c003000303000c1000240c4031a5070b680074031b001d0040402a0184c01c6e030000ca00800032036625082088ac0e03119101c400e1341d58010b5542e44881103091182402c1000340641c080810f03c5420400700420381c2c600c03982581c0034002c00fa240c440030f035004d041d40d4415072802590100100403000d47c0044c1e2a5690350304514000341404c1c80644118000d500690301e0030001903c02420f01c0f40080101c043d8059086c24140b01809040350394082900907140810700b008510311070f00604082081501124122207111025100e184541c00a012484849020031b0100c40020f400500d0390500500d00400308628520019004030000c1e80725450f0035076140321216080c241401c0650041c07500302c4030490110320703414020f82028954500c41081080020002c0c030445aa080020359140b56065190b6050000c007480c80f0083c001510000300d00c10344d8241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 879362796 1250 879361546 879361559
    0x1090209030307060b01120f061502060403051c0603140f01110901140d150b0d0606021501060f0c0c14030105010906060c15060e0a06050f030a02090105060706020c0303070513 77
    0x326501108064015481c0a8943e11000003d1444c842c9550400c02c0d204502d98942c0c080317006142c82100340c2800003c52602d0305d044c002c0c01591401c101e80a540044d020803021903004810b44114041c0d403401800c3d0540c0e040d20644c014465904001c00c003221620644120344000240c1d03c1c0d514142500801c08440071801001c0d95000c1c403502c0070b0009241941c07200c000c0f01e108000d8150307104912804203141d55003402c000c402d12401d0b00300100c1a880807489684c00200c03070182030010704690000d0a010000d11101941002c0140140740900c242d403007064610034820505000c1107078101005041003501d91031813540c511600300741d0314441c0d800e000000c54031240511509041300c1031034840f012240741c40d41d80d400c0007241040b00200c0c20340e41d0310300004082580340c880c588580042840095441c0c10b2108203c100d21a0b2a11340b406030b07115070010801030300c0d00100203040d503104441c0541c5074862403800e000070344200c1d0f405e41441e00000c41032080441e0000003402c4400c0120500400700e035101d07403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 879364046 1250 879362796 879362801
    0x507020a05060c0f1c150608070e040b130c09080c18011a130b0301030618110915041d0708150106050306270a050a090213110909130b0109 61
    0x8001e000d5411407400710301c0c16402d070310080c000c0d0406024401e00344640c10602c0e0307812030091010344840d540c07905020004d43c81c0c2c5001d84000b402a5051211031810600c0006003150b0602010078006ca42c0e886040d10a5503607500503880c2950081814021703003003c0c100007484c0c1e85031441018000d1051a0682d200c0c0d00d0032560616a00b00074070403034110780c1e19001c0d00540e4011480ca2180d040e280030080840c1c130104003100318001c1e2525214a540e294558903106c012900c4000c020340d07020300703604c001c034000502802030703488041d83c125091100c07034850300121b01100e105819503d5001e8034246d80c405099a40e00c1c00101c810b035805041d5062195952031a545810440300d20140305601c0000501405000d080610f03084100540100140d01c0f2900e0880d2400910101da004801008020403094901d607000f40c0382c0c043c4c408441032241c48000d07070214031040d8858130222070035a05e40c4584c6031101c0700d201c00c1d500b00c858020400c00306070800e40c4007042500315085040c3e401180030000480c92804d41d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 879365296 1250 879364046 879364063
    0xd090219050312070c03170c0606040204241808010f0b01110a17040306060801051603020a1d0d02090c0705010b0a0f051309080a030b0f120604081803070306050703050702 75
    0xd400340000300c00c00155102070f507020500c11210561117003004808917110255200199460012407a80c0d03a104081319403400f04003c0981d48110700402042c010891041c2421b0741141c3e080d401c0540240a95100751030007180780e16200749804d4002c1340081c80000540000005060042017005080c105000455112041c80740452503a88601c610711300050101a4510000368101355081c1050b440c1c0d903614007078503401d504c01c030520380d10f03481800382402e00148000540c0c8424102189014080040034103159403a4074a400b01c1c103025480031400e0b889004600345101d0740100700c80720618001406001d160403c10007601c0d07641c60041c10044d1800d10000441c140e0707034150807501c60245040304215440c08400000c83e13026071a14403040002d49030f00b01410320a8204d44020030300c41d242c84d0502841c0001180c07201c0c811603040b40c100e0074000c80480c00d00c5d041504404410b0303070b80b14005440f100455101c05072075003501c5462000401c0c409154412030240990b6607083c0a03507212824100e0351030b001c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 879366546 1250 879365296 879365299
    0xb030d09030209190c050910020a0b0c0904060909122309090403030b0d0b060f060f1b0a14070e0a230a06030b0c0a0807050a02032d0d09021905 63
    0x6034005001500d40a0320465008041c403091a5000e44803958034810f8820300301011001c9100412a10507508c4c10700b50301e4090130074030b10041207801000d8542c8010b170755001d03282502e000e4002546225070340b42d581188014229060041c01200d010b4a0140c0d6208000900b0b080001c0750000c2c0000d014108802c24982e90003e0300c040740c18500c41c0001c0020086002e0802c03400c4c1541c800c06070120361922070302a5080703030180700008450310f8031030280203000151511840c4603d40412010001c0c8100300181e400040b5110441c000d0414020303082d5241c80580f00001d88807054a001000c01c3c0713440014076400b540c0124228000300e85580350b02d50142d54452000a04007043e842020f90f6684150794101e9000d0000d210108a1642d0b98482d03092090044e41c06c80c01c040800a8200542904440c00582154461411a150880c040c0c0025124060f1521400700190281d400f07144034140404499000b0008a8016503501d028855000003044021822400360044d01004c51765644410343c00002c0f10720 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 879367796 1250 879366546 879366557
    0x4030c05150421020d060509060c070f0b090f15060109061b0f06181a0903040503060c0d1b030507090503030f07320321040f0615080f0304090b030d 65
    0x28030750320034180c3c0030385a021000101d20403c0c60380542e070f030700415525176402036200185030b040168209041c40f4004000d5260004100030b4100002d104c143c40922081d0002c01e000040e031039a075070450400c071041d8880040c0707100b038106040100c082905054010502601c03400038059440c5015141c0707610600c001130b4a0714908804c000401c0c004000180c00c00d106d65800504401e13130741088001c403041c15500780c43c4040401c000b440000c0645d441103400c5141140110b06103450080000d0f070300c407401448030700140e0000c9038102c030000c0300c0c0c2c10014003e04011041c00f120b03035050741d0042c01090b04581800000b61411000100c074100030040324840c0740d00811161070b02195813030b05840588ae01107074050018004500d80c00082c61100c4201c00001b0b464091035407040c404040e00141051850512a1034100c070082c80700041c180c079400c091596001502054030703d1503500b01b8899191a81c800300407409000440201c00ca000300090096a0a45030104031b0701c11100141655100304403804004241c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 879369046 1250 879367796 879367799
    0x1c0306080a0f0b130c060e040f0501150f0216060e0f040911060c0304030204050109140117030703030b0f1206070f05040f061b05010c050d0c020a0f020f0102010905030f04030c051504 80
    0x200d04802c090b0f8488100c2044004d0a080c9076075500ca200c00340d0340720100051403400d1050440c80e040c0203003144c03043c3c81d65007172025504010340107452000101c5000c0512004600c8030391594028800d4044003805400d141400a0765520701904103441006114400c0c032010031401c2044c0303010f11510010a811040328070010180505000d035a0740101907008461006010000060ba80c0e80107181c060008144045486103407200d0001c511071040e0040a4918a000348178580008004242ca08054151030040f27031500041d0007290f1001c20011000d030304010100c503401e10f00d1500245240c0075941a40c2e40d1240a0040e0300d080751580581d000e01e48600016103402c001042c4641c1414003481a40d03031641c00015243d40d00d031421500c540e0544004104082103d201e41456881010b800004a0015250b910346c25074602c031140303d641070000d12400e5540800c9401e03901c00d5010105450340f00b002c07240d17034500f603100060032074115100880e001030901d100807540341400700710301010700041c10725035040c103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 879370296 1250 879369046 879369053
    0x405060106031a040608030a0206090703050c19051003050910020702010e120115080a020117130213020c0a050a021f1704030e0904060c080708060d20031c0306080a0f 73
    0x40c00802c001403402c00904642200513980d0b0304c43d20009021440043d42c0c4c811801a01a00700040180b2072003042e08130107010000705a0115001c0c200d010100c41e81c941203280c42d85041c0030600660040758200c0300180560138059050b502c10f074090407848003110300844880c0f03010750aa114140009000034100c0b51621200e013043c0e80c000310300544103000402c82c2d007420021020081c03c0b03a440503480b0f500c03c4210005551300b14901440c50303841203403449564940f0310118000508107540003401415101c000004803500395055031342000202c016603155160398240075685100e4040300f41c0c0324040701c50020198194281c403008030071090f41c0303074103444c042d4004498030b8583c4010003e4080c420b07020f2803258030740c1e41c07003030445d01c02d500c0342000050a500001000300010f000601c240300380107030300c0b082c08083d6a070400600c2c85c05910400d00d0310240c40400740c0c01c403514890840313642c01d8890540354a40381406941400038580e181d0b901040819950407840303585604441d07016050030b14001080012 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 879371546 1250 879370296 879370301
    0x1119030e0310060f03300c12080705041211032e02160807031107120501050f06060d0209030c030307080c0609030315040b12060f0915040c0b0a090b04090504021503040506010603 78
    0x4100b05a4003c5074445840d00a0500c1e040701d2501d01d4000380001d240c0c1f804101c2c480841440030900c502c0c00d480c1070310300f880e4040c045202e140501948e943c607110041040003c0c41381c0b00e900318100a02901d00c01c040f03a9000340114505c55604c109210545182e17440001c400740700740e5200c450880305107900102c00d6215689540d00c1450240c04000340889820748225042200100401440b070b0004c06101d010b08107142111000703841c070b28001107142c0c01d0141c5030741c9520555225115030303900183d031008144006890051744644a81d00342c0008aa01c1c3c090120b9034010740110848101510760030766485480c19100c2c4421141e80d400c065410303401c000d0310300702940244a240d40141180d0784810380480c100e03240503400c0321981d058038050410404008420703c241c00c000c0100641203045030410317941e591000b01090154590840c00403446007403151150241308000c044003086140d6503130f207070b02032130014080072601a4010701082c12003910b01e12f42a402c40344101d800901410103a420020110003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 879372796 1250 879371546 879371573
    0x606110a0203030a0522240f020606060f04030512091513180207140c1f0509060c012a08130f060c030b0301020c06150f010c031119030e0310060f03 65
    0xb2401b14a6650b08509455007000d4009450554555044e0440880c020f031030301800020b01301d04102e08019034603080d40e0000385554020404998080d100c2c0c80303070210b20f4140e000d103a20240c41c91140b454203155034003070b84005020540b02a03603074603080c06031031a00c0500d610030602c8501018400c52030400c94034007038400c584040c002ca514007524180458848512000146046031115081440c0c45001e034a030840f203000031041051a0841510241080604503028017082103016120001d00700d04070020030b40c04600301000c04003103040200c814171002c001038194580390101050350306012034114818a5100701c1065808015103600c0c1841c1e40d1185c024041320121721041c9500d07020041c0300c40e602800078040e0051003d0060000c0c7c030f00881a03480c4002900e50f00e5000d461310070111002641d11440c14160141c06007411100400850400d604d002c01c400400d0ba405a03025501604040d44101981040c07001101160804600c0e680e54004880181c410000c080d40101810070009521030314841 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 879374046 1250 879372796 879372817
    0x4152303011b0c0201020c0a0608101e090207050a170714150103240c11060c1908180723040b01050a0309050a020a080303010518040b06220f0606110a0203030a05 71
    0x1038411007a0390210341d4218089d0045800f16009a017082607a000c205254401440c018081a100790329001070400390031342da4020b0111190300012003a0032710000b0030020303549942c02400a0328440704002908120340001c1c60488200555541800c001c100000e010000e504a10300080795503480c50342c96003000d08504800034100b44c195a24022444600d01c600d018106054440710254804009103d0400f5001005c000d01c10703a090000380d905070303400c4030140440d20607800c244006032904881c03030007040c0381c03c2200807051007040008580a11200358102c454816282c1c81d0b5400021501008203035480621a540090014444004103903c00d8015003540f5002c0d50544040c06a95004182000160707001a050760b400000100054108100448100c9000050161850409507a20b54a400e0080d207800c0c860000302001c4000b403041c14000c511a44041c0404005d1310b00e510102c000602418030910010542c006650888804040b4000000c1c9500a01440c41c007602400700382d48903001204085c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 879375296 1250 879374046 879374053
    0x6020c16080f031222060e100605030106080604020105031e0103120807030b2d0d0f0201020708030313060f0b0d0c030528082503030209031209030d0e04152303011b0c020102 76
    0x11001b0444611410b40761440c003c01510003010250040c00a403140c943c003441c017981c90034604000c490b40201d20706422603424600305a51381c6502c0c04110415008981100004042c48000401c205c500c02000c070b21404151500241f03070f83da9140a80840f8281d440407134100d40b0041b05124000780d160072440010b010b01800361030201c40c0d40c0216020722034044040390f9080111010310151341c2c0411850f00280b0060700158650f1600030a1040002c1c813005004052548030281005d040c0c250f85c2000f9802e120141c8024407070840350070031130300b0b8034400d00c010b0300d25004e000c0c030011110440e5041c180500200c90040300d8036500c1c554a03081a43c2c8201c986805094103500018928101241051031f07040c0695005a101d200c0d0404150400604200c14602c15204200424071070320041215079030340b0070b18282491000c0480300442e0182c045054041c15012801202149010010b009504414100c11001140791814002d25089034046031300c0c0d070b501c881d07810421880188a907402004c0c0070b1061068 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 879376546 1250 879375296 879375361
    0xe010203130b030a140c181302120a0c050301050105121b070503190503060a0513090605010f060e100c02092d070e01030c1b06020c16080f0312 63
    0x210340c0c020107540041c41480000030034841c450020307006541000701003d100031503078200340303100c042d0912075002003501d206106c2c1c0c450070160b940d90800303246202420805650761140800141a5111f0440b4921f03400e503c1d1440007803c07184140e003074a05030b50041c0c49a82c500648030042e2002140000d00c0d2101d40c4003105092043e90401001501c00503200c0c0006507150843c140c0000c2c0d20b44807150b954400c00400380100b0500d50b030341c81d20300e07000c5640030350b07444041d4400020010050441c0550281040d8240000065814648040c03901100c1096403180c004c1380c012010842c0030720441e0110400503088500010151601e8909160402c24128101d95105401d176000300c2c2c407405240c5140c901d0510f03001003040c01508400e078001c103220700746401c00501009000c0a0314041e4071140011111420340017110800c0308681c11a020108120304945880e8120700e011002c2c02d14500038409240100d030b074005004080081a00c3da44080d10601c0d06090352884240061141d566a2613801d00101d200e0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 879377796 1250 879376546 879376567
    0x10e0303090a09330611012c0c18040204180b070302070201110d080103061104120b01052707030b0d1a01080f0a03050d0c0e09070206010509100e0402010e010203 71
    0x140b40180305040c0042884441c034070082102150702c0c0583d00402c8640c141c807014296080c43c20310309a44850900255803070081d1812401080c15400d2025032100349144448050500d2108010701d01b640e001316101c00c030b07540301841441c2d0f41b06d148010061504170082001407a10390410503002185812130320b40c50307800e0346804803030f01c5007514540701003580040c64030259603201030740012404000008164103055400700174860700c01407001400d450364031182401c5900f01e00c000c880c020444081c5214502e4840e0620000c0c0c000c081c400c40344564222102000f0007004200d02555600480d12581c2300b81d0340e0008180c0c050444410302c42d0b1f0021030b070800c0384001a0b04441051400c0d41500417410150304100b80d00d407409c4010091040b51358402c118540c000f942c030000303c0e100004040c9000c40c00c01080d180c15a0b010716115032555001030034400b040310441c1d000034074070704852080742c1020341c03078403200d000400036007083c05072460a000810000707016502460012101e1003040c0f0440f45054800c52 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 879379046 1250 879377796 879377809
    0x6060c08181306030605061203070308070e0d151505060403080702030c130b01020d050f0a18050303040602340302011d06030a330e0907090606030c031503030905010e030309 76
    0x541021240366a00c3c03007401800350901c2500c0d4003030380075100c448280d40c813100d540307a42e406801c10040070414120001020f0900c40e40e905086040081c5c0800040c00c1280340c1030724000100080d42209a03d4070b000c03405840100e0f03000c007044035409002d9500d40742c156182c003425944400c0e02680c0601c0b403102040c3e99501d80c0d454000346c04840190014000e60414002803d290890f0f4108082100131301020031410446c200f1a0900140c600300142c00b2a850640c00c045028940d0095515000110b0001351755074001c603250081c03240c00c0d03e42010034000c6080303070120003010401b0000c8591503a402031005500513202501c4c81b030078400d0307044084070103000024125030045036408142c0381c442c0d07901d4401c2c682c80c2c104189004840303410482c08141c0c02c140502c001c1400d105107008924a040807400402040c0301040c06002d45401c103022154850801601402e0f100103581d001a185c240d80c800c00c0c0e84600c840d2000d896041c0e4445075040c1c644130044850030002138120303600d800304008000391540c601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 879380296 1250 879379046 879379069
    0x6101a03070504080d12150b040902090409081b0601060c03050f1602040f1a012a140d0903020117040c0b25050c18010e1311041a0406060306060c0818 66
    0x10303503034500e0505201130400c0590702d00a200482d1f000e040c01c818480c0042c907609a5041d82d10300c540050b294040100040e0181c5a0030a020b4a00341c4000342e60300307400e401c05c0b00400094518201315a01a61b032503030121010900c8940c0500014010f00c60706207403900c990000d0076404070301801120418502e03000075080f90800c0d02d0700141e440c0c0d1240680103410240790044d500c0302003424484800f4007516048012400c0303100440f5080e0301108140307010050280d8004881c2d42c1c000e0110b456074045480d01030011141800140e0206001317205034003510400e08096407140764070414020540b4075007071400a00b900568a102d81c203018200050041c200b4074103100714940d01410041021000300320a110860740380f12622040f09000718014400c03102140541c50b0840c030290019001e01c0c0c610305262880000d488021640942801d0000c1c0302d100d5000701000034184102c404226640c0d940900303408880c4a8400c0c030340415a0500c2c140c1c08603050385c000c0c1041602c4100e042c0085103404001441301c8040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 879381546 1250 879380296 879380323
    0xc3f16060801060c030207050f0d15090b01090b0f01080c09120717010908030417090a061d0915010c0203010906020c0d0311072a0801020d0b0306101a0307050408 71
    0x1198020414164484205801801c0b5400e100f8104061914000d4950006010703090050035455440f49071a12a40c0e080301a564010784100010191440300c24041d04900f002603814000c0d5400125104100b4890054020002003200200030808001900c060320028036008010509001a5000352680307002d2140840d10200a01405401c0900700501607144401e400c0b600d0b8544420000061a031004681d0812340140180000c2000340040081c0791080580c075130780048a00c400016916001711036490580482d07949480340460500603c00302c000d040340c2003d50300c0c02081032900554003d410440460303002600104003c5200d1312100280d80c407161100c04c455010080303c41d9580ea16100e625000502c8501e0301d854102c1503141c201486058801d60000304045403803c144620240c2d0402c401010007a0080d5100d504007c03400000b030101c0c02280c1d0003802102c0c00600b02030030b4401904203551817031000904060728000c941c6840c0e080203040805006040201140b400b60420825016105 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 879382796 1250 879381546 879381583
    0xc0e12070306200304200604061e0c051009020402160b0402120102040f0911070c15030b0612070f0504030f12141305010e031504080306030c3f 63
    0x35524021003290a0200c80083d41c0c0c0d40600d03105910300703408084903042904520501166090880780809400c400414550b1010000500164681e040b4560310300d01e28060b1900c80d6081c01041003580c01b00000040141141c005800e8401d4584451303000c07051050002e000181880e01840509510031070b04c40e020b44503060250208011842c1c4001040c1440c518003000b5801d0515185ca0900b444400c0e00481c0c43c520b03203942c2003c00d2010140d06a800340c9030000c6009010030782e034403842610040300c3d002c080006030822000554904065080344c00300d07484040b001c03e031a51405800c6950350051078070f0b031081040802000020070000014081414050032203103181080304200a0071140c3c812080b1011420305001d40c20404802002d000200c0300c0a00300184015000c000090500110400b10585010300c0d000744400d014200000d0b43c4580380035800c4032040b50114040006c1c00340d519100a02009801541d44240c1428001e01c2121510145091a44031006014503041c4400500709018045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 879384046 1250 879382796 879382799
    0x5040b0409060f05010c0b01030609020f030105042f06090f0f0d03080f0a0504330c0503060a05090912090d0f0503030a0c030507020d0c1505070c060e120d0c0e1207 72
    0x4000324214005180c03d00340003a1b030070750b01d03940e1104c9618144030181440d46e0310070f1140c0c00d640b2000103840183c94000c6c000c018528061a1054030607201c0c04890380002100002d050043e00d9240b244003daa5000741681d0506450034100321030300383d028903800d420641645410090791511030644115034404e80750501240782c00c5034155403030b100041c41090001e00f0300c01444003264060010001c0b540c0781d1580980c5400c581144204161070020218580c503117000304034203000f64040003079030080600b1120303101c000e95901e041007107504096034804100e400c0381d00081e80c0003aa800c003c0c0000c01001d0a6022901056110300c048510400710513511a00000b003006100803880c4504500c4480a080c10042410704403c000d5450049003c24020700c5090140f500034401a43e58a903681041120280264540040020105c0600c400201c620909042c01ca80318140c000c91a610b05440955115092801000e9100040d02c1c0402c054004e0280348003948105407202c0e001504000c41e92030003403040c0e5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 879385296 1250 879384046 879384059
    0x60e0103060b040204123e0a050d05060c03181c2c011119030f020d020613110613260a080a050903070f03050a122d05040b040906 57
    0x150111555940700e18810002031084041c490022101c041d0403101c8003032001091404ca5070fa107082c50b00d4400040d084030055046480346007807d0b20301030b2403d503070002103150b403a014001045490310004250750414000079491241d240040c561218804900e10013544903c0c4121b800e1442c0c2580d9850541201f490107454650440d00c2500b0101c0041601c0340038049034040d0580f101c0ca007040c081e04011402000000c41d10741081101d00400b1004040d100304100f52030040e00c4185250000000740c0030340300d440b481d0203001181c500c0c8213140da24646500c20f0b40651703a8040c8000075043c01c40e8018018882d0206407040c1c5440e00c00509001031030300d148480c5200303005a05694404440250b0340c030070b0b084800002d0f42402900c40c0c002030b604081d0344440080c40002d0410011382c0007503824013950711001050120026149000f1402003010748441d04615104860101840040c3c0c141c0075401c88100c0da00340f42040c2e1159442540b854084e003841d44451740d000c401da0096210400300d5444803810b0015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 879386546 1250 879385296 879385301
    0xe06040b0d12030c140f030106080f13030507020a09020c07030c0b180f0315090303220803040b180706180801021c0b0616030c060e0303070903170706060e010306 71
    0x40110742070601c0040e036640d52206140c400003550101034030380c050484030502928a40c084880140b10682e00d62000c8244891301d80c101b4800c5400089030600403c2c3c04210980100703014507000c01c06040308580310f840c1075400303a100510480e08071201002c000349012062001d0030340418000702030840389182d0f08004a50301225009810140c2c010013048050079003540300800100c0c4103440c840108402c10001a0030007484c484445c1a109070036040000002c404001107100304d040c07204688604900110b0314000340442c842c000c11516040020601281c98194800d80c41400c0042030112031f01503c40003418103015520450200d05d66002c0041e00c007608800f0300c00a002503c00031420700000342114503200507501c51b2960501e40d1354021006603202c503c21030b08000006000e200d4004d00d176150091070101c250342c0036030300c180ca005005446008084100c4c0c0c0244d1240e50b804400310700750344495070940310502d900e22401c2d20420060000aa07503000705001040e1010300d011a0f0f44c0341d801c20700e06 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 879387796 1250 879386546 879386561
    0x50c0604030b071806090611070b03100e0a0b09070806040e24151f0207030c0608010e0a05160e0a05092d010302010c11010c060e0601060215040206031303180e0604 72
    0x84c91896041480265840a084000c0300c045284c44c038019840f80041c85d0038061590001c0e6100040001040910480c080e4200b0480380b1001c840c0100ea42c0b04c61480040724081d880541e1310200c810040b402c0e0310b104145154014100820004d2242d0710048601c1c6090014540840d0071514407110405001c21300c092142d0103003082400c680f010080100040c1940c0c10305002c1d210340c5c041186c2003000d1a10030444d400c061540300100c80c80383c6403601000740580e0030034410807074001d1500000509c2684540202030080310192408100c00808aa00f540c580c40003505054000c8a020b4000403640d490342c0c00c2c1801200d000408081c0303d0312461a640c5260a001d2619021046070b100400c0180d900036920035a10b600440d01001810001c001250540600c4401504a605000041907006c801160480c100c403456000c0b00c5850040c4036440d107929900b114080c0d8004418070000e0f1211498440341c1c0100d1344030b85400c0b142c41c0c403407058841040325150041099000311908008050406108850 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 879389046 1250 879387796 879387827
    0x30d021c0315050904050304031713090b13050615070f020a06020d082a0c07080c100e090a020f0d0b0f01050304081e0408072405071707050c0604030b07 67
    0x580c400b080090303400c0e80034890280600d40c450002424848184152006954030401d9414140002031041801d81c21909050b0203140000c800024590130710710880c84100005030100c0858500d1704040002464002c020f00e8100500d500f10401441c1d04c80000c010562081000100c00102d0b80180b01010049800c0403065500c4503114944080d04008402d40c800d060380341082081811815014051711000040700c804030002c1030714041001c1c045051410380d0020401c603184205214200042e0a00c850300401c0404e0400e034000c20141826507035207600540c6490050f18100780b074445200c0340e0340020000f010440d40c071507500e850740c642402640c3e1118002d00c0c2a0341103003001c2d221160140300f50020b64000700800034801c1400c0c1d480d207040ea801411404183da098aa4402707400c5000c224681c044401e0040b4045034440e007600880c240c0c0c0c807403900310010700080054010703609400d510064040d15684151401d031912591154010000b8510450440b1424100010040c007100c14a41022 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 879390296 1250 879389046 879389051
    0x307021b1c083001090207030509040603081c0b0f1c0f0f1103010218190e0106050c150103050a0b0903040504091401290d0311010912080c0f0720030d021c03 69
    0x44034a48450f4068155189944016920207007403405503054442c0703035185908141411000401d00855401501c0075484149040f6414081e00d160782044a41004200390301801d4505010014180721194840c1d010503c0e83c01010f880c0c141e05c9030280703050b88038011180540321048100810010340c00408400c00c0c250001d605181e18075441241040e00d07500300b24040c00c2c0c0254003440030401411500024070510795156070700d517150070005140760301048140500d4410300b8104640070300a0407609040f60b8010002d02250070039076039807011001000e0041190f80c4804c2c0b10200d43c0d40c0e03c0c0d00c910011a480307a044417221400c440d60f840c5c00c0d40c254540007243d1200c1000d0415103903400c120110034401c000c8584401c421690700d002e407545940405c1402c1c00d0f610f0030f0b9603001000341110150701405219110886030796100c0615a00900c10040078004080c018000c0f10000f4159500524001d04040c4e0402c0302070610001003413518203d082c4190042c1c0c402e10004190b03405914041240ca2182e1400703 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 879391546 1250 879390296 879390367
    0x1e0304031707080703030e01093011030f1b0f1501050d0c090e030f1309110c0d35010504180203060105060d140106080403140307021b1c08 61
    0xf9110030b03014000b4007030103051312402c50b001c42d0300e020340c056500c4581c017081c0158503811503407055031600902c41c8001e0000c41c032140752841003401010b4070104144050015031030420520b030701002c20340280f1140c458081807400c84910082040c082c441d680004d0324000c040504000c0c0003400201c0307040e842603004030349103030020004c1001e081c0501c0980b10038100208030b00000400c2c081c918440c0107540410140041070307500740003401a100c0300071940803500c07c0c410031181150000c504d200300701003841a5440200c200250b41d008e802e281c11500144d4034904c100940c0703214049850040702ca1107801529031440140014074003440b4810212949001e005507004190f40420b98864041c0141d91003041301160b003180319600307a0072034065940140d500c2c8216596502c00500b00344c0c0281d604402045905081d500c5c2413041105407441072219038014503154614060031f4000107807401c0400d8101e0044042d840ea102030b60549002c44038491400300350380b81e11110050740101c0148481d00885100c4241 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 879392796 1250 879391546 879391553
    0x307140303031324051501140a0f020c212a040f0b0d050604171207030c1e05181c0816152a1409031e0304031707 50
    0x2a00d900200e400b15050141c00d4074101070700c0800d450560610018509013040c1c01c1d14110703801082c007448615409401c074010400054481c1c024406840300340c6a4244400c0c000c45204008260305401c00d40149c0e6240009400412201510000302121502c02c24141c246014401c120008540c8004141c82a007220440f00c40306005000b1100c03980b1403619242c82041d07280c0150300262032241d00900c200301d190300c07900e40980c460808942c2a100400510b804014070300014040741d104164580020180340d80d425800c0e002001040340500401625621075031014802000209000d0700f546c07116915413446c0a0300608a01366803d0b000e0150000c200000810b42552120101950b070090b81e0316182c01c50195050081c01d440320024244114440340f22000b01c0c861f42c001e0700c0700010a525001018041125001c001d072903501030304001140b155440c2e250400b84030143c408030b10008d058514182d40301030710407500c54050300680c829400010f4104104035408030301c10740420401c501e850500c0307003645 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 879394046 1250 879392796 879392803
    0x5010b18041406100e030d11071d13060216081905040b0304030503061903060f05010b03060904201f09150905010f210b0a050a0e04020409020a0305061503071403 71
    0x10441800340d07056110350b100d0217000c1c00701440003007009421619800144c540041044100606408150054200c0030591080b040140c04100d40d9002c68400340f902c4d4402000484103010a0507540e943d8280001740240e086210280804d034001ca46440e220074030b803140200c481c800b4450381010700c081048100030907448602526030040c0c15041258681c0d0b01e60021840405840c1d020848002000c1c2010040020075802450014083c0c1c1c01080070b6070f200d02c03003240703e07100543c2ca8076840b84c040750015000582071129620f05a0b40040308a502880103030208404c2e0451700542d19000103032000841085038007029800007801c0200300c4501e1601003c030082e0090b4651b0040304d0410040c4880030850701d004050900201140720a15414090001c06840040040002080c480c0c10b60500005092900040079829501c00c615024050780f116400c001c000d10144a04a0300824481e50000200d201071000b648220792459486220710b0342c10041500f402d000750403450f407a0350020380c13410fa9603c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 879395296 1250 879394046 879394051
    0x6080718090c08070f0905060409022d130f0b030a0201170907120506190c020d230f0415051801080a060e0705040f0b0909270105010b180414 62
    0x1035000404052600749000c510300e181d00711451070311400e800081d81441850702c40040300e02d800070402030f544508080005481003c2ca0203540700000c0081c0c80d81c03a00020760345150000407140e5100c200541d0301d020034101c082c407840c1b2007006540c0c1c049001400065014400501c001207000e08031102e11a40003070180d1540030002e00342c0e0b4405900096000800704540400b50002039110000c504036481c02c0395643ea82180c0e0481080811440d103020b07060741d0300508102520b250042d10300f45202410460710050b00b00080d0302034074000b203000188150f412000780500782c400701a1a94460030028541e07000d95500d10742008114007000251000844202c040000c03840074a8090102d0b2946040c0708043d03c1250000e0a0024040043c0f200650704a801070049502282025903c0303a034982e0681044c0c002c04a400c0d41090100000411550702100c0d41d00048105440800d540d651010155003115000d0700100c00c00074000407428200d00d901c5034841b110740f0044806012024403034100c120700003000b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 879396546 1250 879395296 879395339
    0x21002030112080a020109060207110301150f061b120e1005070b040f020f0306070816180509060310020309030d1b0f031a04090c050a0e01140d020112020a0c06060807 73
    0x804c0e040741c440e200390000350456030018400e6460300880d0404100420f04d1400d160310075880c00807441001840c4503181c9c021108810301501665180120a585210b440303142c07036601c40303502d40c104400074030804001d0b0a04021980e0b001d03680e000c0601400200745440d01c14006108080c00100b0000d803503100002c5c0d101d0340c411420700c181e010f42d10100e401c44588140315541806444104071070f85d43d0040c0514803032501504124580c42e116141a5002042d01c04003602e058800c05090001d42003031808035401400181c101d41c180344503030708170700100c1c0c000f82c1d00c1100c036400c00a15003001e04014094400c00305114a40040e5545080c203001e0041c01d11100da28082c50344aa2104207070044484400d20b80040181060108401c54039152050901e1130245610500c1807160100e10928100007140c140e40c010711800703070600010b00402c451707042c00c52000ca0401c0710203015040c865490380040e080e482c02603143d810010846113840c6040d14110342026149601c501c00802600510308480200900d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 879397796 1250 879396546 879396563
    0x3031513110304050a0b070f0507020918061005010905011d0405480403030f110a240605010212040b09060d0509030706060905130605070207090e0d021002030112 71
    0x3084035040300504525107241c2071240021040205224000c1070110b0024428040b11550b07940708041510618810040c460009400340171282c0141064042140c0100400910104032404000c01600d4503104484003820504145010007042d60420503020203004c00f400c103400c01076480c409071800350406d6161140300f25151404150b1070002c50080d4080040d80c400700340c4144490180c040c0340c0d614a84482904101003140f142e9014110009440980707900d55100c2030382c8030741c8400444291841c103002c08014041e2440001c005948a080c402d0703800ca074040082c0300741550380307000320880d40540c1c4040e0554202c8404928030f80c0b0150111030541d070001100c0c50b20341045a0104549008054a03c0aa18038150602c15201d000102400c1441e1141c10213010b869100d400010643c0d40039031b840c844074200381080c0c1c40000c5564110b190b0082c1030388111242c00769218041d00c141c2d60b21131403100080e044038606074003e69045c0f0241e0207540d00c071181545103500d030888480180c0c2005e00301a02155 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 879399046 1250 879397796 879397819
    0x140609030a17070e13060617010b04260d0e012c220606020102070b0109020c3a090602070e01080c0f0d080301091a0d12050a030902120618030315 64
    0x90050313205046400d00900700d041100c0b94210510020b00751400b580c030102d81524250300102001c134808a060b600d02d403e0840c01c02d40380020401d045c41969405402e451002540d444100c00100402542071100b41c0e00e003000c000c100340001d01525607050701090021610203140148072011401d40d000c00b07a05030f4801902c1100104034140c007218462003c64100e06100000501caa41500603040850240c210340c803259aa400b016001c0740700b01000061150882d4454a009902c038011060a009004100c1000754011341c096003d40c3e1001000340010402801090042036030404c44c50010306024034122041d0350500124941d510540814588280d8840e000b0b441c494460340c0c039601e120366001c500e61361039503141c01d20710f4040c0c880c114800c9108a20404086a5450aa00e602076105d4004611307040342e050002c0202c1c1c0a5100c0c414410a142d113855828005803501541050000516005031003541407055029070048400c0a10b6a40f9030302c14001d10060382c010804000910700b080b42c2123203094 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 879400296 1250 879399046 879399061
    0x309061b03240a0519080d020a05060105060a1e09060f050915070804080601090e010c0e0d02010e0a0503030714010501060c080d02071b080a0b06030613151107140609030a17 76
    0x1580f9400083d00408185010725004c004c034500c0c2800c1ea240b0f102540c180c2c103500380c412a541d4841b4000a885617000c1d00040002c0c0c240000103190840c15031520003042480e284d070b07141d084050215101e00040b440c45041101ca540322010708000300b20340c43c0c1070b80740407403503c00103d0550842110301c0d2042c00000da8241003003240380445000306555015103ea96030343e2180c3d80020000076044005550a01030070203070191141440000b4034070010247d259154154004480d8003d103a4185500000082d0002c615541d0401c041c01c8007a1150441c4401d50b0503030703a83d8038295803069210f5000d000202081d44001362001c0141c2d0403000010b180182c43e40303070905080042c021080c5004840c100000720200712070707501080e40c0e508240030707401100e202c6c1c031214149941c611003180c0540914000d03250450020340c52810486c44080c2d03010000c64201c00d494042e0a05030f00c400b0044030413404e52501715410050030701105034004900130280d03050082c0b030040944440490000710a00318440800600390 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 879401546 1250 879400296 879400309
    0x4030602160606030c0602060a0c0512060f0307080c01030b10090b181f02010c020601080c0103020a03021201060810080c010f1b0b09060114031c0507170309061b0324 73
    0x103290300400300340500f565a08000710301403410702544005006034400105040031034003803003807245070aa41e028546102110649840d200c058040d80d4807061130700884401313036820400c84010309884006050300c541103000140454220005007401030450305140b241598200e075600048841030300c05941d84003000d289641c0d4a44542c01c0e9964050a21203820303381c0248030340414205030711a00200407680000c131040e03aa031103091240b0a92030f400b554040740203500c2600a05840c03501e50a02600f000c0b400c800c0c400501100760851000252042c04000000d64180c0341040102180030142042061540c0028501046000c2c5101840814003903444445181c158020183c0c0e00600c890a49040082005441d01d0782846036243c0e100380c0c40da15011070b20b0046024500c40110103041c0c01501c4207810b081d01c8503042581705464844075528844802050040198840e0103d0000342443d49441080c1c2d2040f0f022075921950043c1d018020000c0071800c00807002d88800000c0e403e200c00140003030000c1d04c1d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 879402796 1250 879401546 879401587
    0x9030c05031206090a090f1212020d0203060a120507093620060706050c12092107241803020c310c0207091406100306080304030602 58
    0x3284000100c10780400c400b03072181405408211182c032030680b00c0c0c0301c565094075190040905001c104039101c20006450100c103403034080d80c9062082040d82d80004800490f0002400381d450a81c0020820400f460704444280c0a80303a000800c0c0180c03030441c1c0381c0b00d589440341c1c0644c1e025580e0b142004c40c51550039041800800100610b01c07030074420001441e02c3c0404100300126240000c03003046070403480780f04004140720718000d0412400c10669440c0c8601402c0c0c0500f602d0342e01c0204009065081c00e1303180340507106600e84001444410170f0403030390899182d50004900300048050100c03000084408220410030501c11001d03900ea040043c1003000205184d07400803040c2108540c446041540100743c091118208858851a0b40404180340d02107000a0150340c0303480c0340d031108006460304c00d40e1080c09000c01506c1202d0301d09884039100d0080760103800c946206200840c04003c91481c146558104400c103a00d014070040d4600132a030391b900d015901004007010780100c0d40e4112118802000d00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 879404046 1250 879402796 879402803
    0x3021305090901150807060c03080a0902101806080c0f0903010b040f090b101d100305070f0e16021b010302131401020d0201050403090e06060c1002030105030f0a021309030c 76
    0xc940d410b00000450081500b02c0200c0c8101e15126400191004c002c90b90344c00711a0300d0307119079105040c02e5900329640180104140d0510ba0345508540144e200c082c42a440b44546444e114580310007041c0015140005030f000004010300c03e0100100800721201384d44065141ca41c10644a811000c00a80900070000c03a00790014039100d0311a2049416030030205101d40650703481c101a032580507901400c240c0c58001d480090034188580382c194030540d60090790184c414006d20300000e032a0341d50541042c3e03456224442d43d419202007880001481d415081d0007000c2210040d12034a80c5040c040d45654601010040b82c0b40d041c000400c480c0d00a40441c2d1805884840380800e95856080844c1c04a224141050051056090309200140144112383c0901e40540f2000007141c40c103800240449002000d03642c0025090010403d4110b00b002400c006041d030840260304c0f0740c10b101c1854544805500e5030313500c1d0307804018050b001d43c0315041c040f15841c0058801007002021814140c904145084005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 879405296 1250 879404046 879404059
    0x3020d080d0f1e060e3702030708150a05010f11010f020d0b0306040f060b010504052e021204170a0804080a1208010302060a0f02280b070801060f03021305 68
    0x302000c0c0166000c800c09a01c038143c1c40e46003805100800080310414016080c100d038071780000c00ea8a0503240841898812842d00602010540314031b241c00d402e240303201c0c0d0405e85802100380851242c106054552103035207000700d1207030b540315480003031340002040c4103540c1440110901044402d105007440e9820550a50007804280c0c00544408000d520107040d42009524192403494540b8001c602a03000d80c0c1c0060f1b951540003c1c58450100a201c02207a0506200c410071000400380c076008183c080c0f800112105012040c0e2055400d4511281000c050007190081186642e2045e018015603041d00c0c03e0748400c50a904401c606145013400c3d64070301801c00c240100c0d000584080002c0c03030034000352060b1140550018191400d07601e0f4042800000e600c20380c2031100c40d103003d101700d580c3c1c181c603041c1c1d10443d10314005141001e02260707100034200d401c80c0d4020301e8850034400f000d444c16802400038508245150300d441c000900f031010000a0310704041e00007480821034414001c0d114040c05004114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 879406546 1250 879405296 879405311
    0xa0e0406120b0a110a02100c2309090c04061b02040e0a0f03021c090e04020d1712091203011703120c0414040915022109032a0703020d080d 61
    0x41010b40703800301c41e0300c5182401e01220321000b90781ca10540381002601e400505031001d454250001a02d00007015904000c46038810301c0c0903980307500750810641380c50450a0f9840324800c007401f4000703500a003281e680d40700c2007104218207980520641c50758005203403070307071035401c500d2000a0180018440200807032103902001014070078a4034144858900c01d408607602200014005101d403810040090042680748034100300301c0301e6030b0742c1255025200034070754403c40e10507580f5006282240c0c4420b030728505010542d01ca030081070f030851a4021031321200402211365150030b54209031005001d5042c030060030030310390b500c584020020746004681410b20360b03010b450314108503a00d540283c40b8210021840001c851010f04140c8518400e25401806807040346408107060406507209006211805c0fa070811380c16003004124001c00d00030782c042809035555903004075040c0161115080c24807003480d9801440141c0c5800050050300700d95041d15091905a01401c208280b030040c03400d000c050700c1c20030a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 879407796 1250 879406546 879406553
    0xa021c02030f060109080619020c010f05330f121207050303040624030602180d0c052704060507050708030a0b0a080102071e02030c06070303090303061202060a0e040612 74
    0xc42c511400703080c0d8410000720703550215a680d484065500c10794040d001c06004648200c160001c1c980c440e0703034500100340c01031a09601c40031144100c401001111041c00203034410502100c0c082c0400702d1941340701d1220100100010030030748203204014881c80c4200654220020184512102a5000c8141549800036405c119031603a00840d4102d408610b030000544601000070344444500b4800311402c88200d0a5981e00340c001e5000078645070f26040710f186c0c0e1543ca1750b100d003500c03604c1d5803003a0212040c4034034110510031900c04250010301c3e00c200344213040d454803030310301c280343d5100d50825408a6207441e0b00700103460034030440c80c1c0540000400070801440c042250000750800350191020340170103590703580e42c600300d0286400041c0803403a8002902c0030b45040101100c034890000381910009030a50340011540e034400c80e800c80c0030a0b11081900180740c0c05210380b80c02441c4250381840c4031a0a9400200c1520a950104050000b0800174940d1516598030640143c503400c00c444019501a08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 879409046 1250 879407796 879407821
    0x61909080a0c14091510110d030e1e0a0b070c02060c1f0510031b05040204180b030c060f03180102030133020d0f1101021903230a021c0203 61
    0xd4029486400c0b01d015900342001d1080320701c00c60a00d86038540c4000700e17604200c040c1716101c05840820240d410081e00d05c040c148658074544600d0780b00080e1a5120020f01400c1c1900300c03920070300103034101e00c00c490f10180c0418040392081c1d00c45074040043d0b03a0010156081c3d0003038500030b5000b540115840180882c0011881100c40c9841c220f00c1d1000d40090b00310013a42d03c21100005c1c6103c61203001c1001503040b1900c541c0000941d40300642654450002c81d0403a0850ba0064409003203000010100c1c010510400190384001c0d030140114140c41004680c0c680700304c41030031481000020015403094010714500c001940100000d5540307503910b01c03210070b820000b003407901410a1045049082c54501201020300209641c01a080c0074885d01001e440742c41100d0300c0e801c14490500e06180c1d041c4030070b2000740050b0295088da0101d54003039000040c02c45032643c0c00c84000040321842e1800e0700c040c9500c0d190f4420b0292801690300d41e020406074500b100c601c42c0004283d8000700901001ca12101c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 879410296 1250 879409046 879409049
    0xb06220f02071a0106090b09010207091b0f0c020102060117100603110102100207020d2a260d08010509100806011412030403032109020d0507060f0509061909080a0c 72
    0xc990f2110328004500d940010040217221382d07800f00b1130007103080204440030030140442c104140180c610642d615500344007590242e2800703081c26900c0502e086401504442c13499a1442c141c9400b540070340103580041d580f4801070190400101d070b44620b116203078504000b01c0950043c80c00f010b006080d40c03882c0203804442c820703034014058050000100421056031080d9054590010140c030b024031041d80300d596800c035001c410408003014405000502000c0080020000d2880100303e07641480d00040b000081c881500000d10103400804000000c9640000100c0c1919012a81103600d0b071240702140311415040d80c00b8a40c14000c200001400c8505085001400d41090740c1c03c40b6074a06450107075440b807060b4000100852500455540d101c0d85607800c01e09000d0a0400c00a4108034070340008880103440b0318211116800b08400384400d0781e000c0d882c00380c4941141040341c20551008009041401011000031400003c0800004510700c541c44910050013248180d46501c0c0c40740c14040b0410005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 879411546 1250 879410296 879410303
    0x40f0807140607052b14010312090b070206030402041a0a0803041e0f0315061a0702030124061404090e1b060301150507050c030303090114130b06220f0207 68
    0x900b0000b8101c1e40c012403c03a00e00c0b0030365850308000200c0000e00080041d24208204030326907510201c102002c21780c10032983c042e5000d0300c2a801100140c020061855583c0d800203072032030f1400d04c54072005840d0307402035a401a0b070494011400030780740003961202d0302e214500c0c1981702080d41d000007008a03001c002042030310080516002d0b1541400c01103552a0701512810601040c1880200089a010001324005014888003c250a559107214100c80d002d140a217a010680c009101c0007103140034880e4001041110990549440607a904141001c0140c401e03101400480b950741c0c00c20000b010700300e42c0503013900202005850740081d00c155541e904030000d001ca001e001d010117146843d005040e281203410850b201c01440700a044200d4250300082c00840706440344480c1040669011710265116050f003400000e013000f1000c0c100d550341e0307002900520721b00d400410140c0c040b40c1a80c0b9000d901647c20740301078180000d2140d501110180c4e00009071050b03032070604011119016078000f400c00760700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 879412796 1250 879411546 879411553
    0x2040507170618160302040b0a0e090f040804050d03020a060c02211e0a120501030b0703150b07020603071106010602030a080f150f151c110301080c09040f080714 71
    0xb120420303c000751a522442460500100c000240480424020780e00305030841d25000d4281590341510003940e400072050500468045a2801c07110304120300d040d940151080c640d01050b04094031261480e1045005940c0100c6403602d0103424940200849007501da8040300c1000385d4041148000e44070f115034214140000c281e010710b4650501080b00f512403038a42581390210300c0c1d0105100071559030000150205020744025071405000d4544607140c000d40c0942d02d010480c0ca0031190080c210b40020384026481d10036a0410302144010f40b003542d00e4241d05032019642c1e038944240030307110400c405074880c1151068a0001c00c030541c0c0403000d0b002145c19a00d80c40036a03180c081ca68004503104854600542000500003c2d00d440d00c50301081076248003804500000c02801901a01540f00d41c01d00103003101180030308106000a0310524101c60b8500070002d0031541009813480d02c0e00b4030900042e00c111074005c040360900007040d100e201402d500c83e00349607407801c25240c403400503d04850342c40420b00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 879414046 1250 879412796 879412801
    0x209011401090614040608060f09041103010c09060e0906041b031406010509032d01020a0908100522061803180602070807060815030a03170907030b0103080c01090204050717 76
    0x140101c00d58580d1903018584d5a01345800c0c03030021a400b840007800960f0003070000d84000503903110a15030a00607030058100554000c071f000300b03042c01d403030000c0384000c204500c8610070001075500003400c0f805001e084440384910380352240003502408114400032a02d5a192001e19025034155000c0e514007840c1d0010100c007681e9410040d5030364001d05c0302494141d0044602c840c2021506000702d05a14000030040004202054805003241c000c60340510204005980034001c0e52010003481e030040082010904c16131501d00301064240303105040595640c004640320004100154221501d4050110401111090141002080000cfc54a140e1600c49100c5901044441c80481d1480035104184000c00300c481c81c0038022030341460010710383c181c10742c402c00700c0c03140c01d42c0c0601c0308140c00d0707009070740380007210890700c8018406a20103445d000b500d500113038080002078031044505045130b402c1003416895141d1701484c0f82c05443d420b64000d501929240412000d0f68001c04034180b032041580d03c014959 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 879415296 1250 879414046 879414059
    0xa020706021504020a173f2109150406050a0b090f01120503090406120c09021612030209100305090c01030b1f09031202010c030c0e240403020901140109 67
    0x100750a90f806034010a40740428480603100c1003c00c111010440101c5000d25003080407464000002e03c12800a9008468115a00f00050754006102805a424586403144440b050603401101840d50135030040100b000030840351003823000752904414215802034510b4903160507001400c0480700d070304085180071400441800c00144d00c51107541c6d2400c600e60240d081440d800b101d10301100046031076100c04c201c10401134666006042c01003107080404c108001151400310048105a0030141c1d80718814030442010414269442e6121500151b440b88041d6003220704030068451001c281d40c100c5c28821102410641c190b1100b4801c0200d1010745600445c1c40c0011026181da6000240e40078017001125141031074011741000c45600981000c40f42143d41e5920003252070302540da08000350350746010340405590940926a901c0c521450622606045400094011681d5030002200c4048a0300101013030800c0400b00c80140d6001028411690f945212000760b56604500407400101c0188000405 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 879416546 1250 879415296 879415333
    0x42a0b03071e1706060d0f061406130e060a080d0c020f0103060302030606131508100b090f04150204051908100b06041e030f050c0108010f0b0f0d0f020a02070602 71
    0x580300310f40d4914010043c0003401d5050740e0400307009107034041c00030442e20310300e40e10900c80c0038810030b4819408201c00d490900d0100311801e0100099029000401c001c00c00601c00840f004161070300384110a101707881d40004200684800d0b00801414031408441416860300700c1d21006006200701d40303941004001c100110140c4401e0f02c070003501032703101c4404161185002c1241121744403824100107900130305410707070740c11300702050340803500c140c0013050910110021409036040340b500555a0034410b0030100c56040c03118000170409802d0300741441100c040030030740d6012500202802058048010b234410f100d1982c105031813064036424030a0001028420b941c03405000d0920b20300034003003401c1615154154521940040610400319145400030000980340d00585c0300d20f9009800609000804c10005042702c181a00031414a60441a080280c1c058440031903405441e80c07202603488904826a246c06451017030548040107002240c061196035000402404941041c2d0848404980701021080c1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 879417796 1250 879416546 879416597
    0xe0115080a02092503090f020607031709030306100c1a1008100606090303201603120c0b060105070512120910050c07020f2103030702150f042a0b0307 66
    0x448a454400c0c050454000e40c040446940186500c0301f40c01241d0340090003503404180e080380804c2c50790a00d060100d9074001d030113a0280740701c4015417031401c0040c0013400c030708018003031103080020140d102c02c01c001a4031450002565421610101c03418068606020310302540903401c0188180c54050240d1181c50242504079049074981c0000c0300d05540381120b030f04c1c07207081041c1c45000c005640c03041d007500d040154a001c00f84402c40201104d09526002c504120b252000307604200c10070040a0100f0700038001981c1001090a10300d945104503e440c505240c1a01c425419400d00410183c10400c10348600c1ba01c2801a0b07010341c0c0301c0c17000b80d01008044920a480c90110410140081e0005003809901c00d05112001040303811002030f281c0d004a01056240e0300784000c1d030000301c18801e5441d0100400c00d1040300714145080c0c2d0b442c10740c40220a085009002074502030004c4120b0220b803440ea251341101d201013000380034201d9202d40c606546581300340c074110f000994200101c691507565051215 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 879419046 1250 879417796 879417841
    0x14040509130807080a03050105010908061e090c030a050a020315041101050717030a0b0109050409031209020103020c060f012c0a0c211505180a0e0115080a0209 70
    0x48480d10340e410204004840c1d4030301280e08990070801000030410000c0907007001070741607501103010f42c1050001041000305522510103544241c0c28008850398414903140060020400d0041c5666080e2140f4a09901400c0054040c01000d06981c00d010020032103000c1ca90003a01159041c08030f9a900d44a0080f0417a03005e0190b1000000c088010362144008000d80e6000d08075010510035003c2846009070b0007030360504a80b50303a4101d18020307035802c001408024030003160204607920741034401602003208455110f03007455480840504580c003a5044c0e0705440300382d10031900c55150540f0700c04160102170240e521050025007031181d030700c0d080c01c40460714025071803145002c5072a02d1070b1000c09891440340030703018032401080cac242c02c007445000001c46200d1032140115900b001c900c05100c020165400c0103018048100d400c14249003020f003481c0d0403090600000034804910030301c150051444c02c036001700c018494880082c0082d00000d4480c01180221803800264440c40100750100178010080d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 879420296 1250 879419046 879419059
    0xf0a05091c0c0902090d0209011203180f05040b0607060603200a0b0f0c150c13290304030e06070b04050d0e01020d0f1e09061d0303030c07030c020a06030c140405 71
    0xd1010303c1258014104e241006856503a04006590009000d000c09030000f00307030404140303410020305134492034a80c02c01031440c5060710002e00700040085110f00500440340901d1325500d42e07010b01d80350340d0304940752070360881c80801010707482e403a0000b07000c82050315881c20072421048201507880d10b42285002c03a03d426032041c1c80c041888280b00d0302e942040800c8002c90003001010152107035403c0501d07120750094103070039a403600c00300202070005503c1d030007d401040c504005580842900014900c00c81e1410650545a039600e29040722204082d00509801140105040d800c1191100069005500c6201612000d001c00b00c1d08991038613010a10a00681c02000c03001203141c09911603440c0301c1c50f0761400b1152005031409540d401821080c0302c50006013121420080745904c40079128030480e102000c041207211120000303a80340406401d0020a0784000b4180d0100360180c003e003100c04d68042e2182010355036444010f0300034000c00425401051a00b0043c07000440c0c50f504403000d5400c009c181 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 879421546 1250 879420296 879420299
    0x1a030906040b041104060303210b060d1d19061407080105132c010b01020f0304060e0402041728021c031403100303180324020f0a05091c0c 61
    0x10014070348000f90042d599007511000d5842c03d41c40d40e000780009140280c88003401600070010515020080b072203070308200d43c6806000d1a0030745d00d070003c44126520100d00410700311520b011072650f0103844506008039101314088240000c800c2c5845040b8207010311002c2100c00000400c64031300f00d80131108540051200030040c0854580101640d0400510480000d46408880607401c00c00741d010302c2000b844c00c03140c1400010301c0e03001d00980000890a20141c0450086641c3c42036407405140580c10510406660315503e035106d0fa416100240b51074903c0c224030070321000c8010f441b04040d90044041000c41082050b100411040d08401e0390b038083e02509105020081c180c3c079030307550100704504004541c640900c0c03d5210802030746c000c8008280e420000740c914034002e842d800602691015407070340c5000400101e02003840c88808200002d03401d005107900c20310407500902c603070508001e81c0e41020444ca152103a01c00058000d504069503010041d60311000c5d4000c070340c8842d001c020261601c0800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 879422796 1250 879421546 879421553
    0x30a140706031404120e1e0415030209151503040305071202030307022a190837050c060418061403190305070209010603020c0c09040210200d05041a03090604 69
    0x340c00c0064a22460200c43c41a2044001044010144280c48410100380c47e4041d0500e8140714007651600105803480a4a03e190f0104001c203600424026008110040e001d109442c0c40d20340000141510703250075541e142502d8080c005811401040c1c03074108282c0e8100d108a4000000c6a02404881c2c0042c401d00420a02c2c0300d5800110b58112524010051222030041d102e18140d01610400c011810302c02c00e040588003407030a9034090114820318804a5105040a034003a8110091030054482103d0540181012450030200000c4140c0007000000e00080a2841030000144510002c0050040c980e82e520031031903940800b42184c1d4950000410710321150314880040070301307034800d0900c181011441d03000114400750076400200402d0300098507100c3c1c810103112500b0004011140304c05107040c80d40101e00401c050078400018000c0c83c42611401c0f07540c0800c4003000e89010341c125902c180b411703034004200350407030700c500e4011044446003800b40c00ca00d10242d03881030000340c00406035580c5986 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 879424046 1250 879422796 879422813
    0x30103030c1407180f1503051e030a140a050702030625020f06181f1e140a1e02031509161407060e010e06150d03090b03090c030a140706031404 63
    0x10250122140e0302d8503000051114080786c1c100842c02440680300030360000d400524455950090718101c2e8000b040b40344407485c1c00031003104100c4044c400032900e0314441c2e08141e400c1d100c0e0f46c0b23019600d4882c1c1d004100460f040050740f411400c40034175411042040e441d40a0307a8400e20740844206d144c1081000940c0b280d103a81c6401100454803084611030140851041029984002010f0004d07072640f042e041001c1e141d0015001c0c07440000c100f00400750040d500c0c0c01d0781c068058500c680c02502c4080758506c907050020020070440320380320115940e0500c50944014501081c22060081140d040003a52600300c0901d1980c5c420f02d82c0d00c039040301490510900600f5841046c04940c115510280441d840b1024460354003203015401c000c1c451401e0201e4044c142c041c518128920a4200c0700c4080c001039031014045045850401c0196200d8490100035030034184d03106083c079098412400c250082c0000314a55070b040e04d241100703450001e41c90f035004800740e50151449042080b26200803130001003142 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 879425296 1250 879424046 879424061
    0x706240918050a0f0314030a140f01030f06090507051905031509030a0305060a03080307032c030f0f07080a0903060b040606090b030a0608030301080322030302070501050c0a08030103030c140718 85
    0x3d00c1e00ca50742c820706c1c103503851490708160b13485100ba0340ea840d501502c894500300101d0b0080c4181502c100650f00d1540c0360303202448408401450551a0200e481c10000d040140a026040040ca980000700c0c410ba0002034121452080340d10038032030f0311a002400111001c9803805405040040e52900045040980c00361101500f0303d078105201041c0003010508100c060b50090840b0395020031100d0348a40425881d00a80182c0c01e6681204900030704964400070807038007003c1c20b03030b90100c0d1100a40509a02a03002e0801c02800580c0001510f041455012240c0010740c1d10500c0204011500d0209002c2100d03050300441c1e0204940801c2408600801d43c069907000d000500c0100380d140c1c0341e018181c02c40d002a4024410f541c030100351070318003e01d021807110b0989401c16900c1c0c56075107140c07030096031001988030f964140b00e40001c070301113507100500c0b172402c16982242165070750396520329000304480412441514880f810454150003210302107036840807203240107240c284201ca040c007a1001401c40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 879426546 1250 879425296 879425303
    0xf0705070e0c0306012627030d0504050610080c06030c2701110a05120f0403062408011e0c030b03070e041a0702030d020706240918050a0f 61
    0x194140068828a4010120302c40e000c0c4000c8580c9034203020001611403484c0b9007802c49000120400c0c01c0000d20040d0b946903101c025241c541b1000300040c019003080b00f0894646807a58040040d040794400c00e10341103940640e11420490b0b1712541c50500d0034485800c64011041c80b03402248a0100031303c0e0034000b4541101c54440c0540c03820342c1c0c00d072010b42030546040c840c440d01e40d0300700a24009581c104400310902079001c40500540c0807a941d909458890380104204103c5d4081440c041c2100108251000b540d4001800c000160188400c22400b8896011410f01000309940c08100703800103002d42c400005a40c6582000000400c2c000000303046041801010107548816200712a542001300780d0043c220400f10b01d15600300350414031040401e80005240074084141031002c1e640e40041100c1040c1109d08d0011381b51b00c45494170f02c1c050302c0526104a08569604002c1000d14042151b034401c4582c20300d003c124074071214001280304030081502400c40d8114030184c00201d0440754000503894032 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 879427796 1250 879426546 879426553
    0xa0317100501081e0a090302010f11070b040c03150515060a020c040b01120903091a0304051e01110417010f1a09060d08160302060618010b07050c030304080c13020a050f0705 76
    0x41102c01e250380413080720b101c0150307a181c2d03044005158082c4200d00115002c401e091110104007200142c683c030a05100a00100c1700d00f0000c0d0601c510050f80340c014543c07003c0000401c50514890350b002d800c003a41d00705140c00403070201c066980b030441c040350440102074024015450b0480708100c01840d80081050600a004010003e003c0b200e11454060500c41d40354110000e042615010142500000000f00c4840820500001c1000001c10320100c040070703803503a18218005000c45014010400f018196580041000714200708201ea200002d4000035001700003959070307481ca08040d98208040c11410b4184103080307106501b014940030341c0c05800034094818891413a03840b4015507000110881c9100100d07802c0e0010141c0c140314043e040002103a4405503906070760500c040c0010180b11303080f00700400284050802009003c1d01c4107000c80101600c0c1c40b40e40e503801040d19205212026445000b4401140244810742c0c405e880b00080c0540d103ca00340071340890a040190701c0348500741ca4610 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 879429046 1250 879427796 879427831
    0x1015060f051e0c07030b10081507030f1b0f0206161101090f030203040e0109110f03070c0210020609071707050103020f0f0711040c0e01020a06051f080a031710050108 73
    0x2c070300c80010203030000d40074020040c0610314140711b0820b101c050300c151141d030f220300707000c01c841c850010300c2050350004810800050307111440107500074134002071114a95030804e205001c0b554060014500d0380e4115489010f284110400d0813030701c6000480f060921380381c222076001c43c03640c03161940c041e95034000c6000084503407140d120b104a09914400450060340005818070480300070001c070a00601e4040300910808400703109100131400342e0140880101e101000141505105010021045070007502e01454045040c9000b901e45904031100141d44c41110b1000500072418105807030214810409030a59a0030440114042d5108540f524011502403101d10210050030006041c0140b0400601c001040c2d030783d0a00c000ea80850300503a0a22650f04203441960f40c02146003d82154016030008881e075840021004078020700c2a2820b240c00b85d820003282c40c42000440c825101c1c001e1b1200340311503c0c1e0411025080c80116068010301c90589030403c02035015504458100310500c8030481400c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 879430296 1250 879429046 879429097
    0x601080411010e0d140d0c03050a050a12020706060608090a05060f180607020a02010e01030501050d0b0a0f020d15090903050f03040804090218040509280204020904020304051015060f05 81
    0x14080302c00d068405d130001003c1880181000c01022035041030760b00b400103070100c00303131800782107809008039000501500046003450349205000401208034441c00c2192942150b05281d0014841d40c0508000729107090045008003400152007200507612070000c04036540c2d1140002500400a0152080407646507410401307000d0078080184110350560082c51f0108560000412128000114074145460000103015039165540688a40c6d07030018043d0500c3d44a4280c4c000080403a0207003140300c10b20104000c80c151020380c2100b02c0e035151140c09881007a8840d0f00c91811039807000d0006010800170404141d030842150099a4824002d440c610300740380e41c40c504c86041e42d101c428a50051001105102600d107400c1c82440c1c1c00c240e81c10f0050000d10340d0420340744000700741c001411801960b200f400c1c00456580f0703012254194009003080d9203c0c00c1c035241c25030360360341c414000a84c042d0034075042003800302c40146000c007207907211381d00d1001d002140c100c19a280d81c01140c1d03141c002c414810411021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 879431546 1250 879430296 879430309
    0x10140a1d0405090d0e0a1805040201020a051906112110031703060910060801052803030504050909011404032a0b1f0f050f01090f08060f0106080601080411010e 70
    0x140c1908001d800c0c0d60304c07100070081829405130b100910801001409000301c00442c103150b0641c0c03110280000311900c031800103034602000600010304030312808001c16042083d0311265072055204001c01e10501c0005216140d290160600260007003030714044565007c0101c850f1250003210700300c5003000c40303901d80d08d0707260a22441007040300600d5000403e119071030400c0900340b82d1014010700da003400a0b06020004280c600c041c4244c5200310306884c5500302c41c1020700d10030140121400303100b421142c4e0f40d14000c0d00030f400603c2400d00c03800500c030000c0c21080c41030044601e01c860540408860340d42c0d581d002d9803070b8880445040418910303000302c504d40d0920000c0a101403070082d54a1030b41ca2502107801207596840040119004054500c100003031010103c144054078012906443d031503040e0700040720250040d17885414070107100c40740022902004036800d03004070b0410b1112042c0d070b80c9403181661030361700070303690580012001400a004201214284480a1342c14509074912109100010340d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 879432796 1250 879431546 879431551
    0x708030c0301030b090f060403050a03060f0905150102070f0302010c14101a0d050703141f0e0c0402090d0f0203030c0f2a0127090f05040210140a1d0405 67
    0x8000001c014414072455091080c2e000c032021001344100041150b16a44646000c1c00040c2030040110301307190f00340d02981000020788041c0c00c0b18410703d075549130300d540035200641c2c80403101c500c244402070007544003040301800d840450000354221032030342c0d00449401d01d540c40b040c0c0d0001c030446000c4903406c0c018094203444200009011a40f14040d602150315001d8400480d4401c0800205030400a02c000c61041c04a0360000c0c1061030300300e114020305040c000300a84a003494482c1403e0503c800459500c8540449464030407101c031100110280800c9100f1280381c40c0e4485800002400014020400c18403003c1c0302805032400c00c001c0c1c44a25240c0180d00d901c4001d5900070751100401c80d01e2081c44403402c164210a2000c800e0302d1600041c0c1903a55150f40500c103807070982110f00c50803211020410051031180c004100d24402c80440900404003a50124841d00741081900c101c41c0c840d81c90040700104112085241030400401501c00b164030078400709150b6544000b000d041e03601c3d80316031417 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 879434046 1250 879432796 879432811
    0x7120509030123191a091e0c0c06010902030c07240203180f01020712050c010e0307080a020d020703240b121e030a0806011b0b040c050f0d0209060103020f070803 71
    0x100b9030810900c0c02c9000c600000308161101d20380b0440c40c0700c800034110000080017069410b0800d41d01c40616074901140d0185050004c5100b000503c0540381006004000101020701940c1c0c082c0d807281300c440260b21050f5400740342602c080c0701440c007164403940b0720100d60280050b050311000d141e00e208016030300101c640b03625040c49401884d102120500c009031300064210001c500d0144c16550300350791081001406010400007044a26894070300350300c10786100c10b92004498448803175241007807450307104982402c0107000d8407407c030140c1400010311006507a80468008502091016101e00071124843c0c400300c06a00c1c0d03c4480c5803030719505080c0c07507030090b4400500b480c0c85e244101c0e0724031410640e918400c0c0d94010848543e01503882418240c00402c24646402c9154500f01850321b00403806c6006810f1201c418140401c00c04182c1d807100450301c0550f02245c0e0002d20404001011608030000381d0810031010003d001503100e5402042440e2015410508112064440d642550801c40d201c5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 879435296 1250 879434046 879434111
    0x10080d051306081e0726060a1202030304091a0a17150703141608010e070c080901051b0c03010509070308041403030c0d05070201030f1b03050a110a020a0b0903071205090301 76
    0x11007100011441c2210040f81c581b03084400b50616501040520300c90b441411103292804d0450303011550180304131002010031010512006241215110820580203e2079100300c941607000134403010040100340140b02440040c0c206003164075203042100c200100314000b059070711509035404003030000415018510b05401e80f214040c100c1070140c09800103810010400580303004110156501014900440341c1c000002c5440d100346500503162801096171240c2181c4409024030040c1c54006400120703d03c045000340030356260361005a0700e0764070a00028051020410044c01101444c048016040801a080302d02c1c0840901159003001155071120300010030004600e029076a15006048448060000403c061000d1307074a442c4003040008142001d150300c1d107000640c00b107240d61010003d25000551243d66100c4020000d485045010701102d601c08042e011a020346400011750b210070354440c11070f615209803501c05840a4001c070207203a5040d034903041619118a4081074000084076584001c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 879436546 1250 879435296 879435317
    0xf04090305041a0306100512132402070b0105060405030a02280e0103030e0114090409050106030b19111602011107150e01020f1204060c0c030b10080d051306081e07 72
    0xc010307000746d110128104001040c05a0002c0c1c250108559800108111000f0004002c5280034001c2a200b000905a070201903040060080d078590001c1a100b0711606c110380050b170f2518100f259600031401015003540c4107800d00c400509044080c1a402108012982c80603244004100301183c0542c00c01982d00d030044004208054200f000c0320701301d0409003841c145a5010b0740598010b4011a01d172503100c0d5454049c1802441801e62101000d95040304215859281211b0510b00d4106490b0b018a0141d107070072042503500d28000305852140d804845c01c1c0c1600e60540c2c00451784100441000c40c0faa005050b0b0015046034200d1900c581080c036503c880455039120000a41441c0c070030000400e6035044140d0540028040c43c0c03ca80568925051266580c80d860402c030b000030b4055000180091080301c01e004d0b511020000311001c50f08000c3c1103603020028800100c0300e82c000d5108101078085072080a10426004920441c1d10040b60300c00b031641d04640c000c03031246145051b2440c0703002c80da940e0171 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 879437796 1250 879436546 879436549
    0x4110703020d2607030f0c02010c1112090405041a101a030709091e33030804050108131a04290c0f0405030609031305040504020f04090305041a0306 65
    0x1a422540c01e00b42040500300000f030540c101d00d2844034034894418800000000c00c03642c00380e4811040140305031010414622a0b0344060b000300314054010002c0348100c056103079403d070b001a580c003c0c403481d4000340342031400110500000e0704000d40b044600303002c8846010003450130b44113a070340b0402044140c000c1107803501c41300c00044000202259201942041042541c80d00000301d103084034030000000a40030030040c0600049061500f600c0511800c100c220784083c00944035000c0301000c6620a10700c000400700036140c124519200061941ca400d1000b04034560003850a541d01100c6010b507040800d20980c0c2c1d81100f5003a456106c0c10b010b15940030b21050002041e032044c614410100744074401c0d10111340081041400616132000404c0004031075403001020404d98000b0003015040b41c0c0c440c1001d10302e03036859400254248445403426000003c0a262501400e80259000351180b00e8030ba440c0028440500708108054041c02030800c00020721400b84201244070a4a282c82ca54803800c0c10b40 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 879439046 1250 879437796 879437803
    0x20090609130f06050105090d12030e0a0305070506070507021c051e0a060605100c021e040c021f110a08070c05100e0616092d0e07110f030915090411070302 68
    0x100202c2c1048801c2c401f090090700e440c00d43e01540f81d0400800307400703d589281c1c120054500f1803242d010703070702850742040d08043d008000b0701316442c880e00999605944407a0200e466000c3c0d110065800781550582c4801884084203030400306028400b91001c1c0c08500e60181c010700047c41440801d41d008002c988103010291080c10040c0c0f404442802c01036404071401881d0022295002c1d00c29020400c3d28820100b6181c0d800900c158050010b005010108102035141c601000c200c403444c1c44d04140c1100d00d40c580703204031440c0b000c0000c81503041507049141220420401404801484040d06150703010603030130082040c00c103050940c040b485c03030301014080d810000094502d52101e58030424140200343c10143c0c1c041650800c17401140030800d540c6901c0c00c5000418100c1441402070f4401188070859003d541348074100c952a440110f18521482d00d660703514502e0044041d4000307001d000907a1808040c0b0242c0c105401b422070f030900450f2000501100c40054107101900340c009000d408254050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 879440296 1250 879439046 879439049
    0x80d0804020a150509030f06010e10030803040b070c02030703150b0901050a1a0d020a230a0905091b0f090114040e010909030c050f0a0303060920090609130f06 70
    0x24a011695030906501168428240d4040c220320010701c64030100c1010300c65004d603182e0031030040440d1032900c2003a03442a1034040030702580e469117000400041e0084070140c002c0c400c503075005400b40d1850b955612001c0030403001034411000c00070400701a20159400b000414003850240840030040000810f113034089482550340140180912030040047e650fa4036807070011039522850a08155100c1e200c0422140f19464402d143c0c00d10200301d8403c0942d0005000c200c441c00204c03007403402070714103920404501907140d201c0005a514401401542000c16906e504802c5100f03e0587e07408841c1c811900c103401c03500c3c4813402c0103004221058190707171001002943c00609400d240c50181840302c600f421b03a4050140160b4181c4828030001054404c800d1825010f421030300b9a0000c1c1020050140c8905102070168001390a0190100d0b00c10f0980c030a040001c00180e55824405a034034440d41c2182c0c00c2045e003264000e40a220f410500e865145c82581c1071240c8020001d122580e50324142c044840d43d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 879441546 1250 879440296 879440323
    0x3060415051807021b0d0b0c1b0d080705070203100c02030d0236060d1503020d03020a02101805010e03010905010507110721151b05070209090609060c07080d110408 72
    0x1205648254551620400746c4a4104a07414020750368200609401d02c601ca41546441d40c5002441031070000203e80b000806945903142c50040d21051800c4855010750600654103030000c03a0800d00000d420751060300c030040180140d900b0a031050000310100c2e008a0350394901074401540d4602211070703c42c01e41c0f0ba03140c0c50088141ea00d809400111b4210f000f6654003401442c2d49111074080c0700c00c3e100d0030000845c5d0062185000c2901813030000e459125001040707001c2c0b06825100f0b54003d0140480c040d610b01a1a01c041903036180000442d40361821380411505550b884600300c000c1a03084c0201c51181da4107885610040850300203092410681d940125098114075200d040c0502c8621207541c0001d40110480301e0103180f00f580790300202106c50400304209012a90502030035040401707094514000c88078289241d8641c42e0303443d15450201d80414a681103900014440d0042401030103070280101c2849080c130a0a0300007104490842442d013094150105003002619801c110f0009c00600c2c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 879442796 1250 879441546 879441583
    0x5160905010f080a17071b210b0601051c05100315020705030901050d14090601061403090c0409030c1e060509010b0a06031a15070b0106140306041505180702 69
    0x1a014030700e521382a458000034011174a4100315844031100034207841419812030340c03829810115003a411015030251180103d280e40103c880425040901e60350441c890301b210342401c050b82e03032078011074059100c0018803115040011000c0c080c507000e4480c0074803882d043c80540001c1411814614084420694034085003130041060400150f4084141c0d449280700f804c0282d110003000c511000504014804900034004401c01c02031290300c0015103904803505511000151a4008141d410354802140c241d0800d6100d003094070098240b50303120680c1c40c1d0080c548265040700c03c1c1d940103105420786c0c0701d140e00000d06010030028005980314454102070707402d00070810050044041141032405104010070305907601b00310742403e04540241c01401e01c00429441a2441030700801d426a00003030019600c44003010000301d011170217800300c10112a020500b60b81075035180c004100140150345055488680d80e03240c0060306031205107090302c40b8120190b529245d4608048001c2c900386541c41204000034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 879444046 1250 879442796 879442799
    0x2040e0d0c021e0303070c2306040e130804030f1a15090403110f100609020301230619120b0102010606052a030f0d0e01090c09150305160905010f 64
    0x907001103003403021990660b00400c40c8a18111216070600b4450407060301070000244407010002584004020340744462450000b02800507450400c007000743d4181c940186041105100c95854aa88594000010603ca80e1a05c406982d460150b4000d40d20454400e0104458801008040c04105081c100c03040c542411078504000c02c40213015046c00094000c5090501142c10302d480340c50410000c00250044130a0301c1004400b040d42d0704000603c40c1c84152401c0d80c0440c00b8646402201d04850a64101c2e1003889450200255000491240c844d40070707004026006e500782c91004d40c0d031081d125603200c601d0146001a89001515840120740d411a45850805c0c00030740c2d041803d40301f050703025083c4005c10f407407a0203080f181c6c01052a00f0002620000c145851151425401082e070302d502108181318101e22902a10300341c541100d401403200c00d0b0301c001841722016990004000e04110704801840f96626190f550a014042c00c00d11080e1010340018004418070b80605401090103c8002407043d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 879445296 1250 879444046 879444073
    0x7030b06190e04053306030601080606060c011b0f030e2a06070c0b1b0c060304020d08121015110a0210140d0f0e0d200114011202040e 59
    0x3801500603a003605102d0000300d0203000c82008441c0302071000d6011075490451200a00310112042d1010b1140355485000080540c1070114000c0e04a451000041081d61110800c0206a400ca10341c442e00c5503503140025944c0d9100d004804445942c2c5031500c001135903c010f001015903d400b2000501517014101c00d4089040030500d1140180d0042450003c40943c000000c003940b048840151a0340040e80c0041648001c1800900040a2a6074110500b103004010341351101d40403154264007a4050000038054207088140c2e0b00500e1040315000d140100c1c61040e01030103441a03071801c0980200340414482061065907080b00d04030385042608520b20030880a0340c3e46c035501c001c002e010380c0c01807445103034441c0102802ca100c42003648a1740d4030342484920000c010710b022041e14a2107410032806c3d281101001c20a001002c07299502c01803620300d6010308410003442a0340e018000d40d6201c0031100a84442c8111034046e20200c2c20b00580e4070f02900400c81919120b0154039603c0d0420014940710 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 879446546 1250 879445296 879445339
    0x51e1203100e0903070b0a111303060b040e0d0906080709150e03010c02031201031b0305030415030605040c12090809041e0506030601050a090b040f111b031911010902100207030b06 79
    0x2007c071004c0410044107640200017a401407918030294506c2041011042221a1b001550710b01030550f01080f8100503100c1661b500e02c00e1610355000f14100a5062190710321440c01d2507403094503400c00c40c40c0c0c0f640e5804071700300541c001c4c007000d80011104821180c0034a03003030045450101003440218100f00800030007408100e01844002d20f0140e40012040c0d55108843c0240000e6800a051301e4440e03a582140380c00b00d0814204041c00280303020400301d02441d0a00c617440c612009555005840d9891003140802445036142c140c81603d0203110611460781d4900406c10f540d90396480d2003074400030760441078050303d102900b41c40c80794200d0001445191941d40d142c070704585142602040c040e007007001203002050080301d2000e0440c1020701c61480500c007031008203003410241880101e420141d0240d15201c0c040e50034500b180711000000c130100b09100c0d040c1c110412051a000288412181d0b000541320980a00700c1d80c0540c00042c07013002440140d40340c4983c00141a11a54000c83c05004a00e05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 879447796 1250 879446546 879446551
    0xc040b03090a0503030c07150203010f030f14250e01060f0f0302040b12040b10050f04090c1e0e091b0103020a0e210106060c051e1203100e0903070b 65
    0x141100040300090800300104003403010541c0250513259070742007110700c1540030b0b4840300c0169960410240c8854021019100b204d04a54000d4210325200d8110b6407000e8074085e0100c01915203c1583d80d1000003c2c005001100b01c02986038041050403011282819501d00307280d01030b100004888004000440e00b0140340c61301d2414501e007002c42d0500003c4150020301407500032109229002c0b80005450705001a40c0e409680903080d00c09255580b02c22400101186d802043c0d00940000d08000c22070920781c01000d2030078410001110190780b10300300512281d030002c151000100030284d080004d040c902c16455000311889000c1c11041a20349800100f10802c1091b060400d5400204444018401c4044040580000b404480408110040001480304469550308203528010340010350768004d1464100c542da000c0090f144c9206c0c80303800e200b18851841041da142d800364800a110403c1030700e00442c032031106806080c07600341c1000701d2400c076450b00400281076a8010005a0003141c5070082c1a913 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 879449046 1250 879447796 879447809
    0x60a0507030e01200a02120f0a030b0d0512031005183102061c0e150601090f03080a0c05060c03040b01050a060c260409061d1003030309020402070c0e0f010803030c04 73
    0x5d680340c1c55640c04034549032210300e106401c40400304400744065207000c000c241000940d07505004001c10740041212204040100400981c0020f860350b60441e1001e0107181d1040051035002e00044c4e0721408103044c0380c20561242e103852011420440211a00880038541403032018080704004400c50035001d40000812010740303d0b001c0403800043c0300140c5030b07101594204020080c025042c03240b10150340c1c0c40065800c03501d49504400003541e0795100e11100790460b0011052040d0880c40d5450f01a22584405901002c00c00d000c4c00d00c1000c0381041048600130b403a4101495a01d20301400c00c10340115060b0000d600c40d10041800b080082c0e4402d000c2e0708a181c0100004c880004c103119890142c02aa9841901e03c2c100030038001401405540a6011204000888020711400e2000d14000786011210700901030165030090021038460343c015440340d84080c000500d49003c03130301c2701104200e99034450300000c110383d01049182c0480004d003a00401e6003100a5056080003589080c9500031401b440c03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 879450296 1250 879449046 879449111
    0x20603190207061d07140f06070203010608060408040e0702070b0d020a020106081c020f0616080a02090a0308071509050723060301030c0608070f020d0f030b03060a0507030e01 77
    0x203940040e4681c12a181940d00900030071500c4202d181d00c103404601d1144001c1e040c000c01c0e2000035408514410a403030001c00800c4004642003d00810503540c02100c4d0903038040d9a41d400c0032461100402c0030754021809a48190b882d076140800410200000508032021500408010004103a4000a540c1e010003021009601d41c00c0500080b40103007800e61209550784521001d450010f0788503540d0a1500305a907090310a040b040c2e02c1400d9480d0b00984800301408402407882c8403c0303100b8003c5030b070007075001c9001600e01030f0b400c4e00181407007074150016150410300040312001c104000d20b000346040c240940600003032045850300c079294045485407120001200e2502c03000c0701c442d054440d0554500a140740d0326540c590034418050714280c01074601142e018404a10142e02410800b0b5007500c0e954010300d4010140d000c00c598601c080b662001c24540ca070f4440401c4d41d581488814412011130b4000105450030080040c1650a0302452043c240d14003004409803100151f5204075005001480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 879451546 1250 879450296 879450331
    0x402030c100e10030e03190210050903090405062e0509120303010609080a050d030c11030a0f020d05070b180a0206031003020108011a0a0c0201090911120112020603 72
    0x1080c1458109542540d1081c01c03801c401a1841d040703407a64400342416aa24034a482c282c0000b030301266012401d40440d64028040c108042c12044020100d001c4548180c50b50b400c14804660300303858040c0e903ca5840e0f04082194003080c03c15106483c0d1040044070300105143c40030b000c102c00030b08844d54100f441c0401001d480d400f5405441210388415000c2e195852a0610361841500e070380003806004c000070302c3d4840c0040e44500019600b0f4126402074094648030440e450190001e000d0340d90490280804521400c07001142440640403103103460700e408108000e4245d0003810800c54506401c1030200502c07801000ca82c0d01030905600912940d80800380c110071010362450480703010b10082d0320980020030030903080006c28042d81240d1007170300c03402000e076280c0450021b030010f20052007450b80000e104601c4020300c144010150b190060608a40040e11a0601c20aa403089440b4441c12540002d9003000241020301141c014030131301c040d0001003009a4001009403002420111180c0c04002c072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 879452796 1250 879451546 879451549
    0x12030f0403110c031e062d040f0c08031e0a020d08100f030c08010509011b2303013021030222081b031e010e030a020a1b0605120402 58
    0x804034486800800b00c42e580000217071140c1c42e280040c02030b96880d008201c0421203a1901070021000c20b24041031032002d1038481e0110f5105010018016141e02440d5084200403070307503800f005400340182101a50b038403003020000d4204d00641175410001c484007084400c880f541e011070b100e0341e00006850041e44940307034000c51003000c200b16000600208460f00c000403c022062001d5021148440c009108640d902c80c0e00c0e43c222508003c010341c0e0414481e00600c0e5251203903030341c0d02c164040031403120050740302540c42040302d8209030040d1a45400c60400100c0100c05103405514000a5110001c0b29030a15640c42c10041410800340310341044a011113107807c0c1c080c0d01650020202006800080d00c044403140c660b000480c03040c140d45000e1504610807070800b40c000d4001d0110090010310714050600b001140c03056918503046800d55907803000c0c50341140140018509100aa4000c20440d0054103182c03400140541c0c3c1d03215560520780c810016a40c010059446c83da45503452900c41d5030b980e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 879454046 1250 879452796 879452803
    0x2120319021b1c020c010e0405041a0916080303010f0303050a20010b090a05090a031b081b1510090c0e03060f0708100302060d09030201020c0d08040512030f040311 72
    0x151142d00b84003102003000326014006030704041c01c40e4480c1c03001018070500d0800d98942100450090014244100005041c24141c2046030828403d20310341500c0b0f44215020709020303506441006198004c1241c3c026614100100f541c042c008000146d455549084425002d8014611004042c45070101c3c0c80140f41b400390404828003001c803202d81c10280e81c1d8004082c024410740c00c1261040003901c002c55a007145501c20a44501c044e640101100162a00d05981c082c01446801c0ca002c60805140c00003e41c0510260111064a00c5c5141c01c480201c50050300705800185541560342100040080868030400e4000840b0a0a280090200c02a0038115000c0090b15010758252094605200d5000b12a0a913103108003180d0340c901c503050303d0300840351809160510000c0c4d4060382c24003003007400741c02d0355020103c0d4520034000140350080350305a00e421300b440c02c1030b44008501100108403d0150601045404043d40a0618990b140c4072450b00001e40c0701910207420002e586409603e40d26080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 879455296 1250 879454046 879454057
    0xb0609040e0f070807030c30020406180609050703020a0903030806010c0c03030807080105010e06070b19050c030414073506010b0a02011a030303040215040b12040b070212031902 78
    0x20403d40b01c0032034840d90b180703544800320b1104803049440c1950010b03101c081c844a00c0248501d401c91841220455240c04035a503800107401e0340d0169031500002008007480050242d0b030140e1300c1010070300a1505446c0021603200074602401d06004024100200b0b80c00320703d1409480e450700706a0419150703a80102c42505205c0e0000b440340c42d0402001c0103250700304030b01607c204455628100c1d1680c81d031004545500c1c421000c070340c0010b03090000d140064603144219900040581d1942e59801104030031600b51340080e1180d240f082400024001800f4294a1002c441c00c4000020b10310f1030f1401d02d03032182d20255140481c40b0300704e5020303000c5c010b0960f0607580400e81c44030f2800c44003956101c80c080340c4141d2001002c18095031078558241034014040022840c0090014043d5065039510b409210b40c4010b1303101e610304924420403002c10110b44034405000901c1c0d0480b49030030306190034540280c0a85003c5c0c40d036802d40d070003280e1240e100030b60303407045030307805084108480c05103c45205242c000e800b90 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 879456546 1250 879455296 879455323
    0x1611091008010b010903200d050a08090a09020f120604020c07080601050f1509010315030b0f22051209031e030a091527080313180b0609040e 62
    0x5050520051415404180c4155000d2078003c00045212000550b070703c001c3c2d1310004200090108035041d0701c07094a014403100e1903020300000b1030710b02c0c60b55525040c00c09240c0d04854001c00032644643c6410245083c2c2e0141c03c0c060021850000724004000d2580564400c0d40100d00e8001c0c005004d60f103c0d40c041c0c640501c1c80078103c03905543c40b126029140c000c240500d600800310340c0da042c0403524062000c031405c800841801440d0103043e40044021704503607032030400701c0b842784000080010650804188a0765501b115814a400c01c0c4201680c0c040c8260084569010714942c1100499004555140c0b484444a45680c1d00c4450701e02003800c0c0407251589100300c6406042c603440c2c6030004802001c009096642e20640140c0b210500744450800441d03250000724045242d1000346a0680c01560301e8201e240e507140f81540c0e490030383c1c1c656030041e4000402601001010055001800d00a00c0d40326542030302442024444004a845402650419842141c072a4040c0c001c005040c0202c0300140e10 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 879457796 1250 879456546 879456559
    0x5060c10020f04050d0f03112a0d0b0702070e0105040b01021b130f0617060f0414120412120504120b0411061b0c1e240d0903120506061611 61
    0x454106001b003801450819000f2a00b40428110701c0e034004a1176140d07000034184221070001e21a20f159502c0c02060011640081d050000c0d180416050200b542c0700f043d8540c01020b005040481054280906070301130ba000d1400d00c0780543c4540c1c0c02050500341044044801400d40418400054108500000d2a03550620b0714800320000240740d0429001c3c0c4001c400c458121440b400c41d0030b0ba4070601140c08100074031034000401d0009071200d00982d800d50300038080300c0603603170000d28101d0581d0250f403140010004018122080241190910307a007035030b1608040d81807078500803250417107403d0180010000d40001740014200f00449042107404200604980d85800918580c0d1007240042c00042d40c1c1489800c0c590200d9141c00700303080c01e9000120080700d243c42c2c10002404200e1703410032041c43c081603000c1e1002c201c1820318401b4000040304c0860100b00c0070340340d041c0600359002006146503030034100070800000b519400c048a141010031014500c0c5600702d401d0810b60000f00c0418564031a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 879459046 1250 879457796 879457819
    0x3010603080408251d040f020303031e1b0a0c140604120815060a0509030c1807121404110d0b0a0f0f02030708180a0206030108031305060c10020f0405 66
    0x10a2015020060303040c40080da0103600d01500180c8a20500c43c0d420344072410a17140000002100f50020302c9442e0500380184980d00090441c0c00c11540e2800a01c0c000c1d20021901c4500c00d030f850740098105810f40c1c94584900201340e040c2c4203040d103000c00d0000280c0c2c04003c0102d1241c585c400b0300c00100070780e4100c1c14540b8140e800d11700203104010006e07414502180c40161840c00e1909902c00c01003055180c41315855050702e5581043c0e402e15450300074686070b8000707511030444000041e50502d80d521080c0c0362003140a08900c40b01e030000303d600b0307240c004403a4003440f494600300e42254009000c0443e11002c000000c1c01039035041b00060a058042050150744001a001080342c07800c01141400040e003441c1801049010844091000607006008a80c07031000300c410700142c05900905031240300000e600825110703402a0720641c01503200140d41d0a8902d0707180403c401030402200c426150170b12115920390307a80704403850846c1c040e6001404182d0400e0807402c40f8028100600502c5908 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 879460296 1250 879459046 879459059
    0x22020315040b060c07050108190f270c050d050f1608240f0406180503031e010803070818100e030105070f090b0c01060b0f0c01060803090915030106030804 68
    0x14080c06040368051801e10804050503d030007400d48040c01c0b44040181101071030100111010301000d040715403000c41c1c81c2c030105001d24260064801c501480c031400301e4007290b203030031180714449820519070010342d420311803000081844440700100e031000c072000c94984069040003420030f461b0b070422400e507128a403202941801d1020b0f01d0011101c0c40c5003903440401d084101440c0f030080915034403611141101c001240071040100043e00a8003c00d4002418024000129044003035244103540715070021007004412804400c01207660410440800e2040d45072000850fa00d01440c080145490030110301e880449c03c01d0810300c032000301c0003455030104150001018080303200300c00505009509040c0043d00803400707540180c5887d8020364500940c01d00d401035008a81d009034416a041e9500ca0f03800190a0a0440c041c0c201d1100e00900c055031140300c00c040d42d0031105290f00801c4660802d124880e280e980b5a03c1c0307940d01490f084411540508510002070042c44075810081161001040200f00c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 879461546 1250 879460296 879460321
    0x13051b1e0f160c030c060f2c120c15070c12030e030d080106110c1f05091e19080a0209130510020a120527160e0411040515220203 57
    0x450b03000e0614503261541b940030450b0001501d52807800420346201c0f035401d104016030241c0311803c1c60f4811720078103206664000b5690349010054031809a011400030460f81ca0115140d01e090b10144000d00d107000305980c0c48010028a9101d007602c041c3d400c240d104145801180c1181d4002030041c1075462070004150050584102800f802001a07032008210200803400074003501a50342c02000d113929103040075420b120311025528083c0412009000072021034440803002c22060b103800755440001d149510031701c500d0000742420048001f040d504100040000031034070034581601900c010055940742140c41c02c18040c4404020818454415084418040c581c080c006105582e81c81e01403001c03031004400d007505d4040d10203050406503112840040041c82d0342c04404045030300203842c070b101e405d0354403205024465448901c0b45140a07080000304200c82d80c1140e05500704541c104660700704100c0a00420122000c114010ba80707000076a508500c1040c1205001442582c09550741e20b441e8000c48070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 879462796 1250 879461546 879461549
    0x20702060f120708060f09040b07110105010923010311040207080c06070e330a140a03140c0304081606061a0c07150203030a050a0b13051b1e0f160c 65
    0x41c02a102241c0130789024003d485d40318100400344111508c075601e0710307042d102000e04440c042c45414011141d02020a025050081480c0c0034005200302c80030210391030f20007078201440d00c404c0c0408018000105540400c44090300140e40068451302945004942441061041141849464104603a9940c0130001e185d10280075100c0e916882a17442c402250800850000810080940205000752200b90045d10381c145080c50140d035801c00c51008400158080007162000a45501c0804010440000c00319000ba500c03004440c40c0d8646600c901a0bd03029409180d0341c245615829801070190940040c405440e507299040780b980c45c00320051140794080d0040119a00481100180fa140c0100190f21040e1444e005103140d50348000c18a4010040201000507595031402101e02076260704a004245e10181400000c0034281081c2000301c00400360a45a40e1090403c003100c0340001000004860005500d20f42d07494080c2c8040d106050f020300000641d030b4225456450041c011601c1d002c80 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 879464046 1250 879462796 879462811
    0x21e07150b0f060702010e04060e07051b060112030507031701061115130201080919080307021b0a0b0a140f0307140a1d01110a1101031505090703020702060f12 70
    0x60700011000b070048044002400303540c049018810b810240d4000e03080c810341101c0c01800061400e484500808040030305a8a10000400102c0c1144200502c6208981150034980050045601d4840c012035403100340c000c0102003107008038540c03040502408000b0312490b403440c2291002e40c0c440ba401080c08007007200d000068481ea8250813081c403030085105015520003849907054016540043d038488002524000c030781e200d19680101d07500030031403c0320100b41c0b0a0f40d00c0d03035907410400c90007460984000d03e52a02c0c000030001640f01c42d514444120202c42c0d003041c0d0962141c1115009940000a41c180380e0030b064000141c5045181c0c440004520031035464860030700720b040101e4010850301441c2d01e214081100c2203540b42d4880480d88a001103000145402c50301b440d200f0701c06034100000803400700c80ca96000c003c20021580c1500580c000d090b404040303042400c0c5071030300242d043e01016201c40c0515900044060964076150b048036200c800c655a0705944642540909044260441c0c280 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 879465296 1250 879464046 879464051
    0xf120607021c080f060120030a1d01020f060402040e031b16060503040804030f0f0501020d0c1d01050d0b0a1e0303030f0e030304170d09050703140718021e0715 70
    0x490054050740f00140100701c5010181c0c559999440150348420424190a100950310000f05146200402c02002000d0059890304000f0742e03100c505940c03001c00b9400c0345040d0740080003010715940c000a0082d074002d404403808204c40c0b0803441d101e4151311514038040030090043d480148019000190500902c140301529100c0c956a100704079111301054800500c400d004020801c0840e41600c040c03004107014a94104444025944441c00c981c031826698480c540c031516140c055917000b030b5030542903c082c8007400c1144c40000b03000074550f1043e1174410141039950070030007015884184411002d000d050492001d10345402e0050342c0030303200c14427048000904015030807144200900131241d1a19046000714191384940c0d845402d010501c602038044202c040c445610700c4051400350b008414080d20182110b2411070404000b0b00710606c18000e07450344400700030000c400d0040c02805162901c1200140c4803000598a41c20f50b2580c1c1040c0040031201040441c01d0158000d04075104201c540401c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 879466546 1250 879465296 879465343
    0x51303050312090304290f0417010e0c060d051f0806160c0f0b060d0209010f030b010b09010f200604060227090712061a070302060a090b060f12060702 66
    0x50703913244107034000c8859045204201603a0100310b401e00d1801d070006840c0b468140320070f49038540c0450304258800c04040c0c021104075100d001c3c0030700c00d046800742010043e001010b000000308440c2d100300c040e0020566960310002d100b80250a80840c40c69054500c9021240d681352541d03aa501416a4141c00c42c480c01ca100304001130082580005a5500000c06041c048154840c0c11003100300404898000c100c10001000594495181e40d01030b29041081c1b41c055400c2d4102041c2042c41600260b07448481040850800c0c1e030810300065501945107051a040170715540c103e9400c40c03a102c0e203a0b07024460803052004008068018001020405995166150000c0030700042030300c640541540140e082c00204038294812014142e180180c00e401180c829625030340c3d8200349504001c000d41003c000f149281c105036051201d140c0011001809101100054488186114000d8034240c801c3c113280d181480b154603602281e5603d082124151101868025801f0b51074a0441c1c000c1010050520030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 879467796 1250 879466546 879466561
    0xb070c080c03070e25021e1b0d050a0b07030606030b0d020a140303041d060108010e010807050d0f060c170c1c02070303110a0f080604051e07051303050312 68
    0xc07070308100c1a004004000103440c00b080040c01c0070380500f880038503a072100084039075400350401c041c86088160340104603038a03c81c0d01403c408681000181e0254005294116044020380402c1c55040403c40b0505001401450010f19040c0e9080004101c0780c2d000b41000036454042c0d101508541c1c01d42c83c00d10560900f182040614010f05a00030752007c01f101003030190780c0b12485503520705100038045a1600f5100c03e00f100400c1c501154845000c4106001c001d110350380440e05900520450080d0b6010b541042d0905440e042e00f13004990145210381c020009001140070540c4205030801000c0040381c3c1c501d040100340c880d0340c00490312148444400b1030b40e203060520840d00a01c2c44248040b4100e19100307000c002a41c40784100345c080640b243d846c40380403541180180088110313a102c007521420036110262810800400305482030380380004103d07202001440e0325200194801c01a682580c1d01102910a406442d035541070061150078088204000080102090800d10000c051241d45004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 879469046 1250 879467796 879467803
    0x507110406121b050d06020d0c0e060a0507050705042a0f02210d02270103020a090b0a090e01060c050c03011a130905030a030f0b0102120307050714070b070c08 70
    0x11502d514205880850400700d80c4864029600003141055082c1d000d58900024580500c1c00764252189a030000b49481054403920684511000750704005501d6178039200042d0352030052111000900c48000f820300304000c818440040504401081048107000710041041c0740b0382103030324841207440c5507101c0707a4109021780404445260154010500380e50f04056160601e1003070a00d00755000000d0110091018542c009807815800300c03004520b000c40940101d24420640c0482541450720400080400c3c80c1e20200f5034040d60203d012180d030324a5031520413520300c070641e8000c46098110701c002040700e80d8080a542c04850240f000ca4400c04525002c041c02c07540344448411914000203174030001802e00043c003e1342001203c80c0001d83c1c0c071407515a942550300c80c0300ca800c00a40d0754065110071031240d01c9001c0c1426820320007000b65023140e421a401e0361201402c000244907000c244002008003444484124903402d006441d1115a290607030300060b0402d010131141c005071620013281281002 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 879470296 1250 879469046 879469049
    0x1505070303020d0f481e020102031617150303070215030703110c03120c120a0507091203140c011d1b120303061e0306100504060609060815011701060507110406 70
    0x18125020140e00300d070100c043c010404400070041c04200c01b19440007201c4140b0086541d104c0750000b50340c9203000328201c210700c02042060b50510170491104502e074200d10803c59400001c0100c1c4a01c2e1404c0c010001e442e40c002e0040007544000b860a41c0308044a5900c060b6000c0d07542610300344a0582041100c4006000d00e1b480c14041d0750060004824130f9a01d5000d0a0300255203c041524209400031400040241142c514440031348460500061036030110f02c1c030005104025003d404a0302c90341e0000c01503041c0c1207e004c20044007242c5009080802c0d4450303030340e1118510181a061481880e0a9121203c03c11999044c00c402480c540395402c043c1c00250000d403420340590b1551741d5440401007801148409940342e59420b030b640200b203403010008240924028050700300002c5c546402c22081e680f46401031003c02400340d00c104502500482e01603013180c90307044c02100c141044070049030480c10000301320351240b031694000100c4c1a002030041004601a1405004d441d00750001d00044d80e105 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 879471546 1250 879470296 879470381
    0x90503190e031f02090103061a09100e090406050405070b04031b080d020a06051504020f0c060702030a17091203010609030318050d030c0f0215090103050109061505070303020d0f 78
    0x750200d281260044d40c01058004014140007680300d4440040380c400c003804607000394020384002195280c0d4540b10004084225a03803401801c00c2c2420b0000c1044414058030003040381d52110088ad04211080c4100030240c80104030b030f15120342e681e040000342e80e0020901d90310074560307078040840c2910700800e113140000c4458005103440c1d0a50ba490f5801403400a082c01410b44230241201410f50703840c00145207442c841f1a0701a01c0d9984d8480e120309020020f48440290f5104000e039a070066000381c0d588144456005004900d43e80e2000c4e07403820452082c4005c074580c400040003245854014034a40152406981e51820803980d00840d000c100c251401410745c8280f41044400c002846505149003403445141841500c0c5800e6000c201c2c01000e60042d141c0542c404200030055503814441c1c1401080903070420321281d0f180500f41d038150004030400750100b140001d5001d0616000ea0100c504011b0303c19010400e00342025401c2000f070202c05680741501a810503070740540700c0200c0541e0b400070807 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 879472796 1250 879471546 879471583
    0xc010617150708070e030312090c01030e1002070f0f060617070f051516051b030a02060f030705070f05070e0a0b011e021f0e0105010f03050606090a090503190e03 71
    0xb2611003d803407040700240403208001c4c4941c440301c0b003510180081e24070342c440e105445e022810104074503824000302160311070405150400f41c0e010341d000014802d15070b0200e501d00690f03d08450034070301c000d89085400a070100301036100c540e04000181d4881422205464069600300742040283c0740c40713801520814168103c540d000703200320314044804004c00f1040a1030ba501d40440210b00390001d40c1e132860240e03159080314401404200301840400c064a01c110f011341940c416a9000501038000d40042818650f00400000c82041c0110206c41c4d40c00d801ca8428040400c1501d00309179500b01501420382070324041801708488403460702415002007416140e14414141080e001038804000e0500360b0f045202c1da458035400c41543c00360503c0f01040408004c900744410050306030a480f0180e0041611441e0365100b000400c0000c0340141c0c02034401c5900c1c03100c41d201c0304d0403580548644500038006020001c0d11481069404070b5007003046002e80c0360b069001c0c0e8140101501c0e00c003082d01c1e80040c0c24 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 879474046 1250 879472796 879472801
    0x61302190825080c0c15011e08070b090f030a080a0212030618060a0f0b072a18091202010903090906122406080307061103100b0304060608030c01061715 67
    0x5002d070000c9603100304034000e6242031121980380c00d0715007841b1102c2c08007070440d0b03c1c00610051900b0b007603131468000c1c02002c0ca00001e1505028990341e41c481d20a142080c140840c40071b01c0c0d686c4112600e40c605200030205c0340d80e825103003810b01c50307036100c070b440400540709842c5184183c04802c01030f40d204030b00c010403115041c507529079021031401c1c00401c486c0c0e005542210110340a1803c40103400500710b84120a0344038003091401d081445011002c90401d0751426a0480c0c50704254210700041e00e00e0810324000c0310610b01d01d450054041a0300c0245141080307100a0109981503001040b2309020b680c400d8a00f599a840e072004030381c1c5500540c0000e80300c40303803654046407141030340102c1800c0c01003040c001d410001031040c1c11039119400080207600009800028400d1b90b00450039014400c012192030360070300e03005201c1081298031a84000040120001d007e1100c2030384084003c0c518001600e070b075000b030050070b98002c0c2418000e2480b50803043e42c02001d6501c000803c2002032170341841c0e1007910b4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 879475296 1250 879474046 879474121
    0x601061205040c12020d05012f0c03090d0309050d030e180906011202031501030c0501080a050f04060b130c18090204080c190b1603030b1c0b0613021908 67
    0x148014003069800c02c001549040001d07000b407084480e0049e1600c408070400b001410400c40714020040030498001c01400f0307035540303d200441240e90f07400e8115200039041c09a0b207000d4130800300c039610460740301c000452608185604622104060441110201180b03410551000002d1005075030300711042d480480148022604d50740c50101c6980003e04a450303526050300d0b80c0000c004260400c13110910104000c00843d60001640750f00400426014441860701c10038110682100400180c0340c04e441d51511380300d9460318074620550010303c0c50284012808002c3c06007400316005054241d04413800d90000341e0007128400c0e0f905a0701c0721805403d03010f40351410030000c2c1072410010b9003145a4814002284500c480040c0000c8148914400300076010341009400c03a180d016425025104201410020241140d106811039510466062282c1c80c1c48002c03e0700d404110b0300002030740c4d00c000b0b507403010118102c6140b0f00034425665020001d544900c10740203840310b02200160520289910303001e80 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 879476546 1250 879475296 879475319
    0xf010204050f3106030204020c070e0903071a1b12180d0c061a030607020d0e010c0519060b030a03020f0609030405180a0b1503160216032301020a020601061205040c 72
    0x50f0240020104205031a40c000600b282d11051810905501c151003c1000c96090906198020790000146080c045d4545420807002000c4030f00300280c030401400180764804d90b07800305a02108070303d641a01d8201042030046440c900307456040601d40c4c80e40103a104580c0004000008031401d90f640c100101c0c9a60307880e00a80102114000100c00c0100c5610345500c08004e40ca1182c480f0380d0051188940c08040035182d0707182081c1c070381e04204420200b440802c2c80045d0f80039a0814014414040b1142810320a00815171130015650601600540900b4541c1c001000c1c06040710803410340d840c5031107511625a0341e108612803603810072508a26280700c80f00302507049510202a1b41c1c0800e015100e440001e00c0400d11101c454480107000c0103109111001b403524480e400384500041074482d44452003c40d851640d4807004012031040310400030200103021301c1610301443e0724025502c03511400b070044c0d1502424040c1d14001341049070582d50310201ca00510303028035042070030043c4036030030f110f080e00e038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 879477796 1250 879476546 879476629
    0x6070807060c21050c030423121b0601080d180503060703020d050702010603031b0512030c030103141212070203120103080c2a0108060d050f010204050f 67
    0x1400201030103640045030890007114116052550b91801800b1400e0510050041d41c0f0040c0ba10039281c00c04000041103584200c03038109810680d008100c80005000211078049081110f407140140c08a5440481448018214034a02a198695005049a1804ea40348400d00c40d200146c1c3c805500008145e000713140b207800440500403a1400d150b10358000c03038a0004181c80c500c00007540001d50700c4d81440284140c50f0480480c3c40248119032550302c00810200061703595900c017610382104034003041410040d00241c1445031507115100d24103080c010409820910094840c010b0002b00c04c0d90020010034203905450100030a9030500300f012001405101c0024030540540c881088041d5080b281c9200c4180214400c0c0c95040d40c1e503400300003050070300c08070f031184c0f038a01c4140c070611000d2510b09200c080116002841d280c10f0a980b004005046000c841801030070900500010000541e0107400410542d1010781c4c500c40c1003880c407003d00811002007040c0310b03140f843e07240d9190f00e0680303a12008030707 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 879479046 1250 879477796 879477803
    0xf030507050d1808150402090903040e040609030e0d0b070f090e04120e0a0b030a0c20150105010804081c0605190306060e010522021c0c09050a080c0607 67
    0x2820a4903541d18545050000c00214010540034a1410414110b001081024124280142207400c0c0d103d804031a001d003020b0402031041c00d18100080609808209a0b0010700e100c0010080b6400c05041180c01004c44520035030002d00301c0c0d103e5103064200b0300f0b0b415003640d9120000e100d16513103c0804560559100c0a04000c1146000d4000b0700003040c001000d010780e0081c000003603024903883d0050045202d0800240c06110b8800c41080390100d10300681c1e078000b104280c00320b129036456900b1113480722074040c2800f2464418400202d101c60005950f200e005103254800c4032030741ca44d001512915001c44004102c00010403007400b600980020f000001c581c101000b00c0e0594a550006482c3c00ca82070300492290941c0382c04100340a40c60082400030320250301d4494880d4100400314903030644180590040404030765480708080d489030b049a04040c02c000c02e41d0002c10205210340c000c2c08554914900282d8170220114042ca040d54006086510b108010021080c0e00418418181c10040054 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 879480296 1250 879479046 879479057
    0x2d0308090a06050f09010f05010b07020f04060f0e0a0c17060613080601080a2001050f07030e0607060b0f01170115090506030c0325300e030405011209020a030f03 71
    0xd80081d001d0702425016015134400c41001e454251101403c6500101d4405112802c0c4401002042c500b0b8045030101501515100030900eaa100440d002c3c0c03440764461590300600d003400003040840307061b41d54080c024440c000d2140082c0000b0032076021000e608840307a9403c2c440c0206402c0d00d4203000070944100c2c4462044a816078410415080c032900740d008100315080401220100540280c51403820361003920030000010500d80020058011061043c03800000012401c090501850011444a2009016554518a501c0e148010303010100740140609800d0190204940c0141a0710b44040141072034000140e1a159a038864584d0707540b00301c0207210f0112030220b0a6183c20004502c60b2071901441551780c28204941464111042d0107440325000010410401a03170268141d0725012000886509c03900e208141360744110443e065a0b148145080e100004056000c0b01070003c0760400d80360400f1959a9207070440c150b17841000000e522165420003440010310201c0010442e90192a00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 879481546 1250 879480296 879480313
    0x7140d140d031a090906010603240602010f050a1e0513080d0b090105061908071b0f03020d0c020d020405041a0109143402120f072d030809 61
    0x800e0038040d181e41420000307600d4540b580080e1240c02c03041c221003401a54441010b1800400c0a40c8992060140000705504c5d41c4d10b11030207140c403c6008000c4041e42010036041d0303a80d2600603000b459000e4071070140c58103060000d0702d0706482c1e21850161364120908183c80b4078908090318010400244603480c0e11054aa0100200780380d640a0404c80101040000c1c3d085d0b121810003890400583c420b500c50385c0e0410034013008249081ca030385c040080f203040030b8030f0a8858400540d065002c02a000c482444a109003400340050f000050b4500c0d03010f0b4003030f13407202440342908540716403410343c01a411200c00d201d208018102a4080f59115000d1580c40410f00c002d0010725041820031390060740800d88503003804103800720a1114641184a40d80c0f07041615800805c0801070320014024401180400c1d032440141c14020301000c4d2001240a5103540da50100300110030460f081950140d800c21390709401300014400d1900519109000210386910001e0107980c01c441c2417100421032161802016038 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 879482796 1250 879481546 879481583
    0x41103070f0e15030d020d050a0e060d050a0501090513110402090d08040f051909050613051f1a22050306040b060f040b0a06050c03040f090b1207140d 66
    0x40c0c1102400102d01d1110a9007008040050098100100544207800c6900b13041c1c505034000890617400811803e185448200026003903031500090011150010303000200007600c4030403684040e1251a113000100103590700c51010388210781c012241d000e2103015854001021030507814852045090041003d860324a4020202d2105000740d94119608040800c9c1403046259068003400606000c0e14007001c41e4169401a00007252184101c85c41c0c540d80d00080742681d2281d06410810340314290050019050140d2208101c0708094400e41440c100f030000400c0d894000340c0300d1882c40588000590420039503e11119030700c91000d080c814090180352002030355450038803d681c0308900580076070b080e07403409038148034a4200304600c1601c1940390003640b9809580b603c82e01025510645040d50700c3d00c010800b8146113101c0e9400c451031900001c40b001400c401980c006a20a0900b501d00301c14024a044000c1d6680d030792170140c9d011480700d0606084480c2440805810050f000c0e81407010000d41540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 879484046 1250 879482796 879482819
    0x11030f0a11060703151a0d1e1a090705160c140a0e060d12020a02060705011505060418051b0a02160503030405010212030c090312130905070804110307 66
    0x81918010412a8a081d01000c0090010940c040154203040c041062243c1006041403c00d000d800d0410140106824052010750103036020b550810300b0070006540b440c15a04010410b2248251015080c0303000d0803c0d1003181011803880c60307406011a00f0701d031034000742a03134260041c80c0c1d500010713802000c80d0000300b04041c00460040c9007a0b49060522a0500103009a8001d150040c1407016140f0040c02a16100c1c8011400803942240600c6d40345000248201d043c40d030400f501a42c00600420003405200c0194824101906526021104555a2010b01c000c0c0d0155114801c00003d5200b01003519100c113411482d403101a01d002030600d841804120b509a40007078429000590085460195207030b110a0b0400151008030010f50402d031400000070764421020f90860200030005c0085041c0302c4411007078401303c0310003c0584024040300ea041c00129000408007801d4181d44200001c2d80b00b180c1e01c00d4500a03400c03503035103601ca540c0da40ca0f0901d0140c030303580c50250540f2441c100001c0481d00c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 879485296 1250 879484046 879484057
    0x81906021e07210f020d080702010f0e070e06090403090e090a020a030302060a112b0b030d0f031401141c1704050111060106050a14070b0c0706052511030f 68
    0x103c0600e000f10312070120242070f10b65104103400500c4100d41000c0030a036000110b00a40c0c00492800c030760030f5519400c049025120003080c414800d802e012000c11403001c0426a90103441c40500c020040f0b541d840c3c10400340210958028000c0741d01002c043c80b042d546907900e01d1b07110804100b2078501e580181e0200d4500c4c0c0d401d60050b07005130807080600002080b035006500100001124560a25480c50b80400c2c4850041c002c14822002083d00c0000e0941203420034080b160005064802201c0c01c514082c060100d00c42c1c2d06e81c0028601101d01c1e0806294280c046e05803181044003100350403050b402d0220803a0840b0344d41681307107003e12906000400040700220b45c00480e0705c5050b20359190074005450705404903100507260704403000511485a020702070b02c02d81080e5141c100c03048160f50385a074015100c5c030407000c0c2009413101c04100c9625102c8000305000c2c0c0c480d001c200040e903603015850100000c82c01100d51030303000040410310b11600ca0007046801c2c401e6182540e192940d461022102075101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 879486546 1250 879485296 879485303
    0x1e0e03030f0a03051003030f050d06050a0f0303120e03030c090d0c090c120212130f0501020d05061c02221d0d0311340803070801080601081906021e07 66
    0x142c2d10320055050080710b0b00141c00001d404030301411990058210300c0140303885400c004000c03c0e02e450201084c0c01850007064081c003500152912403100c4002c2c000d40c1c1c0400c0e40419500da918010f01040c5118600c0c016044202450840d21010580d44156028180a90b801784078022603030045500710003000003c09001c42d000804a940000140c00410382000702d90500b803040c8007400940d5403124204c2d501c1840d000c076420385484d6614103803800d0309100030003a14561020803d801301015503800980103d00071a003803180b525070100302001056216100079001341a901d4407141c00040700700300f840b41149841c1c0100d40d41e214860524501c1103074a5243d0482d41c0b211041d458031603050301c0f4104540001460a514203071200c2c1610504403d103070708060901d240081c003150591101504111519030200c8050780c0ea04100c00010000da0086c06440000c2c040c4400000c0c50300d400007240322704410180000c07410f00002c1e0312500001d4000c0d101c10b12550442101d1440c014001d0710040010b40d12 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 879487796 1250 879486546 879486577
    0x605090a062c18070e010618090e300a020303160302090918030403080f130e10030b04050c0a15020c0901061e09090c0c0515071e0e0303 60
    0xa403200b41c1031445402c81003440101c140c4070141d64028154403030603034442041a454a1180d040101144ca8075203d42d100d003800540800005c00d0065101c0203010170a6511020758015a488546803030490310a0501c0708080c0c0d0040c803022003008404000241c040140480c1d01e580381e0641500d800099103c0b1550a0050300000b080022aa910b03046440e450380309890308500382210000030800414005d0070080e048000c008511203d0001001100e02450f80583c2050700c42013440e000820903009003802012500d650440801d1284841924521801c1e200ba00c00005074556100c901c030211024100b84e441d4000d030031104400361514103a05005050204030440683c10300400242405103610400f4810040b00d00104540d55005100c1c03c0d510001a20103115604103000584110003264440c01e0300074146031000242d141c021001c03d000714041c00544100c0faa180704100c0c02008110b4041d000f068200c4c4400980390191342d5015402d40450030070462b034120f00b000103842c0d80c00201e04002100b2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 879489046 1250 879487796 879487799
    0x3070f030303110702090c16050a2114040b0901050c0303070503060a17060a020f190e190b1b1207080310061115090a02090a0e01052401050d0605090a06 67
    0x5525220f24840c00281d801540c3c1070807229400a821080c0c054683c0900d18004112003651401c0da40010320080d03401012030742c0001c200e191462090b20b070b5074640304018030006a5100079038092180200c40440d000c40c142d10345030030981102560780182501904001c1c050060450104040000358001c400640752141c0b280b034440c00f0021000c00c541c005940342c51400e280d030840300400107080354015050711030158403034034203604942c000d00130f02000201207261800842d686075048030300d8148004003a0751403101c0741e41c220700c13101c90450707144503a86240c40704000080030580394801103a880304d010010707500c012044502140c9550485081990115400000d00200f82c01400109008040a0030404405e04007080036540324130381800d0006611402c01c0010320382c11003e00c000c41150340c2c0180034140078108403282400506098071400c0f050361030503020800a0a05880110080c00c5101d2490303e818000001101e0300e82183e40c40a03e280e131244c4000c06d03076541d0000310318811100c0708400103189 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 879490296 1250 879489046 879489053
    0xd0915050d020730090b1c0504030e040e0a05060c0c12040803040918050d0e12010e010203040506010e0c1605030405130e0c041a1c060c0f080c090a06030b0102010b03070f03 76
    0x70000d13002041c07107030b0028908030380d158208200c0e074100c0301d014141c1c2d52135400707000c001c80c040340460045400b01480c0900300802c254011107504030142060703800f042000ea020548564441300080050030f954010000112009981d0b4003d0020300444410380d550046802800a440e400c282c00c0305072039410101b400d01c0800752900c40e0908051606a060585900544980ba120038282d10035400300b1801101c210340315100d2030f1140e20543c0000340204004900624014000e4206031001c807424000c0500000d03a81569910441c02082c00224143c0780640901d451480d03940c0c0c101c412039144c0014000000d86a8030300f0b042500d15442d0b0000801c00c0c0500040c070500741282101d02e140300e985080c0f511040350303071198542c409482050780c402e50816283c00b500040c10f200b010004041c40e09003464420030951058400c03148142a845854850302c80302d204940b117014004d07240b50040c0d6052230820866109401c413001803501070000050000800300460b04145541d0007804024240241c00c0042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 879491546 1250 879490296 879490343
    0x209040b01031a0712090611191805091f0e0106050301150f09050f060403150b100507020f04050a2a110102040b07112205040c080d0915050d0207 64
    0x1001c1540ea6440b032070b0b20301020041c0110013400302c0c500b051640c038061001000807584c042c8200c420808d401c01c1e00d07104507441060f02002c01f05842c10000b40b6020000d42000f41d120904d400b540d03002060103502e0307951030104020424910161169481c1034031300001d00c1299510115010307003070300e0303842a9896041110045040c00180441070420a4644c1410106a4010710b21000d6400865107032002540540000d1032500a540000d410290401044469200b83c0e40c01003888590564481020f2200144107440ca0700501102940049030300044154038a4564016a40700d100300d00c000880382c03101c6144000b1aa20703580d0f443d40c5112120340c60f0070601d4200c440030550300b110340007d43c5400e00f8800122000c0c0a40300005180e0410040c0c0842242d4503c0340801103a0b1036014242031282c0248000741c041c000c2510240c4050428070b0740447c000f5408640040701c0484ca48942d00d21a08d828481480c810001004408001c414401202d05001d030740000c18041d0302800240303180310302d01c035041c0c1903 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 879492796 1250 879491546 879491573
    0x30106030f0b0916050306010504031b08013204021f080f0115020a150204080a1104050705030720011e09111009141f02030711060c0a11030a0209040b0103 68
    0x890118001001013088400c00e200306100000d00c2c100741c0700d44540e801030f034080c080c0d6000240660880c003403041d00e001003c03640504079010500244a0743e2002e100001c541d03a100d0b60003203482e50481e40c40304807131100e0300201a041417003d080c0da900f401e0840c0d403960300c0c548604003c1002030b102e2000c1c404c07151400481c143c0505000c40c0f8496500716a1900656942244100200311080404401c80304c1001503050758001c0a132030b003d40311021520b02e0005000c01ca10070803248594035100220301031900c10790a6a10070300150b02d0302d8101ca903c108045000410b8070104040355903c40680900c8100140c1d0720400c4212420004600c02e911898103980303010b24002402d0003580806002180281d01804800407900308a05045030f1108400108099060100c0c840003003142c5801041462540000142482c0c0c0c0100c41c040c68280c10842000030b01d02c5906140d4050303901030240480425002d90482c18101402011078048100c0782c0e0108a451504440640e50725540b2001081881405040941c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 879494046 1250 879492796 879492799
    0x106081009060b04030f230709111201052e0c14010506061c0e0a0f030e010f0e0616140a0506011a040e04020d02150d1a030705040c14030106030f0b 65
    0x20941414861a241d001d141700150109079201102c1051080000d460240480380201c0b4014900d5080000380d510340040c456000e03100d162400f50126030141e641503815140182c0c8500070664a44800c01450003032072807584546990803c43c0c03507500503400138481d050503031540fa0071030546810704000c40180324a001950b03480c0d0614040256607a80c51049503483c902c400c0012000408449136600140800071914206108400160061280c0309403080d4a562003039441d8201580302200444219102012000104042000e02c2c2e1051801030040c0800d07800040503240b4008480d1220702c1c01c0c3c940c40542084a4000c3c4800809128007404001d0160045805103050406032607401a03052203544181501c0460a001150466031000c4500c04500e4000380400b10000c41d14465000d964840ba5000681e50318220782c10f00c00c201114006002000010084d0030a54035000070b0001a010031003d2070100145000c070b00030140d549001844c06440642d0b40000e42c01514242c100490799648401ca = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 879495296 1250 879494046 879494051
    0x106050904050304030204091b260109032010060915051804120306030605270703030801090b06070f061a0f131a030a051c030203090d0810030b0106081009 68
    0xc40410000400c44e02200c2d410790b000550080b01d810701040344900c0360180c2000c481003150007e0b8614054500c001c0044041500c10241c403000b00c452402c03034154182c0140450021080210040120800904180d0784101581e100c0c105000e100421504190040c1c9181540c552840e00300c1c0440200d580040d140076039242d00000844001941d441100400080c44051804c0e5800d95551094000c00000c50f80940280043e0030305034254072401c1080328176181d500e41018800044550005501c0b030450750192200d0515900340a1204041d00f07601a01b01d81091081007140b000400f44070070101118000d400c001883d800c045078038484107008410207072050b030900c041340f42c513551029048818144d05601c0060b8803542030400403451a0175903446a8140030341841030081c1b14000c60030500004248070190b042c0047c2c0c8100780d089000a40c1d0890023075000106400314580904030143e00314079040030840400f95a0790b20007015842c240c0210300001c2002e4117003c042070038000c0586c05003c03c1c0800b03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 879496402 1106 879495296 879495301
    0x714070623010311030d030204120f021c05070f0503030901050f0d2c0f0303041119050904140f070501080a18050303040b0103051005010e0c0c100f0c0201060509 71
    0x213081c000e010303000706680c05034864030841e030030b5a080222151403098a0386500c0085070030070500701c1e0442d111050b0340c00e00403204e0ac400c86031a84548000e018060400c1101111400c09601c0380f03000b07620503c0403070f08980c0c0080036500f515055100303180e00c50361880204c2c0c0140c02050010300d55482c10071050021100b1040c4e13640c40328012907088840c6078544d442ca82d50b0f00d00c42214007070310104503c1c0d481e0301640380008041c909040310b00107110032a80c942000841641c801d4404440c86492031016011400041c4030140f08511840007600107140780c480003800c1c000c2c00901da582e03919500c3c3c1301280e0b038104054000c9010f50304001204d0310b92400c1d107084030b10410280410b841502c103031202504120300900490b4140c90220282400d151202d8091100c82d0300583c003c2c0c911801441807514500c0941d1090408442e0501001700300342c90701c0100030f803c4800c0c0360401030142100c05c04 = true := by decide +kernel

theorem cover : BRFrame.Cov 879316546 879496402 := by
  have h0 := BRFrame.cov_init 879316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 879316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 879316546 ≤ n) (h2 : n < 879496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
