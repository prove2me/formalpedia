-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4514
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:51:58.299432+00:00
-- url     : https://prove2.me/submissions/c1f98ab3-dfb9-476b-b7d4-acba5cd3b29d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 811690647 ≤ n < 811870503 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 811691897 1250 811690647 811690669
    0x4030e04110d0f0c110f060a0c110d1806020304050a050d06020c240c04181a0d0c080706030c050a0f03110403060f0b04020c030a0c08091206070207060c0c05 69
    0x285a8641c2001200c2c540242211080c0c000700241c0c58a03070f50911402c03604601c51307144415202014050000c1201d104c180e6070503026240b814210390340d80d44045514840c00e6001031001d0741000b46e804a02d051a0010040903203151140d092085200c400101103000204440031a400600b854054a2030042040f665607103903801640d4494017040500052070040c0320006100250b68a504155014840c41040000c402000300d801c10304104002c1c0400f280c0560500e401d480d04a601184c0c003580e00c3c840004084203d10320941124810b440d071010060f04054a2095403106c5040f070b500155284030440c04c2e2410b01c1011000b140c810011446c02c0d038425a01c02c03a1200450402054000d5002221140342c0d000b90b00c25250b060f640d000406802c00e10f402080b400c00012642903052201610703000b9124030800040a06000c6224043ca04000ca1042560801200282542c000b0003103082c506407100000c850060041c000d039030300403d10304d00400d0b036800c00ba5000a08030080904000500c840d01f414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 811693147 1250 811691897 811691921
    0x15030b1008070c02190902030f1b03060a170709020c030901083105010605060d0902040b0306072a0807050703020a0f0b0301090c0e120c01170408121902040305150a0504030e04 77
    0x50800815940ca0311f000a50040c81840251440c516211404406a0751517195021001e9800c00070303c111650b45040311002d46440c4007082200382d0110b41c00070700d886034591007401d1032400800c40c2a1040e20210281004c40020380314080c80e41c1d511094502e217912404107110520f03000703500040000d41000702c2640c0702c5206070300000d0010b4030340c8002069500706e815131444064694001c0e400310308040c005c204e04503000360010700075820000000f41200e01c0c4003200008100c2e2501c000600c03c00307004030003001c90341c1203004a0790b1029641881521150361b80005ea008020309580025010700f0324a032142100d1403105040d0075642040f1041e00500540841b080030400712071310096540d0b80300d10448143e0b801070801000807034408000035106c0f001c803c01040e51a265101000003113110f03001280d56481d456070030018076544040303804400c40041d2020a19251011401204100340043c02c4070042c2c800c1d104854890350f038007103d4015260100c80060008650005000d06130401b030b0044416008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 811694397 1250 811693147 811693189
    0xb0d0e030409090b0109111207111207060501080f031e0a0323041707081605031b0105010914060f091005060f030612030f03150a15030b1008070c02 65
    0x15880c40c0c9075055400d10f81c802c0e00c01c941e0f80b40c0100801d9000d48039075502c1500a22015041080307481c446107100d84010600e406114003503540c00040795091100400c10400900040d40300d044904203d00104000d00070200c541c4103540821200704000001d580170000750084108120a5003000c100d840e41098000905064a841a00100b21a111420040341c0c82c1c0c41d0310345007149424205042c0c0d4031000d00100e40034403000c003e4240402d070b04038104d5141c2079070000340a095500d9494501c2c034500c66040d100101c0c080c10b40d0b10354845041900300d981200e0507840103001481035800d94180075003003958850351090b8820f030801020304003d80c14544c0121030480e003808641d03503a40070941c1548802100c078100d2a001081002c585800340341c6903c1249600000d5041c90038030f4003003207071911001e01304d040505503a900c030180e00c4d41c4910180003d40303d0b1809440c82c00c280e10038098064141c03c020144100c4444c40c3c29900315200d5461940302c1c1c0b120799a40040852a502031190152148d160620301103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 811695647 1250 811694397 811694399
    0x503060c0c0102070c1805071b03140c01050907060e09190f0b100201090c0e0f040b15030a0c090b0103050c0301090c0c08070c17061b0a0c061104060e0a0b0d0e0304 72
    0x301100300c0b10001b00b0800d81c1d400300b6880800c060303d084503401001c950500c40328020111003a2214156802784940c0342c2130480340404030403003008144c090001c0440705582481d080000031500410f91358102c441c0e070340750540300c1d518003130800030440c3e81210400f80480c2c030142c000c180c120f4290415100030340001c41c00101071807500049146044103c0d03007031025039110f0041204124204034004000c0030341903800b070340f1030134509008001c6100181c005080e001030180401d81240e8003000e00c40841400078107e030104d0341c0514203042406850b10034070301d80034607280d40f04265501034050248508025844185180c5c01c0c076041c03200616003c80000e0810010209038400071300360070004d10740a4026185e50a04614285801c0204401c9840520f80b503000031041c00180907082506000c410003c20100382c644095070401c41e2211001d40000d00108d00301500e8120400a1000610541c2d4040d910925002508030034130084c1d403114460028801e1003005840c1000040c2d40c0301d40c100609100a8034581 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 811696897 1250 811695647 811695653
    0xa021c0c171006080616140a08160e01090905070509150904050c1201120201140703030e0c01020a0f0f06023f090c1306170303040212070503060c0c010207 68
    0xa800d250300a140034460108000d00c001c4810010301c280d60110031002d005407030420803415240d0710f018020307001100d8040c400c1c0b4070a07402102c04214030010220741c41d807a611006001862514180c841e0390300301c500d0700386220340d2038401e03c41c1200c80d00c1c060b142d8048071890403d40d18010b1200030042c80c20424203210490059488991a00c28a07040781c1504c5e894402c0b0310100802c6034000fa00d0f400a508082209c04404582c1c44070f1141120a0002030100260140c00180c8280c02c281e086515090030001d011001c1582680c88188030303c4c1d081c4101c410591041c001641d0366401100c029224040320f1181500003461560a281301c1352040d14054149100b038503024210058400ba031582403243d10424803040803e148110408403080c0000c0d205030b05001d8400c035221110b1111030b501070f20380c204d4003250301038258100000502c40d0340c00381c103400c206400d8020380340e07002a1002c030b20a0038030301c50100e111000042ca442c155000203004c2c02c0035441e180307210b16040d8000380900380255001c2c4010f0002c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 811698147 1250 811696897 811696913
    0x408010606110706090501091707150305240a030809040e240f0f0f040f0c12110402030f060d0309030510020307170129120c0c070b0a020a021c 63
    0x208015126580a1050840d0b003909044140e00301804000c0c08031700820042c0e92054404084030314040c2c0300351882c44401801814030500707410040d02c1c061840c50344040b4030350540c00107100748040ea402c204aa03001c000c000a204da45142a02d0340100e008906001140c5001c000f022030580003800022180000104c260900300302c81c45060000c000340101141008204461941c0a03030303400300d010b00c60315003000d203405000300240c01081c030b10b468040003400300904c00541d5a0310f184c10112100c1041d540b40b44500d5009400c02c42110400d40018a5400d141454000d4038041c0442c841d0104080d580c0000b0b0144c4030303001c2a41907082100344040040450000c0c8182545404008000f5940b483d001c04054110400c11411a403030003840001009024441c191f01b00341400d03c03900d502420551080304031f0b1907004036440619820170301410f00c41d900303240030002c200007142d410946101c2c3c0d554030018007480c0a9608414052380105884100510344050920750641e0030420b044050b41050300e40e904 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 811699397 1250 811698147 811698149
    0x121a100908060901052406270a0605070c05042f0414030309010c030807050405090f04020f060c0a02010807171003060f0c1211070f1b0501141e04080106 67
    0x101160a041090040107014016240e202030240c0083c421420a2203202003038000a480050401810403d603090950702d01c1c0444100e42c070181e819000d82070086000000806110103568401c080301c000014003207000780151024a5040184903001c103180a003800050324586405220b0100558200e0132100c1a051040102d0f2031200f032180d85440c01c1c04a0070090b01e54012200384240c1c028002800141e912003072640d442c662519054805444001c0c080e10710780510b4120355441001041006200301d05201c180c2e1149000312a40704003080306034144000c922419a092180ba000325138003801550041d40c1c0583c000346d261404040d01c403a410700344800d02c001600d08840c03043d030070b010030000d000705400790321000c0030440c404000260911002501c401041c4e03042020040c5c8810700c41202c154074106a031202600a102251031000ca898078021541c0201c01588108104d41e80201d0740354414038114501c034034000300451904072614400d0000c0c031a40343d69440b0034842001702154500c400e0207958 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 811700647 1250 811699397 811699429
    0x10606180e150307051e030d0c02030318010912030c1a040f170d051f06050307210609060312030509011815090c0b312c070c120f121a 59
    0x10515a206c41e04240c1807481e04c441e1713401001410f400110250750f0200071600c11030440c2c80ca1901c030309900401a18060400c2d401290001401c404200030705d0b4204401e81080d40c403a070444c013500811400d001044140640300507017601841d4400343c0c0025403100801e448180c0240001d0f0a0003602458001036400884001e901e101c1c0880c082e464000d41c492460002e04001d0400e2030552610460041c2406034028031991340c004880200081c03d895540f04c0c001030700844400380007082e01d038142074014800f00465100041e01c1c000024240c0032040c0b19205155204040c0503003455141c0d11100210f1004010003c54141e80c1e10044001480046c0c91100401c155009985c07183c424151541004981c50760f2019101810508800c641c40c05450784400d0322420170034800b00c10003960cd051900300300c1d1050909059520030502c407030700b604844d000b1000c512030300325281c10201c4088225004206a0a43c0011500100540360454003641202131044031030740f10804a03082d454002115a01c01001d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 811701897 1250 811700647 811700689
    0x2109010b0910051f0203250507290412020103110d05090706020c0a080a0f210504050f0634050a111002070b03060d0804090c02010606180e15030705 65
    0x104814207203000107134030b90300748502c030158075910419010752039208080114114404e01031724501c4030b2400005080700580c20100f01d070f8845487c2e01e4400c0012028a6000e021400c242d003503140041035207401c0303c0c155504840c100e41c42c500c0300d034010740150503140d81800e10240180501182041c00384115841000510300800907546007801c041c0c24001003154031341c02100a030809000c400b400180303444005600450300c28500b0305070b041c107029001ea03426044030306500ca94100c880d090b52110281c010780304100c0c1c0303100383c992400e0100150b9205202c20003116484041d01c001c0001c0d42c03441031225605400101e01c1c1410500d40c1c50906000c6035000c11a1011501c949541590038040c0e10451022400d00040403010700340740b500c1d07040303003c01880f0318824449444030900f00104036013640c004010f0400188422090702101901174081401141d0000f02542c0e0704030900c003031b905154000c852601e144503206896100c003102c1d542001600311901403143c8880014140c850010041e6521010090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 811703147 1250 811701897 811701899
    0x6090316180207020f090a020c0a0b0610031a1002011104030501060e06060f030a090f0b0f0a1b050702043c05010501021219020a02030717010e01022109010b0910 71
    0x90a5181000c07031560111180c81031002e400180c444400f2040603440480f81a20703103581d00300c40c040c064071a1810443c03082c02003030340300020841020107150082f1811159491150a6aa022411502c00c411842c143c00e040d0090392000d82000c140092944507544000f1821800314084609690311541c011102a903440c07004019880503001019040340d02151100e281590354440a2707c1ea00010302145c60244c0c1c3d0700d5451003007206442c02800880e034002100741261503c01c2e094001e11404039480c1e0a000e0030600c403400e100e16802c0041444403416150181403188a0b02480010500003400240700150a0140805104000c0142c4080004140154418030441c505003083d101e0692003941950711810410710321380c11203030030b036100d0005802c02e580e0b48502c041c0b822481d100e0381450194250050360f40100301301c18041041410304981400a0040f2003058405a00302c4c802e0504c2100c000001e218292024680011103e400c071030454000b03d03010140ca00040c030b051205503450040e05501241c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 811704397 1250 811703147 811703159
    0x315011503051305031c02090406030c0305060a0e0d0e040e0106080706110d020c2209050303061c0b01090c020f1c1b031d030f0609031803030c1002030606090316 71
    0x4180d070003141a1400d08809903035139601039070380c016580d20f440f00f802c00c2940d0041440c8942d0644039020350050042c4002c075540d081ca661030212500040e00e0314051000000e004190341d0052040301d2000a004112441569004035000c0382c00d4003803540d101e500c80414040c054402d0040303030060120030000c4c0c14100e2030500c001d0710320742d000500e03074249800c00000302c003c0b141c0201e8882e9142c4021b903140f840c804011045010341c0c0013060310041c5c042d40f034500c1c00340500c940040036501c2010255082d42503400315461900c16041c4101000303058501c440c0043c8101c0610381c1118200d01c6403401210b000c2525030004a00b0400c2070034896070b20b06850f4813800c1a86520403660000303040f00c0b05503460b030300fa800c0d10002c0009580c0c4103501c0301d0501d08a40c241c90ba8030300b001000c111400c0038040d1181802c2480800742c80780e01c02603039010700314680e6241c0001c0c0e02d0080700312013081c08072500600e000040041d034080a90401072525a0008080c4400101c0380ca0500680204860902d500010542014 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 811705647 1250 811704397 811704401
    0x1e010e070503070e0c0304080c0303040605101d150a33031a150c0a0c03050d08071d010c0f080c010e0c1509040f110d060812070609020315011503 64
    0x50701480c86548141000c2002000000909800c950010511540d035941d0741800c400300d118034808503a41c0c0c80000104001e100c00ca90045024004404c03e500c45113684445002022011520302850000614040381103501c92054401c50302c8030152103080e2603541c2d0309440308940517211421001c2400d264558050701074152407400000c005050401100301d08198150302d4982c20b420711801041c02e170810740455860002541c041034519000c95001e01001c0c54500c4654060f0300c03040356940301304c80440f0000d030b000300f0003144100e03910b665400803446007040345603010b0915880f1300e045c04405078664011601e440d0398402400d0090281c165100f039800500d03821200210080001504040d10f0100e0365a504030070091040040201301c0e4403000403400280080483c0c840600701246086444101e80702450003412015088002c100b0115a403804540c1c0c07250307400d81880d200c0640401000c0d0001e102948004100c90018049580700040130113008120442a00224011420b000058141d00c2e814 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 811706897 1250 811705647 811705649
    0x18080304060b030102252105040f050301020304050316210806010f03090305030711070b160209010608011202060f070b09030301140a051813060221070302091008091e010e07 76
    0x99008615098140c40c6d00a54540b170710181c501103851031540c00d418049805103429040400c4400344030f132141c0300341000c1e0403580103104291326112901000192450188203076881150403001643c41d00005130985c9107101c08521080761880004003c0c00c040b6800c003c5c603421585a0fa481c5c0100d281040000902845941030103003007094100118030740000c0c5d2040c1506e80249403402c0c00411401e503013440908004154101018909010501c0c508501000300e072030561034020b07265200687d03211078044484c802c00b40642d00c80c2061103d801c00042c1447c200078070000034164240e90a045841c2e031041a04542601c4070050f591000c001440240225070484071002d030101d0360601c03a240380a0102d1905414021301d40b00c0008640001441258032200c1c00401e140c2c0300d0305c111b640d43d45031a1103a545140c0744584030030600071000010301c11030280c400c964840070010031454103000d46180842d20940000e1080110b40164000420303100014103601c08045020301c00032030001d003220166031803c01e403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 811708147 1250 811706897 811706899
    0x25140703050403032a0b100306140403031b020a1502040b07150608010e1b010c1203020c07060801050f0405090c04060801060315051909020a0e0702011506022a0418080304060b 77
    0x1d02402018841c0301a01400070396503121881c6c9074150b440740051f107060607031580b026003050309225640308010310701040188658401d48040002164114141e41540031203d085800741c0d01c106100c4011664ae6400303504040c155000162405803039001d034500640104000315000b0300002c2c0344c1002010f16000d03d5001e080c0400080104044038414503650740014007514810b454040d48961042e44550701400086403c807000091200c22400c00070001d520240d003003a41307401a03000200d2154821486541202d20040c00301c003069040204000c000c0c0006021010144940c5405900d03a480342d029003c01800000d0001400703e2a505140810401403420009040c2c680340401c070980403000702141541156410014489100344041141d40c000c41e000f40c50103480c54420400450f0341500700707a042460303843d081801b0300d5031002d00b680e81e0411080f40b041c1d45030415061491500a004106c010000000c2c000714071001d107119150040c0013100002c0d03070b1980b0004200402d12a840c0a2107504c000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 811709397 1250 811708147 811708187
    0x30905061305010302090a0302040207150b040605060d020a03060f0f03020f0f09180f010906020307020c0f1e04020418150b0418020a050c010501170708062514070305040303 76
    0x780c101d40a00054440740140d40c141540454075481a45070989000003459010300f00710366901160a00b64103d02e8070100c111103690070048201d0250509000d40320031500080c080c0c0d0f082c00b105140440183d00941004d81c105660f0745d20000384451204c490308001d041c420b2001c1541d50641c0144001c0001034401c0302e000368000c1181404645544101d1070b07000e01a807690400d1003403210300d0542400503031020207410390b00346180710007400055401540165003c3c4c00b11842ca4203064184850342100d24509035019400c10000e15108000d5980d80d00203801c010030052038181c4401c4000c00034454405511011603841121a0500d9060003080025011008425003001c1c6401c6c1001070ac840030011400175241c02044c00749020b80620140c40e007550018000307121315070f16a40c060b42c08218145e60340c00c55104d80c000c0090702c0c420104200b401035150041030411920440c610340c0c000d40e2062400c004202c502141001841e071202c01401c11a41700c0e0b42c4d02561145182001002015a200d000300081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 811710647 1250 811709397 811709407
    0x906030b09010506070c03150519051506090406030813210804051005090d0b0402090105040b06251b06030c110a02010e0f03152223030f0a0c03090506 66
    0x951000c5800c0d044503c2140c03040d55a810b1032030413000890503980002d120801d10022804501c1a54104611596451a00746240d1020118800c21b580301910808162074142002d04450300b849401412070140240000c1003081d56aa1001c4040d8050305e908490001126814403990044001c00d14070a0603550492580909a4403040d03424400d502c9080c1c414a448055061308501500a0710350410000700f6800500301c0c2070410307034070a070703400c403012442032040d6400410030f4a4184603070550b06034084c025900700f040c0c0011110000c02400c4d2205040c542c50000200040c00c00c82c2130949407800340d551400c01910301740014058504241195084c80b0140c2c2c0c602c206210f0004401042d83d0b02443d1103000d04d82c2d40c10100e207170490220070158150080d4551140004071581209005180546c0c00c0403880900710001140e94401440003172011b070740701340922400000b02c150b000661503614160707850258002000c00741a0b01c0707003500310046401e000039403040c1504814a0b000400058406520700 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 811711897 1250 811710647 811710649
    0xe070308251205031f1502060604150e04020a120f0501111903050646030203060c0c0f010510030302061e0115030e060c041e031205030901150f05010906030b 69
    0x200584052081000b0f000310000d0700703848506001380da406683c1400171170405c2e1601c01c42490201c5140700b0340d025204440c0030030b0050500d0720441e0329142e502d1090303540c0c4d20300301390480805620240050740c0c40201d4000100d40c202d004280101070512807c9801c0c4038109602c1c025003500c4d0303210030701c1c4607010341889404603405080d0201c041c032490030f140000e1207686900005003904c0303404c083c0c19180c05510300007955040714401c05078000e0604460005142084d030000100014403800000c0d01034120601145107202c0b00400b800a041d8801d055400f40741901640e2402c4401c00c0b240e1a02072420b000b02002410b0b014010142c001d205551030003c4809070400c3c6910411040c401c60f407150380503103840581c01d4825404003160075481800d503842400c1c403521003030f401d400c6402250741e011040701d210700d24030700300c0a0400201c0b9404034100000c42d140400681d241e0700000c1440a495480d00401e6820148241040c009800c1d440d02e502c846e9810200010400d040607040b000601d840d0504010071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 811713147 1250 811711897 811711913
    0xc0501110c060f090c04092105040906090204030512070f14010209090121030e1203071b080d0906050304080904050a1d03090a1e1d01030501140f0403030f0e07030825 73
    0x203004080e03402280b00c62591908d08030302c1580000f0064400d800b00e80c1001c4e62540500100304480d0b04000c00c1c0202602c2c0c0408004034411840010b0403940091030342611183d00c480904a80c2c0d000d10a084501c4020303072900d100715007185200d90740036507002031400340b60310301410032030301401006000c5040011910543c1402514828010f41404805030a92102d41d90f02c1a02c5415540401709a070340b60074103854201004581c0c640b002d04000e030751745400300b846d1000141032021038205945a1f0440b510f81441580c8541c0050000d5841e103c0810941c111038032075006481c025495810000380f072041d00e5801148581c0c2070142510250402c018920403541d0740540d400070307074150a6600354404094015810a40010b91050046071403007007480c1d0b1003680c9c01640742d0403030340510020f1195038841c0d8805035210a0840700c662256800e003000c500468421b41c01601e8400b042c00c40020b0000c68845018600051b1384e02c00c9170000c00005074590a03b80405910301904504181080200341580c0d80481d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 811714397 1250 811713147 811713163
    0x801060507060509070510110f03070503190315140301051503032a0a050a140304060906030c121107170306030c090703090c032102070806070507030c0501110c060f09 73
    0x204181e1202c003c0303525010148415001444c00030a103030880ca1441e5400b230015010044125520301403a5400808400b000c4100c807a11135001c1c3c040d500c1c00580c0010b010401710901c40040405d0703580c2d1005940c1003241c03281140500200c0d014400da10b07011104141c2034071002400c030010703410080a0140c26850000c199801c2074800c0d0001010010300345030b0000200c40700c1160700490f120b04030b900d074280400428607081890082c0440000b100305945015507a214920034440001c181c84020003040e446071388810201c003454504101450f681c020b89006803503030010a8a214031000800d030042000d061980c01056003109010760852034401c0011741c407a24074908080c0100f09040015525500c0380c1d000000f00c50744020001201c80c1c072410591844002031419100c0303404120240f801c00ba000059442c115000500108413583e60103a08560540022500b1001d07c00804000c2e40011001c1c000c0d819996401e4a000b6140c482c2c94090034a042c80280c80c10200600400500c003260380040748000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 811715647 1250 811714397 811714403
    0x5010b0a08120903011e0203180607050a0e030307020a0e0105012d031d0f0102070611070b06151c0510050a030f0605270a052503020d08091e09070801060507 69
    0x25110b11248004c20b000d00224040d1807406000c60100c07845982c100d5010318010140c000c1e900301083c0304046516a540300503203041004c2003050201e1544a40714000502140c030019050320f0030108141d011850000c41d03500690428404080140400e507884540000016403a125034039809103514115405142d403001010101074413001902088400d0440d08016214288100c2d40d0816441c00e15600130340001c40211805d41c1007055004030000c580007602c0985412000100c200c1e22a0f03810000c66400c6151116071a1805010661840c40e06404022841001c3c41d80400c00340740c0324500c0c82d20152250485403003841804018401700790071b000c651140c3e55000c01e0000302c54484501d50341890b503d600c0e42e0b14030492108100c1681c0035000c96180401403103442224a03040c010078420001d03251b959010041c0c10150a810009803404821012130031740a00b0300c29143c400000301007010300c1c1e039444003c040c203484416a40c2841c1000c0d003005500070740e1880c01911550408a000b8420300c03a480b005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 811716897 1250 811715647 811715683
    0x5210901050d0c0201061509140405090c0d050111120628140a0e04030c02040b0328060b090f07080121080a120c0c0b0c071a10050901030c0305010b0a08 67
    0xf42c0a81c1d8001d500801c090252a14500c0391901d60040040ca1210b4038050091000011902c840c40f81c14107001e114000c150b048046c0034644284018001001c80c98a419565036403101c0380a00304c1002c190080a051680c2140541c00349419000c0c00541610032556500423401d1601c1c0a485040d42903a4a003540d501c42d1401a502e081513002130720f4403070550001c5400780040e1051004160300034002c03000700c5100361402d2000d000b5082c1050384a13000200e920b04122000c2074410207103501515020000d030310404000940e04007640c003007020404c0440c0c20007004080f000030b2003032454022240900400380c0d100c1c905030310050020314419461590200819070140403442d240712500a4a8840c02040d104000700440182c2a1004080d902170b01411780351000040082501a210700040312200342c0c004541d403668851151074100d102c040180342940c0c0c808000300c0410960782d400c00043c02580a402080c0f140340c258113180d03084030072045a083c841c2030500d90810503114045503c20551502c0028 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 811718147 1250 811716897 811716911
    0x30c031501051207050402030a062301140915040e07080903040815070c0b0a021312050307080702120a2001030c121509021908060901060806060306011b05210901050d 73
    0xb09464120740307800c1954424004130800c610036442c2e0344a0400c0b204440c0c04c0410048541c1816040c201180cbc2400c0c0c0040c065100711100c04030610300811854401800c8044103280820040605812607002003218441d210107000400c0d41c030065580d0000840000303075160910304800c1655402200c1100c2040300070170300004207054040e040110016030031840c01505450101d844400a600401b03c813400c1510740a408102d02d019074458081c001ea025000b1407030701c801601e03807d03256044081c003241c0c081c0c018000c1d901424410b00004108512510121050b016104801c050a40907500c2d03243c10945448008030740147d01c20151141070040041c00101ca0140c808994501055030300140b501760300010b8a9605480e0085d030312400350015989010250300c44030100460301e00207200d1040041c0c401c2000c82c0241c0303048030007590494414108904001d28203044544040c40742c0310180e4158200d21505400d608124105004c460005681a460031f0340000020f00940640c00740c400903283d41d611 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 811719397 1250 811718147 811718179
    0x2401080a020c010e0f1204030308010b070212070815061f1409040905150c030c0d0c05070f06020705010b03012009031212090c010c110112240302030c03150105 70
    0x10440e90b56444100c001d000c0703800e00e10440b40d522800c00030344410900c1000e40c00d40c502c0d440d1030190381c00d50364992b036500440d03481c1c0304100300b0541000509a90149a220340c000e00c180301042401d00030f10407280504040c200340d129044024100500c924010b07107200b4900100b405000460f5620f00c00700c3d04102d614084130014440090080610301608140340c603d0403428000d00040ea0601102090410503003582e5803d5040c409010644089500400620403582080c1135500b00c103907038001c0d9150032414205035880751020500607180598806a001940400b8003200b13015040c486038007a00240030120303407003128411550002c1002010030030b0106a1140c10f40c0c3c00c0c4040c032261a112006941c480c030219280c0b1490100a44000070b6901c14428041d5031075003c2c0c400309801c0c603002a82469503451034401586c0502c04120f070001c6217a681c660b00000341ea01d51005c10035518240d4040c45007581948145450012400211407182c0d10540007032022035001c128280c190340301a11000010f00d9551 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 811720647 1250 811719397 811719401
    0xe010c022205190e07210f05010f0501170604050c121905030a080f0603060a0504140a03050c07060201062402120d0b010305010506070b0c220b0705062401080a 70
    0x70014281941c01c01060040d00d4259915410300508188410000c070801d01400d01e580715070700d00c100704801e03542861480c0745850b0490641d440500460981c9032110003a80c80c035003164a409080309200d03075074600601440d0300e64030300c1c080c8800390a0020911070400751a41c82d0740301c07000b003051881a00d10480070840c1c40f8081c8000000c159880c5a251101145440d145840e504038050110000380c075000050520501e42ca010b900418024001d08080d0300c80b0307841d05c00545030050003070300c00000b480076180300c518040100010180c002d68a00b82c403200c02e43c032018200350b030642c411811a070401c24240028807228484280211003c1040d0075a20342c0d4400690408510400320001158081001782e481c00341c9070400544244241d0702000203070380f074500f00401401130450142000c0410f400080c0c0218600004110740b600c00c41071400c10400ca00e20400e050b1803035802540030b6100101c1c410040000400031107401142c0c030780504d41d081c100d0314140100c07030301d045400a041151503c0030525011581d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 811721897 1250 811720647 811720699
    0x3020705010e060402240f0d0617151005130b0409020a0b09030715050714010e1002070c0501052106010c0c030b042f09041401091407060e010c02 64
    0x309000740520203071401c00c943c44030400c5905901403000c2842540502403640d010030343c1260b001c03510508009071121a02d069401400c85048000c3c1d40d20b0003c80c001e032600c0c803840c1400e60303a40c0042c0100e0b5414580c4180c0150090200403111903000d9042c001c80e44c0d041c4000030881221500001c0710342c44000010b0107000701c417001a41000403081d02260340f80e4000014041d0a01c281c0403514102d55958081a84905a410701e0000550a0103007000060702034074045015444000042800d4013881d04403402c0c240c0d07024012042c56400154041008051181c61004080908003542041110742c0b01130151544480450700ea140d070240010b03e40ea0003200d1803507025811404140c0700c5a180d152040c0d00c4601900c5c00d440350880d617288042c003440440402d590030888072290808800c4c180c4180320300020080c1c000c69241d0704028006018050911480c0040c1d03020b0200302140d0003841c000030b0701741841074200c0c00130404040344a85860f60013076100c044c82c17035040d6118440c0e0080314150903420212 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 811723147 1250 811721897 811721903
    0x122d130b0c12010b210c09041a0a180b090106140c120a0c02011101060b0405040e0a020301020a0207030b010807061403090309150c010f0216030e03160905180d0915030207 75
    0x201600200304030402e100079003800048000d5124030003044401c17011504d50110340040b00350b48200801303202400d040c4c01c4036988810000092400d54000070000b0070b18101900081207500c070004181c92910b4941c020549200b20907503072030040c0c2d41130a00c010b20091450140c00c40e03030440080c507000b1070002000342560100d522002c1c55210421a0f00040601e0942c41c400c1c0c3c0010710b1280d82d1000400d040c803401c02252440700c103c1e4a0b10340342c4010b0002410b41c01c11413000d9400743c411010056142800104103250250380500002c5040d86803900f4032003c10307040a40706905c5154144042a0424412405418203c028544a0342d56181c401d213544901e22001c0e0308264980400c015a0031888003404208240500903c008101010510228020204504007030307800c1c202810007081c05a250b4251203c40602079480c042c5020440c0024204158000a0800c0d503450070840d07601c002c00b1950245001100242c9218401c80748004c04c4001c8034040d0070341480d0612002c0d010140a07034110742c00719074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 811724397 1250 811723147 811723177
    0xb0c1905190c05090901020910180b0d05010906170a0204020d110a1205070e03031801020c061612050c0d0e0604360c17040206122d130b0c 61
    0xc034900c0d00303460090789407080600880c04131000c00c46000040c000c1c0c1d0901c00001e4071140c0014840e0301c017101c030080b00e03620b50100c0200025001c1101b000100080c2000b000420021905514000e404800c48185e64880000d0900950004010890200d806000d0315012034025845030f81d10010100280078982d5010307440c2c04005181030085801c1345c03c548080007856020003441c1c3d40d03510161108007280f4403040c1d1580003045480100c120301405d00c856041c1c1881201d035112240c10100e0750703542c815121400c842100c1c500e05001c00c40200e001020354550743c03234401e09141c0c0e0609400c2d034424030203407100b05015401c030351504d103601c3c0c410943e001800410609500d0041e980124440319202c00a54880302c1c60580728203501c1c807158080c141c44030740c0540d154004111128001c0b81500342c0500100c0e44244104042001c00082e820720b94020455052002040c4e1a00604121449518404084000000000c104541c110b40075185d18007900003141c000c035603983c0091b580e5180301e4144010300b820 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 811725647 1250 811724397 811724443
    0x61201080a0b06031b220606051b0111070f060b0301021309140f010e09190b0108060708010b0316030930051305040903050c1b0103060b0c1905 63
    0x20001070041c00303a4081c496203440c58440005150b02c4807080c0da252421a5454000303000f40382030803000c40300403c183d0140300c0240708440701c2d20800e0702c04544c402e00000304089a28030302003123600c40400d481d01000b0001c100001e8002d10701d50050203070740380c041c05400c403403000e00f4107000c1213800203409a90000e00071540c5003045150342c26606800c0c042c1002103450119036a2950150103241c5000b14000c2030300c1344050b880c1683c2c203000c0700401440017441d03000b098590350305036001546240c1810310030580030b4007c0d818940014076054006260b001004001c00041042c041740c03004486d00800c100b01c034000c03a600000403d402918081500810bc0c2161000d0300d02d0003c014160910340c6041d40700c14402510610104036110301a01011400c00f01d4148010003035460994066048076200341003182c1440c203171484503824041d61201501c040c40044925025a60341841a003000d050070200c014207085890f181c0030b5403403010364541e00142d43ca442c480c1d4140141000300616040100c1072604610f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 811726897 1250 811725647 811725659
    0x905150a1d0102071106130e01091d061005010806190b0702090f0403021c1704050c092a030606040b04170c0a03120e060c010e010603050d031118061201 67
    0x204020303801e921610701d03504003030040e180040c0211016150051325500910a0540c2001460341c442682a00503160060300015264850704806000b45010000000c019a407100c2c8a24890400d203a01c40640d04a441004403200d02000b241041d42c01c286486501550740402050b0540c0458521480b4403041010006401d2600c0b4000c286941c03003034403945510303121486208a40b43c030a40b00100543c0140440800998a01143c0d42d003844076441e0400c03607400c0705e5810805078001550255040d4100750003180c15402c183c500c1c00e4201c004c0c41d48a02042c021314101c01810340b030943e40c0c851b10301000400f00b2503d41d5040300340e4019104060842c1e41e03441d52000458002e0007014407030180c0340074516207820103240c03402d652001c884c3c00c0600d01c0080409584d046581c01c0803812440d5005106102040c2c110400b48200c0d21201d500c00c00004103181141032251030804100807007410141040c241c0354021460b070301580d8180140c1d90226500700e82d12000160b031802088a4150000ca03007000005903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 811728147 1250 811726897 811726901
    0x610210b06220b03040b0a2a0f030507091d0a09050304081f0603020f041d0607170609041e03050c01090305090f030c031e070f0f0303080f070804060905150a 69
    0x1c1100001c44140b101c0341e80d070045002c01c3c00102d070058038403501da100082001c0c855070451a00560514140e66405540404a80100d8003503044400060030390034450f4104da4051144e190400c0c51403c100d83d80314580750400313201801100000207d00c45080118600c040942c00500303000d6401000e03280c40380d0712081c0b125a1a007404580ba07914003107005201105030000d02c21481520b4025010420000c110003d0101600100e805140c400c0d21198025401c0300040c85005d02036207666079407040380c3c2c125092280300b1400180c5414401d0100000303020000364240d407a030042140c3d07964070700600f1816080036101030040800b5107816500f0010743c08101a03110009003140101100c0b8004c08000b11400e060f9280702800266806030302c018a51040000381e01d0101410008180c12551541d0301c43d0742c8040d00003040c1c1d000100c1e100c450501031081540021505500154860b4011f02501d0031560050844002804c003800c007641d100070301011b2140900a10313241105a4030484d0180c2411007007400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 811729397 1250 811728147 811728187
    0x423071d04050d08090a031b350f0910090f0609170a05120d0e03040902031e090c0d02060c011407020706020703020108010b03100f060809060610210b06 67
    0x16140a0b403514640c3c1c160040c00524002c02803840109412034159a055804014820580c451b0b030521400c044009442580e1000480503054803400360220400000c0f00ca800750701c040c0b0031841005008980f08440354a058804044045642c2c690041750843c2c25207228031280c10010b2400201c0d20045103480e04108200211018a031035602c00c400d020840d01d0300d80b4107440d0010400e810028a40e4403030000030000d060030b05645e010005100175814942403940c0e1190340f000c45025008001c00c00c5a49503440034110a4802d0000042e40c0e20b0700b1881991140307400d20256120795150560202503440700d00c15a205142188020400107c030740d20200f8412108640300001441500d2010900620100d82e000c2243c1d4180c40d5213501340d00303142c0d181d0380c50b400003400050b183c0e080c2803000886080303645c07a1100620003610b400b0b03c142001040981031480c01004e03e405144a480300021140e0300c00c4c800d411343d11440244020180c000d41d02d01d40900707000805030390321a0002c13842540400084005103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 811730647 1250 811729397 811729403
    0x20f100e060a020f15090a11150c010501050a05450f040c05240c101e0506060405010c0308070c0506190f060e071b05030d0f050f0423071d04 62
    0xa80071300b400e101080c0711500464480704160001c4519400207045056601540320300202705001e50700801105001030740000e00425400d80d140c2004001c28203024110301c0242c0b50540b50041a03c024459810401780300c681d00a004050101021a0762041a03110142c442d01032420008241001c0081e541034603006e075070a03180549414400291840e0520341400700451758424002c0c1c22003407900e644119048101c141007140a40319031441010054803030a03c5084011115020009000c0c000b1406c4071001040c0c18083c0b0030400007406540e030004520401d582e8140b400e440540e5410340304440196042d44002e11a100309401d000403078070b0f004440700084000c90703401c1182590500ca03074800d5903050302c6074440341e0100c1400310308050310454101c842d00c00c00100920494020750388051440c0e0080500c107450701c0e036400c03174a9050f40250040e5900700b40c05a100303241e039081549482813060744000c45600350440c007144000f0b14000034000c0c0c10042c0729661342084a410102505a0003075801c440803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 811731897 1250 811730647 811730653
    0x12091606081f180509010b0a091e05161808030313060e0106230d0b0609060114040b030103030909020705101d01020309030a0305011e05090c0d050709050418020f100e060a020f 77
    0x4818140500c42d8203039411006000341c099a00e0204600c0003402b00d041c200307600c580c040903c1ca80070080c40c0501c0c0c0c0500f030f10700c0c1081c000c4048071100500c00030750a1119081002e816604009901001040c1c03900b1246207403203021200d00514045004080500d4100415402c0c4440060000c0240591000704521002601080289082001100285460002c081c1c580244c0420750509081003400c1d80b03e44103052891200b049000d64070941d410907442200d101c04000018030801d940811041d0092000312004e60620050b9582c0710340301c056000f003805040d81e0318414082d50003881c1101c00c0914460b0390085580c1c0c180140000e031213511820031840400e0401740001210070b4160b904520300d490080003a1603140c01c4c08204440b1480141000895100c24086c00c00130881c1032040d240503181544030441440d1510083c401a150b80b840010740e4103028401c41d10150322001c020300806401102e14440c681201c003000e4440303110048040f50400340114110510b950001244140000d00c0021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 811733147 1250 811731897 811731901
    0x402010e04090b040b1e0f0603120a0203030604090512270f0102060f090120070218010605070615120c0e0f070509010f02150a0212091606081f1805 65
    0x148016642c06000052000c04600c000401142d055641140c1150581e01c40503081000c502c1b8181401070113039180602e10700c80c0e60511850313240402080c1c0c0d41a0400703c4a600b0404070a101940b00d0200404550055803100c000d4001c000c01804001d030b6440c2186010f6458207c1405500f504599510701c51a240c0c481a0140c0080d24102c041c12641030340c140c0c028071550f507552110080402016010300c045648440d0711501a400d202c5107d10140100340e00951600d0743e030f00410446014070500d06402101d480b00620046030310800b20746038a5005103010802c2c10391036a0a1b50390400e03587c80840004a001c0d518802c100070746502004880140d00103c041d515201072440c131010041e03480e00301158040041c18855401000702d070400150314010ba5030b4040c50780e8009803030b10900b280c018803408c2d40003461b0850b14102180d041d801c0040e01000f01140c1c88124035220725070000740146420b010340d00e00080e64840c00705030303105044d81d00e003403101014070f5450b550306444032105829854000d00f0840 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 811734397 1250 811733147 811733149
    0xc03270b0408070303020904050c09040506010305101412070807050a14130f0e0d03050a0e0601030f080309030c1c030c02060f04080d020d090507140619030510030213050402010e 78
    0x2800054190300202411515140c0d0381d2422180d0380b002004800303068003805441d036a951a0f20a080c840d141c002141aa100400020001101d0000303040d6414145002c0503c0401c3c00d61034078007010381c3c0601050380035031440304000801401d2288048800340c4030b4010003040301c4101080d120700300c4a082c1d034604c1e441790716451a9034400604c668403d810050001d80002402c019030400502e1a4210034001a00621b40030f046003050b01905030400402c8d112010300610f0145841960340c0510803101811803541142c0e221140d032406403201400344170001c0003185034000c00f4011190303114030010031520750038101010913071280c42125500001c41d01d008600c248090020071014810b5280c2e20b8250140d035a65600c03218660001031001e211540d0a004c10219942c8512546202d903000b04000e10141c0c3c9045218144034036a03800c154000e1106006c80c0100e003440904911800c01e041c2800314145e0354a5071140d8094100d6480658069a0414032841000c4140c2c04607008500030381e43c1400c0030301c02c90 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 811735647 1250 811734397 811734461
    0x106020304030503120a060e1e0603010c08151801060206011a0921031e0d150303020307140a02090c031504020a050d23010803030a0606020a0b27010c03 67
    0x102c000382c025001002041c0312407000d203480651203210441d00042e201d0701c410b0000b00004040b03584072401000341503040e01307450400b8441580000f044002b0700c00c1d40c0140800503d4058041e251074a502c20585145621795a1409102190010700e14000300c04d69440c0c00c029995582880360181030f03082c4044d1802c9840e0110304031359465801410076500c0c0e206002c11a2881c0352840720f4000c0c1400300340141d0400034842d540c0350040d52100013141e03840d0b000141e040822114103104040380d10b9006041040003940204c240e6610300e81101c240443c4940308a1030901b854034442d002503101141004010303001140070095030103466845010101448140244803c134800c1e1180c00000c10402e02c1070f8404640c0f1070b0130001450718400040140c2d03003020508420110070030b800c100050f400200070010030b54044d205000003841c0c01d100820800b081603c40d05003008010300386201800c1d803130800d5407144d1500841c2544811152000700007903219140002e000f000820600d520440b8450340e00389138541c0c07074 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 811736897 1250 811735647 811735649
    0x22b0203010e012706060e0a050603090a020904080d0615020105070e0603010b1c06082803050910170a0c110a080316090b0d02030f0a0516050307020a06050a0605090106020304 77
    0x760052005a403c20055449071880080e04c6146200c02000344107020015018080c01845980ca85081c07010004040018116040d0002c6001d02000d10805ca03440400250003110717940c05480e220350039260307800c2124541c0b01d8441c0b030020f4142441800198007811343c2540f459020075900800143e01c0d006421100c0440304428980c2c0106e0610042c0108014500281016000421041070029030f8100c21010b540b030551100f01940c0241148610441d00448821543c1420344204c24510a117641c010740503000d440705440c002d8911403540d075401d60048442c400004001c0454034080d241c20b9003d43c0c09481c013a004580011050340305080b51010024a07180d05961015141e41103a43c1c2902d22044141c00c1d5094404010741c5142c0002c402d660a07004003c908207111015980c0d1510b9400420204006030112240c103241c10100080020034140661000400e4942169640c8803004102e240801d0390030050b00140c5407009000c148034265010000300c660980b0084601c0c0e80e548801d07600c2c1d02803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 811738147 1250 811736897 811736909
    0x4060506030627031b0601030203210403031b05010207210f0c0b10050d0c0f1401020a060b04022203020315060a1403100c0f031a030a02040f02070501022b020301 71
    0x140c03624032003404000d409290f40071486070100c0307052200e202190310303e45052412084c2280c100074014400e60405210450400c50102d5003045640724011034540b0038495032101800300520b0b4141d484480c103060340b40020307694021009544900541c1802111500340c0545400c00308010180183d455001d02c0b034442c482c00707941c0ca400340c82d03407050f84880707246d5a80248040c12081000f02c000c16180ea0b80032201580750300505040e03244508184464950755400d80001e082d040452014030704583c1d00080198155900940210f600460000494081e00865500c0c5030000c2c20303010004451110300c0c010104590003201107500c00c0003c002400c8000e0419907880350441d40181d0f0500c941d5074480440c070f0482070040c0c1119811503e03501c001c0e04032910a94140d000035201990140010b525002c2c00401c190302800410000101c0070020f0f40d120308440b0024040c40c2c4501d03402c0c0d402070b12541683ca82e40d41000081d50740703c4030407003501d107424428920358200d5880785510980302d64062007030b0303410f0342c031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 811739397 1250 811738147 811738171
    0x2210112031202040914071205011a18090108010b0102071508011211040f020d0c171906120f05060a0e0c1e130b010e01081504020f07060c0503040605060306 69
    0xc62901d00301d910010803128002c0d125020000005c10014501c11190b0100701c12101120605000c807000b45002d404094000285d41080018400c842e0011020706080300700c0398201d03540e0080c0302030a00403201c12010055110001000016052006401010311001c0903825682841e450740c0900d000c0d16001c1d8584070000c0d00e2800148100381d003c2d0302c1090143d010701001c0105451b450001015540c480c040206925004a024148407800b4050180003207010700300301008274028401c0d030000c0c43e00103020361000400d0200110300041e032a800710000d4420200e804c000a00b0f2418507207080554001c08503440d00c51b140000b011551544507810341c0031000c1001d0203551505400304001c03220304040300c0005104200300e4504a0f510301c0c0304080b680d03a003424040348034500080050402602000c4d050706001040041080009150309001c480c0042100c0050b100d5001072640301190280d42c5005114500c5d280594003515081000b952240b4801c00042c80f90741e031000705054a80d94191030002001c5 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 811740647 1250 811739397 811739429
    0x1080d09150c03051207030207020f0409021e0d02060c01231603090c05040911150c03040302150702211608030702040507140d06080607020c0907050310030c0801022101 74
    0x900c07030b12003a40380c5802443e01d00d003490503501c961000942c090b42c21074080381c2d001400c1c00c110304001081001d041c40403030b0104680e501d20b80100704a0060005540081080104040600d60300c07072050010b8690054038a50311000e1021900c1d0003884802d01e920584428102043c98100d8030910091003080d20b0301c142404e18542c00c2c03003940a81103030901218904101a0080b4030303902d6600c01c0240e22402514038a1450303a03040144180d142c0600007408014000b0000c40d00c40390000401c4030708480d415501a032400d80e1241080712240110b1034025480304400b204103d04001b519101c010f410045003e4900c04c680d101c240015031001441005a503400c18030a00c4c1c0035282a42c406940010241002407078140000007141183d03000140d07a0101503a56501809091410859660f00518500051401c9216240024800342c80140203108100700007000902160984241e04d00441c1e0201c101014161924403980c081e401000c2e08000d030158401c801501011110840c0341261450301d5171030309107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 811741897 1250 811740647 811740689
    0xf0a0e0f0c0a090506102d031406011b0221060c0d0b0609210a0210020102070521041211060d05070e01030c051b010204030803010b070c0b0403050712022701080d09 72
    0x80b820306030007140303815207001d810000003150b07c050b4818031400d50307400545003400c1d852402140c40301030505410001e0030704d403d045414400070702101843d0101d0382180c00000111220981d1000340c00d511003c0d000d880705004800c031502c40945070402081400380040841d0206009081c043c4565007607000441d40c200801210008052022400c0c08405654040030350340c010542c800080c00c00e600060398000340e0f14052010a002407110b403c801004518042103480300c0100398011030041218400d000840407041054103d203028001c4005030980c1d0300c0d05001036041008003021034480380407804800c1c400034150702c00d100c1c894a12540d41c8900f4201035054454003940490501c1a218640d8200700c0803011a4030380000e14003c012580061b40e4034511303403901a040c1e800c9030707001400c000014001440029404034091082e10002d101da004000c000f030000428480c000014440a010308020b0401500042502e25060301c12040c2120354440c0285000c84901c8550f00c1030b98010080b001d100000303 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 811743147 1250 811741897 811741907
    0x807020a031b0f05030d0b0d150c0512010306060608090606030d3e010c1d090403030204170105061e01140f0f0c0303090d03060303080f0a0e0f0c0a09050610 69
    0x141c03502c1c0c0c072401d007014805541c0c0d4403030742c5070144419145580301090910042d240c0340200503281c0020760740c003402c1c500c05540c0d0f03545079004844211103c940750300303c1401e41849103059031009800303490704070300950352420810010300030741c02900c0c0001c41c4480001d000c40340c0001e80a02501c3c02038001c00d5201441281154002e040855848851070200e0b0100010016104401c0401803048840e48000b0300741b01c3d50b036003191035400a080a00160701012001c1c04464094030708069420746007000142c0d03a0303190890007403043c0e801c900000e124410641140c460154000c42c822a0156085540d46071407015048d00583c4076540c050000d90000050001c198411001e00700d50580307200ca00d030070700a101103201072580040c182c040e515800401000b2003484100910081c10300a414100a02e81c1140c8000b00304001c01894084180384c0324002c901090210343c0302d1141208028140c0380512201d502c1700e615039a091010b54450115600b02003140303900c03882860300804c4014154104100000d5054078 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 811744397 1250 811743147 811743167
    0x30112060c140a08060301060509070903060e031902010b032e020d0f180c0b0406140c0a02031914010e0304050d08040e010311190b0d0b03070801150e070807020a03 72
    0x30010a9000c02d400c004580010f00344042d090b4130b4a041928040040c0b41c01c6a40070f502242c40b48014005100a582e00700a024003500d41006010460940e0380701c1051562041d1540008080c03489219104c5032390741944011880041102500e4503140100091303070307200c40c40c88980b071000041c8011848881d03580350700410329a60b0003034000c030303032441d02c42c07501001c0300e0110040050604c1a0503490080180c5980d4003809410030b51190f07414581016401018003400f160021042d440028903030b000e85008200c0c0294460303004080b101140d0303410b54820030414800500716580000d003007101e1042d100c18001c2d0568000b00301c0045080510b80340400c00da04500b1001903907404000c000204480d0800441e03a4069030190702c42002d4049600103202c08103074108122900310303804640622405040c2e42c03c64180e1807901c000811207809110009040c0380312a0301440719507107803940da0070307407c450b507150b01d0211101108829020765070500b003501da03144200ca8038001070b04004030a100203802060409 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 811745647 1250 811744397 811744421
    0x5061902010b060f040312080408180f280504140609040c0b0c01020304022707050c070e18011b08010b03040606120b0a05070c0f060509010e0703060f06050603011206 73
    0x1042c00701c01d6002081c01507120641808040b507001500b8028000450340c0740110032668508a805480c0c151548145070040508100c0300c403094402d40c1c074040d07442c0c040070300c5040401404d5141904210310710ba815181c07001c00d10744400d1080c000000f054130349441240c2c2c0c0c41c0f001745843d0202c0d0b40c032081007242941c8020400c0b1000b100c04000492002e5411001c0c1a40041100005a80f0304142c010440d4506200350701e550075a0840480c50a00b8074000d440b260401c929050454581c0b0308601001d041040541205460642c03d03001c200840ca4110710040e49054600000c10056445192190307402c20010464000302b03d2071801048050b402100a40d03001c0e01072100051201d031240c0e440c01c0c680f15402025030381703040000e0178000200150301c5016005032560030003404094996440f4111014880009000c483d65a00000c2800e0801c0d00300e400070b1280981a46c40e401e480f85041c0000742100c0c00c003114100d1a02d070b8007103803a0800c00102c1c0d041c1c426001c6d0782102e03030807155176190140201c00004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 811746897 1250 811745647 811745651
    0xa11041107060203061309110d060b03030c07030b070809071202010201150603023601050310030f050d080a021204081c020d23010b0f0a020a050604031d0102070506190201 75
    0xc05030440c80c0003070540d5501c40e000140e0349080c050100007034041c1c000c4207100030030b1801c0344000000748083d81c4000240401da800814039442070400300001d08516003d02d415010014030079170700c9207000c03501c441681d00c1a0648a015190311008503244101101e00c8001540024000c3c82400040003061010078414800440c6900000c03260880e1103138103500c2140440e401042e000110882c507403107800034407081008a0f1502e6100b055480503042e030010395906010000003c40c04040c1008014405550421410a503082d202c1c039100d540c0d0740300c0d8041ca10025400300302207000305805000f2581004180030902d503240d101c40d00d440c0b085600030100d903001c4004440401400184074000707060640181d420025118402d880b0490002020322202c10900780010300500c00d04d60340005175582148102043c0d40c4442c00c014040c4d01e00300c0c650201403d18820302d400c00c010194045105541603104007400c8204604072401a03940b801c00c2d0243c00d07407140090040014001ea24030340503070300758002c1c400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 811748147 1250 811746897 811746911
    0xf190209061e13020a2c040b0105041a03180a020a03171209010c0914060406050c03040801060e040201030c021c0f0509090406020a11160e060d12030b090106020c030a1104 75
    0x5240314800c0684802415004a4011070742c1d80c02600744946e280ca403482d00450301c0c0751004001e81c09511466454840e031340d201c000034010303440340003550090110301d5601007c0f01252031b40e08016400c103c0328654020040d1101d40002300380414075043c2d56034068010352601c2e003075035501c001c8032280d1a50003401010902811548002c101e0115010755204c100002d882e00c003451004103c0c110b141c120240240541c074041859803151000c49088484526200703850710b40659200e4110300c42c1c0c0d44000e42d19800e00101240c41e00383c01c40e150740550301c00d0300c00308040600150203903291003403142480401100f42030000d140324045c141c00000c03442540b400500d05481140000c0c3c0e074080940701502e18a40c0440e03810007094103c042d081c100c00c0000024000b440380082c0c01e0340c41c00318500903e200d14840c0d5011440e40d40750110484c0d20103034000c400c00c1d02049004001002400b29070202c9114001000000520034004560242c001d41c014000d40401b8a580e181c100503040140185500305a8440e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 811749397 1250 811748147 811748149
    0x2d280c08071101141206060c070e0a050601030b120303040f0c081e0d0905030601120609060903050c0d030209030a0209091c050408010b0f18070c020603090f190209061e 74
    0x30010a445060300310201082c2100040c0140c4000152051003001040650710300320320b04680fa680010203c4030260303100034000c90103007009030310b500c0721500f071054000303101c07010b2410b8001ea8840c04081c2d0b000c00601c0c81a0080000800c41149d42c00c10a410400c04100402c090410207211503015454160103503944036007031b500d8035403c24094200031030740c2d04c44119202c2c024800e01c4440302032480c001c00720b03608100c0069260782040c482c651608120312200350030031202d60002d0044030b0700602d0400c03d006075814090250707405141d030f2842c0e178050800c0410311203009100703684440f2000340080281803400d07400d0100c82c08000e81240a1445500c44614404000c1200481c1114180e43c80039166841c0c08c61a50039601201411072281d858501c1d0301ca10785e10380c5040440303603140e0218207034a1500d40f00d4060f61008180400650881400000c00c0790760704000800c501e44450b03440448120040c0400341140000bd0344000075880710310680421401e2424a1140d079844181e52410054490540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 811750647 1250 811749397 811749413
    0xc050418200a030902040518120a0c060513050c0d0b07052206020109050d2a0809030a0c0f0603060f032d110108061804080307142d280c 60
    0x100c2d520000c0e07100c0095108508190140340e40040007a0b850030714250340701400c02c0d01c4000d0000345900350000031500c0808a480f07141981c08003034120b03400300b00310300b03041d0744207000b185008c401640c203803050003030b6810142051665061015003083d800300030741d29180c0301241c565011025001e5064003101c0d0130b250200c181c1c8000c1004000c260000611801186000d500f040c032007541c41d40900c444040c0e8010008094a03004c1140c400708440e1103a0311600d450b11005074060000d156030548541c1e449002004000c0082030269000c80028145540da00d0380c044091b80e5a80c00382070311005100408200007208020003001b4000c10214174003203601d0601021520310743da81ea050360705000308442c900351960080441900841c3c180c459244809003151400f540a80240c001450300d00c0c0040003e889074070400e11048a421101030079959441442030142c000d1510394808191540401c0700c0400381400703001140d00301d122114074455240c00e4041c45140c03010b207400d001380600c901f00c806c150024a4607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 811751897 1250 811750647 811750657
    0x6030b04020c060a0626060606030604090f0c0e10060e0d0602190309120503150127030c0e090705181923010b16170702040c0801090c05041820 63
    0x11000010707510b07203050009821460311501d104825120002d101104a802151f0140d01800036100107541c1c4d1650004540101403142c0d0203480c13201036580c1102007242d0032100c0c1d4112a110442c0d401d881c1c8130b44021068401d881e129103004560320075507048060800710002285240554001420101e00001c2502c2d01400303d440030300046d03a9080e07074804004110310344940341010391512a0031485c7c04601300400c00100c20140d03040c07040000d1900c2901034024120080304246140c0380c492240c0c0c81c03405d0b0803030000c28003071f00d00002111000200d106400113514011a4402031035a4141d101080c2140304101020780301d41e0310101000311046000100b0701865154504241502080b505240c01c0c03c1482003060304203901d106420007144041c8061500e10780c10361608412a42c1c0d410348c4940300015903100d500b20003504a800c14103030b280f41d250071980300307070495004800a110640000c00704135071074801c9000c3d501500708003074422804658142d0003008000c8040d80301803110b030100317014412141c01c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 811753147 1250 811751897 811751911
    0x80603011508300328060b040e0901060b0a0f020705030604050618010f060f150315050f24030702070608010e01210203010e03040812090604060c1a010303092d06030b04020c06 77
    0x700c601000590031a0170500c0d50b1100c40c1203c04c02210341400c1d22080180702d24411380c405001a0700100da140342c020b44c014001000d100030016980c03212000040c002d5221044482c0c0503020708600005e4905002c10320b03601c15a030002c0609015903821201d2001000148251140d030740d81c0c2c04008500c528544603050203888545140c0c0761403890070945910b00705495014104160902d540900000992203410096500c00c4491110450100e004502100340721041464905040540241d80520581c0198040d035610740c2a514003546a100640d8030078401e1081c5c5010300100300040040c9400e0440050b03070301c10b861071081c1d446640380d00040d08bd03601c4031007200e005410020b8200611541005152081002040080e0804d550100001c42900440c4a0350302803207551023403c0d080084003010f9101c492a440e02a689030350b12400e008000358058094148008004044030b0021002004001a0036449210160186040800440107000340c0d40e145d42c0c0058007070101001000003030000b5881241 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 811754397 1250 811753147 811753171
    0x307210c03050d08180d120f09021809010b030d0e0628080108061305071406070c0f0801050c190f050f0a1e0f0504060f120203070806030115083003 65
    0x24817145e842100284044201c08540c8003101d0207503105c2e08240c1d06000d04100a41c0010f0b10401400d10001400b01110002c0d4050b0300c100c400c074801c01d00203241c43d00948030366008005640005052541d1164030620a034041a101c0f04a40d07164a00b1800034100c0d4501c09c090b03c2c107070314100304e14002c0c1c003101c241145003c20b09100c01800500310400c038141d4040d2041c207800d50001107a845868548046000c0c1030000201618095103070380f1840c00b26414680c0c40a078604a6540e20180300d905050705005880140d4244400b05040304c04007016290103201010044180313208070030301514845551640c2d081804800d0041c4664841208007a143c140358644421441d4040080202c102240b0030404c5824000071142e00b80c0c2c0310340e0100c00d84081c2da030141001007040341016401d075041000c0420081a19000004100c01c0c1644042246d0140200340c00030f00645072604590f84d204003070390044103856400001d4006d41820f42104d00d80303008000d0751008411240f141e0007248184e000311050399a42c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 811755647 1250 811754397 811754401
    0x40f080d0e010b040b060a0c05070503240601050306090c0306220b030c100c031211071101200c0f0d020d1208010f03150504060209130501050f0307210c03050d08 71
    0xc102030044216412044030204894417a2000044050054030390000c2000030320000c400c10400100300200150500804a40c09255184840b25240804d8440035801440560114a4035405142900d018040041001c2525600c0990510058200a000a60000000c001e07515914060500701f04000c403842808960700074500305240c6001c4400c1101c600405803c0b00c9071003020f038004094020b996152926a90308280308920308054030071222000710503000054a0420403941000d0b81840400030b80b00d58403044c814140100c54080c490b800003800b508144101e04c0c1c180361041c4055400c40d002845140101800d0b004070303141c060764040495447e05030141480c0030940180c4418010180d0364442c0789200e003981d17580035000354a070055450041e210b03004141005690f4050743c00003440500032490b114007809030300019003400e115090041c074000104c101e103410042805c10654a0815921445009001d480c00e81158500001d0324420f10500000c00010400e20100240520541c1c0b901514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 811756897 1250 811755647 811755671
    0x73903050c01060b0c10150803040801271a070909110d0605061c0b010c0501150f08010e12070303021b0d0206071707080601050d0f1d0309030312040f080d 68
    0x59805030400c810244d0b06000544502c60b0000d0700380c1e58008400d0010032917184412404030a0325803074000076064000401c0c04030340d060b81540203109000500d1203c14a0b82415400070060300780c10344c0e010f030100c402c03100203002d00c80c981c1108503001200c0d841d00844095403803400324200c030414044403c08030f000040009400405001d05006084201c0d1b030981b412221f03482c0c042102503a004000022a19a54a4056a07001c0d04040404a8100c0d009000c03880c81100f41038101001c0f406500c20138482c5003070205004c20148610002c030250b00c0020000c401350014206c03415008070341d089040507000c0040190160310328000303050102c41e64004142c1a0f403c075070041d0900e1002002402005101c02c1c81e2214949905107850704125941407040b00c644640d001241c1d1840b80e00300d003000b0141406440400f00c0b42030f910001d80000a02c5244007400303000010103449125511046a25038410311500241540c030200f8250080d00c00c040200010711035550320781607a003004400300042540d940020041e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 811758147 1250 811756897 811756901
    0x41701060b03010e01030b070203070f0809030609030a0c0605100902070f171204021201090803130b06091b030c040f030f021f0210090606080f030306031203073903050c01 75
    0x5030001d03003511411903040101051442c4814403000e01400704440214250030700a004882c819900242521040750b544d0401111135804954081d00900c10040014403458022080d40c03d003203c17907954503005211686402c400384c00c4c00342c1217654054070b00a0000309800c25100405606d40300d186400d05480b840d041c0030030740140070044038842d070400301f00e070680d402c0303010070394030b900560440d161902d0140e03840f040381c01400700c1c3c3c000400c2110300109000441c0710203c0d07000801445070542014a0799250140090b134101038032880c030880c80e0b0f149201d032800c00c0d0b00061544005080d1510382000e40e503c000301d6203807410360710a840d5408080b1500c0294145180e40d1880c0b80280441c91170b6500404e40000e641303914404559103202d550f03500d9101004555000b210003406210308581114150003500e40d140e5100f03445c094804c0c810050200b42410086003524482c640c1c64440d00c502003c04e075540c6d25024000300100d0b003c8403030001d070030019402e42c0780d00060319406561196150003111042c207007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 811759397 1250 811758147 811758149
    0x120d0804140a08040909030e090a0b0a050117070c0215130e060315061c1b140904030e060d1116060605010914060d11030f04020a05090103020f01080408040b04170106 73
    0x22034010b85000d20108030840304840071240c0542000560300d00710705084990041b080c003a5a400502881130094400d82604100d010303540031250240d005948100649424003000058074042e80d0303050020700ca40d070042d01c86100306030002e0706401e280090349031490040d600020150401005248091041901c04c82e0040d070300c0320042c0c00030a40c2005042250010020060440d4411400c1c1a150346007050b0300508052040d51144100c101b00e12850300c40c010054113401006442c1919041d540d940d031400301842c0d80102d8040c4c8420304c0c01107004c001d0245070390003881075044561711081031000c1e80b92040008c005925400c4c2d01d00021690758900101940d889600c0141000303805c0300144007035a03180c401490419802c440e034990b280702603005600604844031081c0404200401005400c061742088948604c0c401c440040c40c0540301c1040011112007800080d4104a04a0700382c485540100000f540182c01691081d082641d02c0c4401102a40a600510407541c00001c0640340003c007401018 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 811760647 1250 811759397 811759433
    0x1020a0206010b0720010909061413060513020a140c06060102070504020a05270a0303090e0105310608340602060415020717040e0603010623120d0804 66
    0x41d1515032940c45c2d0a100c01d041040c0200c00303881d5480140712030380c01802d08800420260200f807200b5507030740300b194030007081c034204690190b8000f84a9030120ba243d4402c51007a2031000304440e690020441c03408000350042100901030200c5050040c1ca02c8030791002034076a009000c0020f040c81d160503400241000e10a45c04140039174018000081c40070b030000165100c1b115400014110581707550ba1811400c070803501c1741038000360000004414181d001342c02c18103039400f8030340308229a43e891043c4014215115271a0300c248480c0026949105000c090540200500000110700c0603241c000e02c5040580c0d51341e071a1401c1c24085140c101c81a0b10b0312244081c00001e030a078501092522074080d40b645070040c40203040c5e8400c8042c188005045038160303000181c1042c4c85542d001031000d1490758550003400f404001088000000b9114a8140100d000381c6520500c04101da0141da600081c0c10600120210b6002c5125000000580310402050029a249585040003420241840d09800031240c0e40a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 811761897 1250 811760647 811760669
    0x30105040b09161b120e030f0a0308010b0304020d0b070207170705090f19020313060e0f070501080a060819120f05040b03040c0905190b01030b13090305071401020a020601 75
    0x3101c020289501c203064203a2a04008502d8a14401044003100d212800107001e14a45c06080c41c002e070b80101250b0341c0c042d0940883ea200501d928510b507917070302c1401d03000b070019101c1d20051000744503075000380d5005440030f4800c0c0e034410032a50303034085011342c21078641005038881d4404000c03c1c41158554a02c45200310040c0203201d003018007103007a0b070340000c0c05540c00941402c00300740400b0f05c1b80b100c005500c10810b011512414140415020f06d01c440c0c00a50301c807400c0900012410034040780d4907403407141010003080c07a20310b0300c8010740380f160008000c8140981e45040c0018404800d00078108002c40403c2c003601c0d0318a840c641b1501031a29203807901c007040814505040710030b42000c12503060b1a540004e2070740300d82c3c176840c145803c148560441d442d52030800b010f0000c0400070702d404584180c5410b038288040705c104401141140c08906960b6844070780d05020040140e400d40c0716146550091034003a203402d0b80e9440340f074042000c103050750036669400505410160386c10300c582805000d001c080 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 811763147 1250 811761897 811761901
    0xe0d0c08040e0c070503070516091127030d03060504050c030106050703121503030c2f0d020d0206030f0a18021f1709010608060f040c1226030105040b09 67
    0x55011580154007403442804038880108082e0180c480c00d450500f1750000840390707990380d01e1400c01d48841c3e0700c41c040150448000c90110743c40009010b2210410041030020342042e1404852105d0450302d001a008001000c7d170880489803000e22001c80f070102d5946000c50028a014280801c940009010340450383c0c0600c01440344650240441c0c085540520340010304003d9007030742d08003c0003003c1861b054410f030f800c0000304150300b10851030596802940e0036092040351048400107850007421460381042d251729090500d1404441e1210864000740c20040c0745001030f400b040d665407042d5605400c503000101084064041c901580202c0040c58521844c440c480b540070903444090109150307040c44158540c440341500c20380498030307210b8110700001d44505110170914005c24480c0541d40d10350140400089901008012040c010343c0d003c41c003031501ca4034050a884220760460b0044900c102c001810310380303140508128090340310380500383d0707542d95140030308001c00c40e080620b00034003952040302 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 811764397 1250 811763147 811763153
    0x4050f04090b0f100806010f060201050f010501021c110105070e0a0801020702131a0904080913051e07090b03010803090906030109150c0c02120102130e010b030103170417010e0d0c 79
    0x301c5a402c04040030b010f00383c60711941d1109030b40103800d4004c0b1030340d84543c100014440000e11030110480359550002c000365216007110315504a024021340b405070f0700c54070881102004240301201d8801c600d280594000c07180180490948109441e0200000c00024802070741d4a440d00d03800b4002d10711400210301c0e1418950204860802c000c1c42140d10f15030328400040c0844034420249802c12008040c9442c0340740910f010b1206400030300050340585c1d100201c144142d8518480c140c09815400c1c01e910031a6915041080e400300000d29001c00c100c0d58400010382c00900a028501810403200590340700c09981052041606000f0320340c5219032b0500c41c621010a00b000031410b00a2101240454950082ea405840c4013006c81002900118104039541c0c110a040d4080c182d0080030502006400d9648c5d214040044405c1c0180c03800103604200400002d0360444508094072100c0480e1800c0c2540c80344a0b0182d070089542c6600c1a135101c918641c507903101800340c164205c2141c2084401c50321a52 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 811765647 1250 811764397 811764413
    0x10212041406090f03100f150308030105060d02070f03050d0c05040e070c020f130504110a08060f1e01030b07140a0c020609040207080c070609080a0b220c0b04050f0409 74
    0x58005802078000003540110f40d200d030b100080c80d95901031304070f5010040484418004100051001c6441840d000d00414040340c0300704010112504151200e0071a420002044074681c0610a40e9100740d508200580001d0610100302c1c000d50f00030384617191520700307004541081c0da110350003107000c10908000070303c460240805107507080f039024644484c0c8000944042840e0a2404200d2030703015003042098171803050039402046c81103104460070540404035905005917261035000700d02d200d8015a0001c5c1080d82c1c00a00940d01c030000c60840a072840345034101c5a180f03502a0003d1b00c0a006c0d2004201d000c40e08051226000e10140700b0151178441040c00043c00c1d120070880092180d50005010540390303a0781d8064900054000641e90354560001840c5503036052544560320100702081000501c2c10000b0840d4201150030146003d116500c03401003508603410010403000211083c0642d00110307034030003442009420b666085940c0c85082c0002c01420510028150b0311807800c14030300301c2c0094011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 811766897 1250 811765647 811765679
    0x9380d051e061804150908030108031b01020310031403040513050a29040c1106070507211706031911030c2706060c1f0b09250509060c01090201021204 66
    0x7114200e00780c440e17000024050609030034080d140040120020903a04400300007828180610b41c40e021200b044011200d090b80401c5414a91800c903040c01000450b0f8915800c540034000c83e015245032030344607000181d10509006007128035607950010810180010b2003142da0301d00410070001ca440c500d400980c0d075078003036141819018030344400c440101c0501401c1000c3c3c0036600c0300195240b900e41020014196041041c040c1c620440000489090401c0315400c0402c03000701d995941280102407007603020501010b0b1103070782c06118000401401d100202940c48040e8413800d22504960040340c1054905114141c0061007040c14800b4601901100302d1701e800c650300c0c4180c81c0c1d030031039441c03000099482c01481005001402041d12020010b804510308441c0c0b902140c2c400c218100e503090511942640480d907508001c07444010a4010700c04401b856130800c410b900c0c01c586412241070209030b10b9004400c0c485140d81d144d403440c1d4110360b0144400b2119001241c3c00a04280c54000340740b21450701 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 811768147 1250 811766897 811766903
    0x121503061906091d150c0901030b0604080d08011a0f03130501060f091b0e030c041a1203070c050906060a0305040503040302060c0d09380d051e061804 66
    0x2100c101007807258581d80007000108900702d41004408075101005840c42c500c00c00204076170066004006000c0c400003000d034004c900c4011200e0400300082e0041d001011424607041e4040818840000c14280070011020038150f25a00d4100a51400c01c085034140118110105030050610180c00029040425a45d00002003020b9a10401a13424454010240c0750054500720804a00100b0f201c100f41c0c201d840c09001c061501c3c0c0c08070034805412a22110035880066144c2c002c5640700ca541d103002d8028400f4046010000340c100900c103800607240104411018001c3c0e040490f21409100704034070341c00010101518a03c080389030401c00a82d043c0314802d540018180d40e03034081414880c4c1042a5006998050100703640c40e610350340d00710350b5802a48007400c0028110040401d0428444c40002403040c01c090040e0407000d02c0f24001c000300c200c064807110001c075091100c0481c001d02d50091501840b200c0c0d4680145e040c034403909500422009020502452141025490f880e40999075642d010750 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 811769397 1250 811768147 811768171
    0x10e04020714070e090c030705090a020c0f1c020115140603040c091e05090a05030f18270c03091b030a0b07032403050616050706050c12150306 63
    0x50149040d001241111082401c64403c0c0d00300800e104520101140c01102c0020860350450507402c20540c0e0b40080d0302486030401c1e84040030079a6001c0c15000b03001b01141420a035600e41d40d40021041ca8000045500074410b1848180c0b8202a0340a02c200c080003042c6400700c1e0312641c205001c1403465155043e915005000010000e028401c3c20408503006c0c00f030344c2100340141c030b0b5421130002600755a0000c28103580d103408046090349170f001a04069280c2d10101030b500b040c20600c0c104c0d5040d000121150500a000d10381030072213503030700384200202c580a64168400d403422080c901111180082c080b0000740c0b420011300056400c00218a61445203120424031020510004030782020070320100108002840000c1c440b145805401c0300c15400c204003686107802890a07041e2205074220b02c0081d02540080c4d0210f004d41140f500540c1111a85003025460030741e865561004a8004031078036603103203002080d9225214000c80c0600e03082083e0101f81590545000d001a49a02024111032130843c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 811770647 1250 811769397 811769407
    0xf12020114040f0f1401053606040b0403060c0807210b06070b0a0e030f090906010c0210090504052508070e100e1003180b0702030d0f150b030105010e0402 68
    0x4040e40032100941a0340031101c02a558840e003c0c8990722150107400d14009a25800e00303190b501c01c0301030701c44501031100300a450320090324231800c0030b9901c50326107601401c0e405000c030000d40b120001030004140d10380507a42d54500d54107081c001c031100c2c206080b0404c41070f541070083c46039004074600e030611100d4600c00140720b0b0044a00700108400c8580700d42245010884000740f090700c0e240c2e02e00c12080c80c1c83c14062800d101c1c1400b5200d201b1200503001845042c44800210704180c107085610080604100c80400d00c02c0d000a040c080c00c4940440006051440030701903801c203800791039000002e08691980000260501402212503c8038050801c25260002140d96102d100504030f401c3c00a440300c00c0322070840600030132561b5807254250041106130000c10260b80709106644452804207004101300880d540e40c1800c2d00d10180c841011440140206000c0f00114032468810421400c4000743c045e0b550100390380d0142090b07100c0d420301d80050004000503604609100d8000f40102c40c01a03036a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 811771897 1250 811770647 811770677
    0x20a14120730021c3e01290a090518070609031203020d15090f140c0a390203060f0c030105130603060507020a151e0e0a0b0f100f120201 60
    0x40ea0013105600d03041c24110304c01e128148003207200e64404016044841e0085032007852203087c2c4001d2034522014240184500c10310b6240846c0100c01c032038000f01864200340d616150f12041d035400f5501360b80c80000050030489105070400199005000c00d050a270003462441e00e40e21400d00c0c12110340020302d41c0000d000d12110b00f00d68050100c040c101401125030079295440c3c0c50052001900086c6c889142403c441660300c079850b0b2841c0302d040e045030702e00e29103403030031000b280d5500c62511511010701d410004506002982c034120741d05154000d092030311411540c010149000380103054480302042140600c880c241612049034107680040c3c5804038202c49a541540007894103034000b41c0031903d040d05000403650f0210b01521454015900480c00b043d58100d503a00301c40060101030700d8982c901450100b564400d801c807164040da40030a5414400ba6501c43c005d01000c102d440d10814210081008150120220000b003d48404070550080354185045000007d86403030000e81846003008060745a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 811773147 1250 811771897 811771907
    0xc03040227040308160903020d080f120903092b0210020a0212060a0e030412020d03030b040c09090f090309030f0c03150b01140a020a14120730021c 65
    0x3407101c4400100905180a080040103004141c40f407040d00c80750300c1c0790120300c244142002e10540b03400074000c0700d1003113040d0740d44015548880364a1888182c11711601102403610303641640f160380e211014590340e480910030002408d21810f031030500c1020344126000701c0c00c03500316a0041c0c40d905841000d41f820341684168900220018002d5020038280001528040003103901c03409400703203241c18000211a0f000d4151207000d540134040440e040b040561f070251400c00d02c80644240241000600c040d4802d010406607003845130300b000450640b120400c2004000d124940c0340c55a0b103401004011303565940200f4050b4117210192800260044207814041050180401140d00c0918410b20742c22502240700504102c05515003c43c40c0c3e071346030b440c07080c4102c0f00b140c2d4454150b03406450f10307050b5a41c402e42e4a040210303090303445200d6074100a807074500440040070302c0b80c001c2c0c0400c040080c000f0010050018504088806070308042c090b165400d40020300019401032400b1207101001d0340c0784086031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 811774397 1250 811773147 811773199
    0x408120403030b060a120c0206160302030c04121b1a042c180712080418110d14060a030203070302060f0705010c0f270b07020409022e0201050c030402 66
    0x40c0c01301002800c80d20300c903006030b198005411224818040b01e1100c03041640c036039004450031400e450f125401740c002c581c8240d009651040f550203e60b800c16444070b000941c03120f8003d004580200c0e102000c0700c010040c41d0301d83e13001008c0500940380e0440c0c04a824610500851013007074515100c0e004d00d0300d0918403120000035425040310701d4214a180c6840c0050b203010300c411500c0800c2c01100808140d81e90210030140c1c80a40003410a0311742441c3c100b0382d800c941c0c1404203959985a070384500000c80311000d4000c041c1845540c102180303070b03010403074503440b401c0c0054192881410f40d0241000161404602141120f80468085440f4241c40e030010b81e04c0c0c030a903000140740d940390550003c2610b8000806ca4101c5e91165201da00310844814840c03000300c0c3c40c4102003500c00400b03900700240b401c000c00420b191880a080860555126801b2440d09590440c0c0c603440f03041d5190110020b8060701000a01d40b2420340b00030f02250070800d800d01082c0c84068406030140400d0382d11f0610303440b4030f880110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 811775647 1250 811774397 811774399
    0x51911070f050601030209070e090114031504050f0d020a020a0b22090212150a031104060b1305040e070e01180905030a030506040e1b10031401080c01090605030408120403030b 77
    0x402000c01e0345041038a0321000d002c200d21682c910000b03e030309288a0284da0189200c05080c00340583d00348984c2c3d010340c4500760101c81e80b520514455604c01c400d28a4201d015a2149004105135100c80e01414109428050301404561109104c1000343c6d4032600401c04452408244c150350715004001050482e8808200c81c1c0d274503c1407813002907418070310780c018500d08600000d6061940c5404485100403001e450085900044c2141e040c0041030342c814100640b80c1004000060107903031910040850b03004980e060380d404004180401140c00c0c01d0184a440f5070040340030b04056800c00c0c1c507070000c040040c0501c01c950398207801b1441c0e0703291665010701d41c0d06800c14100ea460382518440103016150442c1e1041c01181040d9070803030540c0c400100b0858401c080d40500110800d40e005020319042480003c000700750700d0341c0075082c01d010b804545030301919400001c1c01c08100842c0c009084d001d1540d102d4001c1140800c100800314038a4029034000582c10074000603a600d403400c1c210040e0028181c00d07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 811776897 1250 811775647 811775663
    0x71b1104150e0601020c010e220e010c110c01030516050f0933040503070303080903210103051236041e140c03070c3002060a05191107 59
    0x810b044802100e981d215200c00d82c00c9444428846004650322100d03000d6842c2c0150501d44120001e54019014034071a0515200005041c2050141c190075280c82c0000b14004c140c100305080c2d11350f8401d01180b6150242801c040c4000d041601d40b001303c0e0b1022041a104004001c6588280004c9a1040b82c494500003003102d07181c008840c20400840c03611000342c030b46162202c84000009054001620202c4d90b0080180a2161550b11f00740d480140003004866a40001c000040c4007690410307000c1184421315451003032642c1146403107407500020180c2c0600701401070040f500f05000070340000d107a4804000e162009221001c0e034091110307160406069004e8101014000f1480030030b0100706040a2410060001050003084a003880d14180c0780102c0301c800c1080010b0019000d14104002584a83c00705a20008040c507040104034020b61740641c201c4040304c50700c0711030740c3c100502a04048450300c1002141407001c12841c2c00c1c0003154000780d400317495811100d00b800401d8123661440d6040362038 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 811778147 1250 811776897 811776899
    0xc060d1a0f010c02090c04090908030115020f030307050f090a0e01051318150e1c0f0c022803050601062006060d0209090102090918010e03042d0308130806071b110415 73
    0x10182b4aa00300740992901d00341800521004c25100140c26400e028106020710f01c1d43d104c1800803107043c2c0c45207031550584001044800300c40e4581e40c00310300007082d043d030103102d06506100c10081c0280491003402049414880d00d1100007403a080c10488042e80420b00c3d07030304c01c0a1100200060918000004420300074110389091040a410343d929079404550382d150500c1c5403800b41551940340c80200031b90024201003070803440c0141203030300d500c4007483c050f10b0102e0300381c0e05c3e5030703ea2400900740c001c5400100201f0b811004500000000c0c0543c403000c00160046141000c04151017800203030700640708007107201c00b0034501d6000394100c8036410409002072603a032601144009076122480c01d040d000f0361a00302c40b407030000300100643d0142c9170010b00c11a550000e810410f0039400106001d4582c000048100100080b5407000910455041c18400c004c0039140243c81c45c2020300040501c0240311b17003581712070b400da01c40314909640203134040100641e41e200700c00460001c05010f58016215042a00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 811779397 1250 811778147 811778153
    0x20306090109051606170a0603020d050a03140405030a0303151a121b030703090501020904020a210e0c130605120601090c09050f10020c060d1a0f010c02090c040909 72
    0x3060800714018000c45035411603900c40c144e2202180d1140c0c030009010074040403011b2401d40e60031070b0032102c00f10000c01d82075280d4000440c0031a10706000c0b80d02d64401403030a0700300b603040f03d140343c4070506407500c050070a850000803d8030307078600746002410181e4501841800100c0c0c42e00e0364000d05507045d4809251200601220601d03403110b841c0d04022070424000070002c5507860341d20a5950803140d002c40c1076803200074007034000d0044004120b82c0c0d55000c0c0a03e0a03a9200c0b071015080981c011750302c4440100c0b5000d140054861418a4018010f00f007220940701541d0000e885d0200d17003410360f5000140d100f16202c40004240301d4000f207900650a20000b14002c60014029043c1d074201c036410040e0b103a0030307c0c0030394800c2a2413203540d42103100c00344c02e10064038084c448640c801c0e840d40140ca050700d90150000301d550748010201c24000c1c4c0e460028400030603c01c00741c86280f8006482e0350001022500020b81207140d035000080c403460b640000a4000312210007030384c0052124490500c101e8407a1301d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 811780647 1250 811779397 811779401
    0x110a0801020a2606010c0f03112b02010e070b0708071208061309020a0b0a0e130f110702092a03090d03390c140d020c18070503060d0203060901 63
    0x603980401c101039503d01c81c5005800780c4003070b0b4000c010517111001464500e9480c001890400324080c1c0030310628000c5005280000c0c4000300f0400d518034200d50060355403003241402a0f4040741400116850040c1c0e25444001c0010f44006171042c800100341c0b61031940c036001c9094441d01d1401001101e006407143c0a80360082c00d20740c0038007011a1503d5148a5007541142106c9050101a6100b00384036001c008040c80301000f031041e000c05240c0a49141002d0700403404000f16505403e01040d503600c0340d03121840442c8030b42801c0b04880180c4603e090300c181c00103140c1001c0503080b455140c0c4d00d0416404124200c05403c60003005214500743c5a15000d0000303500d0f0342c00403602c6000b090410030107002c600301820070a103281904400c40b050b80d80303594407500d081e001c004a80b0030030b20244581d02404906e40f40314032820040f004005109403070b6a035400a082198a44100d0300601d5299034542e40190b00c0c5900799807008107490b10640b01d40c0c4000020341844510f01b07000e505401024140800b012041d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 811781897 1250 811780647 811780667
    0x30801141504031a013f06092a06020601051e0a1806050603040f030e15040306050103061b020307080705070302040e01050403020c01140405220e06190612110a0801020a 74
    0x80f00c01030416030340c598000030421041c028103000e840c50340d21b0004503a2011030742d0011042d503d1010001150455880c403045517403071002691184040640705083c0380b50050b000190036503c1d024481094a000e00107551014103000d1544115070000c41c60b1000480025604910715005000d2000990703105241d90350520b007045400101410420082205e0811800302d038040d0782e20000912811a89032021039070444400318481e23110800c001b031b03040c81c50000c0313003d0f00141d4003882c0c00046952461405da82281c00206800103810089881111504d40220a55180030340004d10650303201a907150590505106410003503000745455140034510380d0560100348164800c1c2c085915001d60080159820190003000004905040000f404a030034615444040740c01e480707184240c924102c012000a690442c0e20820140c0c1c031035401c08c0301903214900b001083c1842c402c03040220504010700e000700024000000340500b28203101c00c101c6074584940e018010108503000b10b40358200c000d4020110b80030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 811783147 1250 811781897 811781933
    0xc0d020f03090c041109061b070605091c03081803090a030f1e020609040e0f0a0b1e0610081906080c030106051e01113a080403080114150403 62
    0x100003201903e81010300c242d0641e8004c0500c01420b03c1100d000708800c9512115050310480d00340b03a000c00110300104018006042c1c01d03240c040e29290403000303014440d110880090895288800010082500031a09a81201058583c2d0151120b196101481d503c00ea840350b503001500c048001090244007240000e045100d40c40313800054902a540311808180040c01962080c002c01c81d141c0540f601d49d101c0c070341d050121820b4401031441d1441c1682072054507c0242c0d43c3d11a0300041003040c2c03088000c041c00e941c0d10314400c010759040580105065414283c101d90038050141e001c5110502e03903040400071010040350501200c0d03107a040181d1103401030011036019600340030020515107420001125101103100d1000f00e05480d0324011a140d0122881640c0c00d40a25554452038038444407007480c91403489000711106848402e030000c0c00444400c2c1041c2000b4241081c8400a68880c00700e0341150b0f60380340320008802c0604009040700020b0f030100f900e030740c000143c00810050b51181d40424800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 811784397 1250 811783147 811783153
    0xc0305120a1409030601140d080711040b15030403030f0b03100c0809010218060a0e090f0708071d040c110f010f150806071214040807050c0f0f090c0d020f0309 70
    0x2041e82c1c81c1e801d1501443c4002545078024200503c803203501d041010011100040032100360892a45850b0700d160700080c2d0580d40e00b0101542c401407800d0038024600d8002d01924805461340003e0601000350001500090400d5114003081c0c0031034203a5042001142402416038860400b4a04440000d00074940000041840c100000304e9801043c420b0340c244d020481c94204070804298100f1240c1d500c004001014020703240040c2d01c680e04c500400b01c1c0301d442608150001800c0083e0f0191918800030100d00c10481800c0d450641d0180036003c071080c1c01d106540201f41c48065180c259102c0d450b101c1c00d44140e1240044001c000c400540210300d001403104820003041001103803c448188207406030b503c290b4400d002084c0355910030a801c0d00c803e00100c5000a007120f40300c058030007035001500c00742d80c10b80d004941c00c018041d05102d03503411b02038111340442000605001142e1110000820300740f040c0e214a00140e0036a1044040f42c04506803000110740e00c07000c00302110f10703540050f00c2000d0244 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 811785647 1250 811784397 811784417
    0x60e0702011e06050f0d1a090a0b0f01060921060513030e03162702070c03060b010801030203120a2006040b1303080105040b03210a12061805040c0305120a 68
    0x1c0b040d00c103002c240d441c0904051000100002030240180703c41354121440c0501409298010b0030344001c43d406001d08002402c0e186000e0305000790a00805400b40500d804404010481507400405a604503070703011030f40342c820b071001e8081c2c1044a400d246000c2c08040c100404c0100328942014085081e52080e1100e424440b81c55090698509010840704e0aa0781c0301d220911040f428441031400700107082d6141082095508030100c180d8201c81001c0791568641c50741407040041c64090110f41603020318261507030358910380000c0c0e82c88a01c60f011001c0d4460004a107440c1c10b20030380c00c0c88241d103400842000c50356841840990303a00b40880b03007951402c0031000072034915400800010041601a9a8681343740d0812041000030025501d685500d44540541d44440700c550015400c044000c40d40101d8680340741820180041c4000704131940f00324078156051200d0b10000c808285400c20307541000405666500d402d080070009908050001c2c46000100310060900c60003c001285141d07032104014 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 811786897 1250 811785647 811785701
    0x2040b0a03230102070b073c09081b06220f14060f03071412070305060f03190b100b340519080d0608010f110913020d060e070201 57
    0x740105c02e0010b00d024021070118040c80c0c4241c40085000307004580c1c002c021100840722620003c1c401207201030352a0203001200000f030304405404010200030000d40074070f208948925003448188070509110742c5001c24400d440c0388112140b03160701c2c00d000c024054405d4a0781012000031503070344901525101217400310120fa007001c0b41030b07684407c000c500b007505545990109a4030049009196515070f0010b10610340e4074400c2912081c0291256280000e690034280248120501000c904074002c0d40510084c108200703491000c40b02017070b0081c0c00e66400d504c42201b6401c18241960225040359008100d01c031030031082d08007086401d0000c0810602d402140044800c10b01c203203d80c00ba010740c010b140b040729038140100c0c2c441441c3e4810500316181c00000503800d02201c5490700081c08581d50f82004400203140c6106240d006c04001803071508110005001070000e40040030081e4074150042018180c01010703400c01e4018281c1c46009001500e440745000b070003412050300b140a1069a441c5103406 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 811788147 1250 811786897 811786901
    0x6030b09070609091a09040b04022e12020705031315090509040f050c19060e062503031e0c08100b092701150f0e010905010c02040b0a032301 62
    0x702e51183d100d111442e40303012514002400300141d805c07240e80e42684508900e50300d40000310b1040d0f12034108007801c4d00303140c0144114070b07561086400c2c3d5140000c01c08640c2e01d02110170340e0880107043c68511400d01c00c151005000c2e0252420052240c880400d404c041c1c04500d0ba0b44605642420544145c03400c2d01c8841243e110386540720362a006150100880d02041c00c01041000c0140102c0c11a089031000c0c00206a507142c2c140104500c41804110074400c15510001041c0c009400325151400e05900801c407080a06000c410501100702000ae103000700341c000e4100380b02d21076a0100710b0303440801903640c000c042c09450410000265141c800501c0c1010341300d1001c02610100c031551307070800009106000d2300c03070600540340c0f40103c601100b1000d00121564814060419826800e040c03c51511000d04000c0d40c1491100174001520710950507030364070195060848000340f030046100e1020380041030007005650148bd4004003035138004001d00c000801c600341860036280d01d180180400c4504242 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 811789397 1250 811788147 811788149
    0xe070504060519050702090a02030108074401050a02090405010b0703080a1503050105010f090c0801080c1011031216020304062f030316030c14030a1a03070906030b0907 74
    0x104100f07100805080e842501c15941c81c1d40c00e030500c1490502c060300000e50042c8120390705801c1d55000401440014403c1c0040e0000782401c3c07103010080e00c480464050a5a40d00f060060244902c1c44041200300003040300c0000304490034001c2006080184507400a0b40c45003001c50b0060782042c00004202c01c88201322403a10350155074100d20b549031507000364060001ea2141442a1041c84008408a0b800b841168000d00422228284513840c1084400175a100050450188a214001000510b00100d80d880443c50106c407000b0103801a11015201142e00c07000b410030912000c03900d2800140c00005160088007840b031410300c03012440c10103d0f80c3e44128040d100000315210780541901020411503100710b2013190b400c4d15120b007003254291658104403100111014400001c540c0d1940522824a1200161030029207012860b920741a1606c0007800310740140b40c0c1c0340d400040300010040300303009004004041d80c2000c0c2c1d036140054003404c124007050314030088a03001302d81000f8000820780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 811790647 1250 811789397 811789409
    0x30b270a0b280608331e0f06030c0d0902060d06090c120c0e0607020a0e0403050d0b0402071101081017031b010e0d0f022518060b09040209040e03030903040e070504 72
    0x74603a41084210b660591001c120184155218003411401550745800103000b606e04003800080c03629410b000c0011000002c402c1c103000701c0040040c041160358030130442c0c40d0500a09404141042c06202059243c403440305101005442c22170040780f820f900b40c002070100401036036102d5900c50344059400c1141d0510103180c01041c076201c0089201d04240001c1c1c03c071180001d200d540c602d075450000c000b032003a08071800c03000544000340000c130302212071044010811083d034085080564036680c500740c4a070303641001418071822000250b480300003840e029010b058081140c0c102451000d43c17203980c0713801c2031170283e0340e014000356a2843d16a05118025100d120740e00140065002d035202500d18250481c1d82508500500160109555503451080ba11214088201c4161032030303d0360902c90110301e041501101824080d04005910f000750580340c0071002104c1c01652003103d040020014200b01c1d400070a2400044200800900c0200242040341c0d100060802190f0796100201d5041c8201c2c0500 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 811791897 1250 811790647 811790671
    0x3041505161211040306020d0c090b0c0601030f021215160c020f01050a0504091b0905040b0a060809010e060103050a050601060c050703080f04091b030b270a0b280608 73
    0xc450503440c1508019043e141c1c05100525040e00e03516580700740d91050074014509515004900c4600e0b40c02070000000f040406c0c40355080440c2100d42580f10b8034184000f400d47c40074210502c0c103541c3c46100b51006c031500442150010760380c0450040d01c0520031502609071955410700c0d141000e000c0c20003002c00310b038028000d551509800005590a8200c0d482031000c110052001007024011480380c8600105c4a05890f94580203030302000b44020040d4200314041d034103241d41c80c80355031503005149056032654144000355540e00c102c1c950061007045c2c01d41c5682d10a060000040c03120103e1681b15083c000d109480302030303803a01d90552b515102c2020041143e0302c0504200045038031000646013400d81d8080c0180b40950714811042916210a1414010526600280c2c42c80303800d8030030030790710550070f13210812641e465440c40c0600c0e480161984880f00c017401c00003080c04040c0e61007010703000c0d001000c0740d0003003003401009108040c41c4d01648018080c070f0703c2d01280940c0212003251040300740c4101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 811793147 1250 811791897 811791917
    0x706090b1605011d0c190305060a0b1203120f150109031e02101106010e01050a033804060e0a1e030905121b0604080d11070b0304150516 60
    0x2500885081c4540162a00d5503940c04115410000a540d0031810303011400404c1c01010080030021003040040c41407260060300142000060804a20b45500202c0d40c800094150019400b04614801c0042400c556010000b10040f044102405540c0501d00d0586014495502c2c1490701100e00b00491010340031414040301000010580e00c02800c403124054240c0030603580542c085443e001454030008086080040c4010038281c00704200c9004000e4070340c8101c000e501d06004545442102d010151210000d030180d15829140c460003c443c00400c880540b080d0710060110501001080e201154006c0c06d0107640944034030001940700c1074981080100400c4868482c8030701007100d655404038140040c000300081c07255140202500702018100180c504a140b20b218968482d1038008428031465040c007041c0801400064030b0114201d081c00d00c80c8940c200d69245501c1d00800c0d030b0021610304000001c00003000f0f85207a000d0001690000244040d445d22940c2d403040010501d0031500003111850 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 811794397 1250 811793147 811793167
    0xc09021c0b22020903030f04150207060f1b1509051c09061b020d350f0309030c0a0f17030f060402090406090e011a03030a02100b0109080d0206090706090b 68
    0x554a0b0686071941001840e003803c0e5004a410740d0400b200804540d880850700304078141c0d0740c8180013200c0310288060210141401380260565104003840c03020072a48032006090b201d00420b04c6240507030030080108920280c410002c02409403c0b90840d01402600300700c845075510890940c040000e19101c4419160400804175030a681c0801054621200c541484000d6200c0200401506014210808882510324594500d8000030a00101001079584001210701800000d54044000e2034050603070b26100d240c82c042c80c5010369902e0800c00c1c0a90540da00402c9481e84080030800d1140680c1ca41440200071007440078001291401c80700d050a00024a080c1b501e580240001040100000340c0551107003100002c07501d0761002203100344c0d51000d100310800040714196007918403c600541c40c003d8401c02c029207400c8141e213005200e5031034080d20749050f8094266480a00007080464208c299603080007903070f4032000d80360b9251600070701c00041207103031040c561082500c1907090f25034540202c0d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 811795647 1250 811794397 811794439
    0x2090f07142b0221060f03030403081b160e0405010c05120403030c09091a090c09031b03071a0a0f0503013c0312030c02030a080619030c09021c0b 64
    0x15100c021960030407103403100c0c0c0b8202005425090004c1e0554920340344c25024007030904c002c20b61a611a51091000f0000100101c0888031450455000d44480d0118500703020300e02440c030035031392195120445000c119074450342c0f9001c0c842c0c0e0290000307010101881805a4407480f0344407a0f10380c4070000a000801103030007608a0b030702954441c548459400e90380d41c900d03001c03184094a4405106818040c0c005180f900d8000c80d600091081c0e04c6138504001c002c0043c0c1c0c4c074141a401d10204503030010342040aa0740c1403040000602c105056850107900c840703842803141e40541d01060104030003854198103944640b040d20f05035842c5c01940840b5032003084482207610080340f030000140300144034940da0091900031900040d0304c02e0315481d00718200e041020b42642d40214070a0110342c8240003a48a082d0710004103a0000c80c02d60702140e403442c5650250743c9011441e00041c00d80d10640c03800280824255000302101e00214070398071458600e000c0c2d1141980e0b8840b905030b51201c802d07048440c180c2080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 811796897 1250 811795647 811795717
    0x906010c050105070e030c030c0306010e04170d14180606060f0c0d1107080303060a0314190323031311011b150b0111070612020702090f0714 62
    0x50412a180a00365910242034800c04c480d00800225502e0803c5030a00342041000b01e01c550803005804114800c00220b5070310441440748226503840d04010030284240c15501d00c1c00b040404800540d42c46040440300e02510381c0a03e080030051640c80001d00b240b2400d0382075041202403401420180c0c64581c1008a1078011310200e029010080003c041300c5441000415141300c62621040e0701042400202030410304180c1c072407521600208100001c55075804900b50075a6403010b141d80100404030700061519519400300810090f80012040c1803640203085124210705044881403907031101c0d01d45864070f001c20303600c12401210012a4400003045e640c0303604810f24061500c203864105112207501403942e242d02c25140b8501080c40d03c42030f03107110300880440a2084c00d02a105600302d0308441e80d500d072240718000810000000e4169500416011240314a8000301140543e04100512a81c0c000041e990840450800c0c0c1c6600e4691221005a41407242800f01c451903141241100c240e402c505 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 811798147 1250 811796897 811796899
    0x1080607120510050915150c030a0507080d1523030a12020c0307030c09050604020a0f35152b03020304030b0103030302030a0c0e030a1104090206070f03020d0c110906 73
    0xc03420300440e02d45c452480710307803182100400511174040140b080c4500441c1500500c0004a0100890500307580c0000880c0e0b200001440c18580c4c0c1c1c6094284a029400344c2c8092110981c18840102c140b609000d5990b025101b100455582040c1c1c1060b000014595484485406400500c01c4201150b90035600d400f20a4041c0103a541c03007100e10000a04101c901d402c11101810711243c2801801814440c00d6031040c4199402c40c0303000c000850103049049048800400c0080000c0d072010000709c180c0c00c080000d003c0c40151704203c00d0345c1140a1144904840201400c081d080010182e407070145910340c0d11817000320050310202c07502090014244214801501907100c05c000000000b0840d4071910300071b5000365001a00c030b041c1190005c00b0388440c10006420090f1241c0404400e030380100d4550b07003895000950141c51000600460050004c40034045d40c050f002080100a0050180c03d0040082c4a6400c0e5546451881000e45401c02c0810001d07054810b881d815009904145035182e8200300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 811799397 1250 811798147 811798171
    0x9010905010504050d030612030c260408030711030109110d082b0b0d200102100c050a090e130609030201020c0f010b15190503040201050f0309010b09010806071205 72
    0x6200d864803800e641c0c00f65001c1301c407a40802100200d0740d0713040c45500043c00918180c0c184008080d10020014a041c902c05850351401800c540814100d10300c912070011f150420440d115550b0780c1480e600c039007040350251030b00c40441e160000c0518061142d04102a841340d0241e801c480c0d440d040c050f110380c1c0a4000c6a1701d090800070012141c0300e00209581c00d610b03180b003001060044408071403e035800010700c6c5000d00350f8008450005101c0d04c100140c1419003072420800e001691004030314140e40707070903c401d1651500b48980c4105510100404002c2e605449240143d56101204c2a01010031075100c22580c102000000014030280c1208285900a20007d418204d000310310320308102d195107a1a4061795a402c8488507428400d181030344400740c560360350b820203c20950007101c42c403e16505008000d00040041c086a00603810385100b4007101c030440c0d4982c5401804240203105840e42d4030b00c5003154000002d144407000a40f01d10402080da10090541c0c0c8528803100030300b40240c510f600c400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 811800647 1250 811799397 811799411
    0x1b0306010311060d111803150a05071403010e01060809070b1e090910030209130201050403020f0a0e010b0d050a02090d0318180b090a0c020a0b1003140604020f010905100302030901 79
    0x1000c1c0d005d0507906150800095070340303080c0c012080780002100b10710707103000c0d4101c85200081004803010720742c0c1c03000301c48401140d15522024211040036584080c034243d030340c1c0480003242040580340310b05d050b20750350b49940310f40d500ca01d921142d42d8043d9101d0180e1500c0104a2044080d0340d100f0387c441181d038009425803c0101010004807089800c5900511f5400c00200400c01d502d030100e6065004030100705181010061500020400c0c442c1d8000603004600c42c1103400415115050090020302c02c0c90755500413561108003401c0b031a88048400d06002c1d007010045a8802c80c6442120540c0d040100f44182184440d0340a44204907515100e01c104200c440000403c0610a60010080052100d0001c1d000c0005000c01c009204090015821246400c90302d0360815000112615209c1c0c1040c48004980d60ba0300c1401100f02c02a00010102c0740f4401006400d040005480c1b80140c0c400c48041800c00c4214004540342d0100340f0416038407003055440302007a1406940250b812002c814004900c070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 811801897 1250 811800647 811800667
    0x607060b040525111216120810050402090310090308010e150a0915051002030d060b0c210c03070b0103051c14070302070302100c0b0a050f04030503071b0b01081b030601031106 77
    0x2035004070f0501c1c1c89940c5508140000c1010207147e200c9003030002d00b0b0058043c1068000310340528240d000b03183c0520707400154681d807550100210000414080003e0000f800c0c0d070b10b0020000c81e001e10a0b00c2008900703001041d440603054141599149000d049505402c0c54412201d0252264420300701103140110000f040903100d0075040401d002c0c80d900150f40d95001e418020003250700700d03030155030f40e04d0b01404001c00e41c840c003040c0500c250240080300a800701d041350b002c10711807082d540b11104501c0001064030401280030010790481e8001c07001c0d94400d00c41a0005401c3d500923a984000041e05004404520b0040d0030107004054000d20440b078860b5101d5010441400d032102e20080442d0f0601000d2003007120400c40146c2c4413004100c140100e0034007015151414501030401400d01c107011001409603441024605a111070001b0041007104160030111a0210207004030f52040c010000b0211004642190300141400301800801c0345a1031600d131403003132400c0b144003ea03102d0300c104038200c59 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 811803147 1250 811801897 811801933
    0x403120504061d06090c0102070357050103020a0206040b0702030c0102040b22060203040513110a09031119031b0b0a033c0b0a050607060b04052511 65
    0x12015500107081604150840790310301b042e450074640c11503001081c1417001928040d414041c4600308070082d0504c0345042e144d1442411074120308107903050301b601b441031032184003a02c0300c0300d9002081e01000f055448800440985c89017420600140c1d01010206000a600c407000316881102c1c0d106407410050b403191807a099a2183d8009004403102090046d0091491020040603c00781e051070a02c0350300d0888040c1d202c0c0907d2107402d02c9541080030210b0503c4203a0031142a032825105001e58401707081c00040c06200c210700050303400c4c408034030490100e810310f400e21425101059102ca0030b09440c540d07410752002c6003400750006414440c8400100242010040d00344640309031000b0421940485a041d4008800292030078039000c84042c000308001174040c00011401c0030300780400c0c00402c2070086214110581e00c5a40c011200140100c01d11106510458102d0f9040700c0500654482246110910801c0c1075001c00000b4920a803030071990240c60140c5500310004107a0f50001c004038100d603a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 811804397 1250 811803147 811803191
    0x130f0f113303090a03110705040204080d030b0604180e0325110405070815040e060112170717210c041514030106050d06031502090907020303040312050406 68
    0x3401d114091001c00380801c9800184000c8914005500d042d0718046401598a80481c040a001c3c80060917080c01c5d030700c005101c0c2c500904000f400039507a40f0355802c40d090355001300201e11030029240102040702833510030f08440031940b582681114184004400100816070883e6504980c07004110400c8201107110000e0341c59809241c0322041d22845060840c803442c0800030440c8100c1c5840200052203030413035441c82e00070183c540e80d00421030080001c1401480050341c0200544640ea000245451046d0810721042d4841c549201c2e44c1030410208001900501d80d0061100c02c0060b200c4c100840200050403034000e003024012210b45041e0300b184600c41d41500c400a410400140074000004070451f20070b8450303903e24000101900144d88510b03035000c1806004104000020012501e2805400c6100a140c004098000140031901e03281b0081d41304800c1940554120000102401c1c0007100fa6445540c041d100c203810010803490210044c00020421074520355905000030704a1000307d40d4407 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 811805647 1250 811804397 811804429
    0x41e0b19030c15030b0a0311030a0506090d02010b0315070503040f06020703050d0b03160501050a140c0307020103060f12020d3e0d0c0b030403210605010305130f0f11 73
    0x15061403c0c011a076403107443d000da02d030b03041c141012482d503000d84401c500402245d8110010481100c4c40400082c02d0012046010b841c0740700318020702200441c0468003903178099890b0001c000740620681495200e0f40e0680c184002130456a00281e8154024402198400d102d8113920181c0c18199454100700c2c0c0010800340c0000342d012541d01c01c05502c0b403090901003c8220300800110801c940c0c81c040b410505c0c01140c2c100100407425080c4c050240c00b907148000e50390340d4070700e807588000e080de03a6998200c91002d03030000b41480d47c00107040085003e21400e50354030000400d500541c0d5000d002c07440d00007071400c842c0390202400d280c106002803c1c241c0002c040c0050140103500401000e00c2c040b0841200e504c2c40f5480405a110015108400c0d0340c0c212504225100d40740e40d1142401d540c5600341c0c015040726141f404009581c4d40f81c4a50144080e00c0c801d0b20b00304046c0c0c4070410308a250740011180180103420140b040360201e4804402903d4080c4500c407030402c0c40f402c2001040e402480b04000d2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 811806897 1250 811805647 811805663
    0x80a020109060c0309112803260304031b05150106050304030e0303161407030507080d12050601050702061e040b0d060b03042103110307080411041e0b1903 68
    0xc60030808507000e110000f21042ca0f060181e0301d0962920000403507054103240c49031342588038220340ca034100b110f025240c094001808480541da4201f5900c150f072848414400e01032020250002030702c0c04c1081c0c84c00340c0c0e0981e94444903030104082200c0c011692207c03e554521030000f51010303121064008034041c15955503155142d050030300d4040d02c0058100d030910701c03a4000f8811164110b0303400407010486504030301c60f0420303502c1c454815410001a03804c0a04580030303801c004039500400040c01c0d02c0c58613031070f0384807065045502944411900151100c07400034508224020151500801a18400703605642c213443d41d03a4601201a010f80c06039020814900c6d0100b4400d00b00350442c407900c001007054810300d038594500b0380da030b05a0068220410f450107102d80c50f403198040340710317621000d01081000d660030341c4e904280f84090150303801250121a91100c0c400850040d042600803464a05501030891450003400c007080303009007003080c092580100710a0642448840001c820b00d00a41c012800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 811808147 1250 811806897 811806911
    0x31203020d0b0a150507110d0b0601080a090309061413090b0301060609030b07051303050a0b150102150601120212010b0d061e05040c05090409110a0f0303080c03060d080a0201 77
    0x7051060300c004440c0507110300503041c810028189542001142c0c403c0ca442c28035074035407040c601991501c0712038045a811882d404601800c12110f6480140200001d80703401d140365560041310f1055a001c601c0040020f03c180c0810000c513801207404603010401d1020050074050350b08825441046154064281103440d0103200c80c0720b040070b10a890150050342b5095102c035081d41c5983c40c6021019150804010b8001041050600c148280c0400740d03078400141c880c0c000e200c0c14440c43c01801a0380811007504032500750324466000191100680f02c21071920f912640d140d600548120303c2e00c00106420b950204180080c0c12464044940a0a8030a100a45461003400c0c200121001c0342c00600302e502540111040b034000d040489001c0760400c03200492119150f14040f901c5021743d1036646c2e013150524030b0704001c02c1901c010840c5101420360340382210300d035959241402d140349c0f444050003241d0010042002c8100000003141d00c0b2001a01c2044042d5656803000c0c1c0a9200c615603100503591120 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 811809397 1250 811808147 811808167
    0x702030316030f0203040f1a07051207031e1706011119150c0914060706091a0708150607210210060608010501090b03060102101d060a05040f030c080403120302 70
    0x141032541285100542c203150810489a480d21168003a075a40c0e034048c1091081403440b0441140d251070b6211081c2c50440360388002c94210758002e10ba0440110b54044020310369240c11a0001c400300280f80d0310501140340c4411030703449000c4007038a5503041040c1d5409813101c41804000980c00000d840c0c011141c80803241c1000710804076510600c400e954141000711903e10f500280c1403003035401c1540d40c034401d1060781000650900c50007900074819410403d075036044c06000ca5034688148425400308440c0e5540d4481103454003400c86800948401d01c142d1550740f0b0a100300075004030f0340b0402552644600035010403260740350407254100180d201c10300042140b06540100c04c000d081d2030510074000d5041c500007819080e03030350041004102021000035500d80c8204015914203080380400c0150190b05220b01030503003070300049203460b440381030003107004c55109215092142d5004600807900d84040d0341c04031580f00003800103485002c0c00780008008203005070780d200304da4079594500582d603000c441 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 811810647 1250 811809397 811809407
    0x612110a080c13030b010e04111221041d0603100608060705030c0915040602010605030a110f030307080310051e0d12020a08040e1506131a070203031603 67
    0x1404120004014011a00e0840e004614141c0203000709030982c2e01e030195000306010b050303166400603100d41454400000c66038001c80700c10b40a9801401402688140030b0300b4003803a0388010003c50000d900440e0a01c11207880714540002c10403841d80c40c540f03080c1e03440c50500820002c007840b251145401c070003404003c0c501000201c10044142c2c20030300909140180300c07615010010702039014810300200140082920740120703408144018080c9154600c081640821600309000d16005986483c5010400345000079086207075580c0f01c0303c28440180ca142c00c1c081034000f07502d15150940702c144001c80015039924050751103030303d40082802c211481c1000b0410840003000304002d0b101da006030083c1c0d40340c44003c103484411340c100210407050f001003c0c0480c0f9000e4800d0015080c09004640030a191306403411160050710440310b030b0030588500c1402c100c1941f08071990b01c40c604541800401010305403c030004036142501109601748007241d00801e007554854000c0104641c8180c5103001019085 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 811811897 1250 811810647 811810661
    0x5010605010905100e01142503030f11180d0b040f2009060103090c150315090606120f060b0c030307090e0907260d02150a0c0f0305060f09010612 64
    0x2165030300800350007120060071001c0a00705c00c504000ea40750195540754518821240c0207085c3d61102011500400d10b101181c0d0880d410440000342080b001c01d105240750b0040310780078070907a00000c0c508109c40c808000c0e010140c10b078171900542c510131420007040011904610440c0583d08484588429181802028400740c520381a00e0407250000000b40d1115404194024000e0800080b0f200035400d01081d000284e60041d645140e2b02c02a942d886c562640103600d400c043c4038078014000340c48e0032100d01074401c41d000300b8000501c80840d0046130300040e005180700c5190483c4c00503810340c8500c032501075030b840301c0314941e500d904c00008d003e0103690112600e4010700200804454905003185403c0c0c84426511410400e400d0901c810814230284800c0384071f0244900088030f4403031060150207502c5c0e46140e004e20041300a580001030100c0e0782c074020b54013040d9056451166520700e03502c082d00249000340c0107641001c0540b10011150300d030010490b0207812161201d100a60391082101e0a031410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 811813147 1250 811811897 811811899
    0x17010605061201061b050f010903200309101101111b060c2a10060f060804020d0311011b0905190b0a200102030f0141040e0a05010605010905 62
    0x2040003882550300030b10944605460007403070500500030910000c20141c100c0188042d01c14044c6188106081c041588105150340c881c0e01d9080c000088115000e000c11428541c9840b15041004580307100e140040f03142031008101d041c2004c00c3c001428880d402c4075900c3e1650480c000d80081c07404511044d00c3d003402e002403041e1000b000c151801120800c1c1c1c502840c1c42503d5420034003800e11446442500e81010301d500700c0c40031201504500348845010309218442c00701008594440494220f2103040d10b14451900a01750080741d480680d402c454032a4240c0c0d40c000c0b80e560340c0d848540d202408900b6241d24004580c1e070300e40002d041504110349082c618000010f95844030302d081040c5034080c0241c400198190034070302d1820f142ca155090f1424140e043c180f0310b5510010402100c60000c210341d43c141c030603480c004158114045442d4407940e816030880307500c030400083d40300703080d0b659882a0b180c0650080e00c0861000e60801c0c00a10384071052b03030308035110b944402c418011541d00c10300700401000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 811814397 1250 811813147 811813159
    0x30507020a0c3c0603020c120f0301090624050a0e10030c120207170310180204090b0d0809040510080703030e120c010813080708030a0c08071e0e0406030c17010605 72
    0xc030498000701604c150014590045105152030609004030710f9502c040d000c4c0541d680c000540600001c0d44240070b840e44c550302c0c1a002040c4043c5011114060358080303416070040807140c4109480d91381020f8003c10402c01c0304030649070342c0e0300c0324078020035034204c56200418890310f0840d01800010340e00e446401c80c20320510000c0e000c120640d14007424030b40500b00c40f84d0741e6128990390030f0105410340c200310480c81c044804008086001d9009104488a100f0204080083d4000f040501c140020015001074424003136a24140f0f0135911650f040b1641c7e428a58203295108007650820100340d1060f03006c242011030308a4142800980c90040159031409024040c40000010300b07400406040c0c0342055210a21074000c00c8241012100c00760340080455803613140146008015001c403484d100000382c04000842c001c140156101c0c5020340e004400c10800b444081d10481da042072a0a141e0342c4030b500c42c000007001c580c0c000c031a43d02030000074022442e034490404071182510810b900050040c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 811815647 1250 811814397 811814489
    0x130b0406080f120c010f0e03070308010f0e0a0e01061505090910030c0e070203130905060f091b0702030a0605160906050f0d05070302070c081e070f0501030507020a0c 73
    0xc0d00460f8242c051a6500030030382d2106007000200d401403501094005403030b482c00c04030070400c15000018100c594880c1e0313142c803502c0c0e88903010040c5002e4070740300303a4441c600c0660104800380c503590080390200c10403400000d83c0707a0740c1d10b90101d02c401c1c0158140e00400c3c00000c2d000c549040c0340c08070550010b001c0450074807103403846c0c2d1a0060001c00d4420a8220b40d12140810348040c401e0044030b0214100c0c0c2072900049484072482c50042a054491030b128074400c1040d01c429080c2555101c0c41402c0c821401d51400c0201030004032554882c03102240c0c54021010900700141c07086c400d250180011030362403620101141c1c40506020041e41001c000e01400388100743c400c2c0038a104031800e4002c7c642c400308054036103020640203401030302e1009108260012010400d00b40c00520102d48181009500c54080c50012659840c1e0b8003d00541c4e040501411003488030394041e410880e005081c51044525542550701c40c500c441c0082c1c2c00ca440042c0c00000b01c114241017250036527000e6802d0901e01c095103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 811816897 1250 811815647 811815673
    0x12040906170307381005090421230a1403040f030309111f030b33070807030306141c23031206040e0606060a1d130b040608 54
    0xb4011407078001c0c21002e90181c4400184a0300b00c0d1107980784081d013507040d00a00c0244040e082d030f8100b00c0c0d0101a4500843c03000030b00345030048a0601480e040401c484002c2003040028407a44550741c040c1050240e07040c521a2640c0348081c81070064940481c50a40314a85604000e0103054854014190501c040c414403010607078000c6042112130781801c0010f210b0042c1d00d0004100740c28140301c0ea9110140c0c034094040c040c2088821160640c503030b81c04205107405030040103c080318040b400c80d11b02c948100406a010b10701c40a0705620741d0700c64403007810441169524006135210f50001c1340000d4440404105210081c061040c49142c11100307100c0c0b400c0340c83c1c907100182211281c09403a01031198114210f008410f104021500b031002c1c03d817660b643c0f000201241c0010b0954031760380103d25080d220402c3e42c9020a403d40130342402090b80b468500190000c42d8080c0c00010415035440801a0704441030ba42c3e81d0045a01c046910000b068108150341000103ca0740e40d0f0101100d41c2020780d08a8031 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 811818147 1250 811816897 811816903
    0x20c060a140a05060f060d02090906060301120b150604061106010b041202010815032d03070503190306051c0623061009080d0203030117280609051204090617 69
    0x2200c0030342880090302d40e4524002802d10040007840e06e81000340080e1540c1b0360300c8035400501030180c2c29500340c480c0340c4844003031000602c070034400d8a480c03592541c0304900141007409100e410103e40b0309120f186040c3c0d000080d4256205500a00200c1c1c40128103102101d014080309004020f60042c49003050703d40035041d550030701800e00007410441c000300012650304c1c0e1080c2c13186080d40c002d401c54034410201902c0400c14070032003040c04d0840d8140508850708403000400ca031042c0d40c0c044059414401038102d800e11030314078240d80d40107258840320041055104c0c400751010303850038460400c02003041d070b040001c01c4501d800300703000104a49585202e454450b4003c1d2540240e01a100c6041d40f020f40c030310840f2001165000034406000e14056202081d82c000044c41c10703101310007100074a034070340051040d0703072403171100c0300c0d40000c0c0070324101c00002c035101031900c10f80640540c0010616607000d94555080501001281700c2c1320340080780910448101d88280400f605032401c141e0007899000d94582c0e5 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 811819397 1250 811818147 811818151
    0x3020609010b03120c191419020d020f01110607080712020702100e1507050d030b0d2d0b0f07030e0721170406111006030b0402150c10020c060a14 64
    0x703008000000c560040780030820451072420180100b05480c1c0ca013a1400c20607e101048168202e40b1030220040115001c40c03800200c1680d004103418130460302603090001d2500c401080385d052000388501e4041e000300030f02840748141c20344ea69040b11850010700c0507041a2800648410707461051011a00503200c110f01c1e009019042d00304541600000400540070407601b00d070052001d180807601504101c03000907040800750403038900344480c0b0210800d21000706200d00010344103070761107000710364510094605034a1669020b03106248549040c1c680e048240d0090b108040032042ca9405c1042c129031510030801e03842d5480c409040d0240c071b0510b441d503c290314070307090704041c0500414046c20010740c4044402c007440422422600e031540c0c0c60000d4048548540a011580120340c0b81c42e0804820b8810a001c0e664015141400c40d212a02444000790580c00c40d003241d0300e000c011014000000f0030006161035045800969200f203180122420a41c0c040d01140d0721904252009609281074090a6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 811820647 1250 811819397 811819423
    0x120f1205060a0b0c060114060309120706020d0612050c040606090e0934080c06030c13090612031211031308090901030b0402030f0a0506160e090a02040303020609010b03 74
    0x10906441d118006070200815074401d40380b030940000c1c05480e0010105041c0c2c101e810150511803980025803c0c000b03c0d100454020343e164224a480d4144651740c4405010418021840181000c1e2241418822242c05401421414a43c042c20b901004001c0040240201040c0d13024800302d03162800242c5030804c03902600743d40700c041400040c2003050800000d0050041c800310061140300c01011119a905543c800030344240b004600420500d070f0014010b8600080a00640e1465445107000070298101141c80706522200006c005050f242500440c00070700303c2480140280c2e2400d2a028000c42d551004002405040001111240d0300c1141580d501103c848600403141c0803030314000c2d40b00d10604541c03560110b041400401805034102000303108600c2a400c03076504061803400310f5520b8005501c01422a40700c100000d000074510522800c13440002e060240f800300352100060342c1c000c1c0c112200b800301a40030034208185030381001101d40001c030100003040385016090120b80c591070442645 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 811821897 1250 811820647 811820651
    0x60e06040908090114120406150801061202040f02070501140a0b01180b03061201140a0606021b130b04090f02010e011110020714161406040e0f10080a0b04120f12 71
    0x7824a90507400d003111104406c241e84240b603480c2c2171a0090003041002c401d84d20f000a40f00d0041a01c0c401441548251600da8102c841e61f500150700300006002010201c2d444643c0900000000030002d0040411594101d0000e0700189020160101110403c2641c0760400c4508501c00b500c0381c8041c02001c040c0c9250b040b140303643ea9181e20102c1c00c08095504201840d62071301c040c92110312070340c0091034000c02d84200305111f80b40c0e980c00101e0359801605035100d6010740203040403c007807504c0701c03a02c80101ca5091380464110f001d1000901121303040c40c001d4540208101c940c000310740c0d0255000c01e244c082402c4c800440b203c034203c4540e9401c00302c08100c8684d50b0002d001e0381404080400c0c200103d400004807041b00d21200e10201955009100c0e402d802082054170004c23515148040e01e081d50200100d900d40d690b1405282d020880014240d0124100300304400f00c0d44580c24070043c112180901054001800d180c504108100ca21410441c104140c864902030a0f650003a141c0c544042a2400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 811823147 1250 811821897 811821917
    0xa15050a0621091a0a1826070206040906030203101a130b1306091103011211010c0618020915060d02071407030b10080a1505091507020a2f09040f06050a060e060409080901 75
    0x144d0b5114452344502075446580424000f031244a503130800420fa0b4801c1d400c1d41d600c080300061207030a036109005101031074030143c3c0d01c040380c1d0700b0903049414000c0299800030408009031804503d00c000c0c0705250064941d2a40c2050099010074001c074041d01400e14a15403856241585800c2041e0f1070190040410541c0d44083d0002d03885401120803840c3c2055081100c0302c400c1d00c0c01103800f61010001c9008c1e001080005043d1541d0511882081c41c0103440d01c1c0c50800611b105031700a42c803c0c4411150001c44c5603101d81c080301d0401c514400f0390301c280a40440b170305048003401c81101842c0d0200310603900c4a158400001c0c25131600080b003141040010405440e9003407564245060491a511400c01003010402c0d42540003075500c2c0c0075030107541131007800129808840602d0140714103198820702c0d203903580ea9040c2000442d407688640104070381e00c4441850750346c0c2000e480d8107640355803003507464001c10311180160001c5990001c2003220100b09007075407562860075074082c0705011414015107030781e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 811824397 1250 811823147 811823213
    0xe031605130b06040b040501110a0519171306111207030e043c050603031614010c0201090611030f01031104140a15050a0621091a0a18 59
    0x2210300e419074014016500d507505c07000400c00503046403066078005244481c02c41c081400215a16007083c0e00a000340107a071802103000d800d400110708040b1617200149281950307444033344000c0c0c145401c003110741c20b03040c1c1c2c03420000500081c64404c95441c15000160f21280c0c0c845540d044800f02036060514103c0102a20006030052501c5111550900040d03854075502980c861080c501c1d43d403900460f184002003400c0709034101c1d0f170211000c4d905a401046203401c00015080c0149607544140082c1c518104520300450039900f140c00d07001e015030b454003001400c0290901843c1900246860f0190030361400303200c0c1c44185107042c800034290114a0230716450a4441c2d40220103640c0d0b800000145a00705540000c0080040b4051500c1c00740030380e030700482c151500010850899403113588080740c8002c0e15408184000c864041d584810b076481341040d0000b110404458961107891031091a6440c0600041c003c0d074142e21198995100b59061040018412451403580604601c1840700107442d115 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 811825647 1250 811824397 811824401
    0x190f020702040f20130b0d1b0f0915230c0304030312060e06010807030c0903140616030605060a2708100e0d0c0b041b060509010e03160513 61
    0x594069045810f00120080c42c031a560002810102c034184c0c0201081e110b0500005a4001c00c8018401500c04040030802013202001420200902110014a42c50380003076900021288034103000110b1208080710070845d403c82c0d41580100380088841c09220070380d00d03000b402d0030384400c025240e500b62038489014071410203041d214450411421242d560382c503801d0190650b080107501a104030300340140480d2018280c070001d07004540684440141d074a60443c150302500c46410900108041c0032000004104d4100d0341c18442e11280002e070507503080550720f202d0a81d882c01c04200601d03007000400c0250b070b1100c00440d809400e05240c21a10100c0380c81c001a074520494105a000d420000004201c856000c03d0481d02c1d08006d0004112564640f00c9a513100c0c0e411040032030104400000c00f070041400401c04686c080d1080c40c00700c000d0001d041110001c80c1d0305c0d4004070000361b03001c42d47c5892075820240c0d80b881104110b00408419400d0049044080c140340603403405011410365442401c04030ba = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 811826897 1250 811825647 811825657
    0x170601061b0c030b07030b030f03090f130207060504060f1d0304060309060b0901060f0801080c090105060318060a0c0e030c0603180a060f051603021e180405090a1406190f02 76
    0xd01110131410840402800303400c040c03030324511a006012000b02c95502c00001c8070703401d02000e4260382105511004000f10789000300e054151041d001c00081e0700107501803280e5849280701d0600011b1390051380d01814100e5a06a882102c0301c4c3c40319082d150b0107407000041d20201d9145140100300360038a0301e050030151030f45407811600f1988182c00891010380000750181d00014aa40d4420180c0e0f903101d510f80d4401148048980000030240103200314100f64004550260700309c9441e180c954118802c46240080858901202c26030320200e01000c290700054512107000120000c2964022150010305580700150041803581c0041000e03500da42002e0140303901c101d40060003040701d45605408a1f02500e411a600b005041003034600d071110a02a2080d212190810911986152805211301daa56406142c00405c603000180c540041c40d51540603c0384500034403000341452505503d41482c02e002d0746030310039040f600110100011540b400e00b0700c02c0e008075640c4010400040700c50780f03c0020320036 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 811828147 1250 811826897 811826903
    0x8030c071a060117010b040b072a0302120339070306050f0708071d0105090402041d01060f0807081909060b01020d05042904080303010609170601061b0c03 68
    0x2082200580e00606541c20300c506001e0304d49080c40c2003804041c400c191400d02601c941c90805020a110140c0b0103805001041d202d24190111809585100c081010440c0d48240481100707080030700031804d00f0102c101c4401b910b04000e5003030140c055410000a0480d00c2e11841441502c489002d2510080d801000c4034000c1d12305542002c0d80742c1c108840904012540c03004456140070214040078803450310f981c0702c0e83d0140c1d1458080c0354490f8407501450240700c80e40b030400000b480300c83c1080e0b070f40384018001420b2440780b4020401c02035002d4042108160b001c00d003442000c0320b49540e001d1300608a503030700102914294100fa5940c407543d2004503d0381f142c2c4082d60b1310740100d40f03041001603400140c0c4500c0903000c441d07801540759001c940314800d0340282c0c942d44000c0031700a044045001a01f070f80c01e9110038525802c16444100740c40c5150400d9020400180020404102c01c00030020f09156807080c05000d00303130359810071402400d458004464007880740c1c184100d0205100f1106c5941001d194 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 811829397 1250 811828147 811828163
    0x2060705040924060203070b06010801050604033905040b3f1e060f010b041503020c010c0c1a1320040e06071b12050c070b030c0d06150c08030c07 64
    0x1e04c038030b0002c0d9a83c0001d4002c443c1000618003081040d805070410305c0c1200d2005100034506401c5640d680700d00040721000a01c0c50a40044401c4200d8644500ca4124240d01c110380700c412346001c0c2008150390b84120040cbc040c600f12008003a4925400d28046180c0c500b003c25103241c01491042034440c0303d000c540c040454065100c4d44030f04141801c114060280c0c24a04490440e110007110621401081c81200c400040c100410420202900d103407503c0860340d42401070505000c1d458050035200c4032000320000410984040c010040041004080c0402c0d80f07151104501d0324003020364088010960203001010300360510840401c03550704070081d203800a0018845040340840043c1d50710015070f85d00011454400400c2070f801c3e0013040c960491a000800190741d0080394005441c0c60340501301c03142c1c007405840004a080074040b8019802840c40a40140e5100403400d2580101c81954000a603e00e111503281809541d000d4030440240d504070300c1c483e5981e1202c601e0110b462056440c0208a14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 811830647 1250 811829397 811829399
    0x307020d050a2a050916180b0318060702120a030f060b1902010605040c05071412070b01080c060711010e01120e0609060903090d080306010c230d02060705040924 71
    0x40048840c0074140000b12000e00c0c0031070340750130422013625011100f51a40d401803070449071005101e54156100701d0f0507030013840442c684900525086a004403a0281840040c004290204104010040c0e02c0491840a003042014100b440044d5100e426000d404041e15031918068500301c03607111000404060020903528041091600001035101503200055440d0001c0080c81d42014021040d162405070b641d9854904a6aa100c0c034540f00b07000700e50300300d01c213110100c03d14204d4080201495030248011452941c03511101b586054107561082e0b00400091105400045c0860403041d1404003d00b064010218201d00498884c6a00700700c148030241441d44900006c0c030013184150088246106039a40b696401e4861a9a80304582183c0d0f00040d546102c2000301e080301d40655004001454442d80081d207a8640492107100948010042e0b80072400000e0390701da08102000c10340383d1900280035907143ca90300141081c010344c4500d100094440a140422134802d41c2c40c01d040740c0b90848110401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 811831897 1250 811830647 811830683
    0x705010504300614071d061e031f0f052b05031303021c08030f09010905060f0f06101d03070308030a06030b090303010e070c02040b040507021c0504080307020d050a 72
    0x50f04e0724003c05100d004000c4045000e01c0c0c17062003a40a45e094a00220140043c000f091018a0740000820340f11020701ca01065000d8203030301c0045008140d4925091194508550300c1c01007003c1680c414bd0481100103010003080e143c0c0071001a4456180b4504c0c02441c0c0f01c24455020018880070040540c040002d1880305154940c03240d00a8074000e40340b04c0443c02d107444030740303d440c4e0810802420504082c400240703150f4288504582c03044041002040d00d10607070b0340301e502d000d2042d00ca0380c0c409000641040080715440c4181d40d4081d40840d01450a4111100040e04140c408180b81881c02800c0300c491005031400c0107074000660784210369503503e2400c0d018140043c11903010403a000721b1144041010b4440000a680c169064862801f54540710f409080d2007415450100301d03003158690042d000255a1446035a20078140394000d850381c09407900c07104400c1c090315102c0b8800c0c03020900c01880f01c003000100b541c00555041d991200040d0060505510b030030742400004104444001c102e10318 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 811833147 1250 811831897 811831901
    0x614220b0a02010609050c0409090302150906040b06040209100305060604030f0b06011107180209010903120206060909010603030c0b04060e0718230a0504080c03040b090a0807050105043006 83
    0x1c00071441d4001c2048540b0384100905503030040d03c504041f481c0500090244503419403090403054400e004681c25855030000041d140901210700c001160482000c01040c000c1a5041d00d5000b001118210300e44402e840000c0d10f101c114203a80000c059681c03000a80c191503200c2180e014540200240709170309054900800d40c404111a0140080c50322100d4003070750f00d00014060260b442901403c4409011a10084020340190994a0400110070f8000010961285148510090a50251400b0b1922000340103a0b01400b81882020b03a1410b9410804241d10407a00394055501000507512911039050000c0600f0403100c610b0850301034400b0001d0b40300400d6038ac50741c0c0440144420301c00459015800b06e4001d4940f42c000b00c2d20ba92040005040a910760300c0168413600c2203407824104000c0001e220301d1600241c002601d2080002030245140c07078180c800034000d01030107004000090034500020f0181c002c07480340803103081c1c41b6400c4000e03000d108910b00703640d100101040c811310346d40c1d4142440 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 811834397 1250 811833147 811833157
    0x1704170604140c030303010306050c040f060c0605070806030a030804050a0803090607020f16150909020d02040512060402101d09072c15070501020702130509070f0614220b 75
    0x42da0b00b0300c0c12284054541c085092042490700074080c42c25a0710310303103070003014120091201c41c45c81010000031035180c410301c10820207084150354090020340035203424412583c01820362000c0c0240c0c10b080009a41d40010450125a4940f030a60040e48403803502a1078140e0101d0000c00c103460200070482c481c54002441485080300d0f130b0071122403196070031616440b00020600142d000c0c0c0c0740714040c060500018801c8050060b203140c9420392503a540c0702030f8100d0308004020481d0a800090800c66442c1c078901098810110002400707131800d0035030000d6103442e80c0e140d60382c06100d10011461192000710400034242d04003d02742410500c1c05400041180c00200420060151a080c1010f11220004080004c028026020b40b04800c5452000061500240e0003100c6540d020440440140c50300100d111200c1480d22010a1074100422140d042c40020f0304518110b40000341c040244075888041c00c8100b42082c0c0c1060f40c2d07600c0000707072400241402000c640a043c0e591310700107003481d0940c000705 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 811835647 1250 811834397 811834403
    0x3080c06061017060127080f010b01180e0612060a0209040c0206060a0e090102130f150807020607031112090a0201030501270e031905130518041704170604 68
    0x540c241c1581d10b041c1e807241d0182c0d070742141c403003030081c0025042d501038a54440040348a0b2420600b980c00908060714144064100035101e4018020486109400340144c4403c40000d0808907503a08407050036004191061048801c02901134010072060349942c0c0720038440f20040c009036140d620f04117400e00040d6102e5410301703000b24600070b09145018804a0344a002d00d00041003800b5203860511800d4540a01804429031950700300030311004104100340b80d0303004200b0003045401d0039103070410300c0310f0048140300c1c101c041c800d2910420407516030104a0716070210150a0001d82d441100402142c54081c41ea554220780141109102182030002442000d0b17038400d9806100d03907a241c010b0002003907188100e00c0a10740942c4c60a540001d03181c1c00c03108154030400c04490520b001912060b0080c001c84c04040b000c913100003540c040505110241e600031b80b0045c0c070040030440080f108417540c008020320242040e03032400200f0742542d5854080b42c00038240c1030b103803101000412084d1512070300c05032812 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 811836897 1250 811835647 811835659
    0xb3c0f06221a030a0507050c011a030d080f0a050919240c0903110414070906140436020f04080f0a1101050c0f0601060305042a0b0702040603080c0606 66
    0xc1c0c4041500304442c24118198120b03007141c44d81c000900181c200601503000f0f024080c4028114601d00b44074810390b48490044184049091900345810001c00c50008010018510100314209205070100e0b500440601c20008140c2e03a42151103082002240420051204034148030092001c1513803081100b480c17641030b8000701503400502c5011201071010281c003240c24028100040f4280c4200640c032020701500205001c101c40030410810b4804486413004a03c01042c00e00440d40d0040840b4180c86140c0c101c5480d06081200c040c402104140054101c00c0c145207105564400c458400036402180704815512444421381041c003542041c010005c1c20700c9090000d55080a000440707110913a007040d00c0c211000c294000454841d40032040c01c0150b841540310300c49030042c0801c2007900804a541c4e000406050500c1c00d055602c041100200c20302c0d032100c0b804201204990600d404030340030a0307009a82c071100c07440414081e0149500207482081c01040d10000001c011504e140b04400490740 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 811838147 1250 811836897 811836899
    0xf02040203011706151c1104020c03031905131101031407091d132d05060a0f0b0a1e090603060c020601080316020906040b04050a0b3c0f0622 62
    0x2c2d940c054041030b44954001203600400103250f0302c5e0810345001b54084c041c4102c1501918021409907802658805202d52000040001030040701412600040d5100c00c140818100000c0e0903101c1c02c8400c2007c2c01c0c11203032034541e1815a0185e849107039103c1048107445414a0703c1603010f44034000d035210340c0503480d410a40c01c3e131101807007102c81445030b120a0780124003224aa180d6412421000348060b0308444d510034043c81c01251420843c3d0000c1c4218000c00c41407a1001ea40070a42d0f1002c04580441d5040c803403200c881d5554410604d056600307110014881440c00b0b100702240e12604c0d40004055450500003106002d0a60801c843c44402ca8007160481d03640c9092141d600d214804a1403149405c4462110040c80c24086580e0810030050010030707401d8039440000c045400944507182000c1e51119610b20604002e24007002c0718038015900100c0d412000050703a201c25410750048000300f198040c60100355900040000a81d03000340445451740d80c080d02c0d4503240c160920014080000148c0c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 811839397 1250 811838147 811838161
    0x506131401080c2704030c02130203060a0b030c0711042304050708030405030304180902100e3105180d0203030a06080a020105070605100302060d060905010506030408160f02040203011706 82
    0x2c034102075802040e035480c0c13044658031411200701e80003400403410800803080d02400769440c5d61072041c0030680d5840041c1c1c0ea080281c100158080580d2011400d90014020008200d030b0030002d0f40c1e00c050300460700340410016400003a00405044040304507070b0314040b0400400d0054640070700d02c644d11401c00c80300e0250b1254240c6589009520980b50705034810001440700e0380028a5030001c004408501107404092a400a141107103103522142c006050041061414070b8005294100c030034041c5140c0085d280c03464501046a01668485050700792a070b00484e00314001600684d884030a910b0944c4c40c210034221009440e0b030300596010000c58102880820089008195400c0e0a80d050b140c01c0d2400e001e698595028050061100380f41c015100b4002000d616800000c0c2202c0c55480000200c1c182058090400c1340c0c01a04030740e0042c28148200000110307043d045501e40100c6207a240d210034902d01c0c042204440c3e9000080d00680040000902c143c500d240916a00c030760441a1200c640d9046 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 811840647 1250 811839397 811839409
    0x51207031d0c0915030a02240a0302090f09010f170c040204350a0b07020313090c021002030105090a0908190f08010611060c0d020d0204122a05040506131401080c 71
    0x100030160305d9046810039200500d4912010401c4242d0010500d40305d4001c1034410300720780c102c205900c0c003081c2c0016031801c0a10781842085884042250b1b01005541001c0d4002c9050b0740c6d502403e004c0ca41c116090b00c000800400806072a020010003e554070341c1c841c0d05e040114001c080503080c25110015004501c0d041d84802c80c01c60650800040c8550340d0300d40c403200da02c1c0001828030307002c1d40410003080500d5000003070b0040c09403003c54404a00100074900003803400122070003542d400c5205100520403070352004d081c1174010420420100d03c1c4843c81c140111107100b21107281d11050800004038084941003e104200b01d1810b03120703402c0c6681d075040e05a6840b1080311601d102c40d0071680c00141d40821541c0600380b00b010700d6000505044213601004103d03805508440700c4c60b491000d01d88200458241c0740c4480c0c0740b18a4000b0104891071fa0041c40c20823246c01410b10852326080042e40540718a240803050200b10581804000310018071a85040005c0c00b0359801c5004d805500c1c0c0301d80c00c000c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 811841897 1250 811840647 811840681
    0x6091b080603070b19031d1c050423030c09070305040210080903030604052206020d05070e01120e1f0c030e06090d030b0a08010519050610051207031d0c09 68
    0x1d80b90b014644680c1c096060328400f070300c40003041030580e0b40c1c015458203502e205820581500d050011300020b05100305010512448d001100d0070800104424049291514861130004420b2703044030300d5046158002034103062005030348a4000c9501c204010640364160030541c0154001c4d01d081e40403039450082110501710480d255403555200b08085091420180d2243c1c1e4850a4440b903e0121030000050f000c090309480015039000e82c000c500c0060078440d03482007607041400c504220442c1c40c040b0b00040d16850722188541500c0d9a9910604122101404200c85410340c000b0001e014450001c6004001c0001d080303d40300080c034100c1c00325620300c00055514021039007800180110f02c440384c02100909170592110342c000004441c00101d20703000b4002c0c1c501800c44841103070748411454031903804503500208414410080d00c0d52044201c0c0d0000b0844042e00d5501e14060702c183d85508059003d030030080700929540c2221922007007800b0700440c1001c0301c0201203c003071001d40c41d03844642790072440c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 811843147 1250 811841897 811841909
    0xd0f09120b15030a020306070215061923042a0923030a0203031917040c0b1b250e040c091e02181804050c0105030a06091b08060307 58
    0x9260108030780d541c10045150b001c03030006041310703600c00c1294040b90070b016003541c0c0c0802580c080782d01c5407040181c00c0d0314991b0201003030712007011080003e80030722a03020003842454403040001c2d4510064050b100161451081d000d001840240d901181c030300d4050301042c407a80b814480006003000064441c5942100b11405001e143c600c0c9018491000c0c6c4140340840400c1c0c1c14411100e0601c0103803410b0001d020703181d02c9a09814001d0041d914060309030180c00c007000d004002e0300f004010001da00e82000d032050340c10001c030a58681076880f01003005500c54503500e490500c222500d030005c00c0d01c51810303200201e40c1d008111000d550f650110ba10044d005840091240c0f0b00c06005200090b065801a41c011404408070110351803e0300c001800c03a4466140d000c1501d0041c0e10744001806c1410440d262a1540b0444044928190f01e0702c988800507500d84a0402c8800030100310f003141c41d6040703800989004141082544100b560f80707078912080e649034601060401d8002a040d24000c01c6010803645 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 811844397 1250 811843147 811843163
    0x9161811090d030302090303091c05011104150f0c141609110409020d060f0905150904110d03090518060310020a0507030c02062503081006210e0d0f0912 67
    0x80b0590701500a0341060202e55090301c030912000920790f0f07941054034129140781c9440506410241083d0b4292078414440300341e172100c100800c0091080c0000041c1804101c0d03e4444200300300f11404403410001c0c040058000c0c41148038482502402103050032424085056003171040f552104014141d5015640b140b03811402444204030612035900100340010f008480014010388805880110807582c2d000035803141d5032401001981103c86402c60042e842c00c950350306a5140c2551400c56580344060701031b0007410900c000b1410507004140c0c110107040c0007481070360480600503540f103289600303d80c0c1911a1103146058027003580c061007110300c501d01c2d9a0fa403500e806159101541d0180141c0412a080ba4040000b6a4000558810f0007001c182404002c0c21055103401c0040100002400c150b0200440d1130081103d03e4001259100309030040f940c8999504008000a004024002004915000340c2080042c642c3d406060100b2000c03403038442600e040d0f1129002e00d0308110380000200307110 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 811845647 1250 811844397 811844419
    0x20d0210110405030105040c1d010b070212070b1605070e07050403120504081204051806060d090302010e100905060c0a0f0302071b180b030a110402030916181109 71
    0x10360341c101145180091403801d10b815030781c40119085542c2100c042d0b80354007052400b4000070410b40540b1a450f0000841e0035101e504040c2c45882c240b24010000f4070540c0d014400400302601844100014041001005d44a00760005036080e40400c000088a85004a0380301140c1c601e0400e0402d03002c0e281f40e507038041c1414115540e070350494031100000020f014060000107142202000b980e910385035032002c129200c0d0300c1c0c40240500a8650200b5180401d0a8002c0000c0341c1c45140c1903c03031000c60035001080000203414181c0c0100300502c0e000c4000c0c0500d404009a541c4e03150032180c580c602c5881150102c0c0e0380d03801154500d0150302e648000044914052004c1c0078401d03000760032014003d2000440e100064842002c80d400e00380c0c03001d27620f05018820880c030149588076140c07601500380c02800e1180302640d01c3c1e802c080d160703840143c0b28513804400701c1c0320b9800812003001d840303c5441c000000a51200701c0d610000d090082074450b00c0b0b042404e1195150594019101840310241241e8112 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 811846897 1250 811845647 811845673
    0x603070503073c030503040f05030606010215060409020d0b0417030910200c010509061e160903020a06020309031605030c0907032007120309050601060c06061a09030c01020d02 77
    0xb1240f1042c802015034003004002e0705000b803c018190003188a0720085640e1440d0034040142030700d940e8000b42c40f0750010420001140d80100e501a420709481c01c56080999601001400400d10004042e40020500c1d10341d4041103401c8040d180a203003c1c009a07880c2c1c2a098070095003a22040340c440c48076070005503807118928034641002c1c0005c900459040300d00511003100090641141078003181c6a9150000d2204031750040c0b0a07250050445000250a44005090005482005400340ca2a44580320a1031b148130301c07400104010756401090001019595007000795280c01c8000254840c0c02040c00301c1460400e00c003100da04032040034018004003405801001341100c0028860401d141c0c980d240f940601754030300717010308000c5500154140c6800c92400c00b01c0200001d90441c03000e05180200400125500069603030448003140b801d400000c001c0d00c4d0010281500760300c100f84e40d0300203c01c80c0d502911107501514451a0a6045441210400b0012a6548454210b47c1c0158001064030408c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 811848147 1250 811846897 811846949
    0x7030c0f020d0b1302010905061e0d020903070b030103061413020d031206060c1a0103110d03110304030c090e1b010f02161412070b160f020a030803060307050307 71
    0x1041c002040004003940743d03200c5030340c0d400f4202c03604510301000000b50400c40d030b002160035000c2c1030162001820103140c80c00c030040c05403260302100341d6280082920f1146c00020340440d10340410241c2901c400596680242030700350801c0c00100c07400c50505040c51408103041064a110340e046180911000040da020b2007441c09141d2420782c01c101e80c1000f09003040c000c42c01090b0081c1320075620000c80c0e60301130910b1008603054032141c5401030184401003003c110031046096210104994041071030a0324038064500300c004429030b4025010118000003801044031151040740c500c60018001150741003e0a40c0f9007610408400b166130305000c1150740c95210780d01d5512540c500d8012107410740c00c1843c140100c00100d611912002e00b02c00000921401c10510680c070fa8000354004180325400e00320111441c3c0644020640668500c01902c0188584074001e4590340d0b030003401c2100785503100d0030802c1c40b950088581a00a20820000203030a080003d502c4040302c2615007081454200c0b0100f10308 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 811849397 1250 811848147 811848173
    0x60415120603050f0f0c06093d0e0105090306010312030e01021308120a0c020f040f1a0a0b040509010e0411030f0d0909060e130611160203010f0207030c 67
    0x1040221190002016100c9485100065801200204111391055628901d0440781440c0400d5030b80220040c0c49203a19818162800d04000311031000f40704204003e580da018095809180400040a4861144403017020394104420711955a10703c5407200c1100540e000c3c8298540c050b096801000108080b80c040030b501200b0080d80d00e80402c40e01720010400f82660847c900480003c64440c20411400030100142e656044210380103a050000340f0102400d01001000041d0059440b00b0b200c81c5250740700c0e488206014014a803c00504030420342c0d4901d0307104c102d6401c90246070807072404074000c40b180050340c0448a004100e9080b6030b0034020034640c0040007030001c540214481540000ca03603801d0080400400100f0010907841540d18801042840240e20402e142071400030140550300745000c5069014105040c071001c10b45051410702700415003085103010b4032401140d4003091881100540d81c00318000c50080c0200e10303251400381c00300e101e1508010085000b1521581c0000c4217400325030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 811850647 1250 811849397 811849439
    0x50907030b150708031f0305030f0d140103060506030c0a0b090f0a0504020a021b0405040308040807020310111b07080c0d1104050712150b270a09050121020604 70
    0x24001100502c4410003682003440101c41da054080200104d425642a2031302440048102c92200d542c40c0d603d6044d140d100e19021a10b280342c0001c1d603401c80c00515000303041c86400e041074410781d48da5241460401000c0c03d8070395a00c01e02502c8400030041c0781c0003045134280c2e84506103491500c40000100504003450200080e04619528000505582c0f284064440f00b11650042e05c481940e00358004ca104100410380e511603803a21090101081d80082d669910903840742c1c025513150482e00000c1c0c80c1c12200900400c5160414082440600800001d0000a005801c40d11101c482443d440e5482d0102401411025030001000d0030743c1d0701c0c01d100f03210041c5001d1144090110600b0f80420107880d0b04542c10070100e9208000e41c0e00104e911f104000b203020003503010ba6095403d02c0c0248030a8803540313254200748444036174165806140d11a5001c03080d00014200780e5500e5482c00040050002441b420050071050703010700404c402100414002580e00800795480c280c24041464081c2403029404 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 811851897 1250 811850647 811850659
    0x60a0903021204082b0504060c020105090306180d0504121212060f030c1211040b130f05070206011d010902071e060b032a0616020904030c050105060109050907030b 72
    0x100b01e240604200410250556030b000e81101018482008109185000352a100c2d0300200c4104104941c404180e03410384840d0700e0700391002540750004840900032030010076031500400b002d10500d039055500020b01c1c2c0803280d06884220030308080603922806184208034410001440280005040340d0340f1a518070340074107000e0308585000510400f158003e401401c2c920b10105801d10901005c408200001d11010b8410502131000d50b46059201d01c180c052103005a440300907058899640c80d8200205400681080011000c07200c0000301512041c1c4005000d40240740000c0f40d441010003004024141b910241802a4a4105007d0080d40046c4094802c0444580c9a0f11034402040f08034135098000d00010036a01d03c1c4074105403d080e500c030341c1040d003240c005069002d01d26240c0111981c0c0354049a05544030448808031003e1900708080007540803901e00b00b00810543c2201c2d0b644056030241c80200600d0380c17500300555240509020350f9500c2410280011800b622070b07000144401406009 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 811853147 1250 811851897 811851913
    0x507050408030f2a0a0c0b0a021903110a050c1903050604140102070f1104060e01050120030702180a0b0609090f060d021908060606090607080f041806180e060a090302 73
    0x2d44d8082c811407032054192500180e031740703400784022040104041c0040d402154a410059035000e9600d14100050800070008281c0520502d030180300300c080a041313030b141a120043c070540381c81a2101c40c400240751052010070145190810149094015698480000c16054549450f4944010700c044920a041d40d020051480001c4a448200c501d00d0302c50113052100c010703204108002d460319604000503404400d40100143d81e4000c480303001d140f0381c400e140341c2d034203c249086608511462201030740114070310030103103400c0205192441c03141965000800120101d6410415a0303c60280960703404901880071035100100c6c50909038100c1e10082c4410303064009035010031b0140d005103c0048180e40340501c1040b00407003c0c803000e940311104a6505250005103000680a070042c03d5000e040700c10301046041c5985800c5007100c0c00b810700740500649254031484100e0180c020341c0038a0300c4490300490841c030b003010a40115100820380102a00256032a442c541009242442d4254114030580031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 811854397 1250 811853147 811853197
    0x3080c0403050a0f02010305070309020306191104080303041211150a14150f040608060f0c04090e030910050a141c09060f1b141b0f0109060507050408030f 68
    0x410f46100c50312404510290f0410380c000502200c00c010244000d05044c1109400180d44c0810745da40e000c4005041c3c07000850703a4150710001000311500324011034400241c04110468000023562056101d111003510300c806c442022034400c4000d00401c06154008001101d2108104507950b50115000400103120114a810016403040650b0404410304e1000312010080c01d00e0880c84401e1801075600303000240c6001d14a9136150070040c080d00c01c01c00340b0790201e040c2413480f5049030002c1003248024001000803001482d2283d1019980e80e2103010310720b8513a501c0b1030060b4240e801ca9441c40d00e40d00e141c1d02d4450414840340d44906a41c014541c02d058508040d442d4a200300d00e0030038020303c07000440d44030241d2a503041b076035403040604001c40c401104814803036002c6030410104010310308260700c0e540347c201400f580788410300380300c0001d010b10400300610f141c0c1503008085030741c0240c1d424810354130b503c0e5040d0303520b201d2405200081d40040040c046822017810003428240d40c020400806844010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 811855647 1250 811854397 811854403
    0x40c030b09130c080f060a020c030412050d0f0f020d1116090902030c0102060103021f090f0b03070f080114090408070611040306110f2a070603060f09060602070303080c040305 77
    0xb82c02c489610301500605040c80920500c100240c5a000003d1605420f0640d645503582030050066a2403500060820901103003802500c0080c08506210905032003e45801d9454590046041c2c0c00030722540031159105126144041e0b01e00a5074024102c0300407000b000301e42c440c0d4001200449803080c20b41c13010310550089a1003004100070f01c4001422085441003508010000e00514110b60101c0010710140e5101d841d014102040c8030684117480e910204190780300b0100d68007820004004150003e200c0381d0b00c0d4021442900940d031111110300c0ca551003607503623035420b0041c204090f4443c0d0b01e039105401c0418000d500725008407802420300b046542d4050644902401268446202041c10020840140652188082c00c00b01e41e5090002c07074a0407880f41c0c05480300d8100705d0005107619440d51b03015040c8001d4030034000b40a03640c40d0b588510014015141c50710440805041c008000244007038140308560030b464132070303014208142c0b45032030440d25180c02400541140303d08100001c0000e07010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 811856897 1250 811855647 811855651
    0x1d07152a03050a092610060f0506070609120e0f120c0607060b120f0706050418020904021c05011403060f01031b090204080a030e060328020c15010f05010c0b06040c030b09 75
    0xb10b120490b05c0300040c400c1a040a030a44040e98401e814850b0500801d05c0c08403001c000c2d0b9009559064555403d420954050302e045440907203001c000f02d0201c00460380c004d94800302d0300b030700f43c54603400c1e140218280201c000640d495000c030350304040000d14940c50554020900180100408903800e8030712000610b8030640080e80e48020340c0001c040e0143c001c01806200028100f07403c00c070b8141442d00b051031a46110b51582e100c0c0e003981c005580100c941c2c4a82c19103c580703411070409070481c0301d04240c0b20020030b020f0040c16680e06600482c040e0301d00c0c0006040d4420305d605c01a00110341d2851350b0305070003d8900d040201030320450a00100b0310311107502c09000200014001898040c0300b45c100038040042c1c0d0350300305d4001c0c541041081074202c00d951032072140c200c020302d645155410598001c0d0003030082904110240c002c51700c0c080b03000301d12210218140c6190207410104595a8001510388818010008002c806010000741140c901036010030500380940c10b011802d80b03844400241e140c401 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 811858147 1250 811856897 811856939
    0x170f060f010f0504031a040201031d030d09080d090609050c0301091e050703170301090605040612020111070b0d0b100206040f0b0402030a0f05101d0a061d07152a03050a09 75
    0xc1c0007c1205541e414002e8920031030b020182000e690320662001c9407070b44507580e10a039141e0b440d02c9114082101e100c04441441d07543e10000c01c0007915a1030050098015070700252071074802d54511091614041c400c0b24060381d8031009510140d06074440c030f02200c3c0c000324000d035814083c140000010490351402d00030301940100740c1d40c0d40c1e58141038182003180d896400c064013071850804240710050300e86200c001c15603024240f204810f0100c1d0440d628090b40c907005004a80004031709000c130720510360040d00207198111203050b883d030b5001100f02d0307880c00211000392245215540c0d0001080c2d0f042022a0458000b8056035000d901c00e4a40e4401200301c3d02c0300300d84a5022805480002400340318000f212044d0325031400b200303211311010568408000c030b800303010f1990318140c2e040b9200807149201c3c1c0e1003940c641950161656490100400d001c2c00860002082d9000003598811030f5268086039202d80c0c4110040b081441030710200c0c0c2c15007090810350207100c2d441d1000724a01002500c10a04545 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 811859397 1250 811858147 811858193
    0x1802040e06090d261f080c03120901081801110a080f090a05060118020c0a06091a0108030d050603100504050601060e03072103021c170f060f010f050403 67
    0x4207000114070300200910080f00b0041c520b0f50094a01034090703034031199002118070b1110151202e0403c1c601c0c1c0c0c81d0400c610343c1c0003441c04c43d00107807684c008108880d000c1e41c100d0a44110b8000002c2c840c14030301c5003681542c0040c040a000408445140c0c4060181055100001401c643c804005820320384c0a05040d6010490a400f0041c5201e00c1c220100e900c45264405015071180d517a49055407601c040c040d2807a00e140e1050b80440c074a41c0c40d810340c0c80f07440300c900450390070102908101c1c006040d048400d0314500354150f820b41c440c3d144c030401981242e1003080210f280402611400c0003c10014000c664503002d4280c240300d6241c0d0310b0046901450251020707200c59450210058100e20013000114040d8000348000c12020f0b641c001035180400300c400c00000d6014a5180480c101103581c0b1103140032059800c014410150b00c100c0103094004200400000d54840304509500c04500301c0741c450340204071225000c41c9502c5410101500380300c0c1d0510500301034a030754405c103000112210003d0088 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 811860647 1250 811859397 811859401
    0x21b010c0806090106020d020c090714040905100b0301030309090213030f0b150102161e0f29040b1c02040f090207110910030809061207030c090b0414041802040e06 72
    0x103d8100002401040b040c0010000b1030035040e40a500d85454543c59845548000005030b10540140c162590381c810195800e5030b180e884100b1300008003c00e44504420f849050070216181100c2c4040341d052320740580342d202e1104d16081540c0040d40c02004040100f500e20b420000c0000c0b010510103510900c1031101c000e05241c050f1496840344080d14005046500141c42d4810018160900c0401d691441c015903014440080041c844440964484004a0411f5100040c1030500c001e07100c50103241840d28040140d1030921000c154043c501607060090000c1111541070b112055015008803240d5102604066032405665882507080d80710500c403d400003803070401c000070710720050325103c1c084030380c09980d06004040038100324540c080108286030005040c441aa501c5050700c10000005c02c024495144c6004010301a1824090b070402096607428082a04203c4000741d07410740341c04521181e5045c001804003c00780c01e114507000c1c0c0300748109500101617110343c000c483c0d50208081c002c0c8114 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 811861897 1250 811860647 811860649
    0x63127020312041211041b0203120105030307121d100e1801140d170a030e0d300f11040518060a060806120109050c030114010506030a021b010c0806 65
    0x1060071104982d0341108100404e1002d079040c0044640f40c00d40222094500e4440c2d04045001001c040300d010010a00d000c484400c5258000010704040c0000904055185d90b14014959240190743c0020440b42040319032003410b501c03039881440d00b00c3d154560410403910040105480b0080706040d1030000ea080000044642841d4120440e16400000281625032404680484503100034480c2c03442107120008031810300019160f880324020410081540d40c0301408006070091055089040c601c1c0070700c1500d90302641c00b0b00e02184581c001046403052010080b0600511000140800041c003592024203000c40791451064100d4101003406980d903883c10002003042034100c0c040e0300c030415903030101080a107446c1d01c08948222407150034120101d850728800150403410b0b16038155002e41c6844018014040001404902c8103030650003048201711010807154030310030074056071744c101c0400c101040c48508550300601301c84141d0f1880300c0c0c081c1507044000d429500e00003107800009801a00748095 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 811863147 1250 811861897 811861903
    0x315180108010c030c0207033809030304110108040510110c03180406050a06170c0c03070b160c0c0e0408121003150e0c0d170a0201090b0631270203 65
    0x444014001426001c7c5580d4a5420b2446a81e0b0b50b0007280034052070750403c80988401c0c60007171b408250700c0c009c0706141808800e91380b504111400c1d618148040480e081c254050071045000d240c02402030084000d01401200141c040d1000d02500c9120030404262024814000b41c10040d00c1c054060403080000030401050703031072540003944120350242c0108010346c3c1207024002e0504040350703a8001c5540d10308103072111f03024030380700d00343d190000060b44c104001d40002e42511854012165402248031b645c401ca07200c80300d420cc01082c500b6621000d01880d048600b41c1c55201e40716600851609252001d034030840001075401c150a8503000200740204629000c02d51031000c91072104000780842c08603400d50b15040c1c0c0100c0c5000e40740c00a4501e092000341501443d028907598120ba41d5aa458403000340245810704080e036280d80458049019498540c000440d81d0400000f4070000108000507015040c0191200341c1c50b0716952550685000c4e0a640c0800c604001d0607850450002ca900501d82 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 811864397 1250 811863147 811863161
    0x16170405030f130504150f060f02030702041a0102060a0608070303050702120102040e090c1813020117010b0a030b0301020a0503072a0c0915060503130c030f061d010c050315180108010c03 82
    0x22620001c050501045c1c881c0d051f64400c4480b6441c1581d9a031098074420703400d6121303a0310017a402c9030600211508511499900d164014801e900f01c0d845580c40100020803941c044c01500c1007900600b0040001c00c1c072802c0a050601d00040622042c0020000380da42243d01540c031014580481904004240900380b050080d140001d4800d581e20051807801c040d8410302c010070f00705a42c1034259a60041d648907161200c000040300081100950312440d1070b40940c5c000101c400002810181100b00038203045c000d6030704044594803100c0c11074451003816a81c1c00c8842c442c9210f0741034640350b00307403250000d0301d0b2410310305d80205240482d040c01c104445c0180ca000c9040418400d408000801000307521038103d0307510116001c0049455800c900e00050702c811240c3c0054448080608070034107003d0319038088640c003400031842e5641900c100031018240c0e03a140c070012001c81d106000182039078a01e540c42c4a04100000c3c42e002c0c0008602c0d9110b8010700c000e0b045120584e546128481e007039509881822 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 811865647 1250 811864397 811864421
    0x20904050a2c0d030c1701030507140402160609170406030c08090d171003050609101b020304050d0f140f0d0e030a14070e01081516170405030f130504 66
    0x1c070400c0854a0140c3d54040e01e4860404150780c425459003039620540d0015480384103c01d40d9480d950b0b603030800720360380c04980c040c3e41d072090b968540079006807510384221214941c02000c0102c0c10802c0751103400c02401403000c00e0741c0461281c4c1c2550321702c00c14100280040c00031074900191803440345500030030b0752038018100660303640004682d03134441d45c00c90400040e80180c0c1c425412280d8590070783ca07070307034031501c0e1300060561250005102038840080b440c841c03a414015001c2060b46024100b20f04041c078480c0d203000141e0001c00050182d8280038148680c1c141c0141d14000d24a180ca87c1c605101009001100181c0c1d084a60f01d012207442c1445038200300c090341d160006001181c0702c0040d482c0c41644500810382d040c02480c19441c25014030800b0014154241031050942c4d5800903140c030b819100f406900b2161a050000342c100d08184002c00900301e8a40da04426074070103182a06607a88060810740e003c1c401448814640c5031114000e000701c0981d2100c045402e0b140c6800e101c02d4400c0d41d4080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 811866897 1250 811865647 811865711
    0x2106080f16060306050d0212010f0f09050c06040e0a0b060f070803270c01030906270302151003080a14030109090506010e0403140703031b05040314010e0c0112020904050a 75
    0x5c0110307699440b40301882540484400016581c6451000d00514071403548014040c100790341d400b5a05000c0d4814081c2ea40100700781d40002850780c08001321031196008082d565007030500400c01c0c00c3c1c0c2607405280a04409405545821005070110002c0d4204070012101450008104014008100621012080050100d1140c00c480c0a039050b11050700304000c604041c0c0e203094031014041c0c1c941201003003252101581042e0040c40344c1c0d060428034600d030160301510a003400b042c100f403810020a44540b0885112400307850540c1e0340c00115030301404000c0308118150068403404940040114000c00c038001000580110a1502c40e050810585c4040c240000f80d40810010030381026241d01200c12441100d2b17076500316440c055004001c952000e440c82e20074a15142245a0080003c10540c0d0058071200c2d13003502500190f034265807640590250b40c0e0041194102d0719405080f01d11580391300454054201243c0e0346c080760464008a94440c0d0a03522601000b201801420709480d85012201e10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 811868147 1250 811866897 811866899
    0x90501140a03020a1a070b012c13150e070801020d060e13081b0106080105100905190507030b030303090d0906090608010e07030f180c08070302012106080f16060306 72
    0x55030030301c0310321401040112031740e42d01045070141c4040382d180b80c1d884a490085940c45242c200041e04085400f140c1c200070780319100401141c0844942c1c0708888422451000205694078001500001e03003540c400b050700e4407110100b513541404400080d040d984001604c91508102607000d4840030750081c2c40344407070b08052011140b40c09011403881c5400c01c103440d41d5200c48045035000d01031361034113040840d4607200c0040350202040d00030b580120803590600d0400340e1249032120840c0d8061340d815a40c524080751500e80c07800c403134122036031008180c2030004d04148590003082c10741d40704440700c014640100070f24101003500072043d04050f168900d08520040e0030003038068a00107043c0212100140d9100c00150400d03c81d401c4004000a40442400105100390542c208020094011100c03c00e2000d0040741c1c0a90000e1000c1c12690140e49800341c1c00441c1c1500c860160030320400c900d01c940c40e04c3c0007084007a01045803e10341c1e403080c40100385a1203004100340340f28515030081000c25040c000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 811869397 1250 811868147 811868149
    0xd05160225050d0503090a0608010936020f04060806040203150c1b07030f0614010905150105070c03050607020a1713050402031024091401020d110f07090501140a0302 73
    0x1c1081d05941080c0e074500b1421070103007040e42c0395020f8030b0219079001d02c0c0300c440441d501e90f000035454100c40030f091003407003169540d11050f54948049010800c050094001c4250181c150010005541c0c0c00a0b005030100304940300810186c1c0c1c110340110b245648003400344021410200010803000203525040c44040c00c250186c0d401610400d529880c1d181111100311001010030300c80d4000442d8010000203c008891400c0c0025115002094201807250000002c44007041e01851348637105403544503200501400054441d500a16026034095003c5480440019001c1103103501810301500141141440c625004803031101904180345180030500c00c01c814000404c00120588800315005603ca0b039691006001c00540d03940002c800140f04107500345a000c91550b2580070246a079950b101c0740340c588500012655256601e43d0050f4048413240186d039101e00d00038150f007190441a1003881c058054080d01d0010326800c40d80c0d2080d56500104480300740c06c1c0c8042c0300141c09035040d460047c5160 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 811870503 1106 811869397 811869463
    0x806070f020123041b030228080709050412170a0f020c060a0b120a0f02060f0d020a1709190b06030a02190305061f05150d051602 57
    0x2e05c80c9185081744507150060300d8014064614140a19600401a05030000c0183e00c00c8804000400d24140038840035008040c803030fa000c00e03141460b04090188156001c0d8010a001000d070b001a07410b822074610b10381c0000082000110601d01d040704001138843c0c5804151701e03000700700801c0004101e030784c4030a4080d841502c5041c6002ca0103031003140d135468803180281451507a0032507080145427200c01021441110402c0505103c0d002c1b405a050360041500c45002c40c0c10b44071091030244900e05940e90050302d502c0241210141140c140300c0c1c0c4112101c010313103000c2001d800140f50b07032010810101000e50141022003100c240d15844842104940821a000c3c041d0001203285245e49000b0070010002055030051054135085c204010f2140c240040c83c2ca8080c2407061410140700c500c03419118590140d20340d034259104c620000d092409940d243d840c107a2a00d96007405448100c = true := by decide +kernel

theorem cover : BRFrame.Cov 811690647 811870503 := by
  have h0 := BRFrame.cov_init 811690647
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 811690647 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 811690647 ≤ n) (h2 : n < 811870503) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
