-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1192
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:41:17.194098+00:00
-- url     : https://prove2.me/submissions/f900e479-f275-4f7b-900d-cb4320877751

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 214208633 ≤ n < 214388489 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 214209883 1250 214208633 214208647
    0x13080609070905060f040914030412261c09020a0b120906160818010914071d01150309051209040506031c080403020a020a170f1c14041a 60
    0x100704003000c0030b0040000c0c14086490035102040440728042c006912480d00d540071003050154600c5945042e11005041d645d6035500c51701c003100598944401118070b16085010904040c2c07040c40c41c1c45004004c88851450070b040100250000c4190008214107242d0313414040005903522010a40105503100715540c031401042103200400d40018280842071b08800208004031140f661a52780d29200760400710001c0e00d500c8202d850184c0d103036482c2c0b0780d04e40c80c052562040c0445000c0b9160003403d044c04644199817030740c3c140303011044110160b52085502c0e4005110801d041d02408103800c8051400144440f00c589a0038030380b80c12034400b00c10003540047c055080d42068010568031108c282c00034103000c9800041e0380d86040d00840c0325010008082c01103400c25100703000d81d051054004204505150f203032848500c294030790401c08210791054003000d101d41c0201203110001075104902c07030502104420005d40e0340780c0190040368501070017000042510910b000600400c01032208009844904d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 214211133 1250 214209883 214209901
    0x80d0f1a120c13090807030c02030f070815090f01050c030a0b06090609121c0f09080c1503090c060d0b0102070617011e030602031303031a0a1a130806 66
    0x1004035065004000c80720340c10366a244001241d6401c00000d442021401112a040d01d0043c403030018002d1080d0000510201855840001a1352580c000c41c144d0741e41c400344601141e40c424461050300000d030030a1300c8066105a6012065030300c00c0209050300c0c7d0700380402140070308640c404c60b0000c00940021050041c02509841b490240c1c0e4000c1c0d4480345441c4001001a90901481080c18458a038000700e02c100098140030b107507524039581c09034162a03190610050320f00021800c105c03001070300140780055910800201b40b110340b10007420003448081000c680801503400240007566900c506a1801443d4a07007200400c0149a11100080d40007a80c0000a0405a45900900401080b074254040d48000315013105c2c112254440000c64903541e16810300c0102a9940c0003600c6940301208000d400d404000c461050320744a5a4100607001031051541d00a502c4204405d400002d1403405001961540441c61003640b075500f07440c1c0c14030f0320001f00c502024007250495001c2e0340000e414040c0443c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 214212383 1250 214211133 214211171
    0x3031404060c0813080405091005060a091d040f020d0c0f060c0c0e2404090b0109050402030c06030106050f030a151706010b0a050702040203190f060303021203160c080d0f 75
    0x801084000c44d91401d298035002079601441c01018031601d48000461000107401215500401000d45015192405000c1c040c007406524401c80c8980d01c40c00032003c1e06d400702c102906209a07841412541100c00075000c1c0060350700d013410101d80c805544a0b010038603007070100070040101303c0c03995241d071910041d01c1c0143c0344250703640c0044550307590300b81800201c0c1103c1064030044010600341e51481130054000401a18a91202400c1407860b4030002c281c1a01940000e8401c074029821200700d00121820300000744402d1207035000158052209504901c82c09000715005200b1040c0825103145940320018204060b6000507851044080e003110481c0003030001c04e00411461138814180b868a40c0060218410008024880e03640000014100c585980d1400100141d2500822210501001840041520780400e502511500d40c0307501321010512300300c92040c90f042c60003002c03816065400b91080c10700e201c0111210281030140c000d2210051203014035155141318045152314000008038007407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 214213633 1250 214212383 214212391
    0x10b1c0903080610050d0501151706030606040b1302030c0306100f020d2601091512080d050403020709020c03070b13020a14030c0301020c070305010621060903031404060c08 76
    0x1003400d1200d000302290304440e88a0f480801039400c03031590000c2c4681200e0038031590354400c011600d04000403c6000858144201c960120f480c0e204400c445100c2070512000110f960662561000001954234280340d0440400d06901038090f9149013805668041070b40c00444014070000404010002c07640340000c141203005909050400000002c0c05009481e04c8641042100340241c1844169a58481201080020b80819110501c40d6140c0d00317031001601c04044604800b0024180c00709010305001429580300da03000d0300c04c41c42c1c00344140e10000501f1000f841502503025845001400000c079000400c0b499540c040619a189818500780c020420050201c041d500c0c80214104016126219404184d80360301c140c8200c001865400a49000b207080350f00da4044d4008241020b082000061440540c1d120310b00900a0300d407180c0c0d1041d1464207007103542d4020b0440031000f2002c01c00c01e5000c080464028600441c240d24002c1005140300c10035101203401c0b998800c074140c0741c00e030700c82402600 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 214214883 1250 214213633 214213687
    0x70e4f0f110f0f07020a050414010e01060e0108010302040b030f12031906030302060619050d0506090105010b0306010f050c0a0204021b010f050c0421020a030803070e04090b0c090f0405010b 83
    0x20070802e0ba49140440c02911902070302c3c0080041c20f10150340d030307103200c5c04001e0400600500120859189125410800384540412625000000300c1c0680c01a4001042c289040e524810b040c1e186400300b00c05801c1c900000d13500b40c096410b140e44101d1007070180c0c4042c00d102000303003950303030800170101c2c200040121121000d00d03103030100910002e540402c06940102007110386081d110000904d41070340070055804142d100c101c81440c00c00700203000c540640706840c558000c00690f0ba846c04880d6080c4800c40c3e0403130003c0c8120b1450910540127101822048950500f159081041680800c080344d0180e000100216000c40089000c030300240202503c000d00004140250309140250038494055406010032400488032004a904c148081c81c07001c51b81c0082001d070700140e03a0306041015500030380700440000e180c15848a0702e41003a001c1e2120320340d030012010ba080d0362000c0c1151100e410640060340d0180380d01c3c40d14100703580c5901900703028000103003103c1d07600d45901d440303003440d10315031800056 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 214216133 1250 214214883 214214887
    0xa0308100f24030605061210150e040b030607050306010c150515040c09141201140a02070c06050304021008060303130609140a140402160807030305070e4f0f11 70
    0x551954810742d4803003031408400e4041d0391102000600600b008d6040200a489200c03d003004060b40480040e003a080140d0f403c2003106c144006054a41c842100c140000c14802c20204040e948542030101030980180007034281d1180c02681c5034240c88060300d00c2100b03400040d00100741c500c0d0502c90814a070704c041c00c00b41041c502d00501040d0802e17030105014880d000804040c050990b003900071030a410b4551509017494035240720080000d400180040d9440c4c00400c00105000f030050701124081c3d500205502190005481c007101c032040000c215179010300003031041e000d40e60380c500c1170000a4089a110011070505108074120151f109643e00b80c03042c05800c40c01c100441c11520300310301c2104150380260380c8070b14291030740c91801800780d03008000f100c0c001040c105050b419400030340103800f1030f540e41c150390702c4050030020b00800700a0741c00d0820b291660145554070b211400c40e00c890800201c0010070250288080f0807a0109000a40d1848c0e202cac0900d81094000d84a4144030f0000098600c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 214217383 1250 214216133 214216139
    0x6080a12031505040f0e070f08070f031a15090403020d030b0a0522240501080c0705030d1508010f020d060510080415020706051603050601110a0308100f240306 70
    0x10542c1e4000c0c440c0501803a5204403880314660b0541104000e0050103007214980c958659411904d158035202c0e050701400f4082c0040b070001c040101c0396003165007142c0035000c140d00c0b1010918080d200502821614601c0822103001030300c91441851203a8041d4001d0030340c2e11080703400030317003a01e000c4012039100380c1c0c140c64184501d0351901d023480e80d07882c8600b00302151150b4031075402c0f004000782204500c95501d401c000c031085070500344e01e050030f40d4000c0c0d1750603c41d41c5030b80c10710078440e00602000074080d4006011041c105c103496480394403c506400b6521480f02d5603003840a003125003540400d010b0300c4d00080e22200d904e00034041d1000a0800380d5200151082c0700038010540503000c0c0000b0194224088120740800c0f241e010781e42c40c250003442c01c1209003881c400f4505800466030004010a0501c0d002844541c0240d6203041c8808002001c1d203002d000b5941d08641d003400050130704458541c1c1400100d003c200c0a00c08002034050791902500e04001c1c20351054144145400c03620415040020034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 214218633 1250 214217383 214217411
    0x50402040f180f080c010501180c08040f1128140a08060c03070306081b01320a0c05030a0918110901210c05040504062301200106080a1203 61
    0x740c200300b5040205803140b0030f0715280080c43d034071441c07200000a41c04c0c60000b10311000100c0072840d07117030940c0b013013002401c03105403081da4001c0301114041d113106c8041c1d8a200100d0307111810000070000c014038414114100088000d80c440e03034803e4442c1d003480c00340c0003403044500110f4103401100c41214801350003441c01124940c0c0300c42c0200403400094002c004a04c40703501a401c107001511900e01035480e40310404080b0701080300fa0403406070010701e0149580b4a10034004164072007458034103101e800038121612004080741c3c0016030007000c00800300c00a9000c52400c0c806410712901c0382d9034503075169203090b080885005a4404a04ea15454140c58010301090082100e00000003801c0c000801c800d0002d03010500d9428940780d82e821070815049040d5154084024402d444041750104002c54440c1700650154801e4418a411800d1040c0c0321211903019940511706a540051003503240545192080c1c00c0d203c89038040c8800394441d80f404401c00582003501c1c80c140718280350400010b0201184 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 214219883 1250 214218633 214218671
    0x609040204021303080307021b01030c1403091603060e011b0903020f1f09060216080a152403050d05090d030c21020606030c03060f01030b101206050402040f 69
    0x8001d10039a03002610100b541c0d01c40300080019608026516202e2a02c0c1c28003a403250700c0414074140e44140311600625960203803007000c050807482d0341c510040c6482d54003002d06c1075002800702516071080720b1016000b66082c0039154090741c4604008500c1880c81e207006425a040c98020490300c2c80c0502d600085258407020001c120b035012503803507100c0304a61002c01c507400b202405a200300030301d9803020324080f60480c40f101c003107504960880b441005007054036501c01095004418050700500c1109000c0f494281c56000466071509000038010b02c13203c641f150441c0e41912840a982c00e50b0303010000d002c001e200c1d02c0d82d04403282c00e2513031905132424005041d141c50850020300b80450307440c0050078805000b0341030049482640d8104400d46d00082d0103960b0f240101e59041c030030311503074003164440e0034003050a602600e800420101c00741d0940d9540400040020301c00354148912001c009186040c0045500c0c19500480303000900342414018041560005000750030b0181c180350b140300741111000340e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 214221133 1250 214219883 214219891
    0x40e010f061b0309150e03060903131806080312070e09100e13050d020c3a05031204060501060305060306010308040501050c07081c0801080111030403030b030c04111804050609 77
    0x245611100b01c185010b41c1d0210700ca1300301405455000340348120b4a030300304400350301d000412000c54140380d84221506030b69216502641007800d075860340401c4500d03142c0c248400f201071000d10100c2c1c501d84a040e8070707166402c06005682030390020402d00442c130343c00000158a50302c00b51401541450007980448481e6054401ca415503580340380052a210410440f0305440c5034004107542607085051070007559240840c1c1010711410010703101409050010760070b04851400301100209030701003900c0452418200c80760a40d12030008108546481d41103c200743e12903849420002402c3d41030036001022550001e103210b00903485480140b003c14082070551303084030401d182c8103a559040c41d80380d070308103c51940100b4452246001c006030301d038802800383c2c00c103c0c0a41d540b80056a600c0c0d280f14242e4901014288080c8003c001240101f8402e8004095400e000340454482c14005404074013211402c4001e06440d0102040d401c5000103504002458905d08803003c1c413040c00c14900064070203201070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 214222383 1250 214221133 214221167
    0x3010501090314011d06010914150d1e0b071103070506010e100b0408060403180303080114060c0f0c10020d0203160c030b01060302070c0905130204050c0d090602040e010f06 76
    0x9001d080c240c25080341e550034031050088a1118175804203966950401c2c02810041d40c01c158110a01c0d0640118007440f6051940e244500e50025400780f10441141440030f603806000345564000d4150f06004510a55202d070407040c0f19490a04002030240f5482800c0c01025042000300c000420b500045c1e00381952481d0b048170044e0f460300b940c5c0d048104241d9010030700c149400304000030f1143c00440ca040c400c0740240c451100b00c035a4079085089031812400000c01090300f0a0040c441c0a81101c007103100c41030090011440c24203050800762074000c0c02103004505911140540d039850819100301c4036141028001003210411010019460340101600700e040002e450040c0d000784101248020011a0414a00c40d810350b154134006005c0c1d84884c0d8191280140ca0380d0006c0e900d01288135091090b07030040c0380341a0700c884a90800c0094680035140c0e1555400a00c20038103214040d10442484134418000165114900454074a00e00f10581c4001049204110100203880c0c100c011114010110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 214223633 1250 214222383 214222403
    0xb1b011803050711040e010f0b030706080112110301020706050103230f150c070b040f0b0f041a0601020a05071512020a02030a0f111009050c0a140409060e0609060f010b030105010903 80
    0x82130101d8001d0107869403113a07066080c000e0741a08101c603079004d0440c82d80c041d03051b502c8150b1075150556040c5402c0c441c00e800307203814080b40c41c0410883e103a604c0c10080c00400241c500490b9440e803200b030314001c1c0c02c240d50110030307902600c024000390039207078003061110f5002d1300480c064148503544420340383e40c04c0031503259194001402c0c00e107200115510309501c546c40c500035007082d05018602c40b00045046501c0102c0e000860074041c0410b074510312403540040c619000407070301c02c00d1202c2130b0b40c00b91000d410348c4a114054000244140003010140485a0b030f0340300c0e4924a402c00502600a020340d00205610400c90401200d5000c01218280c07a02810507842062001c01c0840d10500e40000720b0340c4a008402070940e03102d00e07580081002c240030300110745c040c0b4098420812600c0480c4204001c03a010a5002012401c0640207481d00c2400780c880014144400501c032420082e00310340108158015074200443c0b0141d200700303240540403000701107085606040018003c00190701003e0004c940c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 214224883 1250 214223633 214223663
    0x110907030902010518032a0a060e0a0b07150603030e100c02030c0904020d120504090606030507090e180613050f0a0b04030302070c08010216020a060201090f0f0201090b1b0118030507 80
    0x800c000e64000c4461325660b19a17040c2c0a68800c7d01c05040c0d508200d841075072454000140644540000f180f1710400508d842542d91401b441c02103180d226a170100c64041c01907000204080d400d110b400c00031070080c0c0b1a450b604070000d0820524038106252507050111686143e03015840000c0c0710360b11040203076500d00060300d5600015444150340320000f0a61989004228032803a4850090000c555032000180310141d01d0320300c281e0981c0c8049034001b00281036048200101c080320100c0c0c6401410076140a03420360051200782d4200742c412945480088400b28003101000010070005016078038440c00b4201030109030707998980d925405400502003540104e8100280450705d202c1c0b400130880e9100071540c800440c0c01c0112210300785403043c0c1c417a41e190400041c8180c018080c0c1c03407140f980b01da050003080320703555900040c0707009202c4144d0401c044164003240f032a2420000f48003c2e14025007191810f84c200301c056003554504021107422150308400c1e0070000e81c018081d030707205a80c800c01484103130b04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 214226133 1250 214224883 214224889
    0x3030f27080a0c0203060a06031502030f1f0506071a0a0e030a030b0a0e01180e011803030f090611190504060509010e030f030412110d031b06090b0103110907030902010518 75
    0x145100f4007962500444081c00b062400c0c5502c8a002c41307101d00459200120310050a20890004075039842c01e0040e584c00140c0c800445d401e00b000301c110103c40307403084c0e20340722004036089400650044800002401d0000d1640f501030b000585d0049104600313000c075480070b008083d20b81c0601d80300d04061623220102500d0954030303c0c0558000d80610007000311786684d110080400803a1080c1e405901c140b811840345a503c5041c003803000309504802004104a12660b01180203012a41102803039a9499096000042c400d026034082000c0b100c000c4c5440e40f0811000009040e00c00000d9402e2203000c2008004180d045026244100d1007401c2060b0078601c1c1c0804a420564440628642030100060204c1c3d42191149000d0b1064001c418006400d09444140f003070340b03000da060103008645d4250440d02d240030303140300030300103a48511400304d074030b14a558071140e210342c007a00b080300c0764800c00780e210f0001d00b07010000035400b50b0280b40c03e2166408c1a00060203501c107100e9810817441c080030900203591 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 214227383 1250 214226133 214226147
    0x90a020102073f030807110705010c0204060b0a03020307021b0d06050c1209100e0c1302030403020736050601091a04030f110a0b1e0a110a03030f27080a 67
    0x4a600303070080f0184000d0340300501c0250080c240c12404204a170000c01d101503c64a00d503100d14141c200202801070a101c0151404200c165040381c0c450b40b00c40e40859582c1032078001c3c0c81e02c0c107007545001d40c4a00b00350f05c0181c1032010520200c40c030311180ca99412056075405441c0c00c2d03150f400003000201340e25464204032051003641040b018250009044c04490100015400c486194224080080000b500e078540e844a2090343e145074000c2000b00c2a07442103106074011a0414482e004841149a50b801c540d00c02d1007400d0840c0c03807182d94413020000c07038003a01c4105000000f8412400c110318500140040e0500c407a5008502510154a0100c0008188042201c015580010900e540501e040c6800042e0822a000440c064a4213600015410309400180d4509203904800c015040303280031070300300d0140c00c04a50403081203510030020700c620300c082c4200c080381c0340030366404184103610b00460401d0307524a0981c039400480c0100c010341001c40060020300041d0f8007417543d96a0302c4903103004032848 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 214228633 1250 214227383 214227449
    0xc050c010309060b03062e060e09060d0b091f060e370e010c020f060a02070303060509091006050a080d0305090111040b120609041a0403020a29090a02010207 69
    0x148601b00c140a038039000011034880032110415081041c01e014a040300408100c4c0c400c0307402003480121080c052785000b20f841a1312940c05080501d4070380458855081c2d11405039024042c03900a4207081d80c09650b4410062031690001005001c4280b030503a4994049400400c105100d8050710b00b0510301c0080407494140440c030f0b03c0f0b5100d450070b020400b61002002c015030048080e43ca07140841c040d003800070400216209030039028103916918070b001400a03501c800c804904041d519100802d080d6030344050340b4003400102000382900c00c0400c0f000310031541e032034100c0c83c4543c00c4240304000d070a078001103492400300c1c2c52601003101c0c0c03160355038a40541a003941ca0020103101040c0441e80804103409420012480c0c0700c1e10110f511440207018610b1b00a40b0080c4c02203032420000b40d03080101c01601c5810a11900c1202e924003107036101c1c80100100f41180c6800411403e1020405d04000c000312a04855403c001c0c1140c080c0650000c2d41d04c40580c0709003c02c041310100703400c20700c4454022405030313 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 214229883 1250 214228633 214228639
    0x10060509031c0f1b0b0c0f0906070809010e04090c0521010603050c011e08060409021212041703041d190c0e0411070b010501081803120114010c050c010309060b 70
    0x30110002c000e40001581c100a000098214010030441c000260021842c00d80115a0180c291500704403489242e00ca0311049003160740410074448542c85840041000354003450701c0d5900c0c1c044560004080b45284031039144114140959000460f00042c0e1500803200d044854140204a511581100046403690b000007546410700010500c0004550340d121240700742c0c0c03110078603076412646d00c0b20b41d07802100040015203240b00141c180d09081d400b407583c3e140010281c41115604c5825a89003007005c20b00711082040c082401c010b034103110121583c401c400c4a01942c2442d083c5401c0300d081c49682c95100c0800392201c00840c1c030012840072101e1405011401c140a9491800d2000e050514181c0311103029074a00384400b0b00110307002d0291002140e000543d60f01341e9190030011a28020094003620018180203420142030340100000c2081143d8131841070b10039031400110410f4503201c0e5140c1410f11054110820000b00c0205441942080c01d080000355144203003418401400002c40b1250 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 214231133 1250 214229883 214229923
    0x306050d12091e14060903060a060906080d05071b0b070303061a030402060a0320070c0905070e030304230604060201050a0506010f0e01030906090501090b040611031006050903 77
    0x10038021400640c1c004a6020340300c40681c0303941e0701c8a642c482880e4103642d598100c0d403400c0510445140040315845264018429805c01d1080000a81000e400b5240c8025140c0c0c1c0b190b00700440d45890203584010660b07000078284c00e15001d1006069481482001080d64140b0002c082405001003200c001401100728429142d5005190182c01090540980f07d40034449070607801580707420b030048038403980d405070195090400001007a000390010094a0b5503507810401d10071004ca8420740640a000e0041954000d05031910001c8412105c5c0600f101e000c00c107444c45d44900c1c0c4c0d28004202d40c204c3e00095440d48030b1405000d0390484232800d1911981d44041c001600103550380d030540126000d0541c100c070421158503036000544049180c261042c002c070b8411020082039602960101050501400e400300b80a41c00d96181400c40b200f00c20b003200c03918031140a00c002d00c0898821110203640c402c5d4070030300e5802c10000ca0900511644610400c0100002e09a40240c80070b001501450f10300d061518 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 214232383 1250 214231133 214231159
    0xa0906050103051506030a0807030f210f0f050624090301020f03070f0f2705150c070f030b010302060f07020a0e1603060308190c08070506071202180f01030605 70
    0x20307140e134810380d41980b003000700c18042501c07842c000c901911610762140e5030614000a80c1d0b03040d9040900342447c03806020b104800035103403a00d00620946103641d001000a008103400c0114000c079042a41d900d010319181408001158480301c1c0600e80301c1904040305143d0850408110000c0d21840743c059800d0350021420750504000d50014500a100e136440b2078927030395503e4400700c1d91046035511000004100e8110204c40100904202c4900c2545038241c4a607951610301040c5842481da20082d03610500255140441c8010b00c480701c013400761041c0e1007904900e19210b60540401c107003c0603200e1480022158200c44c010401c4422a96001d0094244140c1c2d031401104498003c03140b101c40d011141c0d0310032a409100f031080c0001e407940214000d050280410020030062209120310b801d1050401a01c00030a20340d10182040380d00c5038004140c03e03c0c0685000b400349054803035110b580c0b40103011484203e0008455400d42400981d01c58003030711a03e01c01240036222a500003a0440c0d0055000 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 214233633 1250 214232383 214232393
    0x7141005040c0e06030a290108030301060807020607091a07140609190206040905040507030c08060601020c010318020d1b03030905100e1e03071701020702030c1005120a0906050103 79
    0x1061080b401100d9001d40c2c0390b030f07070040860f0702e140840f540c035496044084607800081c034100b041200a950302540030f03144000146121104502a040380f140355201200400c107659110030140d44c007138600c0c406818942468000a42512010b0080050140440a000860900d40403c3d140c80c6a00801c4807030355400300c0f40f80c4907154013059a180c9004c1c000c010b8809812420302c1200403000f680a02401d103014540705e20703c4010f21b0090700407941409080030020114000b40006005001d48002a06544c01d082e4000b900d04000e8180ca18185424080034a5440c22118103042030160140c0b00c07203641c88450325080c141c0d03040300c8132514102d0200035404014598025442c505403001655801c034148104001640d08551002c0000d503c61102e804040503502c540131446011840541241d0171180c40b600f40d40000500220f45610700ea5003c200710341540741c00c2111183c81c1c00d040d00c15120804406e800100710303114001309403c52001400c0400c400c90303265030101c525560002c01c10066961070740f504c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 214234883 1250 214233633 214233641
    0xc030f0207121d18040c170d030c080c03010b0a020709060807060201050c040806160318060507020c01090806072105010618090c05250b0702160806090a08071410 71
    0xc1400040e08000642540024102c040e0300c00f01030041c402c2c44010410b00030003686480042003203c00d60883d04c1c00060a50403600300d15904036001c80502500c09410340d0003821504216900c404000707140c5c040c8188544040220b0741035400420b00d0a0f81c98102240581c50584a940055040d51900c080000c661170003050090503142103a00a205a0316803075904052800345c0e0103103004580001003c47c5043d2030b19092045103014904020801d00e83d0b4003190f41d07000c0d10b5514103650f500d071200108001664107005400550109003415130589080001d910b581d1000240550244a076420200071950303114014240701c824a500705107c1d0f582c441000a020b0001c03106441040c500140020440c8403160189034050b0f40c1907a101403d00c2d154881031000010340844035a144049090380601060907a00102e00c10000b507001003840c058211091002e024256010440c00e41008052124008010542a800540001c01d441c2c4504243c100b00c1100c0c51030310b0300f00c410761081d441141e80c3d81490341c00c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 214236133 1250 214234883 214234913
    0x120302030a0f0e030d0e070902040f050f03060405060723070602090301150b030408030a0906050f010e091603021018090504020112050f040b0c13060503180c0a06030c030f0207 77
    0x300a026100046200409480164140c00f10940042c000d1418100071035000001d004409021a000280c1c2d545050b01268000e4000c02d4920000c1d034801c0c442800c000481951701da400360700401281c076040d280c558881801800c16410440b405d4001141000c180001440012182d030341995620030510380300009510510149000c1c2d400e01080c610720078420b044038030403107020208071455541d5554640c0c4403603100030008458a0f80d80e10815000c920b8901c2001c1c0b1841ea000d00540055041001c0802c044c01c005018441592198a100805680d01414135049990580e0052408450304106446489071850728a100f034048080001d04040301e5086140100d000303898043ca410072506442c403d07907000311106a400d80e0518085000241c6100783c05a214075941055820300010000710700501c0760b140e00c2040080c10100034064802c0450024030001012040100241150386011414000b00d902c40d00040c5a80e80b242c2060050103904080451803100c0c60455a4030301c0751034403660740e40e9000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 214237383 1250 214236133 214236151
    0x1b0b0a0801150507020108040605060102010908210c090f04020304150e0d080112030e010c05100c0504030b0903180909010e0a0c03050d020615040c020a02190510050306090402091312030203 83
    0x1c0e0b44050618001d80c202c544040c0c0603590a84141d5564943c02c0c040c02c1d01921140c1107640c0c5d000784c000410b0b034801c054500d5020f641252403907410304c0d842c00a00c0310b002420403020541c0800c4144120341e90f60076041d0005006076000b580380e0b42c560034200750010365500e500d40c42c039007000c200003406c00b00840c04903c0300c034480d00c0e080296600c5510105100502032402004034280c41880001903010b901d500b0740b0684a2403c84580e00701007a02c08007620400c11280b00402c801060600c20401004201c90348695500011820058000d6581d43c100030030380d040d1400381e102070020400c509429044901040b01d0343c1c0803952095140e2504028615017844103580500441c010310000c0c03440814480d001d1841c0c0c00c2900f41c01008501000001c082c2a20954154030517601da403801a194884038190614001d00da241c195440c00e4280031200141080c4da4003041000c03c1045003d0b500ca0030740036006a0169000c5101e941c2c1d501c00a00600e80708040a03140000100c000e03003540794160001d40c4107922031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 214238633 1250 214237383 214237409
    0x50c0301260303060d1e0b06030c01020a05340b0d0506030303100302190324060e010f060818010f05180703020310111e070c140d1b0b0a0801 62
    0xc044071200007500c144400703495001000825640e141c643c0317110341c2c40c038041c1094440051800c031142c441d48030700000442d03011241c40304020321460107000307540c0c600000380050003d05219948864807580080001b01e0140b00780b8a850076008104000f04480032030311100e41140c5501c80f940700f50190401c0c50070b17400050503c80000c0007410040152030082c0c0003004030601080c1141e08000c1102c10034001c0304a40300c509900007001c50813508810300070424204040c0e40581c422162501520090f0308003030a442500c9004100450000c00d08004840241c41e2030140c1c0d031030b825000400c140803a178500110798201280300b454a18542d0000e40103000051340c00d01940800000c042c3c8030704041c40080e600d904000d0940c409103526030403540c2176440c003103005403030174400c150048480440c9166032202d0302d0300800c040d0100844024110064034010b024004241150070008520046811008002c05045819441c2c4250049203007030282c155110465120000628004c6c0b4150003441442d10803801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 214239883 1250 214238633 214238669
    0xa111c060504200318100c0e03100606090b0a031404030305060f040b03030a050d0b0306010303020f0607030b0f04020a090902032d0403050306010f0c0209131101020d27030204050c0301 81
    0x346094a01c08585601c0300a0845e40e401e2180401072003081d00303207411409100b001d01d0f8144031504c07601400b268030b502c41c5410a15401d0a043c82c09409000141440b40790000521507a0740020626080342c074807217801a621564800c048010b0540c0e1003450119101000500c0201505504040d12803181130b107801c402c080002c4200019200d440d001280c0540041045083c2c1a11a000814202000800100b175011140000c01d00d03002c001d0340140c1c0140c0254000c54407804040c003090b1b4011880c0d1509010105901c00010307500036508804500c40d950010b6074501c56400383c0c14400042420501c1103480e460419961060070940c03c603098001501c02c11040f1240c16040711060040d60583c0c0c917141035540e004015100714001d8000c41c0b042c890348110120043e91802c0425124541c42c440048140c2c1003803130101500d8410800c10f505640001c600d244036690b0101e800ac0303402001c070000314100101d2402c43c2d481c0b0343d041e80010f07410a060400304082200d03607000035412206035800c0c501d0080c007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 214241133 1250 214239883 214239911
    0x30102210721020d0b030a030c200f0108073b010504150e22020a030501171f0b03010504062a080f07200d020c0312030a111c060504 58
    0x1d002c0c44800200c1d0184920a200c81079241e026050040c000f00c0d00282030f6089000081c500140904100d0008070f1a0550000b0000242841d04020042c0e4107408003414103900024003041e0300c00c440604000c0b02c4000140030500c294565540c8615a90704a5001c540c1f0031009800d00e50191420010101000743d103484651080741250119000d82050000064900c10111200181c41d00d08a9024840d414446640c050300a4111207405400a0060380d9491044000d0b050340c50580c01501c092801816000c1101c601060b9054030540e9208442e00081d07080d103d2500400d10801425050f41ca403100300010003c4c15884040c244002c068456900440c40b541c00308000600710b62100001c55603004181d00c540b20105450b006501030800c2841d48038440d000e8410400c00340c3e41d49038190b101416a200168041c81110b1504100b40d000e00501074005c1c41d04039203848040d054018156450140522130308824013643c0c0c041049007188000300110078148005025207008040c400d5180041a030071480c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 214242383 1250 214241133 214241147
    0x1809010b131202010c080c1b0916030905010608160806010b04051c0807080715050c0903030f09120706020a060b0904020a120201171003060515030604200301022107 72
    0x11030707400d052a001c282010a1022800600c1008038144403140600e200081e45c400064218103580c10010f1182d000302c43d82c00c403544860341859500a00d000020701051540308a0300b8a00c0e0306203420701051256181c81c0503401049650301214603400740340e0100c003178614012020401c44960b1802c446079070341c035a030b000080b80c0b19030300c211507000340d20b1101000d5421607461505402d038081d80e01107003040740c1912120010790000000311940008442d081d20418201e1141c0b0f40c011164001140c2409403140101ea0340344140340b15460403010110b14400c080d07a8096603a10041b00080640300110b640b0100070b540c400740c0c14400c9400505050003107201f4141201c0080c8580d4004214210503440c2200075039184d0050300b0141e0401c1103140101d4460950203103014050300e005c40c405080b0a2850810008541c400340428172071101507622025156400500190006c0d006101a8000e6a04080a80204402e03035000354044d4004603261000130740d9040310303c0c224000d8842c5000300c0d0366440400c0f1800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 214243633 1250 214242383 214242397
    0x1b0a0e0a03080d0204080c1822060c050c0f0a0222061205010509060a150501140c0106080304060906171513090b0103061d1e010e01020f1e07050a020105030604111809010b 75
    0x441d0340c88c0020704e900181e046000d0701c4040101c90044900034039150030303040d12a24000c4102042d40014507003080070042014a2111405101400c400b41c80d5600007411084240029181c9410301201c5105180c020750080c2d0007041c41c0b0f03021aa541980c1d207040e41c06008120740c1159903001740300000314008c041d4016a101c1d2905075148090803424500150750030740320f107480424010824401418261801d1040c0406445c0307500046459502d40342000740038811070b4010008000a800d152a5110101c0013515041041005a1790040c1074110120b8018403d8607549a0150b08203c0a181880300700c824103070607280114428422188032200500d030400200c4280100e6500040202c3d2140c00c8009810007441e0300c140000c00d4400702e803c1440e0a9070071644c0200318100e000980a030010041a03145110703a9400103245084c0142c9407122078845140e904040d040c4170000002034000e60f1a5480390404001d0542050380301d80344000f0805404d031040c94020b021303900d400c0011841c1c0344500140c84c10 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 214244883 1250 214243633 214243669
    0x10050601180b0301030b0a023a0c05030c070204020c03031003020901090504031b020f0d0b1006030e100504030212040b090108010605090a03060e0a05241b0a0e0a03080d0204080c 78
    0x3d107074070f103907609880c903034008101d241c00ca5421b1120303400d900c00282c1c802c19017500030300e82e5001034035014684440d40c49000c2840b8501c01d00c0c103038040c10120307040400e40380d0001400d0b41594680e5903c0c0003107030180c07045241004103400300104004907200401341c00401d49000340c8010301582e0302d1b5140704048640695014005c00c1030396008074107129246141100d410f01c007038122000e050311400444c0d814025071004136486498041000000050100418000c110529061100841e003060464441c50f0980b051031096449900150915000300011079280c06075001890703845a03609203008040d0003e00c82d03540050054400001c01c0c511a002b610000f1a00078800c0100502d11342c0c41c0001004941d408a1142c00f4420011011440600428804082c03407054015040e2480e040c2c0c8201c41c0008040340d0407081c02d040700580c3c00604c00c09849900406050003494030b20b0300c0000071001909a03000034915440054401c088040d0347d00600102d480001c100d64003000c0141c1080240c944240611007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 214246133 1250 214244883 214244887
    0x4080102040e191a06030402030a0c0b0c010e07120b04030e0901090e160506030a0c020f0609030703140a02060a0216020a0305071508010819020117010e01030c1211040f0e10050601180b 81
    0x601845d00780300960300070b440241200d206070107503901c500b000b1a2a0380300c00380c581004101c0703d080820a00038000c16080100207810344508042c0c1207400080400c4020302595088400142058001c403c0d4804200c4024644145d640e0f548004101070084500703081541c2c091040f2404854180002c2807050f10b0b0001d148600b1a9200803030400105880c0305810214800c2c20442c02c4008410304c01c0a00511051000c3c42e540c2c02142005483e02105030a0250003503000c06ca07541c5c055502141054000141c400056590201000c09505043c0d000703201940c407107a014000000c00c1301c0001e4600484540e144500150403842e0340940301b9031070911507a882608807070480a00815142c140c8042280b0506103d201d03490b2000c6c50742d82210003600305204d40000c100060092000080b00300c0002c0c07000a1140c0a150b1142ea0b4180d402e1101c468801d01a50310748030042204d9131b66401040224807420200d60300c0144e00700054024020a172113507400314100711501d8440e0200080d10906072000801a58 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 214247383 1250 214246133 214246181
    0x105160503130803030610050a0c020a0e1b04030302060a150312030f0e1605040b18040605091c0512060a1706010509180303220804080604021504121704080102040e19 73
    0x141c0d5549c4085000350400c206c039190741e401642d564824102801640300360450710f182400c0c3c4072140e110800c01c01200e84e00d040c8030800c0001d038000340e02907002d40e0a12020521182c440c1150a040b441900018582c4200213943d15100f03a240d4810a04024038075400e0101c038640c2900a915141c0d108003401404000300301c14002c5041a41010010010141c00780070001e114504070800b807202036908850b000e4990050018080080196181d41a01540342c00041362407001c025085100c3d00c0740d041c1845047c2000142031340c0d680094080109448050401c15080c4c012109c0d40340c003000d004040c420300e050307c00b04035005940312031900c0ba422240011403442c6c40e5000180400690b00070908000c0e896590791000007042c180c050001000c2c114000d001d941401d01c10021552481062500c2c03226050004100c0d12540001d1114a181c01110011380c1c8801c10613010503e224941101101d9800003c0014900542080651050340e0101d590650300032b200a02c90161036850034442e110300080c075100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 214248633 1250 214247383 214247387
    0x80603071707080102130e06011403010e07030920040509060106021e0a1a010602060708040b0106050a0309061a01080709080c0f011e0203030106090509010e010e060105160503130803030610 83
    0x41e091030201048404082d5240c0209080ea031051103085031200c82e00600700030250000c511035421003c2420301d00f1011440480560040c0014420402600740c0b10000c109124029071000c1c0885030000411041c0980c0c005601d000da4081e10101c0d805140b0345400601801c0e004290607050300c4a903406010341c00c151210241540075415a0f544140c01400386031400950151064402d22404010400082d0324010020b41010340043c40c140a00402004100006100085550545811b410080d44a120802086005004502c4024503e030f01d0445ca1080c20449981c90200190090f43c8842040c0c1d5500b41c2100e0980e4684248051a8410701c699401c6d03181c0031026004690040c035003c521128480ca165031807428095041c000b40c1c00010040c032080b0b60010000c0041e25090b260074005502d8031515002c203400502c83c3e0043c0032940000705541d603201c0d41c2252a004039082c1c00c0e42074201c5030300b4a241c8a81c020500c188070080482d500003141d040c080181c4e84544802040032507615030440b01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 214249883 1250 214248633 214248659
    0x1172e0b07061524030501080309010f050a02010b0909030d050c1c0506060d09060e0d03020f0d090c08030711041a010e0f03010e0f010914010912110a020a080303150108060307 77
    0x4181119090f0b680046490350f0805007a1032041111903440d4000b1000440c0030342143c206801181c4903401c20007000240b40d0b0020000c11301402c0c0b9140c85942c0b54081003040b801000c82c81c0703400d0340c0050182d05000d07143c0d000001600b110f02c0207490410280c2c80b0a10f0141c901e100e65502c0d0034001903c5421020045031540c060359011501409035481d1419401e650001c99403401d404403440750ba00c0040070f06a803010804108081041c3c20114038008600451100038055a1000751401c0c0e03d80020604001884107003170010810102229161800d0b45000c038100e45024110714040e40c03416503804900642120740100105041e1100c2080e21100c809000c54ac01e254505280c0540d00d071002460f171044100301c7c0b80034940d40c202c00040d01c6100c515184654240c51500d03244241c0c18449540041003001c25200841d04240c10646000c4c2e0072041e01505164481c1d202030740c80710b021240040c20304802300045104030100c200388410241d032040103460a86d401c0c0d880c40c2c1c00d80e0000400380900c04c01c082e5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 214251133 1250 214249883 214249901
    0x10e06040b131e03051305091e0c0403020607200414060108060315161e0503011707090903050403021f020c060f0408070f0e0703062301172e0b0706 65
    0x82e41c6040f2284403101c44000d01802601140010350008004c0c410700801c800403000b4210481c2c00c0b46183c100103800070007020000800d1000d9000304c4004c02d000341c1070902190700070b642c05000151622814101034869185007104150380004194505025207020711404001e0340e0480c846405544a40c80112100c07280241541d816100b0b9a003580007030301c5544c00007881200d081d14810310800b038059000300000342851803000c5080002d00141850f5030001e081e01d0644003131160031450b105500c04d82d0742c540360040c0d002000c020320340a000400d042d4080001e009590003a10106404030740a06112042618110303800300580054410f407000b4600080101044004141c4590425495504050510459030b04c540711200042d5010404092000f065540c480c4860400708070305460036408141c0b048049142112126064501e00d807913a020340d8100641d0003004240101e180381800c2680c0301c03403a803c024000c0704e08404407510888002c40c3c0005003a140340b0800c440c14494a80c3d1340f0400742c40882 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 214252383 1250 214251133 214251143
    0x621090303140f1005040e060105090c04150e012c1e1306050111060108150a0603080d09050c03010c0507021302040302031014071e20030c0a05010e06040b13 69
    0x556042c503451110015103014901942c1e0807941420035400f0725030388070b0141e80114003890034000030880c00d02002c0340080c1140c4059802c0e2900f80d490b41600c2c20700b4401d42d00403a06241c6691440826242d00501d0250600f03000c1c0c80f0880440c52501301307194140100011031003044800000d10f202800d0481003001c0380700144140440141c0704030006185c405e1610b0940351200d6072042e08100d03541c2d07c40707071803141180031034054040c950410240d140c1310000c81c6045000254482c021a044c41d0039980324100440d00907000319140c240c0351070444042c0c40c004005a800d44614011400300d0315040c0304009640056480d01403034680260f00b072085924100c0205040c09030b083c800000503880030f021717030011043c8039007002448207040e005400c00d119002d040710301001b000c404105540589103245070300407207150803c0e001d410000340740900521444c0781454805e00010074100301c001000101e1040741885000203011020001d48061f6903908101c0d0050100510384d00403465100d402400030000f64020 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 214253633 1250 214252383 214252391
    0x110607050a03053403030f0b1008040b060405060913020616051e030a0f0c05121204140102360406120c090203060105090d0503130308030105030c030a051e011401080d090621090303 79
    0x8c04006205500c0c003003041070200f4541c80410042168034446503520030740440702041281480b00104c2c0c81403600a140e043c0b02581580d0403c195501e2005841c05c804031900c4006034800341d4900140c0f01c03440c41c04c0340341b104640c4140152aa03d00030050310344824240d40c0d25080001d805904440345a84114107940500580100d403545403c100000d207100b00c44054020310f82e04061800c61000c0142003062052648180f00c18034650390350001400380000d2802d10140d000c400e8520104404140d841940e83c0b0600c4c0036030004004007080040c01c0b40c02d000d0300c5605100c90356003030f141c02030307100850344140010810408541d092600040c0c440100380100c0449040800202c0440d204500682043c5c0301244040010402c0c1c1c0740410013403004c070f00103602030561310420380c1d03c10340c0c4e505102c0070548028000000c0703000f8440d0700f5400210030415101e0400780650703446103002d89440f60810343c580010001e05020034401d00130031000700740000305406910b07045030303103030410000b003800e084120105038071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 214254883 1250 214253633 214253651
    0x310110c030d02040f0803190302070317040c05030c060403020901060c052119021603080c0a0215030a05070f08010b0d0f050403090f120807110607050a03053403030f 73
    0x40002e80a001c800e00030040e540c6003041e8990301c80300156400691960300800c40102d24400604014015801908000d40c40349040e18044d2500f00d204a4404910680b80b000c00041c0843c10300550100c43c0f040d4152401040d058040c802684218000a90000246001005202d20a05404803554042d2055412070951803540b492404503036906210b013020085041c280c004880e8500c47d8440c20a8001800002c8000d0300e40c44003a201840050301c1c692001c501081e20701c10510013a40d030503600800a00c804403003040107545d184c00030346440f100a4030300380001e15583e001703000c1c0400e410751702e49407856541c0ca0407444201c1a0b00552480a0643e164040c8040001c0c81c0d0041303a0140c4d1190701c0d000842ca08000f020980d08260f42d0004581e8620014243d010450003011540f413582c1000d00740c0c180313a10300743c08241e6a200c0c8107002003851050a500905065101e80036003901c0ca42d5101c6944040352100c22020000d960111a0003095000aa140c0c0002c5c003940c400320031000202400f04001c81 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 214256133 1250 214254883 214254907
    0x20f090d111801140925110d020304230102060a050403021c020d110115050111031306180503121801020106170d1202070c050d11090a02180d02031011 66
    0x5500d201954942ca9008014846180745200c1c8100261040d80c001c083c510f4099003d4114104842c035480082c1c261000c01000c00f80b0800050a248070400b0480d0503070420824000c0d641e512902c5613000c19441c0c95103a01c22860841500092180164005d00d642d0711003d0f5428000e11000d0012400d40c414124000300000300c503985c540c0a134505030050f1015050507000074203200c5240e4841e0800786d16080e111441c201e04001040e0540c0c03c00c0c60030b4042c144640b40b143d03282d44100030103100001c080080c005a070383da000300402201c0f203400f031111072890740e640e0138103503a19007151502d0803203072080c8181c08900c40302c4901005918414400820038980c4c1d582210940ea5070b81c1840415504070100300c0c541c05400c0342034581c40c5200c1c11011460b2883c82d0b00d690202000303034010300b0f1264a250388940d05012071070b6082d4a540340001c100c000785040800d602d0009502c091a080e0844a84a41c1c04041c2e2410000b060fa01c540c000d0042c00003481c3d8643d4038001015258982107160500380840b4901007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 214257383 1250 214256133 214256149
    0x2070c03081308060a0204030b0709050306070e0103090813050a0b0915090d02041a030d17070f210207110d0b01091d06130219082a03030c06010302090703020f090d11 73
    0x50840e030010303031f80e9003142030501030380c0001001c0e4403e000c01d8407010011a01c0009000c2c4c0c0c460424504203c1582240c00100d02406124001a00040003c186417490800c10140c0700f0403581c0458002680559940c2100261b0080c200d481d58021106a520b45056555100406400200401003001f24110354002000c0747c00c01d0480386d500740c6503440c000216050401c00b9900d51021400d001d42440064074452501c0d0344014003400403c100703000006c11440c0260358040d032028011002022a0081c42142e6000b50040030041e26421200162010541840c0060078000340d04488040040ea003003410301c0300a4031503451420182c41541081c686041000d20034140500c14140048070b80140c64010420b051005155001d00401d500604001d40c4500240b83e0012004103035040c03c1840390440107034980080001e105405000008141300e00100201d0681d05980c400c581c07905003911010021000c82c01500c84254140710100004402c603d09030200d01d44c3c480c403c64800c40584428404a0701d49 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 214258633 1250 214257383 214257391
    0x309060e06130c0b07020303090d0302070f03030206071d0906220207060b030f1903030b0f1804061103100902090a1d011a030705040306091106032802070c0308130806 73
    0x1d08001840302c000c01020401c00b100405910200d2030601a444d00040d03224440c400312103110f000c61940d55801c1500910200c0020711125004000080d07990402945545040710b41c0d50000e65102d04c42d408010303542e9403043c4a504007405040c00c079920a01070040c0f001038400c1d400d501c0801d00d4206501e5800702d00090280d02e100300804240c1d0030000003814500860180a0034090308a030b00318601c0340700030001d0103829540502c1c0100328189200003088682e20040b040310381001c000c0c00c01c6040d82c20030351591801244100300410520f041c422441d4802e0205403a031040c80c0b0780400c010804801103030050078181038024907590303400f0b55910b504016102140c036156000c1000c0c000401401280110012030802054012417031840d00100003821449203010041400365a900750100b0300001d0408020502005000b282e42d0f801d011540c900d110b812a855008a9003070581100ca00c001607000b90b0f41c0302507001804007440360866880305c1c83c07500080c800e880c5000540d00e00081c604002c00045000d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 214259883 1250 214258633 214258651
    0x50114042307080105090c0a0e010303050304080d06030206030c030402091008060c07030509090703060f1203351014010c0203070605030c0705010903030c03110c060c03090c0909010b0307081b010309060e06 90
    0x110801f02014403945040d540e01c43c5000410000041000c030760007508480e44683d00818290340e80c5949541d59005048981019403c4076001c030030416034003004801903004034000c481102c90350b40c2c0c0c1c01d0711644596543c0184801c3c1d41046000c59950b18900c0080c0040c1842030820f103040c4035115020801d120f5048501c44d00203500d40750104940924610190301500e84490b8070340c0c0c1c001407910b0180c280300e404041000800f00039031950001c51407920207d58011316440389100c07282001c050f240d030080e0460180d81c40b000402002d41000d503011381481c2d80100e9029014217185407802809841c42c0d00000c018407000c003170811070140060020300c030f03000003c1c0c0309403000241e031501c05070003e044031000c0071003100302c046c00c0000b28840800027403019400401c040003a90f50303540f41c40d50641032540207152150807104002c10b0140c00201900108a901c40c1a070490301c105036615181c1e40c2d80e9075200143d403460f01e84d00c540310990b94170940065000c035025480102c2e0030780420300118501342d811030701150 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 214261133 1250 214259883 214259893
    0xd050309011107060212090d1203140106030b0f0d0201090b030106080f0c030606120402040b04110c060a020f0301030b090c1f03060803040602030909150307060203040305011404230708010509 84
    0xca6810042c58034100061000404401d402c00c0c1d8081d544c1c40c03090601c1c4030400004038415080e90350f815820a0610b0307010351402c20608a540c0060080d050500095408098280022800c075200e44100c41c5460b400038003c514411402c01401192017036100c040e8104403e003070020890f0249140118003d011560f107032000761424030b141680d101c01c0039006100c94401082404440e654807000c0e248182813490703036004076072500d10018000b003048044564101c0d00302100d0404040b4840040d02c4200e0150f805d8079060b580300c5031080200c2c071902c2c90880c81d0040a00040c000f2072855400e41e580a584081180d4a01641e280080c425040c2484407508090b400c501c0c0c00000e03903141c020744008101441c025400c141c14100b01a44071300500131a180500207100c0080c9170040d8030b106103c00500042c003518865500d03000c000b5107030381c820b0000b60303030940c01c0c151051805011050401c2c0300c0d41c1c20031080e400442c805540002d5405410070300501790321071400081031008080c850b02e40070745203040c0101 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 214262383 1250 214261133 214261147
    0x1d120604030c031b0f080c0c100f080f010302210c040518010c02060f0703020f0f0403030306030203120f030a0b031f060501090506121314070803072a03030513050d0503 74
    0x81808907203105030720140810040b04d4000030b00d49284100616400740c2003584685034251007501c1e050764544601e900c8903c0c1c240c0c584081d90054226410445207503101452992494115220035000b1700c00250480c01d00284d00381d68410b48811001c0716001c810a5814214200d0f00103015681c3c150f50703074200e0760820208c95031b01d48000d10400414034414000313050360707143c10050384c10307140c10081462050640007d007038002902400100d60082189a42d0140c54544a0030018000d240c180412800303441540b003c1c0b4882030303000d000d40d546048400105c41c5036aa0f052010b40c083c01e5000c00310781d054807441003010364800c0c03449011640100c0800700020181d2500c40010500a200d0b84000d0103100c04109400540c4c0e1645a030540c0b0400d020041c12001d003c500c1e040303403001007404443c243c40c011a030002c16010404001406140e02410b03500ca1034034000301c0321280c0c071483d05400303103040b80600c0020000a40504080c20702080c1d00c40e105c0324126900c00c045a241c800c2e48034211095040040d2107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 214263633 1250 214262383 214262387
    0xb0106050d0c080912160f050f0d020604050d12111602040b010302070305042903010b0a09061d090403030e030f1c0e2e24050f011d120604030c03 64
    0x49180300c2d4062a00101909041c404562a42050083c4100c3d80c64001481c0c641c0c81780c1d184c07108100c00d920074400c54080e5881c2c100f80c0d49480d055828842140501982d50162502c001445401107800c940944291303007003120700b501d4109242003800c2e41c464441140c0420804004050114401c003128203030703208002d03441000212280b03098424145441441400003083c2d00c0000d940a441c280032101200200c0303904d054045100c000d1341c10541580010011944261140150045201c80e885000307615403207040588280729411600c4900381e01c420031180603031916111743c03a0054000d007400500e21520207012410b43d0304c00c070740040c4182e40021b103200014914418000901000440070000c0611200c2d070551aa00d504010b041e8050848500c2095401500c000c0d006480034842d0030010305101010400415182e60700e070400b200b540d104006040c0c01c0070b110703040c140b00e1705a58032003821801c0203016940035041c40300590410041c030b01c3c0d2540b81c042085114052030080c0c035030300e510399254680 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 214264883 1250 214263633 214263641
    0x61524081e1315061409040606091b0f02120f090a0305011b080a1523040203070801050907170106030e070f03060203100906050d080702011707054609030b0106050d 72
    0x2643c00510b4a00100851180456002d0820500b01c40510781c0303489606000000d4941d0ba0045c10403503140c808101d07203003c40c101440240030210b884241d07400984600a0340c03581d0024044101c044400c000660759012050b00601100b000200000308550b10382d11b440742180c0703c511000541c0c43e02e010a60351116001000b441e40b0a0004201b03000072540142c52840c90405445240840c4038080000b0003a1021084417162810000d0070454480c82c04040c01481c07440280b04690042d10084046042d81d8860031100d0090ba03802101d8010703691170604124014801d4042c0840c42e409070741c8000c83c440c400107101100031030003444096124188014528680101c60340002d40d61031500104001d561149002254040c0d0004001c0740c0b40d0b0700c14001600e080c161003980d40c14043c0044100011580c000c00035050070b01150850442024880100c0c0003040088040340e60500d6080d200b140000445d08005242c840d8180b504008159803a603809918001c203800030750220340d01003152856050070780300d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 214266133 1250 214264883 214264913
    0x9170c0c03030c0a06092a030303050a0c0804030e0d200f0a060207030f11101e050c06130602070b0903030a140f06040e0c0a03061524081e13 62
    0x3002e98508000d92a03096600d0f0300c502c2e80140200d40b0380c40d00c041845010740a81c200541924030010110181c156030320002c000b03e01084020910345004203440100070b12074105110640d44038090b19449a8a0035103404842c402d0195015468080712000528103403071003688296880391000000d040a420049043d1042c480f890050440c08403c0000300c0d40014107100700d03500004841c1c4c103a41142415001e404520842c00e40242c2404485c04409501040342680110b03041c0032808034064083d812640c501ca42c0000c014103134800c1000c900c40040c124050700103d803191000510b8940d15541344035000a086400000c1c0e41c03c007000b0400301100c68000d04a003181020100142e900c1d040f28a880c0d1500c0280500d8020303036603240c0c0b1801240e002c00038614440d10007498503580c030f0f540b403030280d02400304a48602d8260a18820018404a200c200e4500c0343c810044400f40b03800200d40110703000c80000305040c4142400018003c01090f0300e0800c03c0c000c0907000e031143e220140034101003181c04800a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 214267383 1250 214266133 214266139
    0x7050d05070503040e06010302040b0c060a0c090b0a030e03091c0309082b0918020702010e0f0d14010b10270602030405010c0c0317120f19090609170c0c 67
    0x700001c000380c0040112826104620210056900c1c1c07000100c0c02400385411120064000203000300c0c000b000081c020b8031401c21042c0a01c403408115800300c034a0805441480d040c02c2e020b000078061a0300903000350b940e025800088030f040c81000d2002034441c9000d10080d51885171039064200500d03500400c454041c0c101c00e001442c61100384100380d0154103100c038681c2882c141d52085804114407954020b4028003100c1d10031081c141c043ea107002c000390300c050412808540e121441c0c6a0900713000b40646400200145403d810300f0706078a40203600c0d28004202d10584d507944000300620b94031000e40351160340d0b682e6036404030700881983c1207030000000d5043c2c0700c01185607101002800e500200300c405540081c60100c224480502e40030b05680c005402c0101260003640000300d403a5180d00103020384008008854000b07845103d8025150301040d900d503010f40c10003039601e003505050b50b04000c183c01c0c4039100010341028184c9075140b46164030b81c4124100c2c1030029803130480400401400c020490b0031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 214268633 1250 214267383 214267387
    0x201090b0a09050d0f0f0c141f0c0f12020706120b031e01060803040e070f0c050a03030221090c0906100e040504050c06040305150c07030c0b06040b12010207050d05 72
    0x403450142c0003402070b105451040c01e135440d0003000c20074518034240c0712940c4007243c03101280103881c010036026803601451045000182c5181d11600e40309030111003120030051903010004107500101c84503a00e50a00351540440400c1000004802640080514a8070303406000f03e981410002810b001c0c03500c0c0401103403428000304440d103035408954100989a0150249034481d04204030a002d840c85521010840c000820000303071520383d132213605100c0c8200c1d5440785a040718180c1e003a02e500040756000381403940034a020800190082d801841d0b2030f8004042c0440301188455000c44102c421500501941c01100050200d4204442e08070b8118008640e2510f110482000081c00412918159841141c07603101290034000d081c00414110b46000d0000381e0340385c0d100d041590713656000d1009600c10f45480760015042d0107924042e03400c1142d05a80e02c000c407013410340301d036290b5240103040158003550b80c803030000b250340c1c032a2400301a030090a8005600c4140b0f9040150921105401c964140142 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 214269883 1250 214268633 214268647
    0x70503010518042d020f030601060504292106041112130f0804061202040b0a030911041514030705300a0f050f010902010e1c0606120201090b 62
    0x401040341682101d68180940795681c0c0d0404480c2d1503014050141620b0241354100034500420003a40102c84c003d88856801c05076074000d05540300c1c400d118500002d401404184040740022000c401c05405421000302c8102c05100381039041e51280301241c480400000280c014801e0320700c6000d0307010340112402c01c41d4440c6e0110b00b405030b200e0152248241c811120009007240455400126a9500844124400c04903881c00065560003801054080b030714082d1000501c006078000c403002d454100c4c50700350400045040590190075030607400c66031000c4031404001d040d225441100a250b2034080d410720b21a00d0044443d0044540c5d0350102e0190b00f0240e400d0225440d0a8451481ca050b020049020301088008090a0075005098035441340103140300307503003448410400e41404a002d40107855200f0212599903080b601d01004c0203001c00d030004e00741e8000d0310744004100c240c603440310300310303031100c079040c0d5954089481075000440c0400e1154680400d5591021030302010300003d2a5882c60160 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 214271133 1250 214269883 214269889
    0x70305090105090111030112061d0303270a0f140f0706030e1b1c06111207030c02060f0711160e2202040209060c010f060924030b28060503060705030105 67
    0x48140614980010700d00c0c07238082000455442140005001a02d0240d41c482072000180c8950065400d0259111910204100f0610550701e1a2400c02e030303940200606030b0140c5d076031a5450270303044007510801c0d0180c0c02403110440c2804503281e50040b12000c5c01025044c44006022282902d0302c034680e5902a900302c590800e03540c900d1007071140c0c0440d41c02c5407085084164036401c1ca044d02000f481c00341002064001c410305031016040c0010040000b40850b950700c0070403012103e05803003200060f0b00010200c1c00d0500c2c0d00b400390341c02102900d00b2080320400011414680380030509802c0034001002c0b0b0070881420282611030700700d564464200d50303c1481844500e07001501c210007a208550006a0714102e94842080b079600305041030081c010b2030100002d240003048039200e421500d074204040d03c100450401f280200505d8080a001c070300a066454a0201a000070700c00f1080a0340e10010707294146039034002004030303000c406010035214100300a160402c2009800881404428001482155 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 214272383 1250 214271133 214271137
    0x1709010614040504021c1101030f0c0c02010305180f03030901140105090c0f0910080604050622020903150108030406090f031e0203010f0f0917070201092102030303070305090105090111 81
    0x10000b194082102c0d25240000340d03812400041450700c40002e2040b01040000b400c003480f100c0a4240c03001c0120486c44050758003951100b50380200081e0b0821070f08001580241e0003107411076040e0306034811707161052070301c02c1c5401d5440071028a10380c0044200070485000340240505900c210a05081c1d951400001ca0803203200174101d0144604040b80c07003004100164155440002d0090070101009440710000e8801c1000352501400707103080a00080890400001c909000203412030350030712804084d00c0480c001d400884505605000b007000030103620500305402c038060a804009503036510b15000c8040d01084c059070080e190f0740d03107014080020800b900088845184410624056a02140b0000c0e00401d141d03010303440c03814a01140c400b8454a2507001c1001644100b04203500c3c40704074450222075008840c002030004508460500c00f40030055100031404061082c140012030b5240c0c0001c3c11900300700e03000e9000aa03a54100052141e0901866070031502c0d80008000c0f844881c41d10507000c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 214273633 1250 214272383 214272419
    0x150212090115051011150108100e0303010b0f0903010507030c0f020c0108011203020f3012060409031b06142a09130e0609070501050408150417030717090106 69
    0x500d04c14884141c41c6002e502d06500840501043d55030b0a41d580002c466208020f019511882c4114500c40e825503102d4845c41c004203561400071030560786407908039070b0154840e4030340e083c5c107000600101840d51024003a00380280500d80b4003040c901402c0100070300010008050780110b6001003c2905242d030058560303130641e404104980c0d003004440c103040e4905448001585520300c82d144452002d4640c006000d40c40c0002408141c43e050a0305180d044e8501409003400c407454001c20100e040c40c0791661086140520134200343e04011100c0c0c9030f43c034800c03141d0340040e201c50f0340722461102c8412400100d107501c040c0c0007190b20300328480040950382218076010307200e9a52100103401c21051381c610032000d004007088401817014030145140c031030f281c60040d03e01c01428440c0785008a000e40c041c8081ea0103441c40500104a07400d0185054040c40c0c0300a03000f9211941c03011002d074888031443e03004602c07450f5240c951011110b1450812484010000d20118040c0d152140c01d02c09090074040004503 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 214274883 1250 214273633 214273639
    0xa0b0a05130f020f060912100e010c080c0a021207140d090602101d032d04030302031c0603020a080d08060405090a0308041a01150e030106030b0a1815021209011505 72
    0x1400c1c1c20301c40417074240d2051444c100e5100c0b4100e1440f2460321790000e0245880030743c07071600b400403085459046081e40c42141045001c5231041c00020b040740582e03800380042e000644102e03141ca0443c4007150030300c2da00c98881510120241095003000380001c0088030880d01c610710b44615050328054009440c4e1000d1021600b41588481703107403038003e00c0064010012011841540c0e500d25180306d02418010400f000860554221203800506500480c00c2da41102e401d90091840d110096481c01280c5400e80032a500066480c000440581c0b166542c08c80a84101070042c01e40800c5050f01614501004000d50311540c1450200503c0f2100400c100c0196681400d001f106500c0300e18000c40200c02c9041e8840d0301646403070001038071507801c05200c0040f1003661280400e809441c0280340c240e40a03030002501c6c2c4c01c08000806d02261070755014400701032820f0300c0008004083e907121401c1d00c04000303010307145540215400520300070078020242c108031010001c0041003041002840140200d11071244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 214276133 1250 214274883 214274899
    0x7020108010315200706050912041e0b0d021b0105010b160f0609030203030f0709060c03080606090d080405101d09130803090a11030105070905040c050403050a0b0a05130f02 76
    0x14000e64a40004c1c490f01a00440080c01011400c510126908203400940d995030800d8049005100c001c200b4941003205402c1907442c05041504500ca140700c94803a6030b825110041c07001445000c1c0c2000b8214100b0a98000341c2d41c0c3c60700001c2424a51036402c2d16407116490000100604d81c50311048480b00d10b442c80b41c14200c1c0345a4105140a5080c070040034000500301041c031820950701000540c80b94103000b00c1d4071025200c5001c2200d0b02d04032405681c001c50401d0170b607000440e0185014942c07048005100740d2400c0d01400204501d4003002004038dd40701e074081828401443c01d611041d4101c8020b242880c05800e91062044d0340c10712614946004400501c042a04e030700b1048000b0151a41003c402a583e0425601c004c0e42c0d40007242c0150b41813140711806442e10320341030040500800c1550b45000d502802c150800c0010407030f4034a01428004204000000120203000c500b030f60901640410b849840c2c68074800d0140d80c401028005040c55043e5800c00240c540600e2005151301510001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 214277383 1250 214276133 214276163
    0x6010f03020903070e040606080f0c01231b01050a1109090901150315050a020a120b010207050307080f07050f0117040606090204090b15251b2405070201080103 70
    0x16000348a070100b00ba4050144100c0400c681d141d5641d403e01a9100300b404029803035071440469203c0d050201b40c80d81581101506c0081341d0b11900001c1007100c1002c02c1c5410315400800c0e5100719a2169490b44101503200d00d000c07580c04001c0c414641d200030601024856101d540248204a105a2145e540324002c0748001c15080007003580301107200c003070642c110701d0502d0716400d1022040c7d407061001d81da00d0f81010005507039040e090082e180d0031314140c3c44883c2034850390140303600a4070824464a0451042c0d40b40081c066400304461402002d110307002c1c4c21100034921910f400d00107541c0003a40200c81250541741666403242c4102440518421344c265a03450b289801c0e0302030105907100c0312029002050100d40c40019900101181508540e0300340b040a170700399a00001d0044000b03c41e104d55180401c0380005d680c82d01650a0785e4402d002541c21b901a000e09442e003004d450f00000d500381040f80714900803244004d0700e203040066a0501c030f4144000e0303500080c00700314140002002e050b00a000741d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 214278633 1250 214277383 214277387
    0x80309010804170309030705160b120601030f111308060f160306030203010603030509030c0414060402090112060621090b07031a03060c0307090f0506031617040c03060606020f0606010f 81
    0x7040760101d43c140e01d41d44c0c00d20784001c40d500c0d0000c0006030ba0381d00448507504501c00801518600b2240009001800c01c001c4000741c0f06071000c02080c040c1071503124400c0d03511159052140c0b8440000d0038140702d4560710b108c07255804030615900054099482002030002031540e0801a0398000200c0a440040016a800c00c4015010350f0344025095820104040205500840600107114043d022265424002c004000170f940f0100c0400c100442c0c00c40125425041940061220300010b045c552002c0707c0135071410080785c105034030034000541d031086000c4034141500841804010320700028030030b11243d9242c3c6903003a0405811003041c9580c800410610762105421166170400060656107030740f914480302c0700796610490314000010850040410b5408501980750281c510140000d0300390703074032070303011a0700d0b03010700008541409520341e884194511002c205510444c8680400f020031443c5280c01c4041d20306a4210b4402e540002d00108070703501000a5440d0700030340919010443c49621181 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 214279883 1250 214278633 214278653
    0xc020d060c140a0801140306070e01050306010c0c03060905070b19081b0a02060a050703090c030803060a030c06030c0305130203150604110a08040c0f05131e1802030f0601080309010804 81
    0x202c40e0701c00020881c00709080d0001c0100d170407540c0c4c00400c1c0c0f2080d908807040684a00044400e48081020503c241c140d6501c01d1001c3c55020780b06040940400c08152030b89150006a6030080710401d846101600c10444280480380003850445811130600003100c80c2c41021100418028080042d0f0b4000550141900c811185160107002c5000d55500c1608070000d441c0c010446805131850304250201d0300c0c20f8445d11a06960503041050301900314215650840a130348082c09481d882903042d00040049904651000c2c001c1502e030700d00150710b209450b0051706440c402000b2a00c0030b5000c103000c2000d43c601188484104102400141d420351318200004c004010300c60034100a41e0780882e0740c1582030740002c2c1d024010380c020031600e400745584032150030f142002405480d801540103d4003503117060103500180381c020703144000c0345260590101c549003110100b1154005001c0f070b03418400154113007840701c0c01a0700707e1b010241040350704100c0269a40d20407203034000c2c10000c40500240c140102081 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 214281133 1250 214279883 214279907
    0x20c21030f03090d09080c0a06030216060615020d0305010e0601032021060a1a07140303040606140a0602031b1c021c0f02100c03020705060c18010c020d060c 69
    0x1c801510390902100155448145803402030200d0070400000c41c001c074000a2894000741e0003048200d10398102881140a5000300c5104120042c81d01038030300000d4440d000c0c0801030111003c1d650780b0310340e58060092500c04c90700c43c04024546010014006480042881d0342c0c8030b0300c01e01700443c0c298102d10780b0102c28840e541c1242c41087c00466403040e082411030045120200c4800c2021064582d5000c0000070341c07982c4030702c040c04e0031403100582000800c07601a1440ca40206841d003003024030380c1c40d400c3c210341c01141d00b00c540a54800042c080c86d030369000b04a0001c4001d407403000c42d503401d08202a54034440c907009000c19100d555a42204110700b00303d080c44d02d448291401c511007951440195544846618064861049600c8031081c02e03c079500c000b044143d00d900030300c40218421b00755801803401450540800da02000741402040041103064001d880e10b4015a595502140140b07201d9502c95001d24100b003400c010010160380c986031150f00c07940c2c000700f0000781120184e109950544020b1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 214282383 1250 214281133 214281157
    0x4030f050a09060f0c06060e0114040506061b0f010204030303050a06060e030a02060d0209030307141905070e04030c1e2001020703150e0f06072607120213080708010c020c2103 77
    0x340000c43c0c0d2005048e05181290028a485100c05031030404101c181e400450310203402142c140314980e13200005a01d940300c0210540192800b251031030000c1800daa00079041540400d4a490600c0310148040c403a460050001e494814079000c048000252640440140680310300350209a14149640300d5049501c2030724000c044036a0340c901441c216541c032200584802950041d02040c1140210385d840342c400103984400a40003050074240e08560300c0102600a508020b5a1003103000011050f40b1481401202c000b0416908881072400342c54113001ca50503105200b4803844048034590300001c1d000143da52062500c51480c02145501000f850720685891962003105500e00551001091060041c03100e40d4456944500912400302046608078941e0340e0540c2803000940200d2003403d4140d0082000c0001610f885118210103a60038015000180c15410030342c3c040190075024403a10355641a24005440e81c0f000701c00c009049203a8010b0404401d0090600c000740e02e5006000f240c210f11000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 214283633 1250 214282383 214282391
    0x50a0b0d030c060c030513081e0d09020f01050a020c0108060319150b06030408030402060711030f0f01150e041221020c010c030b130b0f0d05030304030f050a09060f0c06 74
    0xd400c00420311840d099003500c0861410b00281c1a03075109000b20f520a8203403040003901060f447d034172a08550301441c01c0401d4109000341c01050190313500000c05444c202d0000100310310400340100180000101100c0c1c0c103000302003210780e4507140c0110714031070311000900b40178040e44e80718404079007802c11100c1902e82607120308010108001040380c0b1040d00c100160702c1000074141010910400d440705480240030098144000303070052800e80c0041607000c0c81203105500303c00d006008203241400b0300d080084641c10461102004138000d2040d1590541d5051030780c0c0546103820340c000000035001e040648211080f18000600c1d900610700c10b043c1e04481034120080c0c0e07a5000d0808001d410000380c1c0c2d1819401d20020121141c400e00503003240c60300041409aa050340171500c030005003155000d403500814030309281002d581d218507030441c1d60f5014601031030ba0f910b014076000b4241c4212660f10700070b201c0c080c070405841d03d40c01103141d825244c2074201280d80c1203820340181c1c0c1c114205c42c1d00400307150030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 214284883 1250 214283633 214283659
    0x11040e0a05070b12010801060b090402070f1406240a030f1a010b04031202060f01060809100e0d0801060228080405060c0d08060f0d1104021b07080c22050a0b 69
    0x14050040001d007101300c181c0d50f05662911400da00340c130030794032542160f9036041c4003458651134203a00806c401d40c45014440008000c56903035500d50f558011441d15241c003c40b04121920813a008041411481c0e00380e241c2c014284080003508050031404064013980082d015001000100792001980e40a40002020036680d41e0500f40120350181c0412141e4000c00c40c11188400e0000035076030b01603504890075006982c201f11040f60000c4001f0100c0f606071090b002c1e8110005d090703100344028800480c000d8840704c00201006014484180e0006085511031200d403090a000780c000382d1808a42d106002c5602074070707410501d4443c040d03a0021a03200038001802c203441d240018244400389500d0b00c565200e076465a08000144100c0411140c000c005000444001403800c1c11451100400a1005043c031905481640e0078100001c40c0101540c05524180130448003000b49440b1948121550403030401181c2c03003282c07a81c805881034100c1540f50750100303440400d9604001501d04020b0310340c0200c50301c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 214286133 1250 214284883 214284899
    0x9040207150b0a05060a0f11012702090f0103020117040203070306111315021f06080106060512090307080a0503040c0b160606170703021306030b0c03040201021911040e0a0507 77
    0x42c0408031a200300c1c1501800241802e00e0015181d4203d5951910440204445429903d841c458100d211481d50707648402c110015080342d8515211500300c5d82503180f01170900c1448103c3d08003501182410703e81c1070042005030780c13180700c1da00c0c11042c40b00780719100e4540c0d202103031510380c40345c2006111908101090b4080d01301d060140c6510204020b0a290103a6a05908801c0d450100310b00c80040e00000c5201d80459a800780c3c00745230b4506404006400780e0740c5c80c01031342102c480f5040310340013500028003002d000c10582e8015801c4071240d000341d450000700daa66000c207480b684080b80e06011005c0f00280c01e1080b8404c41c1c40003014503441306642c903107403030048e24088060104100c0f44076280000115450107403a4510b005a40c0410041c030030f503400c40d000c108240d00f0305800c64070321685a00c0c000c07000602441c8080c1c0141c000720703e01a01c9042900c000783c10010b024481c00000528084070602098a500c8001c04d0040244e40000d0540412070006040400e8a0360250842c4184000010086 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 214287383 1250 214286133 214286141
    0xa020604090f0f140c1b0a0b4302030c0712051002130513020c011b0f0908101e0c020307020a09020a080109050703090212030a09060503160302090109120f0302010506010c0b0a020904020715 83
    0x42c0109c0c0d681404181100c1c11840325860140d41550117110703522004140c02c40742d4510f1100440343e00440e0308114601415a180c074826401010f9040300c081c4002003009020001b1004244540c40305500b4850050115060b00c6202e1242034800c11550328a40202e000039030407030302c0c400d1b420030090110696441050b8660040122010000385102510101d600e202d0804a010b03142e905014010044001c0541006031144c03024a4000c2c0050498034012003419104600c0207140640255490b41d84500401000401a5102c0c0400e03600411003d00c2c8035a04c100e002d41500c42482002526866161080f03000f8014031000035042074421041002800380003002d09041119542c8891039203860340360441d12404184c510308110042c0b4002c283d0701c24040d1b0080d11020030706242c403128880c0d4030700b0700c0440348030064800e40f00d2000520360b500a155081c02056032041081c28140c541c0d13840b6680310014464024015403501e5804030301ca110541c0e85030126982560050603000c0f4084462031018020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 214288633 1250 214287383 214287391
    0x5010f0c1206030308060402130e190507110303040609061e0b0a05030d0c060f090b07080a0f020301051c0f02150408060601020604020904060b030a020604090f0f140c1b0a0b 76
    0x4a00304007401c010003211401808240c96041d5aa5039440e1204014000650041c0408519070a038500001c03400c00d84080c0000c2c0304074804401c5510118825541c0000c48201500050400c2000c900154225000000b01c9410590020340000ca1f90401c1c240b5500421403c407140800d14101790151000042c1c036001081403103030031500344004a5441c1d04140d03803490701c001e41e400400c0c040804100428039035030141c03141c400c0d088800301e4080c109944006c10b885044a4070f8002c03400b0304051101c801d4452190002ea44c8050004515550401e00040d181c4050b0400c064800175100020208000d00100c81c0c09034a82d0241c00f4081100764103150b00c0080d0003a0082c00c401d4403860000489542c80010894001e640143c0581041d03100c07500c441c030142604c2010035406200c0c0c14640c20058a86800420090840e05400508415001200000e17592103c1d80c04602c54245070352944d000d1040b030750454100b011410a41e80c3c480da01c2c201c4001450380129144070901480001009000b4400c0c485442 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 214289883 1250 214288633 214288637
    0x5100b0112060602121c09031d0f01050405100201110301090b1e0a05090a02070f05060a1a06040603051009140708180715030e10090209091b1c05010f0c 67
    0xc40303501022070011100b1510500300164440040c0805400d003c800a00888007011003610024515026020a071084030070304030b0001d2800107030322207010710410511801c280100e4403038a0021003803000900d0340c02907006240c802c070640044882c469000358003280c20915402d081c19100d41e5a20381141c0102901d140c003d001c0d01c8120210000100066801ca0041a006102004407805c3c0b009005c10b4500c01050010925070822a403004620594803861016210314024102c0c0d1030304489413025241003801c0810315280b12044407115a841714155000d0342c0f41c500c0c0c00940c565420403400915141d591280c419185030501d04103581b96102c01080c402c00703094443c9000e544481074541da4106e211864000142c000d02c00a201c00210040002d201495600e000b01d0a8500c4c104107900340002da4145001d45680c2d503d40404508181c4405a84801c0b404050405c4100ca83d400202200d03a20300d100348185502c1701900f98100040c25100c1405408ca8000c21000844840d441b0085c1060116000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 214291133 1250 214289883 214289897
    0x6031109090d0206070c020a120c1401020f03030415060e0a0c020d08010501020a0f0320030403051203040203060103060908120c1c1a0607060608030703050319200703090305100b01 79
    0x1681d050006503200c0b101c0d5140c0d0041809a5070070404840b1444101c0c0d0880c0e0040800f03400041c807040500180f4039413802261003440d0b40380781c8040c00081001e1110400c0c19904085007802004001000762a0701942044920f0a1402e00484100090140d50400040300d40590103100050915901c00c4500543c80d8085482400403503000740d903140806d103d140d0060781300031240800034039035240891a8903c2410071034066494501d40103810031401300c0c41d0b070a550001c034080007441000c2001d400c514510328641031440c01c082d00440e854070014000a000107489080d1001000130030011074044042d00b43c1800d80031300f42141851841d034049010200b03901140103100300f8440c441d00c82d07480c500c03c00e003d0b00701a080c1c0103000c2c0201908840d005540762591440000784401c400d00c000c015041c420390f1415624036001c991820b4007030b841d0614404441c90080c01d5400308040c51302e19001c131449201c0403900d500740c03854100c880308010b800080003030086085049402c1d850750007100600101740c03a255 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 214292383 1250 214291133 214291141
    0x2030307050a030f0801050d060c031103070509040f020918070203090603040c051e091b070206160b010e01030210030e101b0f0302072d0501020f120a02031e1906031109 74
    0x40e0401000e005107680301079801000c08c0011041d50204018000c2c174140412118680c1c401c08600b0b40080b90f2483c0410f00000c3c940b8000c1c034042c444d1044040303c4040840c00c0140c280c01049034124207074964081128a03c001c540d5441c0208250794070442c00402c0681d407407615103043d1f100d0300e00301d100303150088402e0b40205806001340d2840004000d806400001a42d8a01c844980180c0d03480c001c41c0510f4008010090150b20780030010b00c0b60329550320003440c10750380d14a03006502c540140c2c03220383ca02811400500041e0381e0240c034910480c5880c64046400c190b15034980d400c2044601004d280c091505424450500c4049200100a010342c0c2320406d604c1c00000c001d400740c0c4105040204030549443d8102d500d045900d40c0b500749503c06240c0c4021300d01840e0744180c2241d100c80c2070008035440110b40714044a1900166a0748080c03a0a4150705606001d8000707611a152005111806015900013030070404510780482c0c1d00c5001c0883c2401103031340c0d03820803140f202d14508200b400b8111040000b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 214293633 1250 214292383 214292387
    0x4050f0301090b0601200a050105040b070212040902030a0b130920030c1005070803041b120506070e01030b0a031505070f0807050304020a090608030a120605060418060302030307050a030f 82
    0x1140b280c001c00280c200d9034030003004440c90500e40e4000400c0d92003030745030401610020014241c0740c1e40f24800000c3d0034201428000356502c4014803020455100040c2404a100c565080c6c074121b40004002580f65281c1c1c00715800600240300c0125042030254601141c0c00340c1d207400c1415050300445c254400c100c5040c420702d41c40611400c5c080d8166205145000e00c905201c01800d14400c0a498840d00307100490380c0342d44869009480c25518081c050a24a0b080001c00826000502c6c2c00c004400c1c0760041656207544890000f08480d0a0044400010510740d01a03044111505002400d06d00c800d900c034034120001184440c54500c50614000009035424055400341d8400300075629010712554410808649641c4014000c0303030000707040540000d91440b5801050003421100000d181c8810a1080042603403102c001070800c800d0034840100700c40d2b21103034100c1d000d9510202b500036890717a4241080b4090812940001d4061100043c1070040c81808615440400d129640d10401f2511450b01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 214294883 1250 214293633 214293641
    0x20d090605090a0b09030a05010e0706090501051303030f2a0b060f0f090702011506080105130507230c0318090f100603020d090209040b0a200d0b010903050a060204050f0301 76
    0x5070f03041410307a039040c04110702030406000c080300010220341c0d680d01565900340c20f4481540340140c041c0d00c10300c2c042c001242c10000704000f90100707281c0142803101010040c41c2580140c88042c2c14403002c151722030740140c45844405140302d18500074510004585030112000c0c1d0800009580c4039402c0c2002c268607140800182a80a50040000d0f45802134081085400a8050407507400e540d038800039000900174405200004040c1da45031480250702d81800c5c030203807108500d40000100e00c3e020421400d5500140200c8281400b480e19034076206401c40042c401388240c2c1c24a407401e1001043d007051a04a02031911003c01302542d81c0115134442ca084402007280a8030402c10b0328a1060b02488418030030f60181a1f0041d003144089a0300800d900426202c48007030310140c6117075203003108002e1507201901030340c3c1d210b25014003092400540c80c000860070f402503550728000309486078601c41c20307a842456940701564100e01983c0c03074a0001d140c4003000b0345c01031090364058081c0c2640e40820703180c180300d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 214296133 1250 214294883 214294897
    0x603060806040f080322081309020c071a0c01110903071a19030902040e070e092a0102150a0504060b0a03020f041d03040806090f07060c14030d0903020d090605 70
    0x40c400c00c4000342d03131410682d410040031514103c4190790520300d495804500c81035054004e000d001d6075207000920306c0d80c884107a41c00191226004010641c1200340c0041d82c041181d100029000b860014046494083c0c400c07642184065820710040101c426944401000541030490882e00d1460341c980181c151507002035400142c502062006480b4200090b100280c2100740780380000310400340380c0c0050101e640c1d190700c00c152a8411041441551503408003203810084102c000c1c800c410002c2d000c100000240f4050144030300d00310b01d82c11803c2c2d0003005014070305403480003100c41c24509140c0c0000104002c5905507400b508001400541e400c081030903409498003d01031100003140d250a10005d40640c0418541da03014080c00c0e50500c10301800940080c050440c040d00c4207040c4200d0a0b49084041c40c441080c83d000910304022154120307104402141e03100410680103240440c02a00798000c3c00001c503640345c107000c481400c0503404210a420b96000361644e03280c0b44e8540c903080b1000e0203060 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 214297383 1250 214296133 214296143
    0xd05030919050f0d120806130c03050402012007030204020903030c1e0c0604030b150a0504290a0f180f0501060908060a0b030c06070204060f090b18060303070b1503070609060306080604 81
    0xe111799420301c102d01e8030368000806041c03e01070040710446541140c12103001140081d68903401d1100310740c2c3c4000c1c0452200b003050000008401012505911140c181c0b0000380b03d507a000070300541f40d8505000761548030300100103031104400c0d40e02010181200d40d01d56030444e80154103000000703141900664060f00d0f0000e900329440da41380b0b20340a1115004030074003a444085244006070b641c0d5140218450041c0c0d503009000a07458a14044110070b070700561092144501c01020310010344100e4a401c101c130540114090710744c80204c51940240200200e004681e4142030000c01d1003a0405011001c079042c907030071522039548214485013110b41841600758590170825007800c0c1450043c01402c161400180006001c2c0d43d2008144c031052400d9002200054036802c003000c01c0c4c904040554440c0400485d01003580c501000000d0302c911690000801101800740400d00c00040c2141884170080042c2c01c50704c2060b140d4001a2a000d40c501c9401c00107420b05401144031840850714a024a42c03107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 214298633 1250 214297383 214297403
    0x1050709091118010c0f0302010c020712120302160501150311040c0816022401060212120a050a0e0a0b1006020d0203070f050f06040804080106050d020d020d05030919050f0d 76
    0x451560450346101826860400c5403624070170021403003081c4a010310f1442500001103c08510401904080c130039030080d8081c0c0c0b00d00c0d0030300c0c0c040380c103254000c215600f0341e2a005a68030380c030240d5041e80c6c2000440182c503640c44c2a060040700034406d10b01c101902c0c02803081686800342c1c0c50801080d603407a410403200249041007c180140b500705081c0c200c0c00c0090042e51500380340700c000d02403c80740c55040001da05203000010000c2c281c050044064035000e10200901c2c001c00c6c880c0036016040060154140710355038000196108402e98020b1749101d41c45015241018014103040d44c5601040c1e40303075083d0000590001501c9070000400d0340701611150085d6041c5511500c588000460500301512580140700300022102000d0250030300c1a44075108140e12103041480c824211030141e08010b003c0c3d040140c1c8074015a0750141c400c403400d030341200c1403440144103151040c1036028820f480392f00802d4100c1400d050502d400903a0042c3c980a603402c400150300c50342006081a64a80050608158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 214299883 1250 214298633 214298647
    0x5040209010f03110d0302030f13180504050607050c1509060708011e050f060c0d090305070b09150d0b1909050603030301030f030c0302010b03071517010501020d030b041d010507090911 81
    0x400074984c5c00c010b0090043e281000303e90004110305500c0182d0301038602084413001c0c04401c1c2914007402d040c500d83c440401280c5850f135102d80d580d410250150085c00004501d026100d001004030001e0300c0b407449181c00c03aa0808128090b50340c00181c5141002c06c0e105400414092002042c2080c0818411841c0d82c9103490002071001501c40c801c1d0041d0842c070704105094224400700704020005042d503445100c01d07071941c14400c0c00c0440c19001020300d0305007008402101d9561a003801158003d07905516a9141030158444c02004c0171100c083d085089084c02100701e150403140714040740c8118a0074405603035400704050716480240801000c90001120400100b0303c502c207608801c80c07281c000042d0044c0c00c600080d24118990748642100030425040d58507181c1c0c004450b9212003204444290135504040020f521400d0782c0400328101030751140c1c8031185a03955009001040c081101206d040c2c8440344440c1d029040440b6140d01086158200003000c030f5051241500e116200340c200b50134a00 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 214301133 1250 214299883 214299889
    0x10501030b060c0714191a090303130602030d0c180e060604120803160e0306010317120901020403030e03030f1806120708040b060a080709110c070905040209010f0311 73
    0x80441c1400780c02440521080099a00411a0002070b0604114454190030800c04100751403c030032a001052036001e020800c040300e482200c840582220001130b42d124410741001c030f407441c042c041201d000c85d05081d0f0300103119038001c0000d0000840c1c480b41072168146100058800f1041211685189917a1610410448621500098000f030700104564645030ba0340c003004101c0c052811003514074540c00804d1000d24610590080d01d51040350520b4106a40c106000135120001484054450140808050031403180d2008172518900c0a02c1000b07000d051018295000f50041d010441c04149242074100c281d03c0c001040e1140f41b2100d6907803d1070080c5500600021807241c00c03515070070450900c030182042003a501007501c200169503900b011490a0f0a00b26030b0b00501400d140d0007030f0501b070028085507101150540907a2902c01b80480d0150301002d84010603c5024a0404180980200070900c03103206c0c1c22441c0918000c40d0800140c1c0d8903046c001852180c07d1200a0400c0484c10000045007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 214302383 1250 214301133 214301141
    0x31710050916080c070c1a13050d0201051e190809070905160c11040203070c12030c02030d0515030f06040510020a0903020f03011e09060608011817130308030609090a02030601050103 80
    0x80e209007500700c0c180e1f81d0349101404003980b5500b600000400414020342c811984084135009000c226100110552030b034001070130340d1003030021a1040c042e4140206c0d2030340940c90100c0d50101c0842c01243d6141e00c2442d0700034446141902e010a10340030700d6a0004844446015040c010a14a0a41c909610b4580010b0f00c092401600465415640c01443c255990342d03440611310030b000b03645079081441c0c118035000c5400342c8404840d0040c940b500d11500900e9900005440001e0241000000c040c0c44e91001140e14102b070641c01641403007980480c0000c03910100340d50780154403402c100c498060401444006034014500c0c007000027564144104003500d414a4400366420000c1e0001031100f826408031003c0902a5442d100c5c0c01e6180c00e020410000988109401007070000300800200303590450f081d60711600d00502401c1f411110804840c504440011209090b4100c2a650740e6151f03249003003080782d0400c5a8007031040e10303400c00003014407002181100e000b550060262170240e0030040194018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 214303633 1250 214302383 214302397
    0x720090c070f1703190507050f091507350901050d0f06060221070f0b071412040c08061006080c070813091d0c010507031710050916080c 60
    0x10b01c9a0441c140e003c107018030458943c0030f40c4551003550f280b52854900c80b51003100c3d40c500f44518507040420042c1c0c2c0d889419929500025611705a50705801d400080c0d00003041c1c0716a100c500300c001648400c00441c3c180d18000e1b201c80380c00301e040d00a80480e01d160340316000c400c20547c24104008024841d84100300902d0942c83c3c00340d0000e48018080b0700c2c0000c031506a00b14902580c800078a1261546c01580364a22040c44a4061898880c1e0f690f1044070b08084240300a02c040182c00100301114096294018510000c0350300d036448000d1066601d0b901103090340c0a4901442401c13002c61051400b04800f4803810904198514203841d0040c221600c102c020841243c20b903084c009140040c0160b0018482c41428a070000c124a04003600001160310704490342001130719002c1004403140d00413486448948003402e1282d15054507090650310f0465280600c944142002d041204442c0701c0301d0284103903181541c003014159030390204280f07004028142c2034003280d0920002244409450000d2181c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 214304883 1250 214303633 214303643
    0xe0606071a0c210702070f12060b01020f0a03030203150a1d09070b13030b060604081009030e040603081804150e09120705060708070203070807030e040e060901020720090c07 76
    0x5000341524984240c0c0c2c10425060700711aa0710f0080c0310101d581041440d01414440382d00a501c0c0e40b81801c0000c00c503040d0b15000780265111014002c0f16030080c00040f41034540c0805441c3d00410a160040c0298000c0b5600810140c0040b00120203042c496030340e00650310920403c00141d41c0341c020b10391040d003000b0503880346481000400300e03020300038a0140031251004000a4049411841e00440900009040c10302950b014002000181350000b650030301c00310307602c40000d04c43c00b880c20304a416889002c201900705042000000812088000078031380702c00710649015521103400c00b08070548840780b00301151846103120030301409203100e05041e042040e040449140c10101d280750303c90b42c0c0000e00c003600c00e034220b5800c2020991300014040e5024041d8030180d454800c01d0b0f9191540c1c1c1c000e2040190030001d01c1240d01581d5240c96000514072001a003c4902900c0c20300880e40c080d40c0480400c80d00c082c2e01120981e011105510101c48500000341050300c559100081400c917508008c0c000e880d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 214306133 1250 214304883 214304887
    0x10b01120f0b040e010c030e0a020d021e0913030e0109052d0907080912031902090f040f0219050903030a0c031404060e100507031205060303130f0e0606071a0c 70
    0x22040da524030071341c0c041034007100010070b406035a40c40160440340001c10103c45034004806840041e60b0340824004004d5040725140c421003801c04040201c14804006682c01070860300134030450b100d5622030351140c1c901c0380d6500515418540d00444001c0d0742882900e81001d11105114490b43c480b0f42c4074150113140300304000102e20900002101407505580d0180072a010b0070500c1101507080c0001400d00e808214018038609084500240010b40c046822403525404101241290343d115805940c2c400d00034410b00004045004d01c80003980190305c180001c24140f684004000c0c0210161501e10308000d0155003400001c031410740790b801081008508011110a03124400c071641030180024004503a100c144180d050030902013054a81c850f00700511005000c0782e0000703544240710f2000f0000070800440c0c2601c0d01408203146006004500d2480001c10700301140104200d02d443c800c4548144446100340c650609000301d0b03120303410014001c401d0500c0e442c4400250212020703000610a00c0c258 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 214307383 1250 214306133 214306151
    0x102181210020d09110d1a06012f010506011b0206030903070c0806011d090a1103160306020c100204060207090b0a09020a0c020f0a140111010e1603050f010b01120f 72
    0x20040b81d001d00101050a42e0f12074a500070302400e505c0c8a152200c06403115010f440c40d03078558441d20000400503810180c0010300152083c0d01c2801002045200a0a0340e10809403a04004910f0300041c0d08000256103030a000480039841050b8000c0020f803001c4510b441804540c0034410960b100400c000a1343c401000a03100251120020500400c000390180c1402e5060113040e40c1d40d02080e05240c411340c0c00000611454110108540c510158403484150700b001e11803021034200865400c101d03904860403d00017040c01a590000d001c04001d107801d0b58007080c02050503074201e024070f00034100140e1080300148568503159000d0040101c00405030001555101400c2c07050743c0c003503540c5c40000360007400f5031021418601415a200070084a000c0c0c0302d1030030508035005081404070f8140c104660345481074501e03030083d070184c0c43c030160320fa040d40c510140c040f507107000c1c1c17220310b20048406110300c40c401f45078a030781880f9240035140c059503000320b05202550300102400420348000c0a0560740c651706 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 214308633 1250 214307383 214307413
    0x1a040806040812070203030114040b041e06030203010506030328020109060609020409050a0504110114070f0b01061704050304050621090105150406141c0f1505010801021812 76
    0x1a40328500c1840d100f5a01ca4800398a000a4038000c0c2012065510900c010310010340560a0034061440070342d800030342100e8250000e0003401550580c07100600700800d050303014680f80d400080070790340250020711491f120f40702403658902c201d0790307601c200b02042210054501d04500310941c90410610001c0f851000e280c80f550100c54469000602d560360005080204481038041c01da40400c00320740c10400380c0392580380c81d920281d031080c10038100040b02d00300c10164151102601c00b400d4108540c08100380e05850000707040c030028054000440c1c0c0740d08400105401c8040542c0c440c80e4004040c50515243c101800300ba5000786420f4850710355070b4520700b52644012240b20348070f11003e400203d110300303026400320b860300100708440c0c1c001c5090a00078420a10b642a860350201c4d82614102d402441d601c0f000c050300e00040d00001c1040c0a120480024031180f0000c0e44202402070504010780c1c2da032040d24508174400d0b918010f40c0b100c1500c802c1e03605450815115100180e08009885400103a0914 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 214309883 1250 214308633 214308643
    0xc1203090c080d0804030e102016030f0624060c11040507031d0d0503040b070318050703050111070b06010e0109180f060506120f060301021204061e11041a0408 70
    0x3c2000141040080205150780202c5048103d0302c240d840e040d00181c0300708000c1c2002d44d61205c2404d2515010008440c0d1082002900403806a501d02c09000da622071130300c0410b201034450b081c0e8030307241045107440320120400303111042030000140d190840303450108140d81c0302400010980315030b103012052070440d86540c081c40d80b10b0407066400144251041d2241050001401c0101002d0f51012004250190b00401126045a008480c00003da5540903048010b8202c03091803a8000700c440a0301010001d00048003070070340344a000203101030790120401e0080744c0501c4001030b004011040c08a1a154060068203185d40810b1400c2030849443d2068110781c06001c0f1a04000d107036442c11030a00402d09441580060503048400034a4221203800040e60031801030400403001c036601000c9607403503030250304590048400032000b044600e00380c01c0202c0104444241d010741c42421540160280b03105218000c0c1c481500c81c00c2d0390801e0300b4941c081c0002038503000040c011460421000c1a4410200300e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 214311133 1250 214309883 214309903
    0xa05191a0d050c1f0215060a0f0b0730050a020c03030406021609060621091a190506100f020114090a020a09020301050a090c0507020d0b0a0c0c1203090c08 68
    0x20080800400d101c041c4010708070301c0304c0a0361010b0a42c1c8600300c1902d501107040b80c14000340c08100c107a5512054002290500e855000769518180a030002400c0813119024046190040300c0c400d0241c80c480b58901310000610b00c04240560b0440b81a40c9114080d03c0a001030100c0361044a40c03140b150345c040f070300e1a032240d000791016030b001002c0c41130340d9503007150f0b50009400109070904c0710515001c00541401d0071282c2a00c0b18401040300d1b004030311550390010303020760b42200f81c4e0382002c0132002060070400c0003540c80b0807055829078003403d440070041c010940581005401e128140c080316008035102c141601500c4119526038800c01d03c81d05804191038040e000200103000220105c1c4104080060380c1c0d404055a10b0042c40104203e96840070564202c1d0400080841c40c0c240b01001101c1521072068000d51026a400c160700512031120180c41c8143d04141c01003041807124002a0b6401d18140c0d0001c0c10703180e41c8802a15064425085000954450700307880c1070442d1196103da0400c10229 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 214312383 1250 214311133 214311143
    0x50a060327111516060507020a060903031b030b010903170c0f030a030b01110d1202070506090a0318030206030a020711120307051903051e0409090303060e0a05191a0d 73
    0x12604a207460f043c1d09001484902c5943c1c14130301143e0509018456600e07901c003a04196a030400030391200c0c000d01540104c5039000030200144910303494040e0003043c1c0c1d444c6030002c2c454a0024024071031300078400c4015500058407490300440c51a0360f0798400c40f02070039004041580501c05c0c0034641e402048140c100d0500007001e180c886a940380b00504403584010b2440c10400543d00310703003c40a0100741c0c0b2a003030880745803a00c5c030520600d02c2d19011b80b003403900081c0b02d0f2041b8810048401c4000c1845410a48280d44140034518003008000c038035000c3c2c2c080a98412010400301d12504119801020030700d1140d9440c1620004d05030000c0c15558603030450150b103420000700101046000c1c403020821082c050042484c2003140d84004040f4000c40f15130010f03d89014040c040b111a640090390010a4010ba007440014446d01e00180900417511504850300a14804100540d00b1401703540d10842d01380700c0014541a83c2e80251780605005410890340103c550140b0016031a6180241f50240c010303 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 214313633 1250 214312383 214312403
    0x50717040518090c0a0f0b0a03021204050604030206010801020a0e061b031912060e01060c05010b0405010f08060907141e0d060902030d02210a030e0703061e020301050a060327 77
    0x142030718030308000d12890a2445011240014401c0b00c4022506c4c6055502c400c1d0036a0b01c0b0390601c01c0c260002e10445951100c1807840c5020402041400252507100b6440781d03007a00d40d1070340d842c1207250a030301030300da48080460032030350a045650038140090f100041400013601c240202c0b4210f82815079000081042045080b54080c413030f019005100681c82940407030b820001035103805802200850103002e27480030422080c1c100301c01c2c81001d4100558016000f0000c028030350b569806041494a184201031044c06108000b40010101150030811140300528807000c0740310240c1000b07100c4010320584513060700c0c00c5810150548440342501c0d0b14a1060b1400212108240101498501091a607604543c4400d400140c54000034010710b0901252150140d01c903810014150098202e030161420644a40100002402450340244600840d01072649121142c1d24258200303070722007401456004008400c00b00150b6200780e100049131032104401c25002850400c0d5400c8203109182c050b2880240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 214314883 1250 214313633 214313641
    0x30b010c200d0b01170607020703050a02040b041e020307020d0504140918030a090612150b0309070e091507080c03010b0d0204080a0302100c0903030c020d1103101a090601050717040518 81
    0x101b00003054000307030140010100300303255030394495698020b444000d0085865011400c0c903600c454214400d1036041d060400c6002c0d0306840884020f4001b00d0311200180308030300d0500c0300031380a281104d042d18607400c001030b800080c40d424000400c2d0040c04054000f81c8104002c1140c0d84184081c02c2d8401496445d12011403504100810202c8610442e42c0c0b568544264030720003108070441042110244039403107480b0f03030b1010002e80c01c00000380d00c8104402c01501c200500000b000c901d90b00805002c0c42a01d009480c0d000048416031000c03142c1d08540c0d20100010302282000b003028105485203840054502a22414440e04000b55000114096802001101d24011540c003910f8002101c41c6010b004d2586551001041d0f00030944002e030007042140040e800388032903241611030200000d800c403060190121401070040c12840c10350025500d51030070340300807441c2403005d07640514070581d01e0504001090f00d501d90615036070081d40c0408031013000001015203500c5900d040007100401282c4d1a458 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 214316133 1250 214314883 214314929
    0x140a08130f091103070f110307030e1206040503070809190b0a031406060f070507151205060a060f110a0b010603020409050c0a050712121506030b010c200d0b01 70
    0x1c180c00808019040900c0b40b00c048003014196584840c107490700c24070100100ca000d84141000c1d0a0038081c60100140f580141908810244851003098501a03815940850820f8580c002502c00030401d410400a10b404a6124406010f42da040104140d22210b186407001c503000305254041300c44090049030325590560948501c51110869851328011881c0a20004010b4802d40a0074500c0e488003048080c00e1043c01c200700c402404101c03c80e01c41c41c100900000e000080c50440c4400d600b41000c002074501e090403290603045403540c0c0c45d00b01155402c030206072103030300080c0220390f650320611418401050b49801080e0003040a600d005964900b00388261040e1034000740350780b00390801007040f4006154050100c0700140d40003c059419005c4800702182c2c03a078000224003120604000e03400c0ca001e02d410361480304036142500c0401401001c88015580c40388402e00140400d0a40380d408a01e0703100b86e00e644031008030300a08005401071150744d02054601d0a03001080000c001c2c04a0303c207494 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 214317383 1250 214316133 214316159
    0x120e070e06011e140a05120f0912040303120222171009020306061215090c090108150411031e03030103030813050a11040b030f0f0c1804140a0813 64
    0x11003040d0300c00e90b41c5880c180180140040c40c1c00e131000b81ca400104100702e940f142003603ca20404032443e48517141000c880107000a041511515031500641d810300c0204810b03501190201c03645034549590000800c08044001e4020340200200b4041401c18502c0b0b4488048055014003040300d44000d40b0f550410500d4641090441821502e602d0305456002503600051141d03886042251866101d128800c402402c0001c640014802c8401700c03070a03c10300003000704404804050035240781c81c650780c0e5210940e5480c000040100d0303081a01d00d000c200401d0204e003800251100180840705074003440e1044a07410714410a000c9803540001c0b00502c20180d2103804907400c59040008194181d1064031a1915071001d0300e0010301d4200d0b104804650385d22250003000581c01c0003810346181c0c49030301341c00c15100c91601a240d907041c0280d000391b0f0210314055084404050015520701c0065440341e1320344261394101800d5050310f100d80141180001c2035000144642051040b107190494600f02c0122000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 214318633 1250 214317383 214317407
    0x50a140102040b180a0317070b0a0612060b1f09050307060207050121150e0f0604061d0c07020d08040801050708063303010807180903080601120e070e0601 68
    0x140e4010041045038040c060705454200c008000308a804403210340000326074503010b61000340300d02c8101e10844101040a000381c1350050041c004200e2680d10940e00d4022651280200c880c140380750081c43c0e0100c0c800398803100008401030072205c1e100401c25041035411304211444e80009036041c009001d2418140060401032110380010b00c003541c03c20002a0044d000d5a2404141b4190103004400b06003154106a800c1880c00d041c00a0050700e4510f00143d6500c01c40d20350782c04010722808220b03a401d09104841c221000c070b000040310013042460511a0078000340c141c6903c00380500080003d80e541c00c0c0c80c1c1c1400361281d61b169665a1518003400d09443c07008040006001c0d04004100c1c41da280d5171828186420346c66107101151848400c0c1d044901c000442a030b5070200080000f04010500160300d2040e1200400001d0803807144400003010345104e110003d00160080020030055401103c01004007020810003040d4405444201d5203070200a03404258407603200c0061028650b0064401c3c4c9030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 214319883 1250 214318633 214318673
    0x15010908012003041703130201020606010e130903020111040f0501140f0306060309030d14061203072a08010903020d0f0c02090c090d020306041211061515070609050a 73
    0x480d1900404040b242c0c060101c54808400c00000101000580f07a4030040540c20948107607101e003810020104100c1000078202e026100d00c002182041d07010790210b40b103400c00140b04c01c4040322007803407540140805900407402c0d9034a0b00d40d504804d01446003d08090f02c1800303042d044843c40c2c0302c001042e0040f21810203c1030201040030600703540081007141da020304282c812964940354020703118510f1086440304080c640ca401520b810650025144c54040e0f40112a0781065080d40b58216880380300e54880100b03501c018801c581d442201002c0d4181201c000c040000e0696590340c0c144c1030948020760780803001a0007a8449000c850f4008000032a004c1d282d2420f26454015540819581640602218200300c00461940019664080c00302e8405034003500b90b828505292810301400b100108007100031649103460b2204403140092490b02c1005061420991850500709014034046040c5c1c10205400701006850b02081540c026001c1d0070b4400c00040c0625603681c00d180c100c2c0b400324003040300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 214321133 1250 214319883 214319891
    0xf09120406141c09060b09010801110d0b04060807060f09090219180b04080c130c020d0e0604170309040e010216031d180106180f1502070803031501090801 68
    0xa4960300c10966042403040c401c00c1541c43c0e454104482000d0310350b040034418642401d2401042040d141c001422948003500c2c43c1d07605980700d810711400d0750101c541304203c0e28400d2083c1314282e0150b4100c8141128040c00001c1c40c180c4614000b810191560040c1003c00c0f00350000c0c900141e4010000402009441011800d111030070b030400410700b003440ca00d0f408101c9240038465528240d885250002c0c00c40c507000581d250b03601c020254441180d2034680b072050240c074551034281c1d1158001c034420050780f036002e4819800011404c0e2015640c43c1c3e545600104180404140b4031005040842c40e030380c04400943c0c07601c60b00c2040109440c000d60700303c84281d00601040c071401c603100d4410440554036003001211088007209400c02c2905170b030965030b441010035000c030782e040d0300050141e8142c81542d41c9220400d0341d0002803000d429044d03c01c0e0224107450a00821a4000e154604c0102c403071903205a8441540d03480c6140d18640040e194001d14020342180c42540d503801041001c001c1c0301900c001d00c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 214322383 1250 214321133 214321139
    0xf0303050306010c0303060b0c1f02070f02090c0c01090b010e060f010807030b042306031603050303042306180c1e0f061309050613090f031b0b0f091204 67
    0xc140d400040c0c01c8038188a444500101007501a800602c0500b20b030000c03050b10340d0980000240d07920740e151801000c102c0c0f60040720503e40c000e0300845080b40e41144001485121545c03d00c120f401e402050400c0000c002e012903d0000002e00a403a205401959680d0703d550400c03a08503000c40303010701403a12030a40d900b020075060742c04c880c80590100450400181c040704400214001d4034200c00000c02d0b52000b08000190100036a1145002d40003c0c0d0494090400c82420295403c550340009001e641c030034030016000a1031403d41e00540d04442d040c42e0341800203402c0035131800205a6151000d00c0e9640c1403c818070300100401c003031348902240c20350080d545600060503042da03940c5078540207032105e604207170203071701c0c1d5408503060074080c1070f8440f901c40d6840303078100020002070322160720900701c003452512486d046018000c0100c0d0005000103081a8030b507810740711000d10050011303200c022080c189020039400c00134244202c890921107161480d08000060901100501c0018078407018032082c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 214323633 1250 214322383 214322387
    0x4092307030c030915090c080303091203062d03060703111e07050d120c0507020306150f0402070b09011b020d11031207050a030c09050d020904060b040e06040c0f0303 73
    0x880d0801681d0500080c81044850114090654401c001c0d2246460050340b9005240c254032501e80c0a009951034240d1035100c41c00c0b0b903103030b204c103807291101648025520140078105100035900f0800c014480101444810001c4081c0307048004107141c1030305400380840f49820709201090740082c45181c10071081c454280c04d91094040c0e520212018086a102502040c2c82d0404484210b508071080701c2885064500003080c0d500c1064240c00360034102a000709000703001c0c100355200c00e0b500a01801013942d40340c0b42c3e05801c99a65030142e51003d0481e0044459403250300c003c0003502d014003058811460840d60803402d41c2c0c0300e0b0b1000f61144050301d580180c26680400d240e05030508515005100c1c500400e6a00c1ca180a008040c1240005d51418440600e4014004107e801000d44091000701c03000706094490060500c18543c00800c1c45084600514250415541c09446000002961031440022074215026004441c120781d1280040c4800c3c8004411584010513034109001d510604503680 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 214324883 1250 214323633 214323701
    0x3080c160f05121314030a05011e0e120406181503020c16050604270f0b19030503190516050304050a1203020d0804060b19060f0509030303070528050409 67
    0x994030178400400c2c1c00c81c98565041c0b2880f41c10a4201c1c00901c12502050224240e2020300c3c0c41c0185c0f41880d100060381403001c04104030102c0030101d8000c0781024900041034030510807019400912015528011498054982d5000018144c42d030300142c0b0707580040110742c80c058040b038680c94004000c0070304111070f903207002c2100d00b40c035448841076000f41d003020020090f00ca00c039484110454180280103c0800103a40081403001d412036400802c0d844040060040d18030341e001c040c10030781041200c1c0100014803001d1070081030b11481e01c14903026440c505003c2110b60148100c07202c0c0c100080401041c54161410b0024110240c422030007045031b6035010b584c900c0d0504400c0180100940003806100541d0700c102078203400500041c484000f000d80c03031541014103000344c1d03010880c0107038a21035162040040d50100103018005501d542c41e420b5041c0c81c10740101c55075581a43e07241300755103c12a0b5040700c0b00d10302081501c51076101c80c01c0040c3d02003035a070030601c41d0412206595010302d000c0c2503189 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 214326133 1250 214324883 214324889
    0x60905241503210708160b0712020a0c1403090a0b1206060c071e03051006180204140d051c0c06061406070b1807030302061008010c08010303080c160f051213 69
    0x2440ea0b0707100f060b4900790300c4501960241b098505900d080c00414055680c1c15144140000d41d1070180d88035031842d0510403409910180000260b003003100300700251f90002d04201c1c62081000f01d03403c0203640390004111142642040010840218610726110001d41c1580c0d0455412150941000d54400342c4030350301c48040c4a20201914030101d0700210201448581000d550400c0942d02d2651680032114090501d40c0f00710210599940c0c809040e000e264800da80690703404541350b13003001381704800b0014524080e200c199001c0c05007000400703401c08012056081031000d622080c5114585040540071205554080c15410300d010b41c1500341562100c003119031141c0c1c400c0310300700d0980303900e1882045a06092411082c40c45814404014036400240d030501c135001504c13043c400c594076442168281d501d010381000110b0010710044c000207004800d0309502040c0080d64a0801428440107001c0c03c038641000e40d154506480c4090600800713014141d062800b124101c2d103480c0b2100b5004c1000ca103948 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 214327383 1250 214326133 214326193
    0x604031d04020f0409051614090f0f040513151401090504050703060c2c0102030a0c080702030d082401080c0d0908121006030501060c060905241503 65
    0xc1100d100c95600c03076065541089424455640740d0b41c80b105c0300c0e00108070a031422020b6002800325a02c0b1944211556014400010b03c103d0424a000c800d001800700520031503544203c03c0f04981e4520b48541c0b14642c82101c2c071043c2172041400e1400c00300c2c5202088441d500c03a03182068200da456400c84110700b4115443d080000070650344a0403c181018010307000200b6075820300e180c0100f200ea10030500105007001c8501d03860b40d48800c28400488102100c00300d8096001400a031081300d00810381840c1e01c82c001c0c85a41e00d002c06a1303000a042561100b4010007043c180d0303050240d2810000202d0380711a600056416181881000191031900c0041105a04040c0000c0c0d480e15034829130000c200240c1e104c01010f41384c4456a01c41c982040d02240d150320b00c1c2c42c1e09180021514407900074141200c03210381b51404140e034581c03110005401c0e05441558103215100d1100c00050f05a038814011303031240020981203040c08160b04000b0148041440e1007584102010101100b00300045000c0359819 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 214328633 1250 214327383 214327427
    0x90f0f160509030d0503150d0209040314040e0108032a0606090a0e1911030a03050909041103031b0106170309040e0c120c0102160b0315040b060c01090c0602060403 72
    0xc0c1012103440c4034455207240c05002e10380c100c410711500800950b000314520180c8583d0f00c050304092140990361108040d500241c9200400c020a008244940441c03892128440c545610360341010487c90080c1e018060b0b55200041c00400c0f000102c5584150f00b21409a088800c0303500c80d81c06d1b90320603028103050720030810003020410101c0c0c50341c01803030100e13501d005403207803000944070f41d8804540c85041505c55414148203c02130b85004212003004642c56160039041c030700c03540144a481400103008441e01e1421030380404484e50300300041c0c01e16000842d601d1070f50400c0d05507a00c1c255155540904507d8203100107030711004901005030380b003d40e01600c000800c40356080c82c0d81d00c0c2c100c440200c5034121780f00710f00c8254100d001182200d48441c003a003c130b4605d6602080703894507542c039500c00e400c150704003400032031031b031820900301501c20150082000c0303203894010001503119030040c207034520b051303541d01204010041255441c4000b0b09490010709280d02d0f1544000d042d4130950100b00b0218005 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 214329883 1250 214328633 214328671
    0x1201060212033318041703251709010b121f020c01021608040303080c0307050405040216020307181401050f01110111030414010e0a03020c060a0912050c090f0f 70
    0x741041401454100400c000c002c85200101a00403a20a0302d0694440c0d00144002607081a52400c0303a01400c82c0042d8441040e400301402214501152361000c03c0010b0781164044031011030200f40d0051940000000f006011070041200e21a40c80f054603c15400180011400c00c40c05000c40c01c1c0d001c0c107003101590344c142c018502ca00900c249030860a1214204000d4024001080b01610607a4426203508100b0340b10b1a00c1502c4d5400f08490200008900700410300041c01e007500903081118240c184600030f04120740c0040e08054194000d2003140d80980d01c034140d20b00240c054a18001501c018010007541041c000c0b0380d4039219290400d06004014251428070042548801c1ea900c0d000c02c003054680c100f52408038242103220a00e0342880d802c1a4400b2094900813550a0310f442d4503400411004580d00144070668110544080602c141c0c440005052403200359820040c51003070028000f03c511003410001e002e04003407e440201012082008110f4001660310350304060040c09004090107 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 214331133 1250 214329883 214329961
    0x30a03021b0102030f01050907022d160803220b04060e06040801020c2a03150702070e09012a0c0b04060e0f060a0e0a0804090f0b06120106021203 64
    0x91881d0001d819580f001003000041250071242078180d51044900008075210700204a0ba00c607241500b00401151800400140c000007544402652848000307540426200008031360408500b03034001c140ea90030000e580d49408407400f0705050020340b00c0b02e031496803070705051a01446008a010f050140510b030b1541c66401da0310541604c0040188a0003907541e0216108103c0e11120103140d5440c0310580d004181241107204003d03203451100280003400ea40c9100c1c44840b640c141c0180140c81503008000002c80c00b000c1c803422080c030608494001140c1400a2105440030040080501d440c0552920099810a6102e4505c081454010201042e03d80b030f41c2c01c0180040640d1641c0026038840d24000160b1701d0b0000c02d440d0702c0351041c0c5404000040024507526210200e490005200b00f000b00300512652070036030321203080c038150400000755003101e000200710341d640302407030a07400c00010380010000c1650401000c900c00000000c01c0c1d0850a120340c480720100403c1c0b140b410740840a07912200020 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 214332383 1250 214331133 214331167
    0x201060305101d0d030c090504050c090114090a030b01150806030d0c061b030b1014091306030209070512070c08090f040b040204091a030f15180304180506010c0203030a0302 76
    0x40c2d01054a81104c8021000b43c0104044015400407417245900042c9174a414400c142c4600d1200303850307074a8400100011601c4c00d00014080c60800020320100491f0b0b11425208009503200d0b022408a84d41480d201580400b083c0400c201004000310800400d5200466488480c0740c050401c0326240707001e89028406041a04c0016041008011110701c2559044d0050000360100307491000a90510900440d0540d011135500741c1090400c00c40112a030030114003800008910400000360241c0300d5002401270714042d680e05001810105412032482d60320200903800c001d442c1040041c41c88250b41301d05032400742c01d062503c40d6001001391925611150051001e101008204560b225113810005008001c00c41503c0134aa00c00d019103005801c000071168508241c0000810751720801d04900105a103000303000d003d5000380c00140a81e058420005000a040c5100c1205480c140c1444044112070008201c1810800c201e054400540c07804002c56110307882910780035075207030800403441c1030107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 214333633 1250 214332383 214332431
    0x90606030b060a0f0c0c1824060504060c0503091201020316180509181606020708010b090a05090f0a080306102105061c0f1a22020d08070303050105030c01020106030510 74
    0xd00247d080c90140e001281d8482d5110003c0c0d5440c60962000854801301c28844a01545001c180104001e1144030f00440c0780c0702940c0d10500450b4038060010000c038003190414030552106a4022081c41816007040b031122040319000c0c6004200080100103a010a440c58031515005990f203402162150102280006511409034121926941100300010803800703144111001030250a4000c960340704107005000c0260401054000d182e1102c6603903400418029014108a12414440010300802840441b03c0d16000e90000754807498031106000300840b4280f81407040200841b81248000040c1e4400107503180d407444001003070799489011802c03115000a03240c0201081400101c01c00101c04244020a4484d00c8403980180c2112482c80c1603810a65022003036821000d200c40d012a40400054000c90009019000740b071080d450b603001d44d621200041e0006070315070300140300d1402c003080001c901d05020b10080161a03d507481c0c29860300d080080034150503480d515036820510354128006c01d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 214334883 1250 214333633 214333649
    0x503040312050f0109110c03030402150c1501030c09050112030e0111030d020d06090c020a030809100203040f05010b01050c0a02040e071a043b04021504090606030b060a0f0c0c 77
    0x10908050740b09003c1d02800b44103001106052a00800040585100740d9282da05030344000e605503210b541c20030000d605d8107149150021004e02600c2c00800742080f096540c80d604410328882541181007001c81120305401020046050400401c603c1148416010086800d0b03d00364000c10401d80048030082d6840c060302a1a200110303860010340565030042c0b110f424604c20030401c3d0750751a1001c006a60b01c208056025800030205140030901606825501000c1817069540c06e1819120000c101e0701700791002d5500a0400d40c500b000c00c1000d1048108032003007402c1203410120741800166640c07160950003405541c450480c4045042c0400c2040b004c2d207070b005002e118141c0c0002c0c4203a0746030064070610038042012003511100d200013190407000340143e03011604203c50b1070600b01c4164400580200c0e08680c031140710181c40400f440180c0081c0c089480c2c0400c0070f51420038020180e501000a05201b0041040035040303250308a6801e04485402c1d0903c001c60f03000718140f01810255075031018403 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 214336133 1250 214334883 214334891
    0x301151d090c0a0315080601050909010e0a110f0409080906070c0305030d020c06070c030c17070c060e04060603050f0105100c120201140a020703020c040f0603020402070c03030e0915010503040312 86
    0x94501e401d10b01400d9001d010360340030800b03980110580c13038001d4040c3c418003c160304100c00500090400940312a800340e5148000300310076112900e854503040c0d04c1e03070b015902141c0b18000e080142c60920306400d00300c1c10844091082c8400d0b62564100c61103140c0c0420300c180b400060100030044034002940040d80c04ca03040d41c0d00d809002030400c1c0603610528451007a4007030f090015810902540800c0000394050385c480360b01880580c0e8a40c500c14a40580c00329209091119030001007072610910090919560381d420780004100a00042c2c50719908800c1c1803508150800c10b00b2002408943c1c1101c2045900d00d41350402e9844c150380c0d40814030300c0501842440c440d03003415150150480310043c030203000f820009940e50400003089010f0290020016080040544c0341e034502038006040022920130001940c90b41c940c006000ca900c031030004c5070710382c0c0102c000b0400d054111100400b82030342522000b51515014914030381d0480c00100762818018040003040c01e26100780f14008081c00c402c44104 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 214337383 1250 214336133 214336141
    0x124030221040c24020607030902010c0203031303150204030f06020d0216060501060905100e100e0d050105090606040b060d0c03090215090306060109060e01110a1b0612020301151d09 80
    0x78001000e00d000303850048104c6014008040c5803c1641c41106455034040c0180780c4568034101d02401030b040d011703410080b01701c0501c1c01580e41440207000401d030701006040c2241c40d514150b4036000d0380c801c25451162041c0300c01c00104103204007500e032255001c0b400603920322100c40640020b0054155107522000c00380c04040c00c00c0039980c84541620001d440c3e2034241076075401000782d040d548030750060028402c105d4040309402c00040d504100440360604109480055001c6441c0d04825003058407941c1d1900180069040140300840c0c1040c800d0303d06001c001c0c0e001d0b02013025441442090764400c0c1d664a01000314501c09c1c1c2c09990341c140d00810503825a807140705000781796000015102d102c0d01407100807503455802401c58004955090300c41c840c2c032140c03120043d81d02070400040c030000c5000343e500321000500e010f07000703e414208a00c4800303551814102d00903d076002e507102c5140c0e030620420051212030a0542540c01e08251440c1041e803e007500d00070894001e41010040350865845c3d4188 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 214338633 1250 214337383 214337393
    0x19080f03070914060405060f030907031b051806012f0106030b060405060a0305120f0712171e16020c10120b0405040f060902060412030507030305012403022104 70
    0xa80403500800b540006000f25601007005610440c0b059551003d810491500d01c1c2010001030340d84800180e0544211982e0380d22000381b048160002c48905c06010b82d420320080c54210324038403242040d081405180c1c644440013800448620b1002000c104010581c00c611001407a03000d421072000c00001d001d401e036240703813200704000143e0b01688902e081a00180d564108908418100c0b50420020b20911001d0503c919076640b00c00c008426042080156030081031803c8a0b10800702020398840304866408100c4104400f0094114104004490b00c0025807040c01c1c0c03170158010740a002c006220400001040c1e00d08000d8074102600302100a03808503885070030951228030020704140c00c0c410019400200800c407041100c0c02041c12603801d0381500480c1656100144143c80075201c5807030180c44101100d1000c05a1204074005040000c03004101603140c01461b005042c02d28a180d00c19100c0c1078084400d440c402c10b071004142d03010900700c20381c07411075102c09840304c109907a42409050600300 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 214339883 1250 214338633 214338647
    0x50c0603101d1501020a111504091a031905030a1b150b09061507080304020105091905031002030103050c090702011506020105180309010903030c0c09050f0711060919080f0307 77
    0x1a010901043c41000c80340c2d50011a00e038000350750010940441207540c0b4100f000c802004d1160402d003a100b4000420440d04500c2028040c4104040408090700650300b018500004804042c0c10702502f42e5000700003039030000a032080d2802c941442d0b440c0c42c144103485100c08410020142c01000405401d449106007584842c06020003a1203000450b522641446000c040c0c5034820701d03030110108814404030750440d0140d50028414548549040500800103c0018140700510341e941c400c0c010070055882c04200ea240e5429002ca0198155071542e110035032901120030a51380200b008100182525201b03500130b00c01404618134107001117072a0300d0002d0081c0800c89141e080125400b554082c030800006c2070302c0071b0410580d80d0152150031542c040b03400c500d0b4018200c42c0f25113200da010a03459107600406214011194030804030703142c11040146400346508018050350031150a1089600c00480d101380100040c0b0302103003401e910b924124005203d201c0c1040e119500210a1105003644130394 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 214341133 1250 214339883 214339891
    0x10c080304030c030314091b03240f01060e0a090c2a0506010e0103080a050a11030f070b0f010e010504020702030309030d02031b07051011010e01060324020304050c0603101d 76
    0x141c00c11422620708009450888181c035103098983c0444604505074101d01d90000030401c8c042c041e140c644800c1034801c91401d0307000f80344541e0f40591404000e040300300c100c03403940100f0070b0f8908028049189404600c00407001e0051303440702610703200312001081c001c038001c90342a2841c940c5210130340000c090700381200281000407107040c065800005114641010b00c02d05030383d00072604c00e2401205010940d410780c403071642c2c003050000c0c11001e51044041840030f00703036140c41c803000d036070f0742c0c1c2c52a1a14101d500300c002c10080301e001402006100d00c2d028140780c0c4c0d0554070f040c0c400581e074040703900000e1315500554901c2540f42c460034145501103507020015051080c02400c0f500c01560500d81d4507900c50400d4001c040e0000f13600c45295003500d00c0b03810705d21035183c010f80c00080d101072030002032070a58031582c0064442e0303c403c41c0d20310a138401e60000e01d00601c0c5800c00440c118207003565820f4031554500701c450312a05010010030b442d401c82c0300800004019030300d2910141c05520110100c4a5402c507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 214342383 1250 214341133 214341137
    0xd050102130605030405060f18030705071814010e0a0e0f030405090c070308040201050702010c06020d2a09090b190e0a0609090f0f0510020a03090506130b15010c080304030c03 77
    0x40c1c000650380707019000b80c0b0f001d968050058049655000d801582c00007000f00310307420300c4901041c0c05003900c00a00c0204507150060b0068404d9a04203805070052091402d8600c030021702e41079007803004400b030b04511415031750102007040d920780315101726501500d0040c506d210140118600d1900079607000005204540c01035a0700c0300d241e038888800184600540c8000b4000c01e41060000f0f005600c554014080984141040408d490b5075440b40012a0010900d0700540341d07a5245903680a1500780d49440d62215002a411140a203910028481c0080c0e10070340c58090b8440b4020300490b070310100c502642240e54080610296a80c88d1080c00d801c40580b030180805180040c08919510746008610046800c1400b141892103540c0c2d640701c4868000c0310503125030044101d1700e910030700a4001418260840d03980811000241e081990601314050221401000c1d142d000313100080c0825169075000f02e114626245044101005070340c00944002d000b4a003110000820040640000c1c1d001c641c07900a03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 214343633 1250 214342383 214342417
    0x309060a0324030803070302030601051303030206191506080606070803131704061d030a120e01020f060615070501110d0615080403050f07021503040305041d01210203010b0d050102 79
    0x300ba2038040ea082c280405004442d08000180c009406a002140c1141040c07400601d4106954112951010f513038100b140103030007540c00d1088035100c1d8100706c6407046405a0400c403088904540e1182010207224070000e222035000020b11700d9032884241c0b054180c2244403a6070360701c2c0030445061420b040c0c800485040702500000001d00c0d07402e005580030703100340b40c55041d415116505d034101c0c640303071110503e80c3c5842450000b03800280c00a607c501054296200c1a0340048000000381c2003444c8140c6d41a03844c1d0180041007000e60b54a181161012504410340b07a403486c99080c564094022405030700e0511034005420b140c040c1c0d09074050740c01c13200600381040640c003600c50701b140c01074000d0f18090000707003090090b040d54070007c0300204600b03480146410584171112580c541c0c107410490f003d0f0040340001c10700b0010a40c800311106003000304085044243d42c1082983c1c1c01100000c6c041c0c0345801a107070854801c6407000d504ca04007010b001080c004140a161030182d0103503111006001c950030340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 214344883 1250 214343633 214343681
    0x4060206100f0612021309020901020f16030b130816020a1409010302120f1b010e0109080d0f03020d09200f0d020405040809130203150925020309060a03 67
    0x2401e0307214040c0c401c80d1076100740e0035281c890704031444c465403c0c60b4451240d0800241c4211070f025913860000345540380b80581c5888002c400039080c43d500641c609096003010f1403120b040d02c0140030f54019280d00a5240030031b500c824245524954440800400d00440040e1192103a042010006101482160b80070b5030a03450fa0f4065603496047c140b10307900240e0500060005140c4401010a280c4002040343c0880d210085403519061441c0c1410a0000c0690000f20070395030702c20003094171a0002e00341300304181d10b054a001e6074cc074000d25400c42017103280c403008080c240c0f0903012205810381b0000306104030009070401440b100e041e00e00d03014480c8455000071007070341807120f05141011801404012542819002c1c08084e20340100200c8100b80c0400c40c0b1021750380c40400c000c0b4600190180180c81e4a8a01c0c68681050200031109206a00799070070080c410301040b9100340401d89282104020700b014000030380c039600500c1d94040e4007500200700d5140b0194154030000c400e0680c50100d034503204c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 214346133 1250 214344883 214344901
    0x2416050a05030f0403020c1e040509070602070308070c050a030809040f0c020d110309060a120f021c0902180901090c12021027090e0615060a1404081204060206 70
    0x20500180d1404507000307000181d40c3e0000e01083c180d02c02e0003401a03408080483c00003950034000e91186441c0100f03c1d180c411898207051040942c01081742008002440c100307200a50f40e400c0c00c1c400109010720004001042080905042c00100405043e1540080e1680b81910341a0000e4951501030362a10447d10011030540c00b6059000300f180e000b4181541e030303030801150100c0404108d50400d120800100002d501c0f084000c6c07001250310395a13101003c1116400f00c042d60103410701e0032207540c0144900c1690084a040d469401d10b0112030001d14540b840c4080341c0c40c96124600c654802034440104201c69506401c242c5005100b08000040c0f16200c1c2c804e40c0440d46075420103508495402002c004840c06a003240600c03400c401c1c03136840c40d42d6404114116407e9240c20a103c0c45813a0f00488c00500360400140c1d0b00300c95403203100a40b200c103000200e1140c1c012800c401c0108505141882c04c0e541d100403c0310040c01c201d400f81c40d20200e8500034928550301500c0343c04014850500003400d010 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 214347383 1250 214346133 214346137
    0x2130f0602010e0a0c05060d09050706180602030c030f0327010b030f010501030507030609080f030108010912051c0b0109120c0312020d05190306050618041112010302060a02241605 79
    0x130307500c2a40ba01e801820401842007681210041c1021107680d883c040c00070540401c020f0340180001e82d15031404001d02c02881150000b55403041e070540d0700500a40c0d00540006c810b865601ca9410244c07600c0740d81c0c3c90842c1031f90a0f03070403c12090010120481514400064005007550402901203134440502e208044c1e0803100300f4030001c1d04d40e8000e0708082c40000c81a40080d00d5441c0079140e0315060804034003850a1541c003c1e44241c0da2699108622410400280c501e8500340d000c0e424132500b0240464102c2d14549001c813501d00e0900c1d62144140402c3e8015075508015040c0b07211170415003940341c540207050780b030345001c00c1c1e4405c403520f181e07140410301c001001c4001c82d000ea55040d00300340621010130605000c41456409060f220000414152035680c06420b00320140034029408043c001c0c140070440f18039002c0f8520021081086c60b0000845c44603080c1141d605030380c05c41e0307100c8103618100e0600c2c040d001c0592060007020b400e081c079941c1c2080c109018517080d0000440c103811520003640c6034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 214348633 1250 214347383 214347403
    0x5060d0b043f18050f0d0c090603061509020a051207030b0d060f060506130627170c010c1a1503060709090615170a02130f0602010e 58
    0x851000c00080000325071a10080c4401031403a008507081c01c000c00e200801c41c000c90080a440c0000c180d010048a90020500c181c1560980c000c158850078070001c50010b82c8424805405070805514220800104500d003400070210f40d80208409a00c0f4036090700581003013515039840003144600850012100c6c42110180c1007541c60342850b11914419400403254000c004406042d500c1d0240c601c0c9803100102d904009204060014900c040f100002d0304503180c0c0d4102d5405a03009010809024a000c03860070706a9081e410154003401200d4611a1803101005011122000c0000002040851080c841a044441d402070b6165411004011181854100e4003d81070300681c1c075056103185100b03ca00c6420103c0f000300860901201400303c0c1ca001d6081e02c41100050481c0d0040029445512408000e000e140041b940348018102000f84901da8000782d020000c2e45040108151840310f60403207030001e003108414000e550b0b0710381c4076080d866200d20a10016500344000e6100c40c0402240c06014 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 214349883 1250 214348633 214348643
    0x30804080c031b0a030209090c03010c0e031c2007090f14010905060108012601091506060c080f1b120d052206020a05090303121602070308090d0c0302040e1005060d 72
    0xb03485d5400f08900c90324050301082c03082c05901c80e1150b994a081c080e014400e030460321079650f120306031028585409a4000a418020a000c0e821908642d0000741c00d421010848104411200103840460510700d90303502c89000c03545081480c0d4031100080d086034581794414840044580c4e03071a40c1c0d24003901c0f821038656001404010052001c192142c2c80d119044101c1344a840c41e100d43c2040030340c01c6650b03900c000d907815090802004005000350013410041c0c0b08a28000d201c0801542d20451940070f03800c0e22048012010411001484c11002c219540902e002c08031000c0a000c1250b88000750311000120000d2801c1200084042c0d84881e21920000a89440b41552543e01d464083c002d40044a8030000c01c00100000da1043d9000c0016001d41c031120701c00f0325802d04200a075000043d0a81c0c3c07007042503420443c2d00f0404282642c09a072044002130342d511003001681d20f440340c0c5000703c40d003009500c0703894201803406e10800083c0e40d4644110400b0f0800450f01e42404100d03850100800040c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 214351133 1250 214349883 214349899
    0x8010e06010f1707061209060c11060a060501140c010b10030606020c060301080a120504120503031801052e050d030f0f0912020616080403030f17131407030804080c031b 74
    0x74644203e200031200e05018200147c020030075a650001d6480c80402040001d07100615001045824499190011240e84003041041e181400203000710107400e0b020007500401064440307041c0c00030341201e050b2040003010b401c200d80742d03420044d00500d4a03019120052180b5409000305041c10300840341a564114020421074500d13a40e101c403180842844a820060140400101c10202061100042d84074a025540300c1c6042d05034102c00700360301c9991a0841e81424240b02000303603a414014441c01405504c0c414116200030100d80030039055100540198402080206240e8024040301d07030300c841c13542d4070a01c5c1307a5504011114140c0ca030040101e6402d80d5811540180b40401c010301110102e114660603020141c0c88080e07168000b41d1007034011030002071ba6110229804007503807170f81d8a029000220315090001030080190307203100d4010000134404e000d00d100300034108084002980d102020703a41c2e4544410003d501c642004501500034440c15400303800010a000010026030000782a0030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 214352383 1250 214351133 214351139
    0x1050a031b0510090303020111040302010801050904050f100204090b01020c030d12061703040312030203011512090c170c18070e060d1514030a170c0708010e06010f1707 74
    0x401d01c0440905161240c2001000103668a448203407503104022511440d05592560a010b82501d10894040442c240d0400003880140e8100030140c0c10340f10150381112950781c4501d030091400080d01c00ca441c1c2e0788a010708030304580000d50018025100145d0307003444004c00303007001665940c91001501d036062700500300741131201e0701c1034480d052901811300780411041c1d0b59440c02102500494140d00d10740d007000806105014494a2414424180c0e290840ca9585003c41c1c4000b05c6001070311030300801c00160f007400e0380d030301450b0424441660840c2050042c16550b0003800240d03c000c040e000c006025100001c401032614032040310300756405c03900140807075a41100031170300348100030703e9554014801c1c0b003e10000030ba1031140008c6c050400103000e01040c01c109001152014290149209034400c2d2012000201c00c240c03814070081d0000100d0b512084100c24003800d103031194002407031540c41d0a580c01002400095814101c0352008403040c10302e61518510281c003c1d200ca0303500113544c0301480c10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 214353633 1250 214352383 214352393
    0x112b03052a01020309150112021020010b0a090b0117100b07030809060109090f02040f0e0f0303160302071a0405010212090d09080c1c110402070b040c050901050a03 72
    0x812580d840c001084040240703461009203039074040d1448007842d0394080b040000c0d8590802c0780d8031a543c500e500c0d82c49158034180301080000080c17035000b8016070f01018011501c86c000c041030030700b42c1c1c51128845007004841c4501030091490b43e0086100b580d00100020f0402034910891414000681d80da041407540042000800f0b8405003510550800700100000c8013074041b0098440c80d480b0ba5280d008604100501514009040c0c010842c1c1501e403103440f00000d0080c0c0b4500c0100395065402180ca1528490301c180105840b070403014140c0a41c000c4040c1141001c002148220050380e099041480501001c900302d00800f180184100c00070b8200c0c1d002c0c0b410041d0031592041c46400094a004030300b452018200c6030686081816034451001040059049869603001c0e240c8480200800807d01c00043c0c500a880c000c110307520300d00101c1c9241803081e007100710b00380088047c00070765998101e40760200000c841107405031451000341c60301144e14074010200c1812a540207100705140340c15501c807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 214354883 1250 214353633 214353637
    0xb0d06090503090402030403050c150f0106080601020a0503040b073005032d0f06040c05160c08010501030305070311120403140c0a0303020708070603021c0b030a0807112b0305 77
    0x40e1402d100610240020380d80e113000952085110b03655990700c0d070f00c803008405c1c540b02c03011100a80b1440c50404012040d82400c4181c6d044465074035100803543c854800607424214190405052404001804200c980001c00200801d5108440f00c0e079689405a480341d881409401045590314251070404a030340d4440c0e80036607048088800c1d0528080505c0c14081c1400f4900c030420200e061825080050380c804003180039910104c06d50f000c0c8528000d40c04010a10f1159521011501084031010010b104a0703c030b45901070003a52008202c296101c4c14044d019030009802200001c1c0300569401c1075041c045603201b0580741c2c04031030b00c0c00c190559685201c011003d5400c05658820581c00080d2035035564500340042d4000e802a00166041004180c1031038840e80041c01410300400086000903070709401725051900d920380000d013010b19580021704200200310058010003002c24440c042c0b1045a0f02a000d00d0011605004992000080d0002c2c194280e2520350b0800c5690382d000002ca400b41d00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 214356133 1250 214354883 214354901
    0x30c0c0909030a2304090c140307080103061a0307080f070f080613080c0d0807030b01020c0f06070201210606020705040501060804140102040f0306090b061507170909040f020f040b0d06 81
    0x41e81100014a0684180300c0f40c00660044001b0b80d20340382203c032056017022144c0d0000701a4144646185030004000c2d00480040c4401040c250740c9000700300701c40f54603401140c8442c0000303040e6494071395640400d0784c0c3c41c0070001e41908680218913001443c501c403240181c2c211050480985019a2002c2c102600030703054050965002c1000c000b0564180320501201c0c07080c810580300c0704c195042031600202160003030000c0c00d0644d40f280720301046d0fa588080019142240031901d0030754a420a200403074031098214681c02c29810003407520070140109402010560f0a540c1c00c454960382d48500b0001030740c00070b1180710302240e0400045004074501810360034010014400252800c2e540e90340501d40c0c258603038420744480b680c030301c0c50408229094903800e41101088400e814102d540042d0040503200d80000184151aa030582d1440c0700507007020b4820b0340034014403540052516050030340c43c88a090104a01c103c038080c403440071a03c0c10f480782e0b0055007006401c1d00c2c010280c3d5030302c5000600c0e00c41c0d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 214357383 1250 214356133 214356167
    0x30210020903071a070b011a1215060318060f10060c050a05030301090209010801090b0109121a13020321180d0203010501120203100203090613110a0305030c0c0909030a 74
    0x83e00100d0742c2078625410034401405114101d03a1007040e0304280800f1041078000d101803031003a410b4040101043c50075500400c1c002c90310310907940c50300c05040140504007004581c01c024080200030208140f10409440e0300562003e44003183e480a000ba0f40101c001c5941180c00007a0300c034280045803044942d81e00f0944500d0403103550401644071540b5680090380700350101070f00000c80340819603004065030300400344c1100600030f00e001c0303c0001c1c00c13040f0316028508943ea2581400300c00c2c0300203018088088d50f2880030358103c0d03040140300c1c1d021044408005074002c0c8103d0388010141040e42e071204082d003481c044443e05295610705210001c0e668001200d60020030b501048016139028880c80340240310100c2d60030796940051051605144401d508600030510600810407910804079509034801e4500112180220b014a0320b10640c0d4207035101141c01580905000c810040000001e00e41861011304440400c07092170100b00341e4100486d00080e50f5001400b150740b981e4081c2d81d50500e0f402d129 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 214358633 1250 214357383 214357393
    0xe0307030b091501030b0712150501030209131103070e01050a02121e0f1e03010e04020f041107060509011815020307210218010f080f191a0307080703030210020903 72
    0x3c000920048900380c1060740c01d182100180010740c0e400a45c04180d080c8100414044d45032880070020714928648166418036400146042c20340d0707036103050403c0e16608048100443d0819580520741c030340048131500e0126005018110b403541c0664141e8240c90350b65070041032600c421010703000c40764000101c3c24040e8590341c811414915101d070041e0060307030059544592940d00242d400c02e501603031101e286608100401c01400754048141c0e826038040d405441c0d500401448802043c010480c05e02e60381102c403004500d0004100302504842e005010380802132205803110807000c1459140c03510300500000c0c940031000c102c411a03401031940300307041b410b00d610044110800f0102000e02201e078488010f40c000b03030000c4043c00700e903000514980c007071808104601d0f0b04007001d80007083c0a0204402da20502d0300088040c0544400340c10000341c0702c902449071441d0000e400820399000ea45440c464003c1d98800301d0124000180380c01184d4240c3d009001466240780000025031012225517014052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 214359883 1250 214358633 214358653
    0x60a1d030c1b010503160c050703080d05150405010501020a020f03030d230a0204060e1309080f0d060503010e03070308100819030f03110d11040e04050d08070e0307030b09 75
    0x14000340448400410150044801e03202c2000b10120301d0062142c1400b00a00c1801101107440c1160964010507041880121aa038101286098010b900c000e0803414001400300d2803d06542120303009042c07414841d03554406040402042e00e0382405607900690100c24031201525282404403c10200502901e161914400d101802d4846296400170381d03085140d000c40013500c440ba900c550000c51681d003103051508082000702561001c03e0f04038031422070702a001019203280d900c00505241d000a1156640056007400b01c0c4a4105002c0140d07400e24001001030746050602614a900d800780d4045e6207402016a026540b08502818003405c040d51080301203160802040212001e09010301c2200321403e00c0c0c0360040030440340071805400c02d41080300550f003010350a010b42e0f040d0710309008003141d0b0385901c0b51842c405000c5c9902401122030003206000a01c000840c1040b09807035182c0d9425000c0d9501c4a080d9283c1e205c101802d80c0607400700c841040441c088680709a00441c500090b500b00d005 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 214361133 1250 214359883 214359941
    0x604090f0f060204080f190809040f05090106050a0501090e0a1508060f0f16090501110f060408040503151b16141b010e130c0e030d020102040f1403060a 67
    0x71201d403049420035030018007400b0303807982045045060010031006020410301480b4806041d03107010340080ca5a080407030b00c0b003596925600400300300e00c6048410003803031030300c031755282d002c1c12031071003920b000c2c0603500c2000c903881d4420031002c02907441c149200c07912504d07031001c000d00800c0074801a4801c00800507010030880c0c030030300049000f102c03e55243e0010f410030168500c050b01d4040c000d00c4076142080c5d003468445400c41070720303400c4a000b4201fa18641c4205180e080c18030f4095455201c090090104000c01c105041c800751042c1c0d00b05400301d4030f941003085501d51600300151080c6075200392082c03600200d924880c1c01080c2a5990f01ca00070840b096a9480001031800d0480c07d410355000707001d01d01307424403106900101c1c0300400d180690002e0060804500a080000540d400094032005043d00980c0520a403030fa201d08080c0803103105102ea200028000e4000e80140000000d40000024254007460700c590080c003802006010309480d04002c600007080320319400000f0210244811101c82 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 214362383 1250 214361133 214361153
    0x60b030c0a0224010e010506120604090606080a0b010806090d0203180a0b04032303360a0e040303140408120403180906051203070c050d0c090c0e031e060604090f 71
    0xd410f920b0002015410400d0000d04600160000c3c0e00440b403e00c104041c441d41000015040b41c41542e00040030f044505210000c0c3c504c54011700098425240403004010342581018101e6a2a6064907159181c401400b81c56a44403400500181c2c030a200c014500c0000c03580710f1800d00001040b9a66180d916203101030b8980242d4403e4030306036134169010841094940c481500c0f10242c0003d5480c1a56840680311659000c084108051140e403440951846000002014130b40c0014580e031400343c0c2d5108028000e8204580480c0040e0404030055944005078903010b0213586c1c41240c0c9400c20315000356009680c1d4008005030100680742c00a17904440301090305402810003603801042e51400d00080c0014189000d140700410742c8200311307410118410801403015110200e884410810b0301d070510003c00d4460313800c904116458101080310950300b10b000d40f008100c0a600303940e01040800580081c9084d12002440980c10100000300c05103000c1d80020280c91041a000341d0091290311065000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 214363633 1250 214362383 214362433
    0x71208032503020c010e010c3e03070210030606080c210103150e07180b0a030501020c061602030a080411010201020403050a06050907050904150902150a0207060909060b030c0a02 78
    0x220340e001540904c8100c084c007444003c038a07060002e01180d007038030f21300500071035904803619548110b1510620002c444a0b03003c00c9010131b0f160314140c00c0510303c2c440584035480314004070320900b4981102e940040c024000d040c03c480c10740d181c003060f580d00c800170460280c0c0180b4041e0700d0725090303c0202030010301c26101d07280a10300035100c410307449580060100c00c954500c90000d0281c1d11401c42048441221042c1084030440d90300040f0728050070802040d0f0b207805507040200194004a2006060328001410510030b06900711003940303a994002050340c5038030418142c03c0c00110701d980003030046a064a8230f902225010b2000516181da82e458031070a100c0c1628007210042d40380c4040c0321500c08100308240140008540300c04103424141d5a00d10000701d2014101105d030f03140e541080540d03075841d90030100d8011844116503582981d6100a49500d00c0303004034001304c2d12051012426100611400040d142c2c008407240c81c1d40c5484184400d20b421601c410401c5120308070131808101d5840906000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 214364883 1250 214363633 214363637
    0x30b040b0408160c030201030c030b03071202062b060506040e0f101a030103110306010501121a0a080c0405070503060102030702010305150406060503190c0f052214010206090712080325 81
    0x80941181b000505441d8204110420141010301e0003003556004100601100d0488102103c650014408070303010b4051500e182c0b1910302410031108090032802c0e581c24844000441c208030f1951208c1c100b00e414080d600174580500c00b01c8c00000c0f081000008002e0b0081d0103a10b24071402690380040c0800c07600c803402c082a040c0c44c00300040041001c002381e11800c1101c01c40240202e9814040000e082c2c0c2c0410300981040c584403c460860050001441d28802502500c41134200740c443c41f06d585e4070a83c4084040c091407038540000c520610030010350380102d5050340a1442c105c159001107000e0032025003159040b01c01d4042801455403107216400080500f600c1f21502d81c5460407a13401a05000c0c80720303903151401d0018000c2f00c15481841d2405d0b04005041054a540c4c0b0307046042c414864401440009092030b0b00e01041001c80405c000180b240c00740e08450080d541c0e913002680b1080315101e200b1001120076841000210740b000a103a003c0298160001441540300e881c0d03054004410035000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 214366133 1250 214364883 214364903
    0x4090c060c150b011e05040f0f081005040c0b07020604350a030f030c02030904090c090b0f0d020f03150708072d0e0f0a0806010519030b040b040816 65
    0x10400c20004039400b00c041070584100450201030380040c0c807030600c000c00340c0040c0070169540c941803070017070080c3c50141c4941030002d21440d4a50b0507030b00d410b400c1c900580140c1d10414030b0038803d00c880c0d801101d11607917000d5010224149895550f00c0c0740d401108049900032400c4c00701003440d408440010b002900c09078154028400181a8503000780b540f15003154403500411501c03000b01740c02c0245658400304c1032400040b1410700c42c10032400c501908000c02e41c400d04240d001c00c01c1c803031100504801e48040e20800c1202c01100e00400c94121000880aa000040420b03a040546030002c040c060720038028041d40e00c40400c28040c500c0ca00d03411149000800c801000b8400c2c1c260f8000100030400003054051610781101c050803840410300c0403612000c10020114031429600c4030701c0110b40308903016066421760b60300c40340e0142c5c4460003401080e0141441c0f4900d610b130f0070054002e010481381c200b041a01e81c0d0300c95442d4401603000090042d29618010860050b165204000a41174a802442e80c40 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 214367383 1250 214366133 214366157
    0xf04060308030f18071a03070306050612010311060c071509050d0f0303050604111207020f0f01051609150e04090812041202010b0109050f030a140604060f1b03020904090c06 76
    0x100350100d000d036061190b80905c5082c40842c041481c40c4445007000c540c5c013901c0780d4805a0032400380040350000e64210074003160210040f4000c01c05141600d01c911032103042001c416092015500a08440700f0070b0380d00c4418100a038064003600042600000d10704100c2e0030f9101c9020030a543e00b101c0080b9401e054403148003041c9a8180b0075650007010461301800720030904106000d0074000c000d500410ba00c1c401001c203c1650013040b4413154117404005442089566540c081d009080442d40400b02c0342c110035104140b139119a610806075600081011480c82408504070303078100c040100e0980041c2d541d42240c001c076050750050310b6241141202c181081c5020f140145006255840003415a030404002d604141c3e04030415100b552802d03580c04014801301e5001910b41507140390040d1600d41d4880514130b45d100c1c0450f000c2e208074003c61040c03004203419903a02c000c8a660110b2032403465240240b5083c65482070b00280540b0b100140b001c10300840c10346030b00c0b41c2c0440d281c0c0b00c1000311b50141410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 214368633 1250 214367383 214367401
    0xe0a03021f021612021c0306050f030613150f0906091209050901060e03030708070506040221030d05070302090a0906050a0e0603060103020907020f2514010e0f04060308030f 76
    0x40c000c0c110010708158184000100a1010a640700790010310f407602070190b11108520800c2030036103c20030490301d10006d43d490b24000c0c00502d0301703014240c02000b250a84c200756003000210035014210900300c9090307500007515220202c0c00c44440d01c05010751205044600690580514a07070346000300c00c0000c070b020326850403032408a4003500c3c00713090204402d0100001cad13840300d04207030445030f140c2001d031042500030001a003107200c1d011000386680004038800050100c0084c640713200780d2003901c907268000c400c0441c018141c80145518862a4000c01a039201d540c8207400260300300030241805810008600c1c00140603405981004508071782e0703010301b0082842c0c0603a06e01c009010300c140410715810854003203529071005010181c002d801c40307004912810310801450000f0059034003a6660a42200400c40d844240d448512000441c0710070082019441d00002030071280f4161075000c40b0b40078070028842d508007462211a48555501d0001012078172500c01541300300b180301507550a5141c81c0b200 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 214369883 1250 214368633 214368673
    0xc0706080105030c030c0105030a0b040207060b01020c01050309210c0f010b1f09050d08040510030207061119230d06050312040305060c0c0a020d0f032c0d060e0a0302 73
    0x1042e8801d034032040c810321881d100820001c4a0359801c0c0b0f001950390703494014074009407003522080c41d0802e20000b441c006200441c1e00c00d1011010036030a48542c7d0340c2d00401103d0174001a159030b60325030803000003501d500c1c80b0f010f80d10041c030181540140c1000c4512044030b05080b108901c03112a81d454510044032481c20f00301c4141017016003c50107048290410000340420b1540c01650b002d032101c41c140318140003181007610300428008050881c03841c102c6074020041d40000d41e04840c0701c2d04001d85411140050010303505442d6000c803000c0000100304104a071040c0100c21120030f141c403843d060354913178130240c002440118004140442c07800c1c07a00301410f25180900b541b2920611060009100140c2d0204003d83c2180368500b00341d4698440d125010309241a118000350701070800400703c0d040011744007444104074041e403034003005001140c0000e130041d0000003010030742514400c0c850046240060a420419003c0c1c400058142c01c004941032410808207801c0c2c0140c0d00544184402c3c081d403002c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 214371133 1250 214369883 214369889
    0x90e091903020115350106030606151701030b0a0209120609071e030503040b030408160308071d01050306040f0603050f03091e0a06030c02010207171b03120a0504030908030c07060801 80
    0x2a203808030064070159a07500101c1102074100344c2d4841301704e100c0b400801d412071409150484410841c10f5983c050f41400d106142d505000464101054100400b09107c0500d041300d8108807096a40d80c0d07640c8010f00254040a204ca601111040319601991010405140f04201c00f074000d108040c00d24040805003400390350075011840c54000c0a0000078004000d40b0708030360080381c0c03540e16074540d850200384134011f02c551442c05031103080408040c150300061150180841e5155002060035140000440a110841140c081841040810305c40e08095001c00c00e00781c00201c00060701c90312581c5141c2029601403d5007896072001c02c40c841c0c0f91070540e2415035680b48040b210010000d4075000b0508500140c4241c00c1490b603a804452a1385000390100d81c40e035580718003141035814588010090395044402078507041c114203142240a030000004440156600410310f4516030f9650059102805000f80200c04000b05002c0001d080c90041000e001b10800c0a005000480d0034820001c240580c140c1c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 214372383 1250 214371133 214371149
    0x4020d0213080d02100513031803051605040b060726090a14040b0117061302071208070909020c1f0e03030903030402011206030807060c020c060a0201140703050403090e091903020115 80
    0x12061180d130181118020303010035454181001403058902c00c84227442e910f54006052800740c06900c130f082e907460a00d4401a0390046500304023669020003407003144c1c007902070014040c1348211034074101d400701e0266140d04a070090f1091864050240c02158840e2034581c031080034910322002910491506004402e00241c1c01e05e4092100080c00c04041c00108001d0000341c003c915035aa03200d02c10410f03030100d071103854000144503440519800010440082140d102c000a0020040411181c00702d00803070325110355003801070520840c4154244001c4540820000503203581c1c80d9264042c81041c00a58412580c9001442d200d03c0c183c0005081d0a001c94441c02540e8508142480000c502100303070303038505401050004840402c44810b91618142d044195400034000c00c20054059054202140032403c612040c1000c7e200e2400c1607090b200c09680040c0414054001072140d41d5900441503401000b0704104e0b17006d0b003d8100c03143c40109005134150f0040c0d4440080101d0704621040c1c6100600c260 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 214373633 1250 214372383 214372391
    0x305010c05161103033a0203010b0f0d0b0909070306140c0a1d0901171020070f0803040606030605070e15071b08010c1d0f04020d0213080d0210 63
    0xc2c080a05006500101c020840801c2586030000d42d1800c1054841c9281560303100303110f1a081c0703569003460b064010890303100c20804a0720258a00761500a13030341210912031500341404a00a250f04c0e054001070400c03c520340c0e480040448039901c901c40306004800b581e000c1c001d80c2d425410018282c3c1c07000804460b8024074a014045460b8110085502205540c900300400905240b0380c901e4981c101c801c107d51045a4800200303e4214010701c00203201020302c01c41d11040e102ca1800b8044c1e13294030200e440d000d016000401c4045c40701100500000380701d22000892121542e0b01d1070030b076030410b0380c0648065030340301d8091081114501c260750b001541800c05041c0702e188440042e02800d10190b9101c106140031400c00100001c405048029110000307005240b80d84502d6a6070080100b8440c10300002c960116800c58062610384908246601621034181200b1134000d000207580300c107121a41d0194208031900043c1900d2650310060110300000c3d00342e00304558002842e0440404240e40e4080c90 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 214374883 1250 214373633 214373647
    0x1c06150c17030c07060606020106210f020d0c0317092b06021e0304060902040605010f0207050d0812090d0801060512060d03020106120b0a060f030201300c090305010c05 74
    0x780329103070601c220864008540c1c0365208031106000f030080580c000c021034200040403030000c1d0190044000e56008100b20100002c084070b041400c0b0182d01c4000d04001100d00303543c070250130114048006903000354601c0003455900d66030301030f24402030f8900c2010540f0109030a0701902d00260348042502c3e0b0150402c0e2a0010a41d04c2600084401d1000b44a55400642d80a81c0c01e2070f2801c481120f003d048800c0e45a2405080220203840c510074202d100320301e003085c0420b003580200828520f40c107055009045180c2001c0610801c541c1505096899174410b0105806801c04565020b224403202e0001c2e18000c000d4010151010364180c01020074810207200c04201640e100c0112070b4001c8045071155504c2c540c2c1d04003a401080240c004225480d2042c242e0b0050000000d4034a0280c81904001c20030b00340d4541c01c0c1100c503180c074000240002c0340c1c541e01d100140f02070380b00080038040c0070360f40b40029660352100400316040b4488000220f2094401081401002c5c441d02d51001c103241400707850024 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 214376133 1250 214374883 214374893
    0x20f03090c18042003120f040509091603080a0c0c030f031106010b07030c1109180f0105070f0e150c100e0307050a170d0203100510030c050901141c06150c 68
    0x22101304942c0252004103002c031510380c0c00b084100e007403c0000c45100e0703841007105003404c0d6503030050041c2ea008030411000710380c0201e00083c008010481c42558030215a0840d0b03103c64865010340c0c654001c00c0411100d450125209400000081d40f042e842d0086984031841c0107441c0030388118500105402881c01004440c0141d001c690301c05031305182c030b4044210240f81c400c0d00340e024100c1c0c668001001c1002c0006424034881d1f15191040340c003046804002c030102d00340c1d0985a0840300d0000080e030324504410315a001c0c00c006010128002c010407690203060305007940d541c101226008a507440340300b000500d4800d500c284980b0801403409145460b02d19103486d603940d620540c0003490340440c0c0e5406040c40001c00140c03490100034100139950380c02c21048455044c0e00600030f0a11503407608104218482c080d106103031b08000c0544640341010041001901d030141c40e66100c0c10441c40c00c100202441c0115042c0e8640d514100b50b00284203402d002646a0078154214a1400c6c8042000c0040c041a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 214377383 1250 214376133 214376153
    0x318110d03031d01020403170a0e0411090d060b10020a08090111071a09040605030d140901030b03100c0201050601020312010b0a0e03011a09060f22020f03090c1804 72
    0x4000352411a1844514681200100b000001c1040390b0526005001d503811010340043c03040f01e005000b026001e40c2c48054404d41d9100300c035003a00100d00d07a10303580862400c040d08103840306400c3c1081c840c00e01d090100030503070a4101c080c1c11141c240d1744440120700c0f4580019602e40498403171009101140d0350f40d4a01e800752103040446810b100400004800c00c050800448020b8120000c04072407003d04503901605513041003a12034401c1b800c1c20004141814005000c5142c1c90351a5902682c8801782040d82c28181c3c0030390507041c10552118100d036025101007061641040d40c59000103082c000e8280c009007190b001801d05411034108001040c01d400c121405281921031085045554020106065620391080d00d0801d416508120320145030024200d804031f035040c0c042d280234500303694290070002c0800343d007a2503581c07000307000c502c00036001004c800724002210200c40040c90310142214504490f041299412100e50155440c0c035900c4c102404070301d0080d84602e04040090415a81d0f4400c0c1d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 214378633 1250 214377383 214377413
    0x5101e0b16052103010801060b0c06070c0309120312050c0304031d180408071b0807090b1504030b0a060b09090109050709090203070f0e0d0b0c0304030908011b0318 72
    0x8a446401d100060001c14450b204000c00c1003611910003000f00c90000c01560002d20844003e546030000004070169560300b1034042c4e010f170001034000744c1d465000c02e5900001707200c07044c0c082103200d44004c04d040c445010b000354000c0c003d44541031600c55105840c0280c4000600c6281a41410f00500002075007060074a410501400094500140ba0001041145082c440c0070007101e00c0010030b210901000e90024080c80d40180800c08030503600051900200c00303148074081ca9980500c60400200c00e05501c041c034050002400c0d440b0485014000e40c0701070704550001d40b07844464409004070340d011403150500820450050300c3c20200e0500000d004c2d00c0f814443c0d609015110f5000980d05031154400c00c0c0034008000c030440d100c5c01d00c1c0d00e00410b580c07500e2442c400801c15000f00c0b400706180c445001958281e11501880281d03a540720a040c040e0400b03001102408207060010415840c00c1c06180700110100122608110781030000a0a4505000503880c0e0f003032043c100302c000700318000034071024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 214379883 1250 214378633 214378657
    0xf13060f060f0909050705310e060f091c030e030a0905030f070608060913060c021c020609120a020a12080604050a0b030a02040e120c010902150a050d0f0e0105101e0b 73
    0x281000182c02202c03140041e800e500801c018140e0300c40108089600c0270421882142c02c880040c0d4135640710400402e0103603201c0c800c6a00c6a2001001c0d01001d61902c240c0c46150301c1e02050a0083c8840c0e40c1c5182c01840e403120108100701c205000794141007002204008a883c000c02c00d0529103500507014403005024540036090120000340c0082c043c0c03c4140420b0340c8000c0c00c0280c0f403500b990017511b40c00c01000b14180384140045200d0010710000c2d83c1405588454050490f404003060301540641c048042c0c2010f5008403e2143e02040d5141d0b0403a032003110036240c0006500c2c107041000122440200000c1d1042e140102907505500c0001e0700110300b69040d18001020100280428600b030180d5141412175040002e20807500740c1c040d0050081d40c3d2098801d802007250300c403050320740c078042c513060007001074801d03c15200b46400395040310346862020080003c0c5403000000860070344404480015944030560010095801d51683c02d42c0400030303003001c021103142403100356411481340c1401100 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 214381133 1250 214379883 214379899
    0x2303060d080418060f0f0501021218060310030510090519050c0d050f010c0314041e08040b0c0d0207080d050904060b0a0f020f0a02090f13060f060f0909050705 70
    0x2040000720700803180504107030031031040c6030070721101218041c1000380200c520480b0190800100c12440c40240e00a9039016005068414181040700145030050ba00104191901030614502ca80700c15004500452100700095080c03819400e081d4a003800d10f21640d80103d10f003040c103a0200c2c0e40031500c101c440c00c203058101d03d03031807880c2007080c5080e403000d02c003d40c40512602204100000098032412102e802c8000b480800d9508100381c00301c416240040541c03200110014000403a0f08501c0ea04800030036180344500a45501c0d9203c9640003900071003548130000400c1c80940004001c078803080351180c030040070668200001c4a441c3c0072032803c0c0105000011519942079030340c81d0090409001100980c030b440e80c20344d680080c030400c20b0245600150084650707000458501043c42d10000b500a40242815201c410b907450b07030401c0c01007907511005000c0b4078880c0010b0b800d01518502c58038016000c0b81c114208010b038134100f201c0341e0003071640c0c80c90011040000b50300452002d08851003100c40c80 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 214382383 1250 214381133 214381159
    0x10510030e01020d060305060609010605190302040b371e0c050a050705210d05070212011407170f0a02070201050c070905040606080109171b06040c0501230306 70
    0x280140807119421045540085844208503600d0b500c10422603005404907034240d00c5c0e803418441d04050a00900002400402a60100f200003000c2e2810f04003040c034005282903554812907007036801441002040f011145015094090030702c690301c280d204d08a02410440003900c401a04040b08486411a60101c0042001e050b0b4062040007080640203020307076400d030302140f40c0603440e00325a02509205100040f649404000040c2c0c460b50010002002450741d50301000040d9256086200d0490b801111750786190200602805100c0344254800c07100c00742c1d23042a0001030070002124103c455254250001c001d01c602030003115603040400d080c1c2c016038816a90004881d03030301c1503002c90340e0188611840000c0c107000c40d030b021030310590080707400300700080c0c039140c20500340c601003180544006d040c101e540d00221031034402003500c418004400a04001e20820003401d12600310f1b4150355a040c0091b040281d0358004290400c1c101c480440030850a0303140744191864040580b4440c0509070041401d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 214383633 1250 214382383 214382387
    0x509090604020f040902090f0f0121020409060209180601081609030b0601020c060309102d0506060408011a0306090a0b220c09090303141501030b0307050a1502070518010510 76
    0x199011741d0082c114104602d403070710b8036407100781081d00c0b1040c0d6000044000203c103400d90b2000e5403001040c050002e410482d50f002c000103010020401d42e24141d08005103100303a640d5001c1c484211050402c00c4a80d4a0800005808040c1c014001e01d00488401c2503410704690019041050302c1d400101c2000350384030070340101c0c0382075112034545400c0180001440709030b610004400c054001c081d0410b00032880c008000c4005200495404031904928161016104040750401c0c3d03071000010b054181001da641c0500e500b90f607031800341e03480000c010201c042c5180c2800d0100726031004403500140754410842d0f0b15044042001020540c405034000e9010b021503445a070600800c0303402200c0a54a036072102081c4009100d0301034100d006c40d15000303000100045001005103e186003007642d1140242c204015809444141c219035414002d0b048041045d0f9a180c0710440600844503074001640c0081d00301a203000b40b10342000f0b1080b240c001040c0c110000302c1c07805034103403401030f40c89500e86100c240b01 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 214384883 1250 214383633 214383641
    0x1051b0109170301090b010e01080c030604151e121e0303090206120117061006030e030c01090c030c0b091f020a050a121d061e04030b041505010509090604020f04 71
    0x1c014000c1880c0b02424450450440195060301c0e49460300700040e80d00040152815540f02d445a030100d039000b40000c01c46031044019541c00000035002088420784260703c0700f0078400c25000200148691400c501c0d400354142c05030710181441c050145036501c16a11400c0307804035564a0010782608140c40c0f903080500c45e401101080380c1c0682120b0b2a810700c00040901e01c6002d00400b0700c038840345603080f42d43d8480001c0150054074010b111447d55400d012044020300b608408044a500c81040700d450f00c128240f003000145402103051551741d0b4254541300b08009900d9020700000c0d47c0a00201e0b880d540d804000d1080c00002002d160403070500180d0690030009040c1d4050401e000340d1040400303200c2c00f02d042c0c0c2a8003032030b5650700513209008440030f25810100c443d8507070400c8040c082e41584841980014082c2900400b059040c41d5580c0d6038080c3d00407044500311520103883c424119524a030380901405010300b19100b14040c545030701903603640c4000401c00391040496080114643e121684 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 214386133 1250 214384883 214384901
    0x20040920030f0601110a030806041d07091406030a050709021b01050403030504050d0306080618120408100f0207030f0e041d1605100507080304060b06070f0201090b0901051b01 77
    0x20201e84a29041560251842040f50b0720340c0450010014042c51140102d0018020ba60513160407100d038030342c40705100c001c00ea0205071140141c100440c01300310308003c0040c0d00c018120041c000c9000240795182d50407035480a045103020381d208043c03480c001003001c13914800355104410016202c00084038180d0503580c0134000302c031055190a0501082c15815084284114026011a4126030040c24124102c0c0c40354401d100e070a801c12404205095281102041072407420760440e0005260f464015800b503010b5032202031030b0341c030075003200481185a00501020021801046080a20b0358401030107234a80c1c4410403041001c0d0750982b80d1030350b031982d100002c01809801e80c0103c065040c480ca0b603490100c5e03450000d040b003a40c4000240783c51b00004108100382c850366020704100303050b079900e0310681024104941d0a0b88500c2c40010715240e201c0a040c920380203000c011200601d500006d40307401d0403030b0400c02010744100042566641c100b811180c0d503503601c0340c681420401100b0454010a0100 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 214387383 1250 214386133 214386191
    0x5180a03020607110405070815090411040c08100e1e06010908070603090b06030c0307051c12200601050922052d010203070c0201030218030f01050a200409 68
    0x40782883c240301c4502c4403000d201304107583c200a42e8851a1050b106900111202901c09c1040c03801300f4140d081841c4120b400a2142143c1c0038182c0605001805030751107044644000344114041004181181c00a48002d04d010150a001d0f0f0400000d04a803c1500d114039424122924000c40c460387d22600c911001006010251400c60791904c100034090711041030191511480100490300914011441c5440a94010002c0c8141460042030003031201c00d401514600c0588034000d0404a198140780488401240d910204650403208074105090001545e041c603030740c800001842251100d1403183c0d00884481c0c01c03c0394520842501c04002c4980c4d0800030014005c031f405007400c02d01d03141e000d40104c01c14004900300011864190034200c3c00111042c03030000740080901409540a0b500410b4408500882481c01a4051380881e182c5480d00c0c02d01c0c1030a0399210b0400c000d10487d0f2281c3d0f50b62282500c14804503441c450300c0904d0500403405400f039100d55900c0c5410071000c05a09200210701a1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 214388489 1106 214387383 214387387
    0x7050102031801081b030903030117010c080c090409080d06150206091b060c0f0a0303050a090503030a050a0b03060c12220f020a05120102130503060705180a030206 72
    0xd0055440d5440100011780414845002944680c003060000c65480d494078070344140c5848183c9941c18946d24241e142e51a49034003411140d002400b40050f40d440742000e00c000b074003c1031103160042c000ca0700000c24010080312500260f085826808581c0814451920141d031100d0003281c0301c3c1e0003034004948a1805400170000840c0620003c3c00d12400c2c034401c1e2120030b180034032140d00e6824550000406104069060085560101b681902403080300419907880340e5900015104940c015203038400031f400d00b1316035440342e500248018215031306400c00520f5034055510041810713074500340c602c0c00110300070000011414240900c03074501442005603120103031900384014040360b1100c9240000999a0740f0b000b0038580740d40600e000143d54900440901d40203c4c0a41d00580c001c0c0c120008020909070060309035461000c416401c8288000c034040007900e41c580517000254000300c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 214208633 214388489 := by
  have h0 := BRFrame.cov_init 214208633
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 214208633 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 214208633 ≤ n) (h2 : n < 214388489) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
