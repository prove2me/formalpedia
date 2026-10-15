-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5332
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:31:11.697842+00:00
-- url     : https://prove2.me/submissions/59f2ec47-b3fd-4e81-bac7-9316a58b0c97

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 958812949 ≤ n < 958992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 958814199 1250 958812949 958812961
    0x60911030604080f07033e0f10331701060315050405122101090504030e091005150415020a0309050f1302190f03020903100f0e1002040608 61
    0x2580c03486150894521401c0890320740d464078845d8040c05040e010000e40d1200080542000403544102a403201100030030b00c0f220750041c05100001c10890102d5030400344240d01455008280e40b84500d14107040050f001010462100760407200b45c0b40040c0200e00300c904413001c600c50803400000c2d59220701c0d41d100101c040a12103406d03900c0038040100740301d00c00c0c1d2410720255031b160815508940301c1c0050b01c42241e50f0301036107885900408140d10920508499101c088010210602d01504203410180014900f5440190028011411050080b9444000155141d9140d08485c0150034018440300001c2490590203010303801c90700991b50081e09a02456034070600000c2c07410ba0503540741d100c100b6414500003c1214440840030b000d03422840d14050030030484a68802403a60140c888800c54003110150002400205280c4004050520402075a8804d41d8005100845080400c001141c0f80071400e1400c8050103020302c0d0003a441c0316542d901c40b0756500540180007941c0c03869030717001a00d9540e8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 958815449 1250 958814199 958814203
    0x111e101103030f0703110a05070602160f08090406060806090414030c01180b0105042d0603140604060c05040f0b0919030804060f080105060f180627031b0108040f020306010306091103 80
    0x302d031f04000401e070100310702030018040303402800d9034000f00308041c04030360000e88458070308503006201207170030a00000303c81e2110f2070309200c0d41c0003605d01841d1414075454030501003802c03500301034009404100c2d036081c030800110301041251076100500c4000d01a410340007030006508000d501c0c0880390345012070008102070030144640c0c1c0c06404461450003c040308580c0d461908999030814600c07094540300040b0105400c0d140c45814008410010710071403800703080042c101c0d03d4120356003080000401007003159101d102c901e4410b0799008003620790b543ca5188000b03010154400c0101c42c0204c4030410020900c0300d01e00292049401c1030f11001d81c115181d90080300c0c0648240200da03070000c1c007804031001c0b1210038400f82030001d80c00903e00062080410009a0030740002e4640500e56106030301d0b441600000c4001d1801484040d40141032500801008030411403183e40c104d8100450400000c0c10f124840142d03402481d0041d0a580d40c650712404c100e400f030001c42809440907204081c09601600300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 958816699 1250 958815449 958815457
    0xe030a0908010c050703050c0a051603110114032706040c0e070809150702100e061006020a0507210c060503060a05180a0c050906040909111e101103030f070311 70
    0x61303540d60700d42052581d00f500c15070007600881c1e005102c0c07080d9000008808100543d4000d20b0000700001d058a140b50100c00151104d681c241040301c8000a40604803a45090f2900b0100340010003025100d030036021201c80c02c1d02060304070280b1035a0f00b8003082c454000c079041c0592302960340d1400c05503103c00c1c00307849801007500c403200e17680e02032041200296180704900780c000c0c1c80c51040e1109291108401d00c140c804448501c0c0003030b00001c061012190755120007070000c0c1014000f41c51444010b898007501e03044d0500c030700c0c01d040c130083c0140515000700c100c3c00f044170b0303906c030f16003402c100c0e190032008001d5082158003a02030b200c180400300d107a142180320604c6100d42415140003540d5050100d90191604846110601c0320038041c402d0280c0c0c40354003038000341c6409170001600d5245810414a10040d8200b01d0303004c1d40c00e841d400d50480d01c6001c4015000700c42680c42c179142d462030250131102c43c0d00500801d1420300002c02171110303502c28018641d010b0034080c1d506102030201030318400201d100d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 958817949 1250 958816699 958816721
    0x20a0b131a3102040c110102031906080d120515180703060b122403070311130204030c0308030c0d06030b0612010501290412080409050f07050301090510090e030a090801 74
    0x41e1500c03820300113280c00e81107a810603040b0300d0000d4009461070313121826a042502c00080c0214090000300023810923110740f0009244404c000c1c000085224805000c007102d240b0003640c01c40e03c500c00105c4018500340130300b0302130034090120070300704000700542d280350700c419561080001d0402c400024503a546c0801d4a40d0f6940d03090401d215078641011825010701c03642407001c0511050880701c055035600b4401103005602482c0d5080d182c00d548810000300c2488003a0201000384180824170100d0014034244080d02d03441101c0c81d41c1c91b00e80c40c010645a01544810340030305820700b20302000300101c0106090190341d00340c4008003220b6100b80303210f00741d520034000c409601851409400d440501011840002004030607031500c2c01e038a800c1c01a28481410a0130b0b074a031140007404000c0451740d0311460b6804031180083c0540c80c102500300511611048c0b28140c4103070785802c080356842c1c25614111000f080e0f03240080108d12034402d10b02d074032500300c00340c690042185080e002030811010700175424504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 958819199 1250 958817949 958818031
    0xa0c060f0501150c0f050f0d030b1e0907020709050c120a0507081b130b0a110304030b0415020c0a050c130b090f0718080a0c0503030a020a0b131a 64
    0x3001c10300100e139520000241603c1c4201c480c284039000c071700240500000e031800301d13016000c240078010340502a5203502217034034080e412620219003080c440081580b003040b0122102502912207080803482c0504981084820a2808050111036040d100040c00701c4e180c66005802c19580b0640e00c003040f40e00c02c0700c012011030310041c00225009083c00c0c3d24003403039609e00307051800c000c1a6000651070701c1240d0001d0b44d60600000e42d460129800110006010000000170740c80c15056030703207014241e500600014803585054940c205541c00c540c056400e10030720307081103418910990600715a2018002100d90140103180c1c060021081030b8014400f82c0d03000074125030190341742d8034074010f00f4420040502c001c0104c01002038821a0854041034000c161480080815040c1403d00004006084d404684254420052850350326004135100c1240c03604511002c2003a92964000c500740100a4001481c60310b4a5201c4903030001d81110131805450440c240d46d0095030180c1c1100d01000e11000e1200843c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 958820449 1250 958819199 958819229
    0x3031202032415070803090618120307050d020d060608181e0f030a0c020312030106020d0c0203070504021c110909040807020307091b12110f1b030a0c060f0501 70
    0x100e6441d440252004000d00302409602c01c1c3e07400c424041c0c0204030200c2d055903002042c400110700820410350040200500a07154051014609580700c50800343c04140d06008030009160324041d01c150b8841d5518054290350701c00780803403408002c0c050f9000d103001050f01e000100307019030405a8214011078800340280390b02040c2c4100e504441003824800700b6070744a0074291141c5034070181f015203005040307030b04c40000d484140d104050030072902c03041c0c0101c0e01400b48010480203034001610307007400c691070030001c080407040d002003400d010440e041550050700006840500c051440003902d043c040b0000c04015802c0802030b0b0801610031110701940c007800c11340104020803041c1e401070078032034401001c5035412381d607511a010641c1c0d004280e81142c00341e00c01c0b228000c59002001080b02040c900e00c10089003501d004850807500500074003044e49480802c603c1da1515000c02408451141801184d4a603405600c0c001d04480c10501304560003810800d0f150036619103402a0340c10390300040d0092082c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 958821699 1250 958820449 958820491
    0x10c0f09120b34030f020a090e041502221a2a060112300c020102030c010501121e020604050405040609060e010203090f0708101d06070203040303120203 67
    0x100340143c00300300210440d0008420b607612070040c200031680d90180d03030b12100340a0007001d000c071040c1c0610303d9a102d00412400c0c0801e64400d61400546000c42086052a100c60819940068140540807200c074400a105060062448954004003e1101c208420503071503040e031941c49000c0d0328428074414818400703030417a10f282c0c02c419040003c110000d06400081c04031507616018003a80144005000c0d0410311080c414000726441c2400400680080d08480e010a010352418582002c1e00c01c0110b41c2e030a600441e8800d1003200d113154142c01c024895035031a0704264408011201c9c0444280181e880d40c454440c480858aa10340c0350000e0800d07042520f00810310018180080044980329580e02c00003000854500c01d002070400004001030b12403500c0741c055498070814007050f448075030188030b0030004940005003181441d18015804508034024684088882c01c036519203490078000e0600b049403481e400805402140d01a13034984030b03e43d8814480e44203e1105603915031501c0000c4810f038079 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 958822949 1250 958821699 958821713
    0x1505030c031203060105070f030e0f0108100501140f030411011806050f0f071407050a12231c18231e06120a11030c07060b031608010c0f0912 62
    0x1501a00606056103080c500d0755860088202c1908c040b808115a205400500c0c108510226002e4070b003030810100d982400c0c41107004421051084074108034111000d0310f0075034820b50079602c168100041e1151207042501c4e000b600c2400d802c3d0031710300060801c0d0b2410502c1a115803c081225203545416140c808555080c500c554020f6007052081d05040100c0c000154401c143d00004a0303a5001420646040000300440a2143d510690f011240600c3d0b103400704003c80c02021914000c80441018180d85005039030400e2043c10040c1e440c0303000c4052038000c0c240c0200c00d00e080042c00110621500e901c440c3c400c2003099540010122048000242c41403504004140024400d0000303175070700302594043c5c00620b0690010020642c80d1481e003042c80075258041c05008a0110464411415860402104043d0f0b0040620103860651100b40003a40c0b900c003800400e085237106c9203005a0300c3d8480e803a0a010780044550a40040c0d42d450440c0880f5202c0c025030b1080d45d402240c030300c0f14040540c0b6401c0e = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 958824199 1250 958822949 958822951
    0x5100507170d14090c2e1e030209010f180e15060f07060507090e010311010908030309160f060509011413090e0606010815040207080c060108070f08030a0c0807030c0f05011505030c031203 82
    0x2c030a00001f4080051030440c2c1c0429400203e20681d0056510a09138000400400100000c541400346a070300c890301c081510341491094034003007020030a50366a882c44810600b0301004a080e086140054200054030342c20004240c6140501402c0c04035407166402122980c040e8400c04131141143c20040c000070341c0e018144401c1e100d05150400c0032070303100c80785941140d1003912116807d5100c100100b0400840e101964005d0114600032561079240c004050504d20035a6403640c10041841481140301c4110402e640b00b00850782d001201d07090301c8110542c02400000c400c882a407280c400010f80d290301c03c04000b0704c81c0d011021080454801c19050201035001038008441c00c82c401d0041c00098001002294020b000f0700d801000d00e00d2504000e405da036805508800a150020401d80c64220380040b10034070840d42c4180d503a80d4902060a0071030701d10502d1900181031460b1994140180030054207d00751042845480c0c0c603180381c0d92801c041e0b94040070070000e46c05030002a41c001c0213101a02c061 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 958825449 1250 958824199 958824289
    0x5040b0a14070b070e100302030c2d18040f02030603070513270c0614090d030314040b10081912030e101505100507170d14090c 56
    0x10350500a00350f803880310300902182c2c3da000148941441c41c0d0345107001d40c07911000c2c1040f81411490750030003460f6640e40b886146041030300320450300307040c101c0c0e0600c0c1100807a481d410b4400d456280c0491850089003040c648800c288940e0600340c205d00448241c1c42268010700740140100000c6c0d28100070f02507003410202004000580d640660500c3c0704c0301010002c01859610306c07440a14005150502c01100e545d0080020013070030400900c044c8140d40100c070110f48044810700c114589614080300941024499000c0403000402480200401e0b5000180100d985070010010b40d611560b0041c1d40d02400400201415002c01e40b0300d01113401c00b40c00110619403840c020a42c2001060101e2030054004015240c41ea542c40d0516440b44002c100b2034041c24003107030080340341541200000c2090103201809405590080c0c614890400f00000300d0f19601040c0c001849184e4800410105118040f1216001070207005051901c40c507200851900c820341074a4245000248514407010400741c032041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 958826699 1250 958825449 958825487
    0xe060922031211040311120106120803100b0a0203070218390f03071d10030c0908070f03172b0902030114040320031909120b010303020d05040b0a 64
    0xe8040441c0f03014009001950161b02c90303107803a8034400280840c45910042d166100c1e45061410300c89425901682400036400c41d207031a40b6612152100000f4900035441800300f070000107840814203030040041c002440c002c03140c400107a14865102c0070050011190414006510400104000c2800c040400c01d403010708600c0c61801e008030300c00c40c4c00c0c3e8442e2082a89024001c4100800240e2000080303200c4201c001001c000407000301e002c40c1390803214019070070606460f07501500e40c00d40f1400b07865000f030504100b2280e40c50756550010000c101d2500003031310300c0030603240e44000b030340c1c0e0100484403440c80200501901c03c407100030849118a03164015005603480c5e0301100c01683d000d025401f030400601c1c002d009141045c0c60301501540e440543c418440c2082440c1c3e17282114084252490403200d200e41d0804010250011240c3c0c40a40c0c1101c5a0100340c039082500b48050180c0c064180d9110340c00300d54807600e00e0301c0c00b62050b008512034929100001c21400c003c0300d03c1004915000c880c2020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 958827949 1250 958826699 958826711
    0xd03140f0c030d05190903140708070203120309160b030c091f0e040b030a030806101106010f260c0411091309020f040c2c0a0e0609220312 61
    0xc5142154003100c00c40350050380f100c0501c1091021145070300100c0c01001700c200301c1c1e010740b0740e0060000768040450003007084001c11040140000c1d141200c5e404da50040645907204010a51403030a030f0025152401648a50820b1075001c142c019498000d0303e03000c559203030540d950080c140c007990f0f102500c507075045554030110442906c3d80d059107110403800d40d01c5201d40ca8000e401070004990340180c4184c03080e4030045414011070b8106c1c0d00190081e0042c5e843e200550340e0790b0019600c005040707a0548140c810328000003030301800c0301c0c3e442c01521451a44004624804c1e074444e140070a42e1322040415820500c80c500e06450310b0b44c0b04503030505038951541d040c560f2110000300045058403010a02d29141d518820451419507481016100119000c110034105540010400304110460440220140f2207090800caa00803584e090480002c2801038841c0c0c41e08001c03846990300f910b4080c01000700b4404200040c11003460300e182640d204032045640f1030729480468600c2040050410410741d200 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 958829199 1250 958827949 958827967
    0x15010c2d051915290613180b0307050307123f0513030204152706060c03052b060b07030207050a0e0115021006230d03140f 54
    0x200038820003100d50062840c07490700b0b5040655450004003004103465180c50300c07002d04060101945070f52464000d4002c10a140307000f0103d20b0030304c00c040717000d0941d01809600003590302041c010004007600c081e50502040d1070790403e0690300d160303a00486515400c4800305200c1006407566812501e4000c94003024a9804820041c00c98a0f00b14130f448040c200207034801081d140b031084140c00c003443d5803500502e006441101040e140156010080c4101d0b00d0b0111440311180c60403a4a02801c040c24101e400c8000524281c4c1d150916a1540b80c0c15904000001440750300404802c0c00550b00354580c50701d40381c031700228689450f2241101105103072a0040ca4204030003588225400303427240c2458562b0303548050802a01e051066413081d803140d041d0020a110f05070320b21240c2030464000804610741da5244250503405c1c84040648044010b240050000d40050003840504179019035188003118101400184403403e0b26011010380414208007003040441c0000000300700401191140314203081100d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 958830449 1250 958829199 958829203
    0x40f08031f0b0406031d031603030b040c0c1704030201080a0207140d0201022511090903040e1608011409040b0c0f03040c050901050d2d150515010c2d05 67
    0x2d81240344100c80c0402d050107090b8151103a18040c142c0c1d084520080500c150b07446e99284244031070100c250800041040c1014003d8000b19000c0c0030040c8140700039544440e000b803c0d04281b001c2070b11240b1394024040404400b90701210182c0f0b4041e56165034035a40c0002030720180d80503400481d281c042400352240b41c0c6801f44074080d00100c49900140e170764000d041c8100800c074290349040051311000b0a00300f00050180d00003010400b0191a406010b41d60400480d0450007141e11182d01c000e241c004110301d00001405e0000009031175224401c850362504bc0302c00311103240d1141d140c1c22140040201d00031814032600c02c0d0f03001005032030803460320a02c000c203d00310b6001544c0071295082c1100d0b013481a40750400b43d00e40505015200c100b161030007521076200c14604000751410f580c2d03e081c1c01d07215040401ca00800b0458001b41f004d20b48400e06c044d0400100001c45002e18100350078003201202d584036262000301960031410a10403818481c417080203120003c00710100c800310741440c0000113903007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 958831699 1250 958830449 958830511
    0xc0c030c0d0914010c120311072607110f0a091a120d050418020912030c070b180f06070501060e100e0403090e06130608071a03040f0803 60
    0x900d005400c1c0d42a4650000e00b4051058000c2c1d40032a030741031011a01641c0c40201d803802c5c2a000300b152841d403101c00005400810484191424924000501d4024014508002440e00300308080619420440b111010010300400c48010b010010050650f42741e03103014501c800a41200404c22000c0c0f81d030321141c081c04c0310001d41540d418118003c00840ba0741c40c0400419968015000140a8200b801c080041580c441c9000c0c82d10f031031103e01c0c00d1208407091541034807600d02001d04482245000840004d41d25040007000075031500c60090040f8180b2070450950341113103403000c1c007a16415440750800c1481c0742c68441080d00901cac20311080001c03580034095000101004042c0c80c0090502c2c0c0d40082c1d00184581190710018008410b20001030781c0007003480110303048450102800d89620740058000d038001303a48044501e04200001c29540404100f99045079131403402132186442880403070b00c49010403540900540300c0c0011000206802c44025035100131070b060080c0c10281d030847c0c1d100c0803001d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 958832949 1250 958831699 958831717
    0x6180a0509070c0615120f05070305030307091e0f12020f06030c0903070e10260d08010f0501031512021302040902090906010315140102012a1b03170c0c03 68
    0x10307203e6008144515485008132450420751032607002420540b820014110000004020200034828001403203000d0201c440a55804400c0d01d0b5241844c40d40106064620b0003904509a00929401066103000007240c0844000303403100d01400d442d0000048840400c1503080e80c000d0000c402c075032400e54441005610840840c20000d440711507403000d0514144454001c210007040d034400303200000034a19004000c49954000c1c20718102041e81050010b078011484807425403140342d1880205603000b0312080d059552100c94040410340e00d0004405a8546040e032103000c4c281500107010041c1c8184200c510203001410180455200c4050130301240d00c15031003401165401310f0030f0601841c11039103560300030300c003403806102880c204040d40800d540d05100f030061201d801410081d03140d00030f400131380341e400c4ca040c4da00c44c1c40c02843d135001c02d4003405042e180f400201905139003440409802041c6541581658039414004a881e280500c00c0102a19041588100780081c080140c0c04000500d100380d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 958834199 1250 958832949 958832957
    0x17010b090903040e0f070507021005160b06010206150a03120e060412060b0406030b2a0403061e020a0206130c0308031315050c0d1a27070206010506180a050907 70
    0x43c5040c000141509020301040052017004051180c015400015242ca0540440b0015950600c1c540180d800e44102d000b0b01031a03030351410014003405800102240f0410003030b0280c1d907956135094404400300e880c4420040e07215000039414000329800e4150051203000700d0400d04071003030385040010303510b4105074001044000d220074050108071050180700fa507810281c03000d01600c1e04650b03507125040e0b0020300e405041c81000084400746d803c84c071680c1d04400705184449681d10340b03c5c02d154003e0500e4925031050514610304401c080c1200340b0031525501181c2d8040d00f89030300c0354003100030a0190310005541e130000000e404808940361000460084859031403080071140980b402d20100000c000c03100701d0007454442000b002c103810204482d5203142c00701000406175035420401e00000310113494250800800c00c91f08440843e0703c403d0300880c505e10300030b804e02c0d0396842a003248d03500001d0140542000d01401842500507025102e1192108014040c0341d685460704040b943c5c19034200c45500c001 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 958835449 1250 958834199 958834207
    0x1b0711031617071e0603020306040b09090f010522031b05030f0301090b01020f0d180305060408031b07110108040203011b030b0f0105040302030318030a0c090902010e090f0117010b090903 82
    0xd030301c04000b00d0f0300030b105443c1a200c0c030101c022100d203400040ca114010915400000207403031a9140d5100f074101107002401c1d40c400e4100120030a5544080100801040d840c05011540d0000c90b1003110070083d9103005659024001507404845071201072003488000c020140e19000000c10a00160803200c03203c42c000c6071a5031411460409651060301c0a80c15500001522052240c0119070400800340d2401c0c00480071004010700916001c469101614034000d0b4804d020400200c0d80040d40540d01c400388402e4007443c0c45000c40f00600c22007034018441c10814040500c10350140c00c1e03040e403290004000007001ea5201075490400010f00d010b1100195a900300d4203103514090707540390504582031030315031b05250465002c26901d01c00c42c0643d1003040d164841018581d582040352140d1168000b41c24141c0c15030740d0f840000034107110007081740070404038942c6c944641426070099200b01e95411588078036034a4096003031a40040094444850b548405142c0d4543e2610a1954000c02c8400002c55503 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 958836699 1250 958835449 958835489
    0x813300503040819020a1707140102070306020d021905030f0403030504060908071a18030f030a06080f010b1305090a0303050604060f120203060f070206010329070c02091b07110316 79
    0xb1494a41041d01b009450364061101f40c0070004041050b0b6514403050199550b01c0070050340390480c9540002d11080c000110350b5092207a0350040c084081002c1a00b141e80141d82000340c40358042140d58440200440001a010901c0f9070030240c0c0141c000c14000950003410344542c041035010b01800d0b00c00710390071900400889180c8400ba580511070300120366906031039800c81501d03031180103c1e220004030040040b03040b0020641c42040106014800c6a11345a0100d02840c041c0003150302041c880c2004a01420481c5480d00442e803242c441c3c10054102d944995a007a0001c090190115802a42e0707228041807a1140c00501c0340030349a10602034100346030320f04c10149011002404001804802010f0043c8241c0014045041d039902c07203006000c0f0745225030b6495001011802d4600891460360910041c503421840d02c510b21802a61600c0040c1e9400c070382d07012452889003084a182c03c04101c09030100340300c2c00c00e01c1e021034001000d507040806180040d02d2880310302d80011003440000041920 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 958837949 1250 958836699 958836709
    0x30041a13060806060901200106230a060f030c0309080a09081903021e100f1d010603050304050f060405370e0a0c0219081330050304081902 61
    0x2401c0619001c01a031500d000851401c0c000c202400303061084808811243c48404400c03241810001c400030498075a44080200740301c0420803400c1d4520018801192141c14201541400e590381034450010020503202c2c100c2c02031140c01d2a0104242d542d10a150000f5203c2c0000c040840c1d2940d2000404c608120580d4200014144e10040e10005418044006038012031503c1141001003604101142e018040718205002782003c009401d1030030055070014481940301d120b29401d201d106c0c044220f9180307181400c8590900001e4600d80c0288010407140c41c14600c2040c41035405000b00b801d080d95040411011141d010b00185041301144212716040114140ca182d0040c00c6103c0445c502d01e000c4503250041009801c401d04030b6252858070f034507607008000040044510b0700050492646d02d05151420b038000d001501c00e41100104005150044159030350fa80c1075a4240c0c040016283e8410004c00010140003100c69000c103110004800c601441b0f1106805a80307443c2800080d40c40c41002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 958839199 1250 958837949 958837987
    0x130b01120b030a060b030f060901060321080c0904020c070b03070e100c03051b0f0f06070504080c1c0b07030e060703021219150306090606050330041a 66
    0x1100d40d0300e40116214150382c0000c804107010f82000d00025881e80c8a00403074244500345030100700e644900700a1050580b0151700c80030407a40076000e604941c441602000100007045045600040c0500021030a40c1440000615207000b00400c018505910420034908280d0359600c0b0414000c0040100034002e0f400410b2030700288000c5a04c00504000c121020704154548203000e410458081281411005a60402d4512500c240d046415a48140d401c00341c1c0c07000e0b08800c580311402010003080c5954000c5d4152810f030b07812800a4003410b102e000a20148a00003400104030603107a000c1c03c00400d01d01d00d40907008502036034000c0703500000b1a848524101004e0181302c200b5104010310204411b881d108c50790424854100769201114215500c1c01411003004c0300a59462448030010401003a940300c0918107100d00424000281c0c1c42007090788401d10011101a0001d0032800c420740c07001811084803408016010300c605054440c151540c0d14001d1000f0341004081c002642810046608120 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 958840449 1250 958839199 958839227
    0x100207050d24230c0412080a030f0506030a020f06040f1e0b0a090302040504050a061e050f060603161206031101020c040c120e071806061409031c0509130b01 69
    0x500070101d01030303a0454141141260201c112003244045a0b40c80c0b11302c800c8030b005205600480b03440c10118140000709502c620301200102c0d00d022400d802640d0b85020700d62003004010702400206440780c0034040d0b07260030748401650101041002003070b02407e00381c0c842c02620f480710010b0040c07508020980c0350300015800c0004000c0013448002010790340941c2503400e60340c2c1914007207800c0c0c8442c07038a58500065080b00034015414041d000304100020400301d10314014a01c010b001ca625001015a0164410748a090700148104005051080ba11503c1200c1e1440c91400d609505050a0041e040310900d0300700f103030f2000340c0d0401c0c5021580e04000350280c0ca48100e03030400540003d0000503000e6a10111a11842902d4108185000074140140401401c10443c10417059100040703420041a40f4000c0001088100b84a11007141d4507400b81d40b0321480240080c034400000b5980c0d4000d11001c0d03c04401003050410802c10036480c0e13504504440c005da510045441450748002603d14080d255207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 958841699 1250 958840449 958840451
    0xc020f010608030d111303030327050601030b0402190303020a02090a020a021c0903050109060e0f03030f060f04090218071b020607060903090f0f06120218100207050d24 74
    0x206000b0188080200d850351215000002030000400454151034000c0750050041d100104100000b8550141c0150090200c5c80041c0d681d0314080070082007500b00401c80191443e40b01000600009001e04907443e04180001c0c84841031b01040c00305038881c40441e410840040c0c01481c8414214240340c003005401280180003541017982515009544440d0601c10300f94840201c0780a621081c003070040c1d640599007042c024041c00c1e01c2803c121018084400c61458188071350190380c95840c0c004001e0321700030801041200da09844500810403c1d061380c01c0c1107603115640b040c20380d00503519030f141d0003217248075001803511502d0b184002501c011000d9001d0f02c010f02400c480d0900507a00c25044518965004c0030001d02c165142c01c0c1103a031032095800481288045040c040795031034002c010441220b1095913842e101e00452010760302a0300900810340824030382c101c0c00d000146080c4603002d98030180c0b0310445a1469680c0000340081982120a54280e1000060010700715100d0021a000c070b00c00c664 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 958842949 1250 958841699 958841711
    0x3061d030d0605100f0e102618060103020604090e03090409060e0c0a12020607051603080c06090a150c0c020324061c03050f0910050a0e0a08070506090f130c020f01 72
    0xc07010b00040e8161203031a00c076003103220445910a010b52380d1048000c405002140c3c4d08002802e68003c181d1050341e8501c2d4040c08091340c400d58140020302c60b41642d901625940c00d242c0b030003c2d03000c0906206498188503000500140c90240c0b1035200c1c881c500ea0050101003924050291442d041c40071002c0502c2c015411031342c060004501d200301c0240b81d564140d07141a0760b03035450304005040c441c0c002c10385445c032044c1d4903002061010a00c05400d1380080799007a5607090316086107041d90381c07884180003011031888008180004e070036584182c1a102807401c0c0780d60010f50990002e82841d240e4400f0000d407501e901c414844016070311f004554000c0e03041d5a0350f002c400c0031300d007125400c03500d010004040000004241402c80840380031789a410001421180d0016050741d0040c0c01074200c010b0440000d803028190f203400785040d508150032110b000014141441c201014400680d01c0b000b26150890560b950100f10b51b22004c6c07031080d0840701c031074000a00555040c4000d00700030080d11000f03c140c1c1004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 958844199 1250 958842949 958842977
    0x27060b09040b0135070810020406120b0402070f150c050717130e0703020d05090d0e101b050106031e0503040519080a061b02120403061d030d060510 65
    0x12402d107042d52016440443e5035020300c501202081c0f4001110b00c003c280d011126820f560001408009540020040e43e0422000e18085400c0f03014074860314000039014030700d040440150b40e01040c0b6214000e4005450010740d619403101140a4001c03c07100300c81e900d803425854842d40e01c5418401802e52501615000311030310741100d0141c01090000303400740c1c0000c446150b120280c5031040204031079007403444d0701d1800400150080d048540a000741a041c0340010b00203e00120702460644a25162101d41e01c0c441c206102d203e60706141000140a500c125840541030943c441d440740522500000c1600e6056150100c4104204c80800151341d8107140d48000040000c41520140d51041e650343d480d90f0311080006840d40c01c01c3d400400316014480380e00092011a40040750800310740ca10b0f154210b549440b0480c0e44043e00c03014a044124144400c0c400500580c0010000700410243d49a2403851440383d1819544113886100a40b035907030b2020025800c2c1149a001c401c001403d05000c0070b1500 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 958845449 1250 958844199 958844213
    0xc06040206090d0b0f16030e0a03080702030c0102070f1203061802130510170c0c1e07080d080901290f150d0b0906090714070627060b0904 61
    0x15200910072500410b030781100381c407804104051150000c41068103410310180800c512007094031603440b0549010408030045002c1e0060b50100c0041c0f90007050046003a8900b241c408038007415040460004102d94041c0800034000b402c4280d0040e240d00c1d00300b070307218608040c04030405510036044c18101402009400c0c18400200304c0ca42002402603034549062401e05130034071964022542c8135403441003141d0080d81c082c7c3d04d90b440308200b1154a8031a11050f40c44002c0d80201031401050b907110400d8080c064406c1c0c2c807a450346000e00c0089940b03480d11848010b040c0070100d080140002c04220402c01640024021107a650b106a4082040c0c9580900d00b400d603014400c51560180c290b00665242d5526010b004600031614a6401902c0d12981030004010781104ca41c100e1140c0c0c8103001180c0da40c9001c1d401d940c002c80041e01c60102c4501d560484850541082009035105552040c4c450b4140c07003002410b0601d00c2c0c503080801c030b884a45140200842e0000003006010700c100b0010000051301c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 958846699 1250 958845449 958845451
    0x7021e12030c0c010207020d03080609070806060d180f030512010e0106051803160321050c06040210140d060e130210210f05060f100813081b070303020c060c06 70
    0x242c034001c10342d210b42880160f030280c0b040c050001d411010704101182455801108540a17480c00c0769000515141d6081c129a01c080c1901c905501c0b035400c018229210b10f0641c0008040300f5078a2080306000c42c1521258824501c0403001e0340803500001d041b01c024040c042c10140500f402c0c0403018225414960024507600818000034030742c4d628034854024584d410043d01c80c94000320003000740c002c0c0c1c036490607080d4682c0403a0b600d02900400d0540d0048035000703406541c0358031400b400500c4240e40302d4080144410440700c4840510181400740c1d03540d4500d160003818403144c400001700e89686010805510108001c02d014800034104000400590b103029403400040c07000d20b800d951228071401e060b001c0082c4088a054441d24008a094809206401851080c8400c8138294003840c1e850080c04a103241d80c045c008005048000041c582da1039020040c514540103017078203411b0202d11034141644c06250340711200340f544419410020198100301155005409a42c01400e0000880480d650740f40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 958847949 1250 958846699 958846711
    0xf03010b04060e063127030e0f0105120a0903050403050d0c020a050a030f030f0e03070906050a05060f0f160c170607030c090e0c090306240411091c0b07021e1203 71
    0x6d224100100c0703218070501d504102013141c420041c03214403d8540039080b0400a84ca650082e003422042094075805031050303c080300303000850740c54550744003d070301801032061100032401d02c1424000400402c2080248115000064840440c04021030041004441c0a680450b00ca0025088180300255032070140da441c440c0e040c10320f07801041080f07a050300c1c1c04903030b244c45940510541c0c00c00501d00026802032012204c5c1990042100c0f43c40d4014012640f050010038004c51100704401c0d80505858002171055400320118840000c11a988054a14056500021a42c0c4000f11004402d1100340101d0340c0040031070400304550282035070302402c2000b980c41940150b01145000612480c00307902200c02e4003100400740d41c0d091a141400311034a00070104004804880520f54a5050400d0321412800146201c0d0450626405908204040c005030030301d05105040c801080780018085804540910b240380c02500c2400c0d4460041b071003c00c0407080c414100d500808400040381254000c880d0804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 958849199 1250 958847949 958847951
    0x180915020a110f0d031505030304121a0c042310181e151b060504140d030b030c09060a05060f0c030309100f020c07050f03010b04060e0631 61
    0x1520001600e00d11145084440180128850440f04a0003c40c990380c02408945003081418012a5400c0990115005103a00769204000078025441554051030490348105000e00c00c01c8070344180c00080e96010f03505201600004542400465803140382d0310308000c1044100151540b1410000301030611041258062002d411411812988450f9100001d8800f40a40869444000359428072004480c030404800d41d0b050042d071101503108402000d0750650450042e00c20400588038000100380150007101d101d01c2000140740b03190300910000003c406551000680c144810b0f0500d410140c0040c0c240c1d02c00d03045c180c00c229080d035524201c941610402e840b040d0701c0f0b0001c103030b280880340f045101d0413403e844003000704880b40000152111b04049146028450740312044c94201c242d0103034905140261300103100c1440380341030a900155010f14000e0012590102041c0818210f03901900015010b0042204000e0941401a409001846040a00c4000003001101220b1202d9a070014140076 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 958850449 1250 958849199 958849207
    0x201080109090f02240c0a0605060102030c0615120f060f070320030711061303090504020301152d0806181303032c0c030609010204060c02010c020d060606050418091502 74
    0x34040c100c06101405c00459030b036440510b488240e548500c954000c440b001c1c1810300051555101005a514015401004081a40700c0070084003840031440c04c400c3d044012440f400c51ba45c4000c00141d0660803045005e0921405c0c9070b8101d0680001c01070401c000c1c90304010401c4140c1070180046102855a40d100e02e40301e4803a10401c0311000010014480688504804e05c03641100d02415040000d00c00c1c1c5405e00055500c100780b000340d0000b4890a0b45010700c0c1c140e0365400300e000d0300d160303100c00020381011007140c106503180c0300104980d200140000b401301001c005250602880c9524940c00c01079804200340b4204d17200c03401c00b00d03c000c00103041540700c0e040c1d410f480184020960400048105109026500302c1d5617a82c1c3e400d184041034882c0c8688404503229a20610840c2c00381d0704650740d10f294903051600159508046007000300e801c80304a0b81d04201046442c415000903000c0e0750b40d481c4e981d51503c0081a5001079a03020495668645501032000411000480120700c106020161312 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 958851699 1250 958850449 958850479
    0x11403120304050a0c0b0309010b04110702240a02010606021902030c010c1104020315010201050f0f0c0903070819021509241b060a240522090f0201080109090f02 71
    0xc151104e80000d000300d0700128040384403201c1030051485020a64000c01008491000704004c0e11800645004501c4c0200074030005420a2100124401c01402e503803a28003464207411070b074643c4440580e0b40145d42d904003d0040a074140135800200200381108100e42d01d480d00000c2d103c078500c066641c1800707104c87e0840704000740644121039041004004645074079044803483c13421420b45030791074019460800016601030100c0851406194600d0555040c1e6a441503030200c681c0c854500d86506100c1d4040019504104001c0c651031100d0103091801c2c0c440d8540f05222800c1c0c0000400c0309500c109000701340c05511506828190301642016044526141513142021031040e500c1802d016541d00c000b52000c1e01e0300251a5004214604c0100100512000154402c007200e0406007581080100c00b005945004c000c41e05000d000d042841d0003e11080c1094000c68092150440d40340b00000e11307481c00c3d9030b0081318150040c00b0f101001e00445140742c1e942c12070300140401c000d206d01c400100c0d0a007 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 958852949 1250 958851699 958851703
    0x1107020d03350a021b030a0201060906171b19032001080c0a1803020d0f03090504090b0a020c010608060711100b0913030905030706030f0605060a0813111003021201140312030405 78
    0x642c2c14070304011b5030366404031010028041c1c5079901449180328141200012a03034907070b04c683c0c0d203001900d038054442012403040b10010420020754a41e0300620080310800c90035a0080058000d504c1114060b03125005c3c100c0c40010b840f1195100303030600072460b00300410007080c072040f1411001c01d0320701156000e6a6401c0d8801c010305076003029402011075180b007800c00c070700e50740000030444c0252504001e0640c0d410420054505089004008040c0c082c0464400030040d006042070030304a0002244d01c80c1c48034615440e042003101c010000828a0a0803103042c0c030140500c414420310380c0b00031b1100704002c2c1c002ca000c1100c003404981040200b40801024580704144400141c2002402d42c0c80e10380c1e0b112801005003219241450942d4540500018945420004c640c03142c481a00c0360a0301d40e5801c0261203000d400060300307403005001d442c0250195074415103c91092000394a0040e25030401e008c102190401c1600101700810244600300355030f503000103941c2c0003c03407448016030b0343e81d0300d40c1740c058 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 958854199 1250 958852949 958852987
    0x70305040221030318010e030706020d020708030907031502120103110301060816180507080606130e0f04030201140c1e0d060b25030c061107020d03350a02 68
    0xc078200b01c0103003039900c00081c0400154000c2c41c2004c40311110740d600020f210b00b251824800c1c0d9103503601c100b2481000800640140c00140b540b2000103040c682d503a141c088084c1c0c011103480300560003c50051040110320f01c10b040c00640010341c110b0502120000341c8901030418040508420072148144280344d0f0250414400b0b40b002c0000d4841810720314190343e1100580d4086c91425803110349200f282d186191003034511038046641c0342c607001c0e15144207001d01d0758054008070585c014150400b190f1100c03440c42845c0035103412401340030513207061f090082c00c488844440d04020004042400020110401034412900004407100e8054120303040040042c400c00712003d6910341031200014000e40318002903ca04546c05048000072102c03900c08620400708510000c011404800c0d900d004111240c1c003101508003901c0c2c1d030074a000440d8001860b41c01126038110005003481c0c130a4100442d41c4803031a100341c5400042d09204400c19000002601c40080000c0c032543e42c0844c02500c220903654002c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 958855449 1250 958854199 958854229
    0x71205030a200f0c10050711061605070e071b050709020f0d0e0304091112010b070305041214160b03040f0c030c0f03030f05190e030102041a0d06120b0703050402 71
    0x3c0b241442034900d050f03240e090030546640301e00d00000101c000c5d01d003d0000c80d000300c0d070300042da80d502d401ca90041220729046825185000d803880300c500e0340011010008a006002c06000c4460303a41340103800140218075640852040c80b44840d0403030300146000031071341c0070344003031010168440c0da4480301d0640c0c1d0f0041c100483d000700c4c104141d0000450000c00100142c400c04c480038006451070410b56101880340b01c01d160b08140d4280010800c00741c481001e0000320340320380342207454142ea030084001100d00343c01e000d403051521882c1e00c2d0a09203040040410440f40741c1c08030b2800b04d01e05410305180340401080908200a40300798030080298402401015546c00014481c4003030300d8001070100e81000707000071008070702d282a5044040d40540d05a41450744e0480e80301c00c903e0162a81200c020505041e825090f6400b40008207410001001c00c202c1040d6a4111945070804440900240c580030303131200d1700e0f01300b1a00c0d00341c000c50200300400354000c0ca00d043c0850b13140c0752880400c0929103c0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 958856699 1250 958855449 958855453
    0xc0e030d030f0e0a0606170c0109180603061103060a0e090c0402030c07050d0206070e040b0603011215110a031104060e060c030c010203070806090f0105370801050603071205030a20 79
    0x40c0b01d0401045600502c15100c007448081505900c048406a231401940705150204400c0513003008000e00007005076a020342c01081c0400c5031660313030381c4583c15100280100130a00d1070201c200102810708018600080c07461014251042c104101c40c5516442100445c80c0101d40000c005003a40010310121521207a06c00101ca50070500224003e407075080545000d80058400205490329143c41d0051000f4a04018003c034556407a013400e20901000600040310000704415038810860b86502c229400c004a00340c0c0720341e40b000d1ba1790000301110360f4850058881d01d020b0209000e000d0f0720000900f140c2400b038403040da0341c0c02c01c400e0f01459402420840f0340306600007c10000d44c980d100c80c405000c1c1e9410340300c24202d515031055020f0114800d02509812000c08a050395110300046280342071a2410502890880104403114107081d201e1b4100d590103030b44800500629003001c01913800140300c0314400d1004504140c0d103598492050089e20350810000411032460101e2140800c0010007404007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 958857949 1250 958856699 958856713
    0x80301050d110901060f09080102091e041b180e13020f01050d020a0e100201020a021c030612051506090403090905060a050d0f0b0a0c021011160b01090c0e030d030f0e 73
    0x20246c0d0000044840000c840c0341c0300144901c014020340b102041c0050000711041c4070788039259298a000300c1002d601940707030208081c0111210010295030b031401d5442080000c001d892103a80302c0761903032148951150150802007011003162090041c2c076412500c90380b040714028012034003409150100c5417180c1c40080d000c241c3c40d41150b0502600b91059901c1c01300c401d003e100690813070180c000340c140503030440c60b41c8eaa880340300544003403040030b810b04001031565202e40c0c000c210540840f0f81241c1a0380800010440110300c06c05070765010380d086550001a03d45030b60b0040522085104886000e031700d640c0401d01e582c0e1191004c4010349800b1f040011741ca010340c00c00c2d840c41d540c10034003643c10182403000304501d0b0740d05008850600035990018254003140020407801050000c901400c500410301100c205a41d500b0390070b10f403844c0101210701c8154142010001107464002c0c0540a11082d00e1402803039031030201d24403110030418140040c0b600301a80a040140c11244843c9600d07000d0b41c0703 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 958859199 1250 958857949 958857959
    0x61e0f06040b0f19091404050429060a120c0b180d12081506070b0406020c03070c03120c03090b0c070803040803180d0b0414010f050a05061903080301050d110901 71
    0xf40a0040344082030100020048030301d40955400760140541c04226085d03505951050405070443c90b00b240c81101c81b1014001c1c807004800041091600e00390380f403c1a072003840a00d140141115015041031200184904c0c81603591000c03034501485107501080c0d001c200d00c8118051051254039204015141c131542045901c1e14405803210302d4a407202141c0010081069003809108946000d04081e150a00e0061113880301d9001d0800144101d446c0c82d001c20042010f410284064401d045c03160210707160450951501c1012150310007054020001029514000309500c451402c0c00c40b0100c00d902c42e03071074004070003071410030249400c02c1b80305210000b000541c11800000130034804000020710380300590440c04008190800c0c90024008030804000700d4085100c04583e100c980221600014100400005000a0350011240e19407000d580e1000c001507420f101080ca04039000310040c0c428614151750f00c2d4001d81c0418000c1a01500701d0a501c0c001f0007034a02d01d200c100c2c060003003a82510b50ba6032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 958860449 1250 958859199 958859227
    0x180b0a2402072105061e0a020906071a0405060c0306150901020c2206061b17120c07120c0b1b09090406020a030b1801060315090207120206061e0f06040b 67
    0x580d0b0200c4c0c1c3c9110b25800503100390b981200c1c4c2c504198800c00c2854180e11800c00f608080d4010a8040fa4004000c020801c0000c041c04c4080d0030b0700c00503500700e041525250901604000c8010070310003000000f00200704aa41c1d855141c1e0400b0140c2d5188103490b2411540100d18184a90340000d40007048030000740001c00100c0d42d48000d0a00360081840556150842240c1320a60144050500280647c6420010340400300c0210140c0c0002000c07410702006401c2807050180c1500c1c8407021000020f2040148040f8083d403489000240c28803017030100c00741c1e031031001030f640052411400c85e200c248885690f002240440b58203800040000740181482d04015000350300041c000e001282c5003031784c003070910f05110241200f0400c601c90f040c80ca5030310302001500035000781c034502100d04207540400314070030540e440903025103402840c1402842002c1c0502924090018200314411a001d200702c44c0703080110b00701c054810740c068440402d40600032022450b940a680c210b8030300d00300d0201c0c41c403602400b4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 958861699 1250 958860449 958860509
    0x1003051b040c03141602121b1501060e0f0301062d0e01030f1506050d060c0806060301050607060e012325090b130b0301180b0a240207 59
    0x45404000c42029200260700721100d40514032011007440c4d0004603040041001d0300d1552042d80195a036060b4940212142c0b81d00010740c4998000d80304815180d400f0007001500001c44018402008a504000340540070085100340755101d18400311002015450a40051004028005054941c2840c0306031040f4240388007907e65101100000f00001d80e50540800c1504a9401c4207591040e5070f02d80d2580c01c08044444981d0300c1c0103031909400503013521081c42c800e11481c00f441001440c8142c8c03400c0100784450140c200c5200740400d00040c80300d950b41800315142d060b4000400500d413205100240c2c0540240c0e0005070110203081100c00500e609054000e220304013002605d80c5052904c401000c80c1101110440c0001710340130800d00526844400804041403901c06081141c0d54030000684c090b4001d0b00581201c0d070840701241c1d61845180030704081c40718100c8003182694204140a108049543c82d94141001d0540b80100094001e01c03144014102c5148082c1200442400c0ca01c00e10305 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 958862949 1250 958861699 958861753
    0x1503100203132609120109020a030b1e0403050f0a032405010f030e0712110306090d020d05040506091c050a0503041403030c0d080705040806011203030606021504020108100305 77
    0x210411071a000b144400f4010301c5074aa0482c1012682e0342072040525603186900100d640e1179030b403500980c2d00c41101200039071041d040144c1c02d24080440e00c55a001c1c910362503042c003847d8001c0c0030010f0b400405580c190b5054070b44141e01e0311003410044000c1c01210b00e80300c01481c0440103401c520240da02171001980c0082e2526141181c1d1800220700300c5c0d41c0c40c000c0079800e4102031414001900c000101c3e0041c1405040d4070b501d28044280001d0414100303680d9403e260388003ea0850350540c040c000c240048240c1d04003a400c003868500860118031903051081e1007110382d41c80304002c441010031154106034020085400380c00b00361030320750303a69807050040d2115070080103402c00f07041c900002103410382a4540b018140d0080300c42030540e01002c01408140c02e00006000202e9200400c00985000f44190010f200c2222400e04000d400c9440e550402c1e03003113400c101170600c0d150b01c0741001c590f00540d084c40c100300d2599542d0705d6007604c40c802e500010414051841d600c02082004120a62a58 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 958864199 1250 958862949 958862963
    0x5060f1e130b250804151808150c030a1b050a03150b0a080405030903010903020105043f2c010e0301290a0512060a050901060e150310020313 62
    0x41c0c0390300b0300b1403940c000c0301d40c400d40752a5400c443c0760100706805003c41680d48282d0103c2d040580f150400f8181c003107090900e13030000300300c07140e04501c04171588040c40c002c00300403014040c005002d06076141510030003007048102d034000002142551482d80c0c8030301500d0038005501d180702c81c3c2c100c800400c0d03036001c807aa440000741803074810003054001d55001c104407403440d02c003989811002c200650760303c0f1000340195124001071100d0300c0307540c42c20701840724003920a03800054140303850314049541000700d000c80102c15141c201c09503960300712071078680c4000c468841102000100c13054211842c60801e28400d110211181e545541c2e10750301d45001801103000d0301d52141d1810414281030072030f01c180c42c0c10030311740310500d00b40000d1450031000314641210140c182071010f40c455000c54080f40604401002540c48407040042d050010300c502500001780400030300c0201c2c506415030003420405001920700d034201c0c9603030008560f000c0000080c4041c1043d010340d20303483c003601030f20801c0703200940036940a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 958865449 1250 958864199 958864237
    0x110a020d050303072a030c02030111030c1b060606090111031c0f1d1f09060c0503040318050a0b030c070b0a0b04060e06030303040609050f032205010e01020705060f1e 73
    0x5c1a1a052500248000301010801c002901e44003101d03001c1d108441a60155610303003200580440c49001980b00e00c01807074450380e503604070703c2004030310404003035091406401060034440e01c0e46d13414048400d03003e401d01c1d00400d1a00c409640c1130451183c00002c0440120032014440480c14030b410413001c1525440c400c0208a03900c0c46d0516510102407040202d0f81c011030341c01c03c400e45115200da0b0040c00002e400050002c450350701d5200325074040c014140818400700030001059070040301080c00c2210401600b9106140c100440c24190036070150000c4004040001204d15800b44243c6201c01d40280c003c0c042d90500c42c1c02c1c003008014602ca02030241d41801004600c004441250328040c1c10081c00541c695038075511581d009000184080702c0301d00811810043c411400c10280031003007140002106080120701e8a0b905d281c0d035a51000341030019642d100002680c022800804480064840a40c0d5112087c0d40d00040d205504c180401100c4010281e100508000c01502c40207582034451401c0b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 958866699 1250 958865449 958865477
    0x1b030507170106030c211a011103090f040209030d0c0507120506130201030e071419060f0804060b030d020303060a090b06041509090f0509070e0105060a110a020d05030307 75
    0x541c031002540c1c84031824001000010b00ca40d200c1c44080c00b452502c1c860a0300c00340000c1020811142d4000509611a581008484074080d00c0310141c8000b401c3c42240c244008000c140c0f00d008003d0500c0c41101280d150102645460701140c40d030807001000d03104980003108001d051004d80d008180d82600c21100080350712040d102e08128501d0f04480180829580e4048145140541640480c10540c9039511301c50101b00800c0124003810a034200c070100110180c0602076541c2da000c0b002100000300301c0c2c041000c250898a000a00016440c2500c12940e95040160107481001c900303903054405c110554460340d60210144d40110701c202c50031414070340c1d03c1c240300c401e4070101d2100d0fa0707000600700020442d200481c0040404102c1c43d08240580c075a84002e600100c0c0c3e04a43c65a203800d4486007003141804d810f10215002e000f14010a0440d941081c1c089099402004280e5080c00201c40c0c07030410170034040201d070820b44d500402c2000800424906242c49810980369000490007004c0705150b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 958867949 1250 958866699 958866707
    0x702160806191e09080702060a050c1603020d300c1e38010b03040326010b09041b02011b03090b37020a020d020a0b18101b030507 57
    0x42142c5403002c0e032090004203041804000c0204580444150f43c08120706d10043c0c40780405001c0303007015500c415172941c2e00e50003440d0034151440d81500d00000b00000078070042e0744524a1a080c0c581062a5441031440b4512140301e908641e41095984103a00410b118110b03400304139104e81d6480744081081410402e911001c0c07a900d000c900406485280340100c07140c1c8407501d065580036190749190382051107a04c1c55125502d40a0b0008070200300000100018950840180039092941c1d901d600c807521101483c1d00d0181506000c0d400c00a00d0000b1001d465070f807590020801820014885410029180000303402084c0313412203100d181c1c0b420140a400140284541400c86411a19170112607880c14110007080c1d441003904c1590082d000309203035000711441c00000d0b0782c00c404200140d0701c0c03c02c0c0c5806490310100201d00021175011225410000d01042003450700000800d881511141f80307500050305180441d9002103d032441c01c2440020011060640d941c03880103910100415150305074122 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 958869199 1250 958867949 958867961
    0x12d03110f0609030d0318061a01111c180305070b04090e0a03020a0312230117010e07170a05060c040905130b0601080601110f0304170106050a030b070216080619 71
    0x994150003040301529203038000d400480340c0100e04080c2c81e481407001d544d01c80c03c450494400b270b0f1400d030b000d00d9402c0e02541c1150100e04d0043c800c0d40100300640703030525804045650710140300200200078280030060317401c00b06060f0142d5842030548460540300d03901850380307402a00c10070b80d01c141403a40041d910302000c20b5296900c0e4155029114018140e14160742880070388812066140d902c038105200c43c0b00711080241c89600c1c1c216443c20a500d03010600e01001c45d886070000050340341100d10224408001524030403540d22281901001c100c0c1c50025007802c583c000301030081c0c0240d20400039962001d20003401503c003c60000c0150382c031880c1550002c10114072000705484942d074041520303903000c0c03050380758031580503d40891312a1440c001181041e072040391b1605507600200c0c0a00a5100030071400d010405078100803c09540b030540000d2908110b4031014008400800c089003007507209210404140c003c0c490b01d0804565a0060b6a40d200e000700d5105400c500c1c04000d00b000e92070280030310 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 958870449 1250 958869199 958869217
    0xa1109060a18020315120a02090a0b0a05150c03190f0905060d18081c051b0403080f0d05190c0e010e060a03140a1d15012d03110f06 58
    0x305902c807081d0450b00002c1d480604003d200740f00e400c13a5603110359910750b942910b503000c00000c7e007445509441440808032000c0d241400880c1020302d00c6882e61107407481e01c42190401c48102c019400c1700e40002e0700314403d0309803500f40382c00009501c00d02ca080102005c02400c00d5039a5080c013038042d8180c129190001405082c0c0d011404000c42c81d03031004280c01607103102443c0b40c0000900e20059031114542c1d44008200140080210b40c41043c05480b84034291740240d5105000b24030b0f882d03501c1d0f0030107184039a001c01892288042130491180b2440000e58500f60000d150400003403c10204442144408070107401c0b0742810010300f003030083c1c41810800076402041c1c41b0070380c0b0701240350b0030001e00c1e80011901004041e03440e00020598201e8601e4203000701901000041d203428240d501d03039404800c1c00c3d0201c02550104904404843c00d05102904449403502d5209501810300041c03d240b241d418484000f0f05990400841404075102500110407411210b841c4400603e5041c051030740111080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 958871699 1250 958870449 958870469
    0x90809310e060a0b060910030b0a09050405070b1c1a0a15020a03050d0f150e0f011a0304031b060c0e030111120a150e061804081e04080a1109060a 64
    0xb00f0b0940025410450081400800490134101040301040e15260030b0502c410010340c0b203242c049030a080c0500254080c0003000c80c103001d1031405482e810f988100512481040340302c0050013003a0909050036040e0203144c0000140b00500762040c4c540319070018514807d124481c2c0d00703000640212110b1242c282c184041d000303030544200507101903d8940190418030010b68039005054500d0046110f5000d040c9505207145640509000400d002514020700c4008081100401403000003010900104144c552081082e5242d50758075048440d51008007440310604e01d44480c0d0f00401585030403010748003200760703501140c60030000101070030703200b807041c0700b09070000108010212192003020240e07000c00d14480118400b01f0300d84840408075400c0c0d00040760387e00c2c000107100461400c225100e030540b280c05800d030340303d043c9911494141c0c40340350309518051840c0c282d03c10355240c0440c1994000d08060b020354600765002d003807406404c8101c4900e144501032410008285284c404144001e995503090 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 958872949 1250 958871699 958871701
    0xe0a0602150612010606081005030a15050910020a0c1209140105030a0b031606090b0909011205100203091506060a02060f07020a0f0c1404050105090a090809310e06 72
    0xe010300c1c401005003465410403428000303050401402d00400004041d25556040240b82c9400032002c1c54103260401c4c0d104c0d07001a070050000c0345400c0d0110a0490321100000740320f840790242985840e6488100c803031040d0020420300d80258102c40070320b4200d40030380240040000034100841e82d986150050b078900c0e91091098000952041001d55400020301000180c1070b0002000249081d2130180407104008405000788603869000307401200410a00d0440c0e41056900e00026140d80c03c14015000c0f440790115095003404070400c6076800c8042c40900442d50780c2409030950342c90303c2c000c1c42002c900040d480d0101c2d040c0e041c040201c69200450b5030142079a900d8820842112507009040201140704100c10000031680080d40c240c010b6125044007005180f41c08511260040140a041d10452410b0010415925084000b0386e00c24400b49000070100c20a01d0110424000c04e00001e810580c0500c100c40644880035120b140420744c0301c502004210803040c0030083d03c810104901c0e058124030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 958874199 1250 958872949 958872973
    0xe0d050a030f060f1703090405040b1b03060f012601031506050f0906010305130c0803031602010504030c0303020c1509030306210304030b040c0801091a150f060306010e0a03050a030e0a0602 83
    0x1800c0c2c0041403240d00561f464402c081002070290b800564060380d500350b5035824010500501c10420658103800510036055141050004600368084003115050000d415010400142242c070b0b030031b5081850441e02c00044d40c480c1030403691521281d515241040c40c0110100300c6151150340080c012100412084071907949000450240801900c010307140b894026041000400000800700a4480c4d00000d54482c44d00105403040341e00c0e80010300042da40350030188808603a1001d50303807a170f164150070056a199038102101e49003800000243700001003107420300c490008040001c5000c1e28080340e80c21811814030703101c01c0c00302c003a22030b0403001a40100000c10000d1407180713450354404d0085c006001c160383e03a200000d0941d08440405c444184a24081c00511380f039140c0c0194000b070000ba44400085040c20104041341c064400d154824140840041d1f0700f42e1080445a07860140a42845120f81d83d91806940d6440501d60490206000c0c3c18100094209141c00900703c0e50361f0350003406401980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 958875449 1250 958874199 958874219
    0x10091707060608030d0b10080903162a03120e13050a11073906110f0d0203030403031a09010501030b040e0d020a1a15130e0d050a030f060f 61
    0x510800c07036103552035903400100f9180600140c000b0004104020456003003140405c20028007103001c560500c4801c506210303048030000169030080ca548806081103010b42d0400d110f020b0301e440482c481c4c0110300c2175800d002110481c42c540c1102d12070520b940300020700f604251410640b004903150800c5640101440100140e0800c40d0800b40230f14000480646003100c0803810380c000a41036902030111400c445181c000c400080b0102e495164280c4e042641415150b56040014032401e02082190304040e141e90400f84444140c1c9402c580844056000c4201c0181d181d070821907054002c285800c280004201c0411216080c0304070080290715107038240b5006400034113240c11102d811540d1110b0074200300300c08011210418503160000c120850883c90103072108200264550465041d007000c1c80315152001c1152611054220b42600c02c007003240b010000244111848400d05104628160400f15002001800040129075042c4800c540b100c0301601a00c0461141700e804400714803080000e0061 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 958876699 1250 958875449 958875457
    0x30108060415060807060806030d0207051309110d03080103120309050c120a1b05030d0215040f02030a15020a090b09030a02040b0a051f0e010804031d061b06040302100917 75
    0x400c800107902915113210516049054104034085030088082c00700c41d140c20000c06040c051240300500d2205d0504000c503d01c00082016030300321645410501e02000070002a88512180c05080d0020804090800511400c000e1001b42e40d5170200c0c40741818014404d0080100b120f401100910307007030b1a072002340b180c0d8410910300700d4a01e000381800c140008d201703060b469051201d5202ca549055003003408041c05c1060906440d41551b10480d0202c866103d20701040b64029041181480341036601d00100e8200110f060004081400ea802c1c208003104060740507190010340c0340e0724000a00d441d42e022044a104001c0c000d9410f03170085181400620301b54225440d041006007018803019501c102080d58007041040420240801016400d01260710865a040c2c0002c00d10308003100d401d2545010700800c0394802101d403038142c0100001420344402d011280009010010280c440d980e50700e825450b060152000c4005025000038213100c5c100780c0c000e1100300da4102c8030701d24458004402065942c4c1c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 958877949 1250 958876699 958876733
    0xb0f040f260d0c03050604060f1226032703030a0b06040504360c0303080c070c0909050f0f0c06130b03010608011802040e010e10030606060f03050c0301080604 70
    0x403145040021180c008050070704240031a20108a5400200b0f004e420382c1c00c024110f80c019480c15904006096050541d074003101c502c052100c864a142c0d040c09040d0162010070096034101d40c08242c520714400c4001140708805585080d2041c0142c1030302103440700c07040c04001645070300600108203072503590750188800450060019103450b40d41c0700880c050b06c0c01d0640700c2441112055250281081d01d4240c202201c15203c0b0885280405035550305100f4110700000d000c010901000618441080d030899005a405c4440302e40e09c1961441c5000290005007411075031800b49071559840c250000400b0b1b50300c2c080101c040d10004400300e080c0151500b100740400c141e059241c80008042003280c00840c041c040b95aa0000692304008021000880e034801c00120070344100000c000c0700348802d07051070540701240001502620fa4840c2c4c2440307000785410181905203001c10005903e600708804490000c0141c43c00e00c4255110b10742c0155601092080d408647c00000016001904004082c1c00402c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 958879199 1250 958877949 958877993
    0x403052a010f2f010e01200d090204090c0302040b0f01050a0c050a020d0303050609090307151d0607110f190201140c06100306060b09010207060e120f0105040b0f040f 73
    0x4100002804403200d425494001030400f0104020310040d003c0c01804500582d640092185c0900c01001d410042c0c10042c1442c1e50301c83c0030414a80c82e20283d00000300c80354004101384004d2915003852542d105480c84100e2107540340001000c1c044c02c02070520a101d64058440c1401d19803642810b650f009180a01210ba0380101200d16005a440f5521103607500d000e0b6030b0001d0146400b80c144400d02101900c0340186070703c244101400291455401c007506640200085001e52481084000d28085940706c50442e0003100c04102c40c161b40205441c102c80801800c40e942140740000b0a82c03900c10003540d05000c1e00341d2102c0a40035500800c400c410740d503140e1500901e07007050b034580b40303007001c9003034440041c1c111350780e06c08006000c4540601d101800c409441b41e468000b0703540003c0d40d207504600c01c05050012000e1002c0c41c0e030b905d00c011401d031070700380c0d90540340b0034a400c04503103000746402c640c01c58007007440e0000314459040c022106440380d80e00c58a000c0c0c104020703407204080c4814051240c6445 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 958880449 1250 958879199 958879217
    0x10e1201090b090f0d0c0c140a09021204060b010516020f010c050709050114100807120204120308180309061806070215090109090e07050f190b0403052a010f 69
    0xb50012540d144205622005013071120740c42c2007807600b030010b410603607400c220120540c140810280100c140495420500104008100c1e502050b05a40c0e40e41c4280034403071003c540403070403901050145102e907106031820409042c2c9c00c80155031900030015480320824016480301c0040c2001010065000d07014102000c030b58400307907180c0b0700e085010b41156105544440040101c48032030785030401c102c2011904007072080b0034882d00805802c0004c203642c0c2044020078014a01201a9048401030b281425511068194900303014090325001d441c07501c00021101a14540c0a03000f00c29602886030040500c0d28011003501c001c040c0140080c076250344242c040121500590703c940c00341030140001101345031102d244c040013512050f020360100d03c1c0340781002c81c2d8444108000c98118140c45040b1008035245203030b140401c46120000d200c0c2041c45d110510003040a500c0003015108681c801c0f4115407007000d001038024554400843c205c03100048440a10200e98010413100761403050503d088006 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 958881699 1250 958880449 958880453
    0x1d0a08071a0c04140f0d0f0f17040f0803040602070e100f090b130c02120f04030606060201060305242212050a1b0c03020907050f0a1814010e120109 65
    0xd075007000e032008401410000b908118001443c078003900101012112210742c680c400000ca541e01c2c442150083c194068400302008014200d0180d10050384c01204034500d03000200c8003802140d000d401000b80c3c02e400103000181071007000040b18107940059002e804107500d03002940d080201c3c007030103014450103440800701700c94000200c1c24005000310f01c00420b05040ca0301c144100030000c2d407183c5140328144148080c02c1034000031a05002c0d040803025540e03c010000307a0031521301a80e08010031642c10100001041c517815001281900e020b101510202d0340c070001c807120100450b00706044190180000500150b03582d1510140340361040521401e5480306032fa41d81d23804410300c660000400e402045001007182d1201e800804c1e0300c41a00100c1c61408180c4401c009000180300c0244143c40d42c400240b600342c0b08034240d44d161400001c0950312045a460003802d00103404002c000d00303410200c4c00007403801c11704000220a56040c1c44070700e880b108403000c1c0107144040040d521001d40d222803103200 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 958882949 1250 958881699 958881743
    0xf0a140c0f0105070306060c021012020702040f0e0723040903030204050301050915010503150c070206041e090516050d0c260a0b03010501150f09271d0a0807 69
    0x1000020341c00081c091512807030150484050b50012420010300000302001600e41d011030701c29000550522000031183c14090f81c000e4810440300941160801400054a4182d42c0080304036144608c1511810f5469580306105910061040441000300720307402007042c1843d9010082150091401518282e02c80000c0307401c4d1242503580c5401c40e4407040300d002580c2d4220740d00c2809028120050141e8140c68542482e0034040135140840000002601e04c0c00c640c1d485017140c0041c1416502804665040d5001c82d0b00201705203d04d0b18034034105000255607284160411080541030344a05003072000c0c0e0092000140401c3c0c20400600204000e02c0740d560b107440131041d000035014040000c03a464840050025601c05400e0a802030381480d0040c400185503c0074410402e18910f811000424100c02c00c8882c9501e56101e030b4010040c5411b00c1301d4035031803e0aa115240c200c403006006030400c0309000030b110303c4090300c4031040d0f820140e00800003130190402480312900400084c03680310000c03d140c00f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 958884199 1250 958882949 958882963
    0x603070614071712181b19080d08090303060a03080706061a0d0b04050907030803100e0703050919030905010c1704080f061501050913090f060c03060b0f0a140c 70
    0x10511402c040b84002d44103088141041d4001004c05004c0501458114250383c0c8046d07110107040c00c5440a00d510410ba1910140c040c0c6088082601c5541d003a9142901a2620764001c042e0000402600008201420000850b40505000340202c402140f40d41c0365118a9080800300702c92061315900700241b00300c494040c0120b440ca00014150b510b00d15115800c003201c10f03020f40c40e030186091004000704840e012a88204503a0415001d4cc0d0301e9840000c15410b4203090f40104540007018404d1114040d031690003180f25914040481e903a14020301a0701034441614000140010401c203014001d0394426840b2400041c49403500c50503001a00c000c8644607001074002d00f4041d030043c07002101c0b105080000a4001c0d40c40320382c202000100e400020201c0c401c04010b14040c100c004608071009c41907502807200300350000c28000c448a0a450702d0005804010070580000c0e0078481d002c02e20094000480c0d4021603d10301042c030f000703d9031505aa030606840461700310a50240680c2c41415020b00c411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 958885449 1250 958884199 958884233
    0x151c0606022d210f0d020304020f1e1003090f291911040323010b030d050d09021810031209081b130e030c060f060307061407 55
    0x20700100825001003207440c0c01d59400061003682c0d15905842c080802140c0c04a615800d4034010030059003504026106104020000d0301c1030300002000d600c10314241d405180034074401c4684880301240d20b000c02c08104c1030101c64011011104140e00341d03034a8108a40c204c69020340c1800b02c0c82a403291100c001c0b041c1c44607005d41e290003081c00e00c5003041400824140506911100c8040b4508241041c0c1c1c40400500728140d0f02560380310080c031903121050059a00550380249040701480229001019042240703113044220340c2084042c3c0304e52320700403c3c4150303042015628507003400407403601d180c081c200e085000e9030490306054a10891943d000350552140f00c01091100000b072440c0b070140036514000c0901400c020f8102e81c01d00c01000c0209800d00d281000e903603441041c1c0400000230701702004440c12038056034501810034105103400700141000c00c441200f03a505a42e203031600740f20100030494903164140c00241d010b010450185080d0150411284c07000d90070125240e4564240d01400002 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 958886699 1250 958885449 958885453
    0x510261909111305220f0b01080102070c060207060f030b1318050706020a020d140c0a060306030204050114060301030f05070b0304060b10170a0b01050c10060f0f05151c060602 77
    0x880c10541410201c581214044550400051a041c5c407040d04146038080c5d00420000700a000310140b000048400341030503000f22a0810a5170f440145074002c0d07003d04003c59040c0d03520b1200040030360021900e0340480300661540980036881c0c64084004186086145501090021904c0321100721403084c110f8180e00030100c004150380c035003859071a148081c1c0c029800c562000304070800503124807404400303c81e440b1015005902c40c6141150810407251600d41e00070030480c02c00100542d058001c40c040303e009603000c22507a622080034030180030b0810481038010301c0800040001540e00c0400702e0030b25008070180c0f03106c192070740c41c0060345900540701a15036075111a00c000e42031030068040e440043d11401d00841e1200f800d526400d1051380200310048882e512011240f191340640c08030b40f03020b103411040e548404000b6201c0c50042640340034031401305001500216980007040000301c140d0728010042c1102081350114101d00780d00c20511015039503560603808400290030b00901000d0591500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 958887949 1250 958886699 958886723
    0x1b0309050915210f0a2f090414120a0504091404110f030c0603090a05010c020a150902060702220e1b040e0304030215040510261909 58
    0x42080400900a00100301c000c50318590101c0980d6500d038180c1c4014100410300400900c51801c40703042030051080a241350017282441010050800e100402d6401c4091000c0c55140303402d04144c441c1104440c2c420381000700b050214002c510400d01c050000e490207000c0700d6880c003000c25614400e4102c1d0003084003043c0041001c1c06092424094042d144040355050034062601c0d85440c500c11031040d00c0c9600400d1200e490009645044c8800c0e071044501901d6039507207080100420380d40d45811002075500c2d500e014110a007042c804100c40010941010b0011200c5000c98400c8006000482c2c003240e0110081200d0320050320340d02000580d000041b0004507803d8610700505064a04843c09492203400c0429010341c03e0842c80350302448080243c800203050051407030041d01d144130340d0700040c1d8020b05000041030b0a03c601e100a02c240c1d10142e440d0268052820425164a070111015002c61484e40030600d08100c3e10f485000d0f4000a110440401031640070708078021920100402d0701d002c680c0034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 958889199 1250 958887949 958887959
    0x902060c0601051f2102130b03090714180901150e0609090a0b010303080a0f0507031514010c110418050d0f02070f030803190c030c02060c030c040b071515140a180209011b0309 77
    0x2f110000040a00c00102903000480100003000d103042c2859200c1c07142140d0010680aa030254051490a0b9100701c4a0039042e440f940f40b07080e4050100c4030540309601e103c0006074044800b0031007001d9150300912003501a400c40d0307000d5450020041000d140c113a174a40710b4001c1503025014190140080e9280003030583d156245151416980e90002c031f80d000740d040d007100b030566400000240756603003100c1290454107842c1c0004001d80814810702d0b045044502d8264213001c0e0210321407a0300011502d512040c0c0d41d84840a80e00d655043c803804000f01c136560010008642040004c1d03600984400c00d088141c20540280e00840350b1849000000a0380c85c808040515010840c2da9008039025010a0035490020500302062055004002c01ca102c0416044100807081d03052088410045805004852260b80c103603000052511860040540c4a407000b00e060611310000b60a840c0c10300b0700035044281042540010394400d441c003504201c402c2100b800d5443c00131180c1e1403101d100e551182d072558901 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 958890449 1250 958889199 958889203
    0x106030819020d020613050c040f060e090a030c020103093e0a0b040317040b0315100305090703031409090a020a200a03030f0902060c0601051f2102130b0309 69
    0x25411500a541c0030f40c0300071050a400140c0719a00c10000690404150424900b4504041580c603889401500b0700340752806a8100350410000d4a40000030405a0f544801486035506070550300603011811100d14200554400c1d04040640c9010748110030920f26940341d10448004118103040241c1a511040d130004c1007543d44071940c00f03000301c592095043c2481402c0d5a075118501c8001d24040032400300102c2d5406000540340140340c00c04405e500c0745000e020030315030001d02c1c02c042031056a580c0c505500e000e000c0d101d201c0c0903916020040c00390606690b03083e22000c80c2c4c080511070301c20003407110101a60351116060f204075800d040150700c541118030041d142034081d262495400501c0104100e40c504002104035580e0342526001c2500c1492403000705c0200310480c4041e4001500146004a602c000030743d05040350703020350307910703c1030000c2040c00c0e14002151804100010030701c80c40700d074081201442480b9400c0002c00d0040c5026091456a10107607016848190b8816020040001c01c80c42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 958891699 1250 958890449 958890487
    0xe040816060b09092103100e0c0a0921120e0d05010b0a0501050306060a050d0f0c0224150d050f010603050f06100605160f0b1302150f09010c05030c01060308 69
    0x180802400c00c00b980c0820548020f0303071703810001d0b0481000700029406068001d803040041080460b890607500f4078020b4000958002c800700b0307011130020440001c02c1c4032901c00340e40003040c02041111003040245e8914100c0e00501c003145040103040305d880b038034554910704c06940040c40b46000050b100700120510590706043d0740400e060120a10411889448880440740301407050f15280303517a03483c580c6c0744100811041180d081c246240c07a4a02e03507660740000b550441d03d04c03140280c81c007201e007240e5944000300084a50108900740e04510140c20b0401e007a5420302103205070103966461080c3c19070682103860a41c030942e1240c1c0b0010080450035020301c107840e004100c00e20390200c0d0600305903020f0f0651060401d249900d42c107141441d01030040600e030b1b419590b84c0c0240021070900380410542480c0740ca50a09034810540214400d18924602085448103000104c0c110b003040300e00e40c0152609c0c040c8a600382c8003030008020301000301000b031050401961080303901986605114a5000020403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 958892949 1250 958891699 958891711
    0xd110d1a0d020306040b0907152d090504092306040317060922050109050105011802340804030c03030e03030a02071502070315020901020c0d0c0e040816060b09 70
    0x200c0070100402503100828480e0388285c0103007208005407103c1c19100e240051b5540800c00e80b0800c641d2031a1110b0b80041082d00200005203400810218610306604000c03e80c0100e00201d251554100a241880d410034000c00707005005100a502d00b21542c03c0302c5086582d0304151940000040000309904010592181488401411f1840c41c02501003414a00040c000074400302a0b6203408601c59001c445000c20a94040020b108080c21842c0070b6010701020f009001d0727170a46c074005041030b18100344251900110174219180d1940090b500d84031384101414510082954045444000b043e0084002c0004510407401211841e245041c002d100c91a0380b40480d210b500f0070410303100040c1c0d00261110a48180d078140141c01202104140d01d404003d52005007558940b1422108070041b65004c0c1c168110700fa001c2c2d410203242c410412000d0300a03008000c000808100040c8280d446403c403080e4464814001c4525020400764505500d1540781c034220b5810380c4543d09101681050369500303801ca4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 958894199 1250 958892949 958892959
    0x22060b10020313050d080c0f0a12050c21071a0411090105091618062006071704050109021c020f091509060310060602150705030601140d110d1a 63
    0x1026144283c00f6a1064a200d80260008141840380e802c00711a0300310801301c11500b180300160700075a1680c0c1054420755003240c05400f640f01c41c0d401041126200a002000351116034040d40c2d500b054910080c2280c3d4000f8018050300001404250000240b03940e0311500d14000c0c6820700c1d080e002000441c1509008155000c0100507613115011241d80010704070b520010000020981100c0311724885800f400c14201d00400010340c00c0c0c220b0855403054685003941c02a0344250340c03013035913240c00560b8a00006040316181c0c60301c0c0e6510302c0318a50850304c21400480c0c818003940000b1003102c1c40400c6e0309107548401303a80f5400c500c0c01118000200d04160b0780400c6610b0140c4880400022012001c0d001c0c403500c00000d051541d05000540903040c5442007004210b0300d440d00203595010780100b0412149510020a1030301d4015001e4038840c0f10141d4070902d00000f1940840c840783c00406000200540750400a400c80d4420006010038041d04400043d0329181e420040041040d91b0304a9070180e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 958895449 1250 958894199 958894207
    0xb0604030201052b0213060318050616111c0f020c090109180c091e02090f010507060e0f0d0306060305010e01210512030402130b031522060b100203 65
    0x140d0b081425503115107100201034900e10204c01015400a1000401565680c03000515016503503203e102d25043c0c1c0c41710b0b5410080c0c040c50601c81d40200400007400380c8940d20020008080301d42e1401442d9400040d0314150800c03040c13408038a441d000c040142d804042d2048031800030300035448842d0721400f141c2e503c0241623440404003c100810b2040c020700300d515858415810301209a5500d40382441d40c040c0d100780c1d2495a903280040201512202c141c0303940000451040403824a0082d1b0f107040700018414407103007581d40015501540500070840e0000d403242074540414905125100605403075101070200445462001030840e856a0040e1003407514203c01444081c1c602d182c0b0b030b81500c10f0100c01c00049004040d0707401c41c3c446d03c8500105240b00701e00d01ea40d0460010340255009034400d0785c0006146400760384180036240944180c2e07405034850301c45030100810080303003650004a50340351844011801d05150001a55a910961300c1707a48580b230035000c90515460320000801c00f84095818 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 958896699 1250 958895449 958895453
    0xd060e0f06091909080408010b030c0111030307031a0d0f03080a02070302031c110a0509150405031504060221011a0a080103031d040c0e040609023112150b060403 71
    0x801c09025140c0c41c00d20345003e650400240060340680252504030403c540c6035507035102d0301d80c041d20095822034000e014240f240d0f000b0303501039020b450060b01001d0140d811661180400c4000742001c4000c6105400f8040f400d030050f480700240e454072a0300034000012100b2075802c01402005001c0c145204042c410004100441d9002c001d813400001c0039240881d08040045200d00580380085801c0003842000640e5440181c01c14002e100100c0e052300e4100043d807070520694000c0c000c91087c0d40c0c00d034200040400e0903000300c0b20840e5020748100e90040c20658074082d202540410315800c042c00120f400300502040c850245502042c103500d401040c0b0300600b03200010807102c0184801000d0181180360148e42890a819840300130314085c0c001c011030075070140014503a50301c00f46454001c80c900403010510494a000300d0b580d04030320044841080b6a803003107014280c40c40009030003443c03203103010114412049501a00600e0b00850481c1c62510f00d024515086403112030425102d00810001000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 958897949 1250 958896699 958896709
    0xe060601090b03060d3801060f0c0b010e0a0e1b04050f090d11120f0301051c110f030c040e06040c06020c01090e07020c040507200105040b16140d060e0f06 68
    0xf0140ba4044000360700030346400321519650012046c22904102d0b140c0c2028000c400003d20181202e01c159030310002020401e9090783d14040c040030240007102c05000600c0801e51442171160400341c0804001010340c40107150b2814407200e01080f8094040d0591000410318044c05659003161401900c00302d2400c26a0426590b0850980c01100b403020744502606540000d01c96208039181121200e941c46100c8981c0c0f4000d5402400384922a049159024444c611880002caa5240d44405800414088a010411400392500007254944541244800381c0d44a034042d022034512410300910480c10213142a036414001c54102c40d04560041d8a40300150307070f106000c0c10486511602d8140307942c8801d02c0403030406c409064405e4106051005216041c2c2e480055000101040b0140c1c40000e812951494242c0d9015070380036000e442e074440424417128550f110143c514800b4201036800100c05048d1860035000000002c41682d17503000104990100300d5070f4241e010380e840303509122510f89034000807 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 958899199 1250 958897949 958897969
    0x5031b19030902130603110913030801050103020309010f1e06240509041d0a20010e041107021009030203060a0207020d061a0a0902040815100e13060e060601090b0306 73
    0x30200354581c5140d20540d01c41444000e003014110005209079502c0742032100204808075075080c0124003100001d20405001141c1c200c20941c1a0b98100c8540d19102c011400780d080a4001c040039540e0304515407a401c850b100d2070600010b203004000741803007800301e048202c4050b68808800c28941c003014440303181d95014080996041030070402c2e03d500d981c01c0400c000301802c48025000203140002c0d0882c6210000f440d03c0000e1090a80142071042801031001ea654001038050204141440708032541c9402e4005040640c40b40420724104400da400041c1810344039031620000c038a80d03400a00660034141300d0301ea0300000b818021762810788d0300e0b800320b00c000030b64143c040c0c9100da484042481c3c001000d00c900c0000b01008141e01e12881c0c468010400950141c4142d10991041080041d000622074074503604c03410f03030f00315650800d6140840510800d40001c11100e0404445507400000034414816601008200b200422451501a002401c480d0485c0c10805c00e40d001441003009659440300c00d0b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 958900449 1250 958899199 958899247
    0x60e0604090c090e0a0207060510050d03080928060b01020a031b06062408060d020d0807061b0309140c09010b160203190506100b030109020f1905031b 66
    0x503651100359800c9500f5005034002207110f0b2855000c0c456100d00607006071002c1ca000d00420405905c0340d100300e9016a08a12500385c0020084244d90701090242c01921351020b28442030300c1003030080c0c1114400135400c601d400c8109001241c1c2c441e0030300102c1d20510000314000c2c00140320900094601030646a800e10f502841810031a03010307410080607422600041440389140b0646004401104400f01039104000c000a58440c0002d240d910b48440343b011055000380c03030120740900340d48500505901110044d940319803517205407a0101d604071017248480304d0943e000101000d00d480d044044421024000c82c2d80d5000d0001e5a40680d241780885044036403081c0c540d030f07603544a1031074506400503400001c1e51601444045a000002d0b007499003007a9480f48060742c0c515583d401050b41007031114011901051410b0005004415481d80100812042152198101a800ca8900d83c40c403c200c1304a0000407404410f1003042010070742030b189400301e0707204007a0a0084400051903c07607800000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 958901699 1250 958900449 958900451
    0x3090603070c02030d02060718030f12180602100f0e06010620030f0702030f030a0f030b040905030c10050901091104020f04030213020a0e0d0819020c0301140907060e060409 76
    0x100341c07594050010b1802003907000d400d480400b1125030011391a808104d031411b0200d8081e0404014070180c00a0420580c0c5e40b010380065586102d40303402c40048042c05c0d00c1c02c14449403003103034000c2542600300200105200c0e4020500d0304c5041d00a10156004040010ba584c0d05040412418035030108402d0305544443c580032028071444181e102c40c048080340880f8680c000041c00c00300c108508002444018000d90480d2100012803004603038a1144140020000b40340c5020141c1c9035100b90890021402d009001150108550f140e980c11980419032034040d0383d01c0713130302d1082c80b9803680d016903580020060020407800d215500e03018050311070302c620584102d81c0002d42612480508054070095500030703000c20324108401d00c200009601400800703011a00c0e0502061701460300c402c4200341d00d80e0001c40141400100300c00306100c0060002c4a0040d401003140700a0141c500340b24050b408902624004603c0c2081d00c111400d10702c1d40c0d00301030100000d8043d0071407542c8601d42100d0460740c40b010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 958902949 1250 958901699 958901701
    0x3060f05040f020f300c060703300e0d1119030804080d09030c110406050609091902030a090318032619090e060901030b070c03020f030304030201061a0c03090603 71
    0x800100a414408254200050300c5d1000b042c003501703010340c40740c5070890110031600865405803c005107401403c2c0010006040d40d8640c00b0092003109880d51880d401c141c4c00c900b00803964040105443c1c0640e4401082c3e80301780804180b86d9070150a000c502c840e0840a045d6888018085052a105801024090044440104040050070411950101e0350601c040100001c18500181294507a05040e02c115410810b4130102e468103100398000c542c0010481481e00101c20148045440001c2450386221001d5407120107001d1680021407056091050010740d0514500d0b01808944070140d20017089c61114600303100003508015007002040154841c41d040d144680d108180622a084650780d00c0c41100c0320426146421001180c1664100307171990169541d81d03014056110360034030000d000d04145a003c41c1ca41402507941c1104203001e4070580c0c0200d91a225818a0f680c001c2d00e0480040c3c3d5604010040c13018105d03039003488000c201810519103110720406651780d0149040c003a1150740004 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 958904199 1250 958902949 958902979
    0x30a0c1b140d0305121501020d03050f011809021e15030f1305070f031b050303070c0902090a031b051813110f0405070e030606030c1e060c061003060f05040f02 70
    0xc0d094034100d0140648064241c51b00b0032180d100144410074250151040040b01041c0700e0103400707054420500c1304145100341e0710303001080302440084110064021380e03c40040d005a00c0707001c104410b4203942c09000b0b0350040303210b040c0000c0300840e41529600c44024000d00150214041c1159003008405d0200c01c00043c8604000b070808174241e214a95000f16020300008002d00b424908550f1032918042d02c0d080d03036562040c1610ba01c0f66650080100040120174420400c10740d010745050000a03080f000d00a48941c2d0b00040c2d000300034000700b01181da0302000c000e5483c0042c0302d54010400701301c0e40402c40c00c00307103c5400380403420400108030700c40103841408141c903040f180e101e005c40300400034032681c18640e1020f02889200c980c054060b00803040054280d00300022200f08244012302840e1a803403195014492108101428503802282080384a1822004211190241400180018805103545482d074126550300d800314968034240402c00000c10f00015140201c3ca4060300c20030403010f814 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 958905449 1250 958904199 958904207
    0x2b0903141e0d0b0418030807120f0e0a02130b150901030207061a24040e0c0405040c05120708010b0d0e0f06090c150325020a05030a0c1b140d03 63
    0x910700c40c00a00030082040e00d241e901c20307005480708860945003000100582c100818180d6003c00014010980a0021600d070501c22086501c4401440b41c000541c8411203189409480e00d42c1c42d0310310240d0001c51800258905172280e904031a61408003044804440300c0804c0034101015110090303c10045480300460b4044e404561500b0b500000c1080251032008000002034184040217000384001a0400340418041826500745805910b035541014540f101a50744020000c080b141024424800014241c80300d0040031015050350703c0b2103440d800c0400d09260b14090013083c2c60200300c081e0004000302d0803400221500b4a45840c0d001c40c0c1050180c00c580e142400740d145802d02071040c1c8040100f8200080b03000700d200f50086901c504000c0c0c450b80c2e0003803a07000940751440044407030307a00703803102c0d03000790034ac0b1a42c4220f5401682c242ca00503031140d9040d074120040f400f02161542da400404c1200105156601e51001c100302d56083d800d01001c00c100b00010b41c0e41e240603010301e92943c0145402 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 958906699 1250 958905449 958905487
    0x307170c190503360a06082e080105010303120c12091e050d02100b06040e040213020c1b030d0804060c051b010b10020601150e060408032b090314 64
    0x6414240341c40f20750003c440e44100010a284519088501391020720702d4402e58038401ca555aa072050000c0e1204110750817103500720600d00d24020200055508040d0100c05018006c11280c80005650b47c9142030140c80303500044504800940b80c140c88060598009270306441d00403001000142d03512840c544a104454440c030280b400c0c200012038042080780010700c1140701000c550075541e24a90070340008081c1c8041c0c15800354095030600c8107200a00c225803001d50700900007081d60416103030301e50b010000c9a010100709007880e0414039048001496040301c8039403108098000340454410008000e0004402500c0100640d85075000d04655502c10350541c0e500402039542c40c02e034065120a000d000b4184070310000e000300803058034020310324008200d50341201e0b00041c8000030300042340011188007500503c566440305042c040031078401000c00161086e40f110b00328001c901d20824219a46001c0c05c031040e00801410081d0380c0d00041d620100801030061440401034481c47c505040b00d044000b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 958907949 1250 958906699 958906717
    0x103080d020417010f060609030f120e061c0506120a03081f060507020306010902120406110f030a0e120f0429030c03040b0a0c090e04230307170c190503 67
    0xc80800410f520401076004054440b1071010400c41c156444c0015100c807802c0c0c1c400500320b694480c240d480400c002c140e040c20048642d15002d5501c0000e000050041c0d08001100502a603403404c5200360040544681c1e134004004403600413000d909100b000e5540c0550a000500f0081514003185451101c202800e4a95507030003100e440792521404000c0060b0803c107000c3e8401c3c030580c800010381c4070091084600c00384e940c60b0400510368032500e8010140031241c580e015010820060903003084658070246024007403280000c5a05406a01d19500e0541d281044289020341000001c0380d0003a15002c440840354145070075030064004614200744008190700c0e21042c0d01e000002c028917010000000c6104602c60a00f0149580341c41198108964038040030402194041805001441c0c0800e0400d0b40a4443d118150000b1441c1002c0900c0402d0451006884c0d030011a44c1000c0006080000100c405a041010305240018000079541c0709140d00ca10903c5031650a00300901800b03100300c40c14a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 958909199 1250 958907949 958907969
    0x2010c050304060507060b040c0f11030906040905060907030e1b0117070f09060f08040b0a02090409050d030b06132601020c07090b0409230a0f050c0108070908060103080d0204 77
    0x3035907004058015401000215101b82c6450304008092400f480b030309807481100d5884c10318a410005003500e03040d11403442c901561106000356445c0f80e0740c07440180b0181c555001c0100f41810030200b404442507002d0320301c07800d0504042c586692550001000c0080d0540088601e01d08042d4400503107100c907004918140d440d040388100003020303400c102d00d0341901800c7e545007032106584090071540c107580310301d050f800140c81c0c1000c50007003000c1c1050340d900000700e0364005103404e44942c00030303082320b000c64011111b0742c100103900230b5002e070180700302e10a141d02a2411440c003070340c2d4005a12946e0383d500503820780040110664140003103002c03000b040d90800c01c000b159240004040c6582e6040a131060411140c00c1a0f02c0912a04040c013500405503403142088801e51203201900418100201525219104060702030000c00c0c0513100051049006102400c034820780f000006203480002001d0ba81031007c4040c0c10022900c001030b1260460b5044140c8a84884114100700003920550340811206 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 958910449 1250 958909199 958909207
    0x71515080f060912040608040b061216052704060e01090f050a290604051503120301030605061c030c0204020d2a091203030f061e030c0f0e1302010c0503 67
    0x40c0000030400c1c003c2190f04200c880c40b0711031503020441d51042c1e00810b8002056800400d00150a03220082e8110b10010300b800e2110b0141030509240043c0030744101042c0486810030403081c1003c8402c0a258940807121031511114550300c1c07564514041d100801032507880050721001003007980610166980800310200c00d01c0c5034189a60784890850081d50b9405540460041c40e01107c80c0306c5001b94201480c520f03050307a4010401001303040060100502c00703070080030910680d5050004004484030243c5a50322541181440011610b0080c000b0b4010444204e0a41030b1301440b000c1440019410300e00460411218404200079005500001f10342e5420151255507000e550b60500004c0c403001100009040c081d4102166004505d01c5a0f150391303466102d40d0f46c0031905c2034100400e010b0815201007000d6030703607074105030311011740144007015085507050610070061081503010007020141070b40141e440c00d046a445805601402641004070b40e003400c2800c40e40505000d0680a400106036512 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 958911699 1250 958910449 958910473
    0x50a0f08030109050f060a15020f0601060f020f031201030219050603040309080c010305061c06060b0301080a020a061404060c4b11041e0504060b1507151508 69
    0x107070000e014155129080200043c4400c40f00a001e91069200400d01000b0b10f01d07240d0440684100803000d0411130044000701c0380d0154040018038000d03c03107aa220512090a00e00c000c0c107000d030305484407175260020071000c48500c65071006141502d030100d50840c40c543c40d081c40191840660390019400900c00b108000034160030490580459a04c40191642030000f03200440440d1740c100c41c840e81c0102d506101610150b41403c0074541c0b41e115801c00101107484041c6c210039030b0000d0b80030204903402116074004506000c08038400800541c20807913410314034402d6418180c010b80c0201002c014010f01884140b0003c00000c40c8540403003140a10340844600300107410088058820b0621078450458100b800c6a058111040c1600100b6400c0c020395081f04200260004050080c01420113a003005000f001920441d405141b040400282d590b50880c203104030031407140d8444141a02c180800c001068000c400c091001c6c85045000a20b1907900c420682d10700010b400c01107840c4109050050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 958912949 1250 958911699 958911713
    0x905090f1506010e010c050703080f070c091a0109060504151205070e150c250510050309011b230f040608010519031a04172701050a0f0c050a0f 63
    0x1c0034110a80c3d8405044c4070401c015180c04195420060055024840c1040841d05d040c1c082c00d80414202c4005141c94084c0c0c8600c94007941d9604954803207a0340d44036203031003d818035076409460b500030300300a02d4061030103a01808500551190413068000d19907400c440c28812089405068100642040035081c0040001d00003405c41840d580035250000502d14807030091405da5060016103801001e0f211142e041a20003000d0408003200c3d020f46404010442c2e0b52100400c81c549015a41c825407a450518192400e45441d25100d544d85501c0404950556074000c490b41c0340403120841e21305036010100034001c2c00d8484d2441c0150305c603001203800310785503900c03d10301412182d04070f0320310110f090f1240c4080207208a0344030082c107614030850008007103140c0c0741c896903105000c2c4841071203190b01e007181c9078200d500919024000c003140540381c00b00c0009806451801c04401c0c6807550501c02000c81c00340000f4280307144402804010000102004410000101c06540c4030104255005262170814 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 958914199 1250 958912949 958912951
    0x503011e0f090b19080a170f0a0c06150f0302062107030b0f03070b0913020403020a0b19020106030b0601050c07150203040e2a070203190803090d09030503040905090f15 74
    0xe22524a002060000d03604d500103036019289880c01410824240d0361301c85400303402ca41120b121084050003c0c000d000c4004003e0680d4040a0302d03925848865450b200c401c031850088102e01c1e0070100503040c070000054070301c0e15094a50540e03400346da03186100f982d00c0d0700e103019090604d0542c1c1040c0c20495090341c142c008000f600800c0d151503244020f0001015101c0355540a0801c010070140500304607840c00102003401280c1c14840180307040d4994011442c0e545141c3c120001000001620001601003da408142c9215606c005c1000c1800d55980e03000c04040504981c2c10040c020441c10709600c070a001c4a002082c1c6c0c07108980c000080004c01a4994000d4450600c40b5160040014164894044240c1f0100300190941003080320003021140540c101f04070603601441281e044030b0704003014075680245036004054403522450300c1d0340010714200c0e01c1d0f03c440042100a03101003000a8002059409591002802040c19a02d03804d43c28a004044110780000307209080c0313603100031501d4034822 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 958915449 1250 958914199 958914221
    0x706030e10051014030f370803180d140a0e12071e27090204090609050c030f1e2803030c030c1d06040b0711120604030503011e0f09 58
    0x3140c01345024201500d031072002c401c0c4c0020f0b40210520301d9482c440541c00501128984c0c0c040310032944030449806402c220002d003220806e100000340f00d880340107190194a03141c0c0d88002014111481440101803000c1011001c100341c4010400840d01802400b9403404680d000d040004680020040250340c1e480c284600b4500f2283d8074020f00600020b1403518050b40c03100c01c1401e070280d101050b03009030100c3d1903404004069554a107140166203038015140980e00400000ca1034840740d04083d400c000c240324030703e4800c0d80075807d138225221000c50001c072600d200300448240c0d4a825900c150802541c04041b004445942e6040a002c02802c0200c82078940207030b80411061404c4079040d8211036071600c860020828440f003540543e9a522034001c41c21401500840c2455a9622300d0300098208600407100b001d003c024451940c2465050074184040c500c0081070182000d44001c1c03c42d1206014480b80f41d4030983c0080030404429075050010300c021840c00285903556110b4030020000700c500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 958916699 1250 958915449 958915469
    0x3302030a1506020d0f0c12021b120703030315030209240a03030806060304050f0f0f010f090b01050d141b040515010915030b04180c170706030e100510 66
    0x104441034101c10315080c02e55031250000c1000801054007510800041030715101084444c154810006804e0900c80119005640040400c0000c01020b41503d42c007200c405409844880d46240c1010000103076441100d40605000034243c3c100091107407051f07100c3d0000307034101d05008240107201038441d01210030f83c00e101041515501902d02004084111840081e00040c0c1c65000705015162100003103800c54491030448814641c400c5540d800c004840414041c0d42d04040000100700e0004e0007940030044072110200b01b0700c0030a035100344030503c06001f0300f80542c000980358000c1000c18040191640802400c454000301184118003014003504030841c02242400041030720340c10207e5801e10602e40585030f082c41d00f820301c4455600b20000341d58042c105608c1d104a48095100c92103000e000a0019002017030820700303800c281044140b150301c42e0f41e1001c1172601c800c2d9980d10104015050701c0803440e000c1a02c40c000c922140c5040921717507500410900d040c0910a106400311206001c8642d9214 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 958917949 1250 958916699 958916711
    0x71109090f030405090a090c0e01060207091e0b01110102120105121b04181509140615010f120e0601090c05072d0b09060118090206073302030a 63
    0x152158540d5022040985030742d00500c0305001c18039080c00490f80c4520315500015450000380c50f08a180070381d82c0d2180300c03a000c850b80144100795043c415000a400790481c1400803a40c40d00d0b18002041c04c11115402ea15554020900c480e03110f9500100383c1503118000703549803200160000d80e110780a220f06d500c5240c0310a0b4900540c54041100c0354100c140d4098100300031240020710010344039104000030a06c4282c05910300180440c0b450104603542528001042c035a6454609085900460344000b1a0b10280c20031032280b04003803944071030b6002841c281003105d02241080c0d503580e1485142500b0541030401003404d050000038141d04803800c01e6014804080c0c0f9440540d400c0c842c3d0500035058000403140c41090900ce410802c10b25091508a01001c44ca20f40b11210300303400c00d40701354031039800c4400100128149003149014850f07580c50100500e522690004001d445400d4004000d54401c1e000078202050041c0210003000704032142c00e50840f01d200c820070003540120764489090345001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 958919199 1250 958917949 958917961
    0x801020c071202030d03151d1801051b1804020412060b012102070c0e0c0a030501060f200a140102090117153a03080702370206071109 59
    0x42d6000005500640500712020a02d43c0450207000c4418000e02c200c600d2240000e049a100030340386e0362000d8040d00c40d000c3d0b4182104044c0300392801001c409040d0381042c0600c414055409581c81d01011a0260f0507620000306010072074820041200e05e078080e102040c0014200c004859944101d032142c4070070000701001800549410f44540d2070940307101d6800110324030800c1194000c0501a004605d400801640c0d4040300c0d0900d1012034a24004d014041800b5147c2501030050501501c540e0800c0e5040b40041403000b00410204284209414280341b02d40b0400103052102d4890a5000b00800001060a00c0054041d41c80010081c1c0014030041c80d40300e040b0b003a207038140c0c014000303030164881c2d01e02c2c14030400c401d1181160176200462800d12069030700549103000c0807110079540100101e040e2440c20050a0080000e061000b5504001c01d070191a410410002040c104018800d0000706d25000240d15044c150781402074010b140001d90b0700500c40042484c0d0b0800380c049907010f040303944007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 958920449 1250 958919199 958919219
    0x30302030921190204151809060612031806030b0105030c0d18050f07050a1412030f0706051605030402090624030c0c0f071a03220b0702010e011401151403010801020c07 74
    0x510813110a80720100f001d070411f4440e40c100182c0107024200c0414850b8480c0070350380401c880d2407012000300701071810880c055015006010014400390900700f10f1105a00c1c0040c00c940300080001c5080701c40051001e0310701115904c0198007004038035401981c0b4009250580c0e40e0301e400764000403540f0503400000b07a5403400242040076500217003440c4240103118018081001800c445d00300c0140414404500600d000d840a8510580141d00214050510b0b18160110f440e441d03519000300301d000c05c1000003580703510340f0054100d0b4040e6600d25110103140d2020714001440e000710354015000106100711002c0941c007824044808900f540c4407045804000c0ba6540c0c0b1520403041080464400705824140c20f01c007465000c3e0259070b03400280740c285419034400d425124403c4a2030a82c10007401400c5a091060303800f0385041c0703c02040750400018400220a070148500c034003051070044101c3d61244901d0244600106c1081d0450300d0b0f58540d00128042c3d000b860042c015031040d024000380290803 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 958921699 1250 958920449 958920491
    0x50105041217480a0b100806070e0108071704020f0a120c0914010305151518040506060105030915090a02030610080f06041a040303200409050907030302030921190204 73
    0x1801c3c010000c2050710b54440d503544070000c4c29002925050040015000c030144625485215150f4608580c240740704000340400720302400140c00c105400c40c40c042e4010103000003039002a01110168500c0c1590b800041e071040f00740d0001c04030b0001302108040dc01424411000030307102c2e030748030901a0f194800a03060071614244405040e40c2d001c500d03c1060700d490440d140e41c1046400108501c007030002e0004c5210318503840c1000501503551002c00043c08418041590410300034a005461400c1c17403c01c942d40c134001074007061005064603000c1000300e02c082020b02c90035503010b0252109482d285d00c18001114540c81084524060719565000360080821950701c1251702086071003401c0b034440d8040214900c0200f040301450750b03401c405c600284004e08a0040758011003500d5a840d070500e280034054030005009403010360301c016400c0c40040d4010050300d1514000b40c2c0c450204c81511214400052030300701d20b903e414081d440300a0900c2c200e1155241d05603009650500101c10442000c03059030030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 958922949 1250 958921699 958921837
    0x9021c0b16022508030723070302060d021309051e090109080a0807050c0a05070f1d1f1a28021e1218010306050105041217 54
    0x10030000000200c004183c03107803240d041038245440c81d21070410380e10b5a841040c0a982c1c6035a200c0080c1c048000d1041c07618194030140014005942c03969010540502442403000a8160003041019100121aa415000b000c00200a024500745090641c5102c0c500810105580401d0b8000403091030050040003c05030780011201c2ca0a2602c0c8402c50b02408003130004000c11500700103c08103548104030341001503001e807019004d0145006403820b4403072030340d521000502d0f15482e55031005c0113403101ca0542c40346400800b0350060000e9915061914450b13045011103041080700c00d1071520920001e00710030302602c00b0b421904131401c1e160744942108a0f40040040c1d0040000c40943c1c2400001182c0341380007042196803052075803a904107c2d403c0321003810030510f103280e244200c969150185274000d03c0b00303003801441c1a00b03128603032070481d12100001d4108101c01e1007120409a1010407a12a030303a1b11210400c0400d48510890307a21001d070112207281c042c0c25041a41d01c070000500c0d8070343e080 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 958924199 1250 958922949 958922953
    0x822120209130b0403080609130201320f03160c050d0e010216030f050d080c0d0e03120109201303031805090108030301090c0f050306060d09021c0b1602 67
    0x114039420401002001801e20741d071010021080b80c0040d051041d2107029912a480d0f40d040d901e40f40f0148400c901c8010240b00403c7c8800a0660260342c01500c3e560300c484940181880c1c2401ea0310780c1c9011000510003522050300d001520700c2d0b6000c002e00145000f4082032011229840041104499100b10040c0107040740d0803548140308454029500c1c041140c130306006a4654000c23864980c00020307007950060340c0700c00e071405c0340f0f8080001c103001c060302d044c0c500d0804034181d00b40101c0c00c0d6003130301a0245080c152580c451100b4000c880400c00c0c0c0d40c140040320326141c420343e141c2e02aa4094480a016203001d080c0206609101036503000a5071000822031290143d41480c41e101202e00411948844d0b844801c41203000c03c40751151428140a0030f112001941e40e035152084450880d0030705807030081000552002c5401c0c09901500f10382d040071040324143e445050181c0074400400c8a5a0002d620140e800190540a6411055003c106008403011207495a5840c08500003120b40c489282c016 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 958925449 1250 958924199 958924229
    0x100b0d080a03020a0c0204020d0b12030f16050307050313080607022b11030a030504050d0203090d11030319110c1807080c12070804110f010e01051e070822 68
    0x90384a54040c1c0071300c0701e540c90034600e180c2d2190040342c100d0b0712000511000b06e0f121204a481c50a0121040c0d1001c91590000c40c9405540072104407e07020301c041c500110080c43e8a0803080c41000c00a41d1f419603005425255205400103410111782c0321885005a14010a4001400d85001191200080ca0b01440b417490148951100c2c1c0c0d6100d8810a0301020301c650459002c25028081000e0303c42004251000130382420b080c2030041ca09801003055404660040000d00416214442c0f40c100d40c6a02134000c4080310240700000c1c0c218058281c5078101d01c0d12441254050302c6d07004411302070301241c00e805d0700d00d04604041440303078030103101d8400c0e1f84012128000c104054880e0764015440310b0240700080c200440d004000d90126425141000017032b008100340b10034001030103071200c102001216480e05240800d8001781611500e1180039040c800003190b0184400005121009807109200526569806a00d081c5d82d0a400401612840d40c0c80542c030000c800e02600307141c1c1700303503440301e0042461 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 958926699 1250 958925449 958925467
    0x90605210604060305070b0903121e030c070203100507110708150c0c0604030e01090f03051902010302091c142e0924050609060607031b080c100b0d08 66
    0x1100c0d201600c07640d0455501c05000001c40c0c02800f401c2d025040da84030b1a9a01c0d0801000c0601d0200361420080e000801003045410000c13802980300c505401482016460350380300340740c100715400b42d000b011b034042c021840d10454400140d8800c51042c0540e445030207204507005042640c038040340c062001243d01c90450b482516001f41250b507032240c00e5503134007498070220f040d41d01d08141d01514100c1c0803c003003920303c920941e04401554054161000c901101074070350307140d4559980808151440002c00c05c00d640c000d6921940480e91f00c60400b034955000e00a400000100c1d00e0002d940c00e58081e41c0b54441104094000704106d036404034084030032940b1704c41c050f14036160104409c0b4982c810ba80c1e41c01c0c00c50001200e480018218078648039104000746009030b0510151003000300342070700c25082c460422850f59520010703900401e03014604500c0701d40c04001b03007600000c080f04001d801e028011501c0c03c0c180a00203101036802482c0343c0d0510030082ca1000f80304480891141c0140303840d40520030500 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 958927949 1250 958926699 958926757
    0x709090504020316080f1c0f0c03091a0703110c030717150c0d1803020d140408010f0203180a0b07030f1b0306050301060605070209060402090303120a0606090605 71
    0x5007140c00101a61190381044045074100d41550b403248a440d040030040941c0e986003801040c07503c1c030400c0e0400104103060b400c0140940305030398000b002c1c011860b499a05052042107010060001840c552601050440c1c14080e03a4101100840025402000d8a00d19203004100d14140200c042c00404001342009008241c00c1c00d8015260243e100e520a0403000441951340c090140c10b040c69170640e104012070304001038802d4082c0640794001141c11040009a00081c05802900240f41c14070000079608603030141c0b807040368000142d642c201801d818910546900a41c0200c480d030f494060b8075107a26800c582c81741032100c0050a80f02c0e581e4002034040307001e03820820b0110540d0b070000ce00501c2012900c204441e0010481000981d120828852400c00340701d0b0703002400d80b034240a81001055400500040b500401160055030042034440e4191010000d542080100c1041d109051800341c4904c4028512881340c00c001480a40000440601a00c111050751a24030f4041c030380e420400158034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 958929199 1250 958927949 958927951
    0x311030a0803040317180d05030c09030a050c2b060504111002061023040c02030f030408341b0b0d0f110306130f020f070807060608030307090905 64
    0x5816008100400300010a4140114401c0c1c0c8603403a00034203894465080e15100038010f001c10a4400000c071010205a00040c14200d0440a4030b08141d6941d20700841071124080d10000507094030441d00b503801080004904074003185001d0b1512004031154004898084a0350b41d0301d1011a1811119403011074030360b402950380180620301800300b1426403c0070800c0500c00780300324130060f0845010322150580d0740302d9903001070242118240750f541080305100c080800c40440301d40320b40d07a10150000c09034020300c165084000321015150710707440d00c0e0416060550002445040c0d881d4000040c0d24010450f49440081101c442c9000c40680482e03900c2c0314900000e940ca80000001040c40010700c00e40070002000c1c8a042c14602007034440e84400510103a9226000d41549500203208124881d201c400b81c1005080020078041481d00300130035008000d101d4414001e440c182d0000b40c0ca8144071350a002045068801c0604009440c0d545244903220b010588060340001c00b0f99004010005581e0089 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 958930449 1250 958929199 958929233
    0x5121005101a0d0204030f030f0f02060115200f0a060b09010609090506040f020c100f0b090f040c0f1203020c01030908190e27071e03020f19080a06050406080703 71
    0x146440c0d00c6c0e0301d50070081200000c04900160f000e500000140342d02a040619115031070000345070301c0d41801c59044440c025580d40204001d880b001031807d88081ca20350b200854a080f0640d81000d00005070a40c4500403400d041e02d41c80c2c10b02e002118182403000700c00741201c4080d95512240b504140c400d07000750038081d122542c4191201c2c04c1c1c05900d16103100400c62121000020024501d00010250a5035a20703032100d01903c0c58004240195101c03444500c0d800021007162010641c0d5a00c4c02810b040303095001402884140417000c43e0b440ca07000100411503010f80c003103030703a070341960b00045069030314904000f008000706010882c50140c0c4030081c0d1050049504000a0000902000c5060b25101c0481c0c0702c1507801004840c041c560034540e4641c0c00c940a45400d02400c1400c070342600d01e9404498995042682c000380340d6500c0d241d69010b1714401c00c40d451107241e070050342580c000c104000a0f541107107030038546000025945810302c18802101d0031310014104807803854603040140410b007100c1c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 958931699 1250 958930449 958930451
    0x7050c0307020307140f030c13050603030c1c112b020f100614060a02030a0503040c120303141311100c150204081c08060f010905121005101a0d 63
    0x410010781d028840c0a025000043c0c03461880c020b0402041b49010720074008078020b400c803000c000400d8440c850004014640c120020906484802c00700e450b51180750210f418134028003151030300d01c0b803800c0509031400c9090303582c060f0002104001141c5039911030780b502103520440c1d843c06000f0042c480008135403402c0f50054864000508040c10f080c1390107054851410b80c0c1c0e9407000d0040c424100241d00043c00c003a21140d0505809100180d0760744103118110b801e0140100004003000318140e0200040d01a59412107504426031070054082d1012503040f0100a0210b80061081501c100c0980b4080390441c00f07803a4204041018880001c074000786502c01c000c042850f0f2004076088900d0f400144907501030042c0e94518020f5a981044c3c92070705403003405460030121007074450340318030340c142c009078200e62480a1480ea40300503a00506180e0109801a8200c054018101c00100f2403048607014401c0c248015650103043c039200311400d005054400c0300d0248803003513a0014030060420010703102c00c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 958932949 1250 958931699 958931707
    0x29100201020d060608090d0309080a120209270f1e10080703030f12020306010815010c200f120718150e09011406060f0f1606050915010e07050c03 64
    0x282d0142642e800350403000100c2c07120303420f1080c89042000716450030004da180030804091181e64003461803040882c0c1504205030082803442c203132140c0d811120380f140014400c03131070511174040d28841480c626448204000070900000c0340c4000d5440854821840d4403140c605030300e618100c0c1d0544604c094241d003045c00c103100e0003103003401c02000104065030003034881b0110114148001030070074090f2646260140c0c014018008580d801050300c540100302041e40760a081c0401004903100303030810348041c0c80c0b200110100c29864442c3d03440340c00c000000b500d001d0b0b4014000390612000a444501e0110036601000301004080f50308036404400e585028400300d000c43c4c560841a65124a9403c044012680c4800f8848601c10174810225503001c010071b20f00c85841e2110004200b809030011520480500148003084585290308903141c16528a50790760b4000380b941002002040308480011075032251701e901c0313500701115174201030488403c14000e88407680c0b0a030007160660031401d00301985200c240 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 958934199 1250 958932949 958932967
    0x3120906021303081c14070e0f0d080310090603020612100f180507180504021e0f03060307060c0506070f120509100f1808090f0901080102040302042910020102 70
    0x30810055014200b41c1e511005c811810181039001c208000c0f422620300701418800d00e5540700029803003401c42c01c054002042d1500800c0d982110b0042c50f5a0206611070040e0030000000d001e140101c50744042a4441c50311851588101d420600020b58400414000009112505001d080e0300c00c038030503007003070389c003035130ba07107484080048580000c1d481504084848500c898148103095010310700740b414000b2204030903009042d040081c040d0318091500040d110402c804d4041c0211848403100d5440c0d6950b031080c010768803003500103507180717032090213021000150244500c8030002d0840c0c0042c09081262200074060f1140710a50490000388100c250100c03000b541180324a40c4203800b24000340c1807482c5107000b5802203415a10190310070790315081d02c0c805240805851315180960240046607507805180015400940044c0c2c159030214042001146a91040d0044d01c2141d20076101400100051004002012003034202a500458501841c20071031410882d20b420900950000514103c850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 958935449 1250 958934199 958934227
    0x91c110a0b0306030c1f14160609050c03010203061503061c0b0f01080d0f030b03030903070b0d05070e0f0f0f100e090105030d091a0d0609050105090907030312090602 73
    0x50344110100740303000c020080b803410144984640920300b02d41c01490560902ca28107008402c2044400c204025400d8070000c0f09070b403804a644c10440700080b10252003151a200d009003031076440840341405548102c10290034140240c82c0034540041104500c100c0a02c54481140c10051220b5400031307040d100d21150002c0c803442144400e00480c220300191030015580004a030b010f80c040d044642c00121101c800300e60002c280700c0700f06241d14020a0030404800000d10b0b6001b01101240e0501407000c1c00605840104010242410420002e10031980e510106840080055500540044500400302ca95281c0070104481c03140008011055880b03c910100d8000821000a880030813454200c009081c60104462401041300b140188985a0a1000105903a00904c1603107031200c500304025154071000d00c1a5000030300910010406181c1d113107900340c00350a081c81003500030140900402c4c1d4100012a1f41c0c07040d203806032a170b1520056200e000c2030060240510a6850a0f0700f8890460f8040b01 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 958936699 1250 958935449 958935469
    0x601050c12041d0f0c0d0e1e16230904020d0b09100605220e10020304050c04060902210a0e1b28030201120f05180d0302091c11 56
    0x3a4010306501007904a08908020344007920620325102d40307100300011441c5c0e03902152804003038040046240e154160305240b038135204d54885034040070034170706071a64260002124050074016124030700b19a0b640c2c0190558842d54000301c40c0c0703840024045481c0c5824480c50180e080f520151050b07507404141d4072002100d51043d80e0200c0250814a005020410030340038203406800111a04c06032810b140c3c441c0000742400101c401c402546a1101404c5c151050009421080110009550745d10749850115200c40d041204140710300e10780b90000c00c1c1d180c4280300b500c441c40c24108561180a2181152455105005000300c5805031164003d11030030409002c032124880107220030351801ca011004108140009802803802401c540c141e1026101210b0030140440e6020b0034106054030501c0d09400c05007001d116550a054100f605004400c5a04800b10050b0511002502c8188032440011002c1e032069040f015400084000e005e0441d204000300700220034420582d89820718100d1000c01d18100f8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 958937949 1250 958936699 958936709
    0xc0f0d090c060306140d050f030c01022101050303120603031905030a0614061611090f070915090b03130209010e04110405010308041502011d0a290601050c1204 70
    0x1485444500c100140450300310041c100c81c2c10306000c11410280da0155008204d0a95840307201181e04040501100340441d0460340c1c203a0007901da503046403100c641d02175803044040581c084403000c02070380003555500c105c030b050f250b004005d1890820813001c00e00101c040902504d6143c0000c015008202484002144400c80300d5180c4503140d01e841c0c0039140c12204c1303560002c04a1900d00b20040f0303ccc0d80da0b6000312010aa04048006480516410000d1003c88000c10a6400000c0300d814041e44d80b00c9440b03090b00c20314040c3c0d10182e07021703140c5c81d110804884440c4000040f5000e94000c0c00340038201c0000d03650050681c400f0320304449458001941c40e24080e4003959010150030240405c3c80620000c0486403d4143c030180030b0765241d60341d030012034803940c030806403800c201d0114045414400e40240901c840040d846241c040303050b07030f1041c4d11219144801c43e4443e88000f4850030002e0398040d030051010380800140c2c0f0903940c94006580d030382d0044400403218080d0951980f040ca1510300a032010700 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 958939199 1250 958937949 958937951
    0x209180a06030b06030606010e13020d06032f010e0424140901150f030507030b100e030f0613030c05030c060702030403031403310606090f0b0a0b0405090c0f0d 70
    0x791650508010b00c10024104d40c0c0070350060010000c1990300502c0b1b00d0031541c010780c0c2481201d02885801e00003405003018240c052030400000000f40b0200b83d91890a021440940c1012905c46034104034052810803080350200f0b03011400011245080e52180f02202c000b41803125030089803502c000000805a080502240d40c114050350031824980c1485000d1f1007030700c4030038404082c240d0380940a08418014542016107500010f80380c0d44c03090b0400744d043c4034051310041383c84c0450304016082044d242c44040c000c2c480c42040101c0c1f000001906401102e002c0940986604251801c481110300c4200580e01480200000b00000c0790800260784290302950281d078441d421490010802603040c03240c502260401c0c030601109212507158110075111401c400080300c07034880f0101c4050800f10f038000d0100e501e40440003454446c00c0d0081600d43c0003103842044030540e400200040e403442da0040c0720301d540d001d01c030510450410828650300040014199400d00445225201e0143d101c024014081 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 958940449 1250 958939199 958939211
    0x72c06030f0907151403070e0607050a02040b010905060d0c0309300c03080a09060608010903020303060a08210d0213030f02040608010618090f051e0709050402060d0209180a 76
    0x4a8400c0c04541d000c0d211110b911413400c1c5940100a2161502409096908000102040d40315008041c3c1000b8613601400c09926103020b400e20780c1d1249a180421b038016402c0c0b03514408158880e130244425220020720712410700a01d000004001c02080083c0001c0c580e0b00d804040c00701d1a2030005c0d4114204406100d15203c80c0440c201d010441c60520716414082a1121400000d8101241c0c50344011044800908104e1034140030b0003419190b4807030410795103011a9002416130220081d403190000360f03a2011b04696030420103941b01c0780a0001c00ba81085001e201e41000c0968000300941c03590084098285000184a400c803420168411102c5004011020045051074040d8800410070200200603252402c03050110440496080c89a10765841d14550100901b0554070341801d038200044850500c00c0403100c40c8001e0400c1644281881003c90009070304180d0b028140c49540d000d00014100a00205030320060f412509855600104264400c2c212403c000080c40c440c0550034804109 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 958941699 1250 958940449 958940461
    0x150807060f020109020a03022806020705030601151e120507030203010305010c11061801021201060203041e0501020c010503060f2e021506090c0f0c010c1106072c06030f 74
    0x201c461a0710403415641054851005a03864002c640102c0b5019510700110b2101c0b20130600041120030381c1035441c0f440c01c400100755680d0004401c01600c105030f0450b580340e600c3d00382c004440c803400040030001500700e8103002010341c291110041c0c0c007115803e0140a5001d0110b0300c01c184c4c1e20868062000a50120040060103424052000c20742c905e070034412601784052000b0303500c4207401040b103002d40c40103d000000081c070960440303039240d81e210000c000c9561900002502d9900500c5022441c03001003d00c03018451201000c003084a405030000c1c82d002c2c420300015241904010a4079034442103400f0100001d440743e0108142c403e001400c40c1c01041c040c84040300d20340180e40350100842d84402e07414422420006078454100c8000c440d081e51913510041d1403005840760340003c284002c004101c03c0085641500f02017511030640d00da031929503441d401850380c5c0e000104c441c8000641d0031806070340030040c409032165408143c0009800a0000d4074081804d41d03209880e04142c0c12000700800071 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 958942949 1250 958941699 958941707
    0x220806190b030c1c0615051207061b030e0319020108130b0a0b120a0308061e06070201030e0304090c0e040b100f030b1f051b010c02031b0115080706 65
    0xc481480e0810400c065078811010964038081043d0041c051146801d41c80d13900050003003056a2154810414000516400b450002001551007503c0c006d6548601000f41d140001c1380b01400d5803d40e80e03c4180362041d40003a51107401030038500b135051100f50880b00300241c4051090740c1d5076083c01c020081b190010340c80010f0416500400c8a100c08080b185a80000340c601d0130041d42004880c080890803020100010361001c5149501100501c900315031241050303000103d00344114400c440100740d40c190541050400756916480561040c000c0004070010360180e480b01f004c51110340c2c00c036406c0c00e45900c6240300301d40105602d5404540c0000c200311003440d042c050745092000076281c1a54100790203038040d000f802c3d030b50080806d03d9100e840c94101500ca021103111008444402c815051000d0440908103510840b4070103584a000b1b2907908083d40c050069a9000328940e000f103103004e410128181c0c001070b12120700704055403503a01108001102c811040013629622000d00310103482c242d0094 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 958944199 1250 958942949 958942981
    0x1109150f0402040b09130f0e060f0c040e0c0a03060308040b04050f0a0302010c0201260703020c0c04090203060a09030908030c03040f08010504110f1201090c050f03160b220806 77
    0xd01c0365004100621402c0c0031201620180d000030b5803a6441c030100c40d540c030343c0582615100184c1c0e040c40c0c08280c0e20004c0700002c019009082807451011030740c9030150411003510840c052405000a10310104004030100d000801ca600c80c039140c006203042d02c0365107400140e44540d01030401480d011034240441e1034000010b010030705049412078119440c5a0000e00b4031405450702030f040c03002c11001010b020b020700e0108169142c0026107041e05140103540070700290059120402c0c1072050000440c4942020710800c3d00e1315030018024801c0755502c04540d0040c0c042c0820890800c816144001070000080014095050051016603100c0e402d14803c80c4149009034000d4005078188410300001c104640c0140ca41b6400503541030340c59920190104c5c2c01d07110300c2d2501000c40d41ca004c002c1018415441078040980d01c2c00c0764008100001c9804066079240d0072034200160380c040c030400b0040002c00c50020600349207140c4115402d408140c07842610340b60540d03c02040354111400b0001c124820030045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 958945449 1250 958944199 958944229
    0x906010e1e0726011a1c060803130b18090703060306050108072d0b2b0f111c05041406010b1201060f0e010c03030b060c0a02031203091504110915 64
    0x1124558900904c0002c2003081070032041c9442800103040006c1458503c03580700c10a0103190a008255540c000a0f81d00c2e400751007000d9a8200e4a1404500916090120b8211410a8010074078140400d02000800c1b10060050014565540c0300040015a54003415000700388610141607558681640c100c200021805a0102000203040c9810403400361215142558881500641c894442e603054050300b81e42c010400780080407200014944c0307138440c1c0103041230303002d0494103106805240400ec4528001c1c403200c4406444078000c52801e10580c4c0e880503610502480c21890342e5808040c600c0d003040800e030130200c650b901c0016164592046108518010b20040c40e1031002d09484043c0100085940d0380c940f030401881d0215002494480c4c2c1004000f404010700303069640058054142c0c5d1404500c40403800b034019240f14192081e0348200b0390348541c0ea04006000c0e0b5070402c4c411400c1c0b2201c0104115810251649911220b0700c42c40139261040c2c1c811032101030240b06507402c001c0034009605030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 958946699 1250 958945449 958945517
    0x409050c1e0a171e0c041a0d020121060b030411190e040c15030e010509150f180a08120f100618080a06020915030906010e1e07 56
    0x9401d840e210b9042d0003088030401640c1c0840d2541c0c00d25014108900c168254080c921003200050600e100420300c1004240101d90401040700c0d510145051410205104d0f5030264074403400d4800340d4002c0c001a0300201e01c0c3d000034809580100199000c5658a0f00054004503010040108200d05410004c01c1804102c0350039105002c01c0044d040f12100600803403401103000c401103410440c00d42d00400203040402141c52941240540081c010030304480080310795070a10000c50154000400c0042500d020f0710000901c6070754003480002c4003000603000e998404207071034200c0d2240d41c05002c0c0c154241d2003070b6801703a03489003150743c00861000c026290004004072001800542403140c0e6031002110359904140906901440d50700b04260f100b0351211000b802a895244200100341d402450101e2040f01c4461096015007502c1c10305020071104c070840c9901403030046c4a48074201101a40c0004400c50030b10b908201c0402c03200c0b03070000c00d036040c00200310360007129402100c100b030340d112400d091300c81 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 958947949 1250 958946699 958946749
    0x90b07020303070228171b2404080a0c0906060305091c0908030304050a0314070503040501230c01140903070b0610090b07030e0112020712120b0409050c 67
    0x25102d1280c1c15000380b04071140c0d02014402d400701503512150084410084c0f600582c2c8640040c504106d400b11004103000e14240f0001000e201c00c1c65000b0804090450202244801e2840000821b9410008101001440001001041044403640d202d1048101841c142e02d41a503420654150350032540906090804010310b00f90000f441003c0d41c1010042d500c10f81c001c1001c1660148400d801100c0a400008200024040b0024166034140c1c0b10769240c50201d48514620300250003840d60040c00707608100000c1000c1c0d807107070b0070103e82c11010780444a40d00f508040d0b0f0100c2984100310543c001d94450b02c800b09810120000240d2081002010318642100d81d6078101e000b6000038440c602c11a205031407581d1a500c5411982c0203801ca030740702541e03151407600f0054060645843c407540000c600c1c0d00100282d0505000b510b001644c000a04104e25004080503518289040c0000994960b6112080f14070b80c1c0b28003d080c0b03c940107a0142c082070b60b81605220f000501b140c881150a88050 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 958949199 1250 958947949 958947953
    0xc120a0c0314210c0c010603051b0907050a14390705060d051b030408130f030c150c02030d0c0c0b030903070f170d06060813120c1b0e07090b07 63
    0x3a010315007a800900c03ca0303550f82e0700e40c200581e5014940c0021250341c03030901c1c08000c200000403010b07100c01c1c00d40c038400c20b01c407a240100b0622040c101c0d45d200004205001804c2404d0040c8640c00340c090007040110b0600c1d46201400d82d44c142c0c00c05941d8074002c1c184000c28444544241d075864000f580d64080c1c01203d0a100202d0281d110f83c1d003c01e880349a650000440c4c072004042540c8101c2d0b10900e070203a503414141401a032503004030041c401340c54005600050031a810425060072282d02039000c0c5025460300c03100070404e40000d010041404419803400006982c01c5c864940392480688566020b01602d041c070390014152030300400440303d020810f01441140000969581960207a85a00c0d181814907000f420745504150803800300301c01042c44044a042904210103a40041e681d415803a901c0c0b03500b080c100088124040c1404810b141c01800f070138414164a03030000d01403981c0440c24015009000786540d480d9025070489207c81051210856124100200604000c500681801125 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 958950449 1250 958949199 958949227
    0xa1101120b09130305070219030b07170705090d0c1701060b160f03021203040804030b0601020a020a090507020705090a0c09050a140402090d0209130519030804080c120a0c0314 77
    0x9810f03501d4071001d10101c0f608040c4244110303511554042c00035400c2e149013014051071001e07240002c83d8400307040303400921654410350b00d02c0244a101c21003065281c03201c010070b540b6603000f060a142c00000920900c000300d03088120301002068411102c104030340e001804a42101c2a81d00101d031022000c00c580220002038102c2000340c0ca811035661040d400407440c0036844e00005c0c07005543c0c0500084200424400940c000d4411039000303411056a6541c1c481c012620303458031040007940211600740a00c01c026450340007036402030850040715030403034a036070010b203014a0840342e0200b09901d800c0810407456000c0c1c20300d801071205580c0320f9201c07030034521500e140c0c02d00011a00e0080f030340404c03480c4d0f0a507100171040c0c00642c1c01a20340c3d045810011140e060245988000741d509210302810350118583c51805403c07e07a40590b42c40d1255110340d0380d00d012981c0b0000e09032010317100c0c81d804411840c00c200d008003110303040754544020640e180d20b0040c1c1124400203214003908014000013484884d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 958951699 1250 958950449 958950451
    0x9031806030e061618090c180605070f11130e0f070b0a03151a090f090c090405040602130e040311070e0c09040906050c040612060803091c050a1101120b09 68
    0x3400c1c0c54524413030b0001c804c0300d00302d440c0c010700c0038000c02d8a000019280e58503842106400c2c1c1f01c3d6903904c0c010701c140e1040300c0285203074450103000440030010b00b000308e000046d0244040784030316075101040305107c0c0003c80e102000c03054902100d94425902c81d24100402002d41e01c94500005098010724001c6c40301c1e510701401d011007050640328100d99007501055104100640b114015525480040c4488018541c00607408035006001c810003c076403a1a1928007184544800c1502c5490501d0810610000d08000b5000b00c890903020301030b032180b080c01c1404180140400300301c203d41c141390904005107210011002c1c6031068005080503c01f001d110750b119a4400c0a45410075980d54580b00480c0007401002e02c041c184500c2e16060000b8503032170308010400c030f038090354500d50032214042c101400c0710b545114200459004000460306405d150a640800f01d0605140b40010801e0b0f4503650305002d58181c0845422a203e150084190b07008082c0400b0440004000c00881e0300da140440c04c6800c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 958952949 1250 958951699 958951711
    0xb0903070f140112110d060e071812050316050f0d050c06151306030308090106140d022e0314071b0209060d14060412170c1c09031806030e06 62
    0x11901002c2402041900314040c4000191701c03080d41e516086001c03d004283c0d90145402214103040803800c2c440c800c40301c4260758030390000842000c602c2d005520940804440c01103d00740010711544444080075840120143d0160011300100b090300b070552030810400d0b803030740d0050101c1405214020702c0001007869010b4454019203a0b100c107803c0001341074400c0c10781001101400e00c400841015444401e00d4001d1f14114000d011990b00c0321a018101442c941000340c004420342028000340c50070100e040300b05d42d5500c40034003041c040548010400560060400d020a407140d044201d018100003129a000c06240750080407007043c08000884880d0010006e031042c0380c94400708595580310122117110545c000300100414201214003034440d001240c00b6140b1710010008001702c103005492106024081070780701041d540d00d552080317101c0d40040544040054172000c10303035000d0b40300d44100b840550180d12088a640c001c000c0450400302c842d08840d0415080100c2d010f0b0191000490300e030019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 958954199 1250 958952949 958952957
    0x103081204080d02030a0c03231b090303070c060e0906130c05161a060402030c030c0304050c040c0815121e010b04150602070f150509040b0a0b0903070f1401 69
    0x80c07907904203402a401a24085001e140c4004107000442050307900401e040c8159440038001100310803544060080e11100c1507407004c1c811310004440d0381640d60407035101303010001d885d0700300207402c0c02082c43c541201004888850380c89009100464001101e262081400c41d070410403841c1680200d2412181e1228865840b034503017084015480c020300594080801d0310030701e4455040c0c14200610240421200307015a4802e4801041c094105402242e2040303002074000303451612340890f103682581c0300400a07100d600407451848000c0c4d0300c0c0d0056202e80304c0705945000c89400c14000b10304420055804c07040c07103880c10140c2c503841d540010642c8184006810034000c04080706151890242208003040e03a4400e18050140c06041300c4100790a040d05c0340c6900f00c50103146c03141000e9486480c0e60240003602003e0104240d5064403810040c440c07058043c1c4041745010065021810b465050b41206401000109100c06141000c00c5070b41c0042161032040c16a603450f0440758034102c400850414104 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 958955449 1250 958954199 958954201
    0x10b181912020312030c0918040b010510110703060b090601020d0e1309050111040305150403200a05070806060102210f0318060906040605070e0f0103020d0e0601120b0f01030812 78
    0x140d0f806118900c5400c040301403407580c80c6020941100b09900250284e88207101e1030b080a10010348503000d07544100c0e80030f2100c2c2d00c3c503428001000501d0080c0d101c114100801100c0c070000d911000d00c0003000540c8a21808542241c44030208045c28400a2026046600010303058600700d40c00b1103203c5005606903200850001901141c0024200e800300c080d00c0c960804100d0340c120003c1c80000c00442e801001901d110100440e0290150b0384240c80117400550140141c1c0e4a4055000e1103850341d6104400301c1d81170100b15070b59142810300c03070303800302c00ca0385c01243c10085a560140b004000a04010000780040901c2300b030586218011450f01721980391011000032210111448041c00455542e01100c5886c134111100540d01d4600b210308a600701c0c1040003040146000740c41c510381790f0320000c10103c1d00c0c01903c00114001d4001e240c001462a0f110f6905000c2d094007441024042c00740084581d0b404903507410b00c00e0390090013074171200b03520881d81c00400105401e8015200c203140004003c05c52 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 958956699 1250 958955449 958955453
    0xb070e01020a02030a0c0915241e0e0a060512010e061c0c05010e0904112e080603011104080601030809030709111201060905010c0b090a0b010b181912 66
    0x1030010b84020080d0584108050b680038480845465011249202c000f8051660100b40c001c007010510300c140c26114403c400340c0043e450710141c412202040d5440d20141000d08416001e21508030103034030001045400c2c201c0c48241c00d18520385805041c080c10319600c2e017140b6110340d0721010414403076040c01002e401e0102e2556907984846201800301c56000c411079a03204e0230500d03d21690f0f4407420b2301040c800440342c403507810000080d520541e0444c215106855a910501501e121801c1c260303080000b4440b20081280d1003084010211911036aa40030249010b81c00d05003102c010710320b44e50040d9000c0c402003084010004040e410740c0d5010003010346408864010030b01c0c103052a080401058100500c41d85c801c440c49010b004019861010800e259a0b140019151403c881c02803c0c0001c1c2075001d00030100c0e2006030201d8011591360201c0d9421206038403800d011000a800c408550b110004e86010046011800d407000500100c40c4142d400c90440d40a0b01340302040d1107444110301030a0202d43c1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 958957949 1250 958956699 958956703
    0xa051605030906040602100b0a060c0609140d03022502030c0d0302010905030f09041407080c07050a0b0f090d02151b0c01050106200105010b07080f0d020c0d1106040b070e0102 77
    0x2e4548090022919251075405c0a515840c040050a0f85d491030001c0500c03a03458a600300383c08031903036602c8914202c6480e80343c0d1005000401800d491840d044145101d00050400664101d03a81c1d03503400685074041d15190f1010038001d25014130440803010300200143c3d40224844052540807123842944000034034099002d060010303009400c0307000200d100d80c04e85824000070310f122002141e003000400701d9190180f00d11b21044e65000005811000016940601c440041001034019811540001c000303540c1c00c102d8610803540300780d02c03410004c180480c506080108454100c028000b030080403000b9120f1207141040140105201e10804c80d02d0450001c1060486150040780c100a110303c3d170b10761101800d0074841c28113180340d01a000a90710b40b05c010600c81d00c0d042c0c800807114145031174010388980c42940c1001e10041c020701030411449054600c1e900c02414803106420180c0380d07424444c000640203400c03002581009400032010080044e25944269074041d20314240522041c4011004074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 958959199 1250 958957949 958957957
    0x6040c12020408060609010b0a020c040c0c020405010902040626070513050301051e1b04090207020103140403120c050414131d03130503010209030a0303090510020d0b090c0a05160503 80
    0x140d1480010003160b590f20118090384200000d98080c0c0d010390b130320582c0e030150340704414100006801a51020145203405d400c4459180900d24003031213301d440e6000a412a035082c0d010311002a80002d04110194201056200c480032056a480c0c1d601100701740244c184000500d150200640040c040c6040d0311500218070240c60050700030445c9150149800e00300000c0485152901010480044d0075005c5c000004048240901d1405042034500048800a9080850224181921800c200c0d080c444103540a610407402551a0745c2e900e481044c0c00c10482d200700b02408108282007005021112041e11202c40104094074426005040e02e2941c00003829251031105802400c0a054250142c0000251899030a907142a10001c1c1e682c7c82010708034866a040190140c200000c007002217406a030107610807a016105590b2030320302001411049034045240100c20560301c01d1480c0c80350410341007040e44843c800d0841c41c6002003c8a0250181c0038034204c25108507284600c0108000040c01a6 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 958960449 1250 958959199 958959227
    0xa0303032d0b03010b1906050706110f1809160c06200d050f01060e0603071b150b09060a090905210415020a02011d0d0507090b0307140906040c 63
    0x31032001c0210800c4401a000518290303100b98284074810201d031034403500c840e202c4155824103048613890810151029004000c0590f00150742c2c0440c440120605030080c18203610781590683d98101d41c100404811800e5400580990400740420807051030400200050020030305101d10015111714000300602140c84c501c0002500a0b03401840c5100e1440150540c001c210805001c107a07995095621859400d22501c0000340c0f00c9a1840c0235410500c00071504401a4500032841101909030640301b100f00040c00c51700d913100780b45000a066507910a40840c00011520a140d504014000400352a90f9005188d42640d9039540c500c10407604200d07194480b620707007003081381202c4c13001c1d45010f65070040c2c0b00306400d02e441006406012840400d03507081981c1d058407070909034151401031001000c400f038200782d00001000864400700da02007008000030020050081500d180c00c80500d403d0003495804210001d0540a00306150350320107c040354054400e03900001c4218103128119251521031001e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 958961699 1250 958960449 958960511
    0x12031605030d180c03030c0f120c1a06010e100323040203060705190e0d0206070c03060c091211010207170105040506160c0b042a0f0b090a030303 64
    0x228104200020000d03000b0344103880c1080081c050907618026401c149480c1c010500000540d040c00040d0289507141e205034003800b1108984400380e81c9019411560f084c013640401e07000c0c0c0c51007040101c1507182c2c01d03d904041d90390085504042d00040c02e070b112403440301d03885004912078011045c1d100352702c0a5500000c050022011301c1c0600f140380745c6000d05550682c064026580040c1700c0c64010000c580c0201e81203070741d00c20500c460074001c880792003501c40c505500c034100c0c0c041c0002694469026140e0f9030301482d0308000da5891490600121074185000100303002d03035078900b004200e042185c14200e054000410031400780b1f08400403414014a5044900c40d0120200742c0034074881705501c1240308911550880303010b5221103144204240c0801d8580c030000340440049000a080310300c0003070b0880e03c01c51140761030b0182c035a2040100500c0050155514000c11810000520401c2c46d1a000b4600c24081c0781c47c2803031100c081165000d403804003074240358452a80c59002002144c0d030302036042480e08 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 958962949 1250 958961699 958961737
    0xa0920011e1e0908060f09011d0f0c1509090901180521040b0301140d020916090b07020a031b08030703120c140d1d0d080708011208091203 61
    0x7424000c050102c40040a62030290790720b2070b074042c3e1101c0f03040c0d490140041c005940da51014078114180208420500e5407134140c0119444a0807000c15211f40c031810240181100c0501d0301032030b0942c0032500c13920911210541281405114089039000c2109943d02080340d601e250b50f0601403c95104200201a070b08401d800034401c2c0803540d0510540f01c000c25104000501c402d0000c80e0056000340300001030104010410f004141204500c6041d01070000c0c000d40f01650006074801d0070480d24640785921102000a0403644462488040d059a8001506182580d00481d95002460100401c40040003001d0140c0010b40d40617580205121822a59510031500d00201280e0810703290310000e604107003442c4911070107250b82c0407806500c0307010182080c007440030308009802303003a0345400503422003070500d581c403c024040c8000340f4072140c580c42d80c2428166070052682405901001800801c41413203000101403108840c3c03100811220701d05000207200b04c050035407050134102e240c12840c00e1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 958964199 1250 958962949 958963007
    0xc0509070c020108010e070f0f030f1d0c0d050c090711070b120901020316080c270a0b030c030103032d08010602120703020303132f0301050a092001 65
    0x701c80301580078400c0e0703182d0b001640d99006400d00480140d5031140410300048042e2422441075080481c1d405092a000c42c6510442500004445001003040410340700888a01d00000301004a24080d00c1c058078403a29000c026140d040e252440d03005041e102d01c450310082080d040c4581e0004410b03500708400d68001035980d284010b0039a02128420152990032000034030a6101071090300c0c0b16032048d07003c001c0e8425001004a5000d1001081030050203420f04c02c21031180f0f034103c20601540701c1c032100c1100c000480380400c80f07900496888240100c0d0100200018201038205490440790b0504018000505113a910410f0389401001c524405444900b4191709a50152910341210019001c0d145c0003401c11900c131849105030070021b00564000c0020403902441e912642d001c180c001e2a41e201e1405440703450001410300014541e602c1410b03002402c20504d001e200f942e800c40c0714868104803202e10cd0361105246021160280c204a0200d80e003803846034005d44850000c18918103040c07403400c0c024 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 958965449 1250 958964199 958964207
    0x40f090203072d26010f0f0207060e032b021c1d030f04180608010e0d021236040612030216060203040e0901060b070c0303030e06060a09090c050907 65
    0x10125408001c00c1d0070303600c40d03002440600d2000a6510108410900001d50420412a14820403130080c00d50358407240e07124040700500c03c0031907208103204051780d503054505002058841c0c452000c861030b041042540000490004089599003680c405001e4100390007554000a01a414440601c0f000010080600000e603034000c50154900111440c0c40b0b51500e032a60380c0c0ca02600c1d25541c3c14040410080c45801c03601005c404603000d184c3c1c80071401c951030703130750307150969514107400101c65010500d41e5010580500420051903c2008114200014585004200b1546c4400d00384400d0f6104120b0a481a805400015100001d08140281941c03213103d0810250038810640050040030130300c20f420000840b2001c200c82650340194242428a00c3e051680301025003210407541d078038240028ac0e5811800030b03101143c018080c80c003003a450342c100a8180d40d08803601b41c1582e006082003004ca44d50f40d484800c10784e081200c001402c1084d911b00850000713010741245510010140c03c1080c42a40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 958966699 1250 958965449 958965479
    0xa0c05121c05150f0f030106030c060816020a0c0b0705010209040e07050319020307031e050a12090b0a020601030b18030408032203050604080703030207140d02010c0509030c040f09020307 82
    0x8011000c0042d5900c6400c03c42002064503021076018018803400700d910324010702403000c0c0d070100a0000030195500d6540200070720075035101c80049170150301006607004040b5501420f41101e40090541c00f0143d6845450320401030040343c1900f800071400100303201d42513040d246082009030040281030082201c641c1d80700ca0a101e41072007485032400f605034980c000107020050796800f600a116650456480c105600c1f00c141283e14008801d041c4500462000c1050354009402500500c0442000c0180100185203d400c03040d040c40003040007040440c1d001a41c241101c0d0441d610001039110070800c406055402d4030b49070340600c004240462042000f0000340005400c4800144111120071103103121000075100140081d040100050081280764008051076072081c9001440e0407200d03510302014031180d06954845d0780c840351100d40110707024170404442d140329052042c1005034400002e50364207400c5035901e00440e114013401c920702c00f6035008602c0345913000341030321b0809490700020042c00ba8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 958967949 1250 958966699 958966747
    0x106080c0d020a0504270e0a0b0621030f09041406011e050f04090501051009030203070b090312030403020f060f010f090e07081c1403160c1b0f17060c0a0c0512 70
    0x128255981c0141c50000230b03806c3d000c5a000d0f412146540e1108204201e02540d4a00c50500401c42851500e50700001c1c0000d1458400383c40380740c3e0700c8500001c00d12003100c00c07101070351074105a80030510041ea0b801131242c80c20b8820428005065641801003100d003801900000141b00b40c0101e0301003030341c404541225040e80c4099954171082c144400044446415511001e905500184000d015043c0e990b03004100c1001d014088400c0c031090315081c24115403080303070240c006802a0f0b11b96050480e05101480d00301d01a070894054550400c1005900300c84688941c2d50415a641008010743c0740a100c150000c144071800d0760880c840f80d68501c201e4040030310710080002d041401400008803690103403409441c00510110701d00303503002d409582c4032a50580075104440b265510310f0315a48040500d5000d0000e4809011280c1c0c0751155034040c1c51256140d40c0f025070030040c100041c00c58058152015111980b815011049030390421038200a0714080c610124500000c40f803019180508095400354 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 958969199 1250 958967949 958967951
    0xb040b06012a140109080a0c050109021801051003050c181302070c05101d010e01050909160e062503091a03011a0c0a081e1605060106080c0d020a050427 67
    0x180300c8420f5007200c0c42c0e03d40081c0300030700a210072111148a0040110018450400050710280c00e80010302d1001000000909122a6000507c540e04183c20340c00220341440c14184150b05040340c0700708a03409550030241c4412400c1c1007080c250b50780d8200c98100c00032090b07011591041e40d41440c1c101e914041c01058000c440d45940e0000c0c2034403642e000c40d40d000806884c403207110100340046a8040385284007504014083c80060150313a0340c40c0b0b20a00984112086004c0d00840c880d0152800790070440702c5101d66820710040102008801c5402041500a644502d015a003454140d036010404c1e0030008041c402c01c0340e20380307615007a0350095040e10000042c00f1041e01901c0184075003840f40103100300d806c2d0020000c11000514400243c0703030588403071b42c0c0007140401d8a901e491031074005020940700080d0440480303080c880c050011502500c05803500701c04510b802c4445a8103403180d51804210581c0c005403040c01170341300b142030790003414510100003039014807130321110384103212220122505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 958970449 1250 958969199 958969223
    0x509130e1501030b070806040f0f1b180e060303070c0609030b06040621030201110a020705090f130b0a0b09011412010203150f040603050123130b040b06012a 69
    0x12070036000025048079445000158140c0c3c4000044941c0349001d0681074015071182641c809c0c2c5915401414648507002e000080d6010a50046c44105001d43c0c0400040c083d0074680000c0741034203000c01e0016208040001d103000e8881e400401c1c036500c030300c08028280102001c0d01154181c0e01c00c07801811a40292440d04068035a0420041115014070600000070701e0401070041d02d40c0c1001d036080c0c01d28064000081d0501c40403906141542c010040a00140c000c54814052441c1c1440b0407900301600142524103445c0c03079600002c110b102a18058080540b800c00108100a1900142e0509a0140100c01e443d699070309101d4101030001130380d5218000003005060210300510940e07208000c014a00c40806480381c0038007907184142d0744c1c80c641040c0c5070240400030400034001c3e051103111049035102d078118600c00c00080890040c2c00e19000c01c095400d0800403480595910780c0160308001c0c2501d00781c5030140103981c0ca003264034960303541c0d52402109101ea16481d103000e40080d070003600c524402c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 958971699 1250 958970449 958970473
    0x6070c0e0105101e020c130e01180803041704030203010609050402010324121a01080724120b06070b0c0a32130911130815010e070509130e 61
    0x20301da80301c070000c80018581240c0c904c003c08801101c281800e0f043d0042c0ea07804010031340400d01c010042d40b4201011a143c4090740c00707140013407092070030362520950842281d10a0756a400b2040c4005007003e4012205c2d88210810700a481086900455004000300304256544405401a03c0b0484040e1301103460215801c0480c40312604030391aa006000300a143c0b14101210001e580f03440c240b06031207584c02c0150300100c10258a207003501a007610ba00074201c03907107014000320180044c0711200303203107070b4103403e42c0c030205500000c01c1c40200002d4500401c0e140c2c45d01c0c0c04121140200040a0004100030092000e00d104000c002d042800d803d6031503140019002e191030039121101e003450100801d2030041d0100a4010a01034007148035264051031381c150352102c24009035000420f0303460054800051180307200100404650043c011076001d070018400d540310400103414148580c84006050b080012441c922800841c2e500402c0281403241c0c1c41c0c010300c40880108030aa5030000310b0311515500d185 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 958972949 1250 958971699 958971709
    0x1b09020c0c0f0121051b070b1503030703050f071e0c030b010f051311070c03050303010620060a3b061005031b0d080307080405010c05091806060906070c0e0105 70
    0x1d004082c601d8610000100080c03444c005250052507080103e64441802165000d02001060018001c6050003103d051164821320702c03102200206220390b0041082e000025088429a0440c0003a010350340d03141d0a8609020003030720686901c9800502c01c01020008120100208a003564082c08000a007680c940c00700b0303c01c42d8058010340b5804449820f00950204454000c60701840920070b40904124040d50354403003044181e0022039140c0c00100041c04950382c005d03480c050302441c0c082d50740d0049031780c004141d841f4240a003003120107a0300e40f0700d00c4000c0d200310b290120450a03400030812425100c040d0494000c100503038190b4841c001c0d540410300c604403075602d07141950b000a0141070031008491070315101d85982c504642c7c004024801030310200e40c5404c00395100358943c1d242c01e00c55260619142d400c441c103566130030041c000180701195050f11034840b82c840101c40c914030124507859090014400d400744030b030110740c45000058031408000c6400403d00444119044890480e601d07281006 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 958974199 1250 958972949 958972967
    0x30b090609030a090b07020d0b090a03080702010612020111011b05091504050114031305030d0209090f090309060a090e010f0503100b130507030207140309010215040c031b09020c0c0f01 81
    0x300010340242814041411700c40001d0050038030003410143c1e050115a220000e04200321061445500024514814150086199a44104184000c200c16800d10042c104603044508001c3d040110756066043c0c62003003548103450160b107611400040b00480d103002805544900c4c001030103120706106003ca2181441c0958085e220140c40da00c00d07440003010441c156410051614002626070456403000c14014030090003341e42c0507030302507038443d004814442260005810154000c1500c2c00700105a0804016250721080032030f01165910031746101200c030182107030810744039102100e000140007017a49070058101da50950a60394030010002284003100c01041055030410003003082c901d8021a903a210582c00141410010f040c60b10a8a03140700806500b0000720340d41d800003511904660b010070414036054460f02c0b805589180943c0c580301e0407000ca1000400040c07000c004030820905425842c030140c402000c0c02c42d1030301040140c42c0d1369a555102410b000d03112041040819502c1500c650b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 958975449 1250 958974199 958974217
    0x11d040812070c0f0302010c1706031b010509030f1501060215010302012001150f1413090519150513021e01121109091e01030f050c0a030b09060903 65
    0x19820000300c80d00c0c0c0400390074001c0c90390041108203003608001031440901c2c100d55501990000460868480c0090405010142c030314400c0e4001d24200011550002841c0f40e20500d004025140c0445110040c0d405024803e400f80d8140a105407265040c2400905911a40c40407040110f4690381c0d4501607895008142d007800114000d580144007550040810345640c0600d21040349214803044280e508640000a5030b4142c192641c030708004111001400c14045c2081074446402010640b0004140b4030310502d40ba00c0285d2590304203c01c3c400103100300ca450ba124591511918109450a00003c0c44d00103510b041451400c00419006039030400000c0d441070340035042d14840c1c0000b00b0006142c65888841c0b03410070600b900d0b031030000d08842c0580c4191021100419480b45010010468403400003840382c01c0c0000e20007610261102110642411290810031014140059050807030170540c1c0300a015400803821036000042000002e4081d1054200405540c120f4444034019910b0b44164450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 958976699 1250 958975449 958975463
    0x90a05090706050a090306060603051503030306030a110f0d0803070224010902070507151106060d0305030415020403061404060b010216140303130b1e0705060f041109040b011d04 78
    0x1051069500030401000400014148150102c6e603d079206001d80e5107a42080d8002915102404441100c1110300d05c04408118061400d51400b8400700742d0343e142d4194064400c541e0303607451100940715902d4a9450b07010281500075500c0f943d0601d09059070007030384e001e001842498850b004840703400e0000c101081c283c1200c03440c1d3f0303441e083c10301d0042c0d04104002d40c1c1e6806086c0f07000949103c8900000e040781040d84811601d0300c09582d920341403820091440780211088a4500f0000341c1c0701c2d0440783d03c40d0b406864008005543c0400f00024025504014a482c3ca80f102c10154001c410f19694400e07807066000303004404002c00120784840f00070120b2001310140e00410320526140d101c11404a29010b02100c1c180312042440c00e400100560120340210400601c840e20f40700c41944e485400e2141000c07151904109030354490b0344003001022801c0c0d00190301c01141c10002400d16540010740d0091280b40c03603003002d04203030613122000c1c4038002e85544442442e0740502740c4a00741078031807078200e40 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 958977949 1250 958976699 958976713
    0xc050a08131e06020d0905240c0d020f07170702040e0f0a0816080f0a1e05070b0613052419050d0201020708070b190302040302060702150c010e0c090a0509 68
    0x4040c0030b40c595814000c0b41c085800f4008034002c01128410000c080c0c0c01100140b4981004a9500c501c42c2d030500b5001f000003802800b0401c0b00e1800600f1100303980301d00e08005a891100d40c802030018020140c2c014161001245030b40307078007205c50010707003031150085074200050b08440e580540e582e8070484608540fa009201c8000104441c9005009506070300166400d24103856a5000c521358002279556240b02c3c400700c2c1c1380f9101503210b1a100c40c6180b103086500c0d140c080101020341140244000144058840000201d0130340700c0006c1405014070f000414003540c14146060b100d54005014024403480b0024103500c940e180180820780e403040c81078204020281000103104140454030b4041c1e040d4443d00c54001001c04081000310010002c070740c8075035105c08a86100d12022625403541030209070040c4070030320259030b6030006c80c1e224903811141800c0390039003042585030f0760060383d5018040c1d5133008034040c14000c010400c021003031400c03502c40a01c0e5464a540c04211201a00c446050f540408 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 958979199 1250 958977949 958977983
    0x20717030d1b231c140a0b09011514030a0c0f02010c0903060506120f0703120f0f0e040b1f080a05130201050a020c0405070c02030606031507050d020d0c050a0813 71
    0x500d01203042a8200000741c40c00d161010f40c1ca00c04014495100301c0c1590307030345c080940440400451500b00c00c02d60428000b40340c25000040d4400010f000380703094003005007400c0d402127000702c16118401200100c0b890b05da02d855001e0000510b003020003a4040f582120a1502440c418070848945116035152180b05a00310b840312001044000c00103a04040c2044200d81c8031102081541c41500301314006048850442c40c00300d0422078241e030340b1030034070180b10318a0340300e107070001840040702d0107518110021410a5000801030070712540307115040b94a000c1d610f607060170b00e48003640d1090701d0303503c1d808556110142107a0440f04110b5012043c0d50003120614010742c4070f08018140c9200c03510458103203801400020341107030010382d05000490807034114181141018800c0c6548203a04401910f61282503141c404079144000340701d1410001c3c0005d01c0500b104255064071a021680301c000c201e80b00c2200d1000e01603900c81c940d2100800c0c0010002880040c010300d07200860342c0e0200d03201d0710030060300c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 958980449 1250 958979199 958979237
    0x4030804050114060a21062a1d0607030c020907021c09030c0312090905010e011412100c0207030501020f030919110402071401050f0f0604020a02070312020717030d1b 73
    0x52807070f451b141c0d01d82010300404035117140a44e8020000e04a62404015800b070016441403203000f10309400d0001c40e003264403155001e1b11005d102414141c0320941e41e90110310742100c0060300d0107002580a0080342c248808550700141030340049054100d0b80c3c1012145010a030307040003041c80010000e20803007000740005200ca10540504c4500f600f800c0c20001c0c0c6801001c01039403001d8200325620320155004000c40180c5500a545285055a17031803500a610424135807100003d0100300c0015480d0381203000400d1003001040021900800210344038001403841d0780203584103640d81c030390302c4c81940d08442c1d040702850810740109600051803a07107060700d0b005110294101090581e590002094480c0d07a80d0000e008003445001d0314403106c241450080300c180201c2c1406444180902d00c1801441065a0001164002e1701d80010010300707001c0d5123200c00c0b8a0b04030356420610200003050511040141d00002800c0c0c00002c0b001d0900c03450807040300c038040301d036840b8013101d00040c91010207400040751 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 958981699 1250 958980449 958980479
    0x3150f1b110f0601091a030d0302070204061a0313030522090501051f0827010f1d0d08190212180a08090405090703050105091506030c010509010f020a020904030804050114060a 77
    0xb1400c0e01c0b8000e14550000e41000c00e807088c1c81c004242c0000b03000c01107241c644070700809400c180d0302d04c1030714200d03a00c954a12404001c0581c0c03201c108241c4c044050500a90949140c5201070400001a14025070001c1c5180a540306e2101041c0c101000804d03036142c0261511b4410b1107a802010040d00c031800f0449071048050705851803a40d245551000e0108034505901c0f241d1242c0c000402e5103103000a81004440550903184d100b0350f40075074500d864074004145036154010794030741030909803661200e241e02c5500080143d130f20030340b00149074038017149c41400c014800c50702c0c484408a1044050401612000f80354401440c2440401c561101132034242c0c08030360060a8502107400c2c0d04d0f22591080d003181e4051f00c4424944c1e00410f41400030381c0b5041703010703540981c0a42c042c14000c2c0d00c010010700540031701c0704014141b00d100f04a4050181c0300304681a0899001000c02c0c01c00d003068180a46060380556007907440b94200051824407850130404c080c000e8002410744548030740750044c90f10103021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 958982949 1250 958981699 958981721
    0x1090210180b0a08010602060a050105010504061d0d0b01080f031c09030c050609030c010b0a050a0303080612070323010203130201080603010f06090e0c0d080403150f1b110f060109 79
    0x8007080100c0d0001090000d0410b458250729042c0c115418002d010703280001c01000484d000d030500c070050283ea43d1050a4400301c0ea00d6081c480311030400352903100302028800182070f40090840d0000c005001d03e1a041c541200e000c00c00740c41900140d6840c0c1516807003034803280107011006483c2590321818a500821606000780b0f41202e01038580d035541400c0c9081652908031a900206605200902c03c0c03181c034280110803200d01409518000202e0220327180c520000d414000408005051500e818650144c504000c070251070019480340b50548407003490700440342100400c50394200503030b10140700300d9000e940c1c40702545065240a034011110584020010758241d521b40e100365012000c01e0140c00080d200698000c18941000700c04145010200c2c0040e038401d2002540440c0400c1900c070881d0151382c2c0210b460520380d024641820007404409882e1340c1c0c4e8034070705511141201503075070315800c010070070355141050b002001001b507940d041c50b0454402a500700d040100196515580304952540d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 958984199 1250 958982949 958982987
    0xa08160e04030323040c171506280e0c07020d11211c090e2a04031104060527041109010803030108070f0e04030c020325030c0801090210 60
    0x31004d0341450f800c0c00d1103814484110645007060000f0044400e507600060450b811805c10428000d1115036914a607008400b400d45001101148041d200c04c0c004a4038820858a106180039100078140c99100c110f100703a142190741400810f02c018103035030894411a4000b405d07441e1070358090700d64982c240b01e0700015980c0224a446120600c800741000c4d180450080c002030100fa54081040000d0b26165000041c104181e5a000348500350031040550b8000d00c20002040250316081640c00100c03221845518618601050010800140d84000841d41d1010740c0d00740b0000713556105019614541d604041c0f031601103800704424a50755227102c0366010b400358846403c6a031000340407544216003a0090542500004018080c1100400c0f039440140725a03084088218500408080340000240c00142084140b698400540d603040000c0c071401498588441500520700ca489080103000303100c01c98440d4650301002071480810f20400740c1e1180c02401c100d840d5451000c080341c041e03403c110060444 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 958985449 1250 958984199 958984211
    0x5030603070e010902040509090c0102150403020a060f02040602010f140606070f0813150216030b06130c200714060906190513080c0a05060d0f09050307020a08160e040303 75
    0x88254030b46440d008100280c00103a8580c1000b05000020384020408000c5500c19003288049907400601e0008400c2c00548990303940d115441d04a003003068001010305841c1c2032500f05111507007694001c204542503500200031003a8000103500a4035101d80c1184800d540042c0000c81e1030520038010b00d03202c0d109071341c1d100103810995940340e5150072100d8801e004d40c010850601100c44640c3c1c91a20b03181300b17400206441106822091032040c3c560100410f0468114041000e41e1550b16000145905902060007603e040340d000a15115451102d80710300e9402d2042255100004540001035480803200ca8466822020600c0311640c01013860f42d4103d8020000700e4810402d5064044c0b0b0110265980d982d00c1d0485007104002100c20b40040c040e6400a081d4001d2070341d221800c1c0e504035071040d01c10b00e072502441d83c0341c00010b004040c410b061503802c0080c15070400074040003d0101901c2207500312400e503298000e0a640d0300180602d480900000c62081c031a80c40341900f070f5540644246404509 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 958986699 1250 958985449 958985459
    0x1060c051b030c1302030403180f060c0303020712020a12030204030317060a080d0512060f06070609060204050d0804050307140d063c0b0312090613080703031707020304150503060307 80
    0x1980113050038903005603010003844205070707006403000f0303040461544008001d1308150040b480c17000140b2484050044486020080501030b030140c8003125080f211f44210403a10400c0030b5181c641e01241103860000311180c1054081c003038401d403010390340c15643e054a030381402c000c0f044240d030010b0110360340300c4210749002501e100c04101d80d1302091401d80d41c1540f19900300140c5d40300c0d02005080b55124600c012f80c50040fa498600554850b107421001c082506007403810101c1c001d1046402031500035101281d003034140001d010013002140c8055040b19026503807088081c4c0c0c044020380400354003131301200300c0101041c42600004e0b465818681040b07207801b0480307215034407100d658042c000c0300290700701c505584490601c1a4103556000307802500c0c0a40c0c010000c1805403091398000c070f20070a00414000c1c848040d4940507000750003148115004c040d181c1c14090081c0000c0007000c2944c40d10301002420300c51010007501c0c01c640048000581600c040c91058a1a41008007229014801c2780c0f00014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 958987949 1250 958986699 958986709
    0xd08130804030311211206040e0f0318060a02120714060f0619060807110a0c0801020921072310030b01030c0311030a020307110303040b0106030501060c051b030c 71
    0x86200b0713124034620251540101e070500400001e40d00e00c10400b0341900b42801e0350702e802c42d08448005118410305540e4540020000c011403201d5405a1064801004840703c1c000f006042100090040160034100d1008000184c46031905140040c0c100c5420401281049800f4000c0d55200d0410103941120f100c45151824208a41c11500c03030841e001885200e04011058072000c803140201a20f9950800c4005414060003800c800100005000c001401420500069440381d501c2160303000f034603940c1c0c0303c414041c1d0006030400e48a00314615030080f864020a040305921400000500013180c502040100c400b006140f20407100443c6c01310300342e0140d0781c4040021020f503041c1c038005085043c2400050448605811400070315103408a54603520321010103581c2c3c084506500580d5aa03201042182c0c000b0102d0441c07081407001109000030401c240071000e058400550381049a80c0c3d03140d904480706c0c8841c12000c0c001c0d4004001c4c0342d8072460704600e4042003c6000d4100c03402c2c4080100810 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 958989199 1250 958987949 958987957
    0x1030203042f0a081b101b0f02041413080f0c0109030c141501050d110d0f12080f06100e130e010b0103110d0509100e0a030816020d081308 61
    0x502c15980301c5644162034000e0300d4001a10310100145401d80c080503104061600100c03182d4816401c01007942c8842d4824000c1f103001811030074450b034034000c44e8a0284131900a98604034811400c141002c81c03001042449035100700445035802c0300c21031280c1c8901e031080d40303e003554280b1040d007040740c40c1c0242d600340102c0840921039a650300c145c40c06410401400040b80407184099001994410360310b9203c07001e00c1e411342d141211180c00750701c05894051a0f14010b00c14440e00425895803100a12010301e6480c03410a010702c106c680f40440c0e104084461a030208c0d10000d07096a500041200c031708180c1790440c080040c2d418428140d03080301000441d1428218503800b8000d48034800102c408600707014103502401c083c00e0a03c2200c25802c4840840d00501e983d40019540d240009180124100848802411000010010300300c40348c084546a03490381e0403e80210380c41001140288107540c00001d215852540640807424648100b100c15240141111070360503a05078915003c0741c5c00d08020 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 958990449 1250 958989199 958989263
    0x100908120408120c1e160605010b030412090302090a02090a090f290f010f030b090c04031a1b07060603021002030703140309030703030e0a1a06010e0d08090103020304 73
    0xb183d100c0820744148140039030000c11030000d18070180251083d0b01415131158582c0c0385941c4203586c982c40700c00300704198205684d20180444e0b0070000000b680004180046000e9801801c0b5140d04014030242550071003820301c8004c0d00414000c00045002c02598080c2625000040910702402d0380c3e048840142e070042e5040b0b5007003a680340344004540c179041c54189150115103110000020000c1c0004401d0080c540480c0e041c40043d02c0308901042c400c0d400f410241000500c9481c00b818189047c00c4250801e00003210145a002d0f0304c291540c0d80003024a111b2445000741d5003c940e61080c01e001e050304030030000c85002c3c0c3c44400100042e030354140d900752140d02a5005644509150030b00400b03034a441c9400c503842901c10410b10141c080701004880c0140d8142c140860380ca0103280c816803410070507101c09400301100e02d9905116a04650390316014140c242d80d0402603130144000c00c1550200c69800034922141080b0000b16035002ea000341d503015000d440041f2804404c4400c0c40f024030051040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 958991699 1250 958990449 958990463
    0xc08191a040f061a131b03021c111b191704030203060f151f031a030f01060e0108010e15060d02091603181a06130e0624031009081204 59
    0x1502200d0920021781c595039168084240070032445070764110076240680540100301600002c13441898401040b03e0004424421403c00801d2152b045040d41030704400c641d13080706140318a480510910010340e0b5210711007200110415072205503203020002c0250203010240020030300c80000940d40c03d20001c0c1c8900c1d04e958400e901032a2481e00440c00070681105d49104070040d50358080780c85511038810b8900c0001d070800141d418009002035040c0030302c081e603c40d0b141c85800c080201e40441900071900b203400601c0010816602c03941110b007690100031500800f640300f0f8050000c02201d85c100e181e0842006040e5102000d92070b00070641c200300403229680c405542d40c900040c0240c1c5071160701715440e6080d40d0011f204101d1341d512035650306100400303642c810301d01c40403800071354603495002100a02c00300104861841c408805454850840d260306440302001c2c0380c4920001c107080307402c03c0320310020f020301100103134049504c004110450b425645204140041041c03001461201030260b405608 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 958992805 1106 958991699 958991741
    0x15031003080d15061d041a06030c190908060618182a0406080c060a0518060d1a0a0f0506070515040c08191a040f06 51
    0x1140b0f000c0c0b1400e655001481d00c0c0c00c140030f540c039814150101c495150301541000f04076406110712078996000510001c0103494214000c0d43d00c141c116001500307106a6100d4480942401d036110030129010050501501804118940e40240b0890701070b801081c500c0d048490000010b002001006020f00076003d42078010700010381c007200c1c5848a01070804a00e0030a070007441001003403074011440c040300452030035000f240c9041020f0b0042c0220349405c0d414441150254001c456040c0d68040e08200110701d65920b00003442600f41208021441c6010041301011104414103854410a201c24041081c00909001542102e504440d22500e406842c20032904208038000d094000b10035000c2040100811013800c4001c0d24049d60482e042010005c1d0541d81180c0340c0e6401030b0158024a080c10701443c4c10110082d0f01c00e100740380c45413604000b5034501080e5440030802e081d080a17289 = true := by decide +kernel

theorem cover : BRFrame.Cov 958812949 958992805 := by
  have h0 := BRFrame.cov_init 958812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 958812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 958812949 ≤ n) (h2 : n < 958992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
