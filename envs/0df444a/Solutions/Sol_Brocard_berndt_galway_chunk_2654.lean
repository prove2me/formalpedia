-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2654
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:20:53.384469+00:00
-- url     : https://prove2.me/submissions/5222236e-4634-44a1-a903-b8da46cafe58

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 477158273 ≤ n < 477338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 477159523 1250 477158273 477158309
    0xc0a0f080421050601060e06030f0c0c010608071502010c08161803060203040203010b04060f0e0414011b090e0402100e0a0b040626090613031103030a020901181404090507 75
    0x341084a00b000f400b600a07074199a9851209913482003410740b449a0101040001901442800007500d4001c15011011400c0c54080c0d04240e08580340d682010300c0951000c18208510708e10020005041d401610003805401e40d8104040c016100240900030301200d14002140105d1045280c0246400301d1032481d5940340d86ca003004002540150b6080c0d00035401c120240580c0c3c240b9024100445103120403c40d540d03440c01c11960607981c809082110071890030841c05100f21000d01860046103120440740c40c0c00c410344c45018264010650101c080b200f84801004090f0381d0760700c403143d007100742428135142c80f800d200000341022140ea0016100500c0104004c55200e500800044007815452501600c54803800b44c03140d0500c1c2c040b110340b0f01c994442000501d002d0715120074040c0c0710b072207408d10381f80c080c030181600703400e40c1c0045900003846503000ca4414001c1d0390003a03502c0e40480032002e400d00c0c42c80c1050383c201440359100b200c0f035000b1034442c0c09480030002c0400c0444001c1480d0007600c821080 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 477160773 1250 477159523 477159569
    0x3280b130c090b0310090c0b0c030d060e090706020d0f05210f01090e0304080d0c031b0b2401080601030e1f05060f0a080a0b072604050d03020c0a0f0804 67
    0x46402440c024403170306600d1142008284034100400e90040400b8500502d0078074a01010b41c406d9107011684d01050000f0848001c0c103000e5000034100400412400703181c0911840d25007130150303001800315445060b05403849030f0410910003500b0780c0c030716046554041c10b101c2544c0141c40e014206030f400b8641c001300110340c030311160310034142c0391050421f002c40703190b0300a80744c1d4074021409141d200340c105502804d107243c060f10258064503c40c2c00c01c030560001c051600c80706c402031030b0b80c1501c001280b40108071142510401e2000703110080c03400c2c400394684000000f818010000c00752414150765518501d480c8808100c41030103520450b108400bc80c1c0b200e5540300c00750000ba035265001d0480c04c11881d105140609450080d190084001c0c003000b40d06442d144480480030740441d0a001c04000c28140204a00c0b04031821201006040e83c00e42c2003e1034094500311485403003100f01881480103050700d081c0450ba00311318503009090b1388482501400d2602c40d5109070f52241905148a0b001070384964 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 477162023 1250 477160773 477160781
    0x302030604051f0c090b0703030b03030c0f1203010303171902040f0515040302010206040f150c2d0903020108090f03130906050402030f060904060b0303030c070203280b130c09 77
    0x2404007042c0a03d028003807012040d41d10350051080490361242c401c1c020083ca40d03014054241c0285400319000e102000070a040d603101c0440d0301e00a411080c07041d04c0c80d6904000d002e0203001908596803a43d0f155440080c015040e0405003506e0072a0328000c500543d812414020880480308e07421503440f9030754070742080b6240c171500c9030b24022070035481406401c0e107540040d1402c81c0d4040e00902016611a500e105000000d404201d0701d00d602d200701d42070704410511800801c00e00c4d80d2251034501d20350313485410503128180c5a184280110005405c056076000e0702c010100d030fa0a0030f08402079103500b4041c50410410102404030380c440403414481c04c0c0720300e4000710100d600e100307420002d1070307150030900050b44000c9503c1c0c640b403030f13020002c10078030f090612105030b101f0300610780010b50000c0c0c40000303030850740705450102180b0030101d0700d401903107424800d00f400302130160501c0b00d03450800f4a50440c5a41408809442c0340b1304100019072888020404003000d81d4001c140700030154590304140002c0c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 477163273 1250 477162023 477162043
    0x20919090b12151801060f090902041506050a0f120903020606011d0307050d050f1219030b0d0f1b030602120a0b0a14040b04020d0c03050c0a080a1104030203060405 72
    0x1145804482c0840003000f00d007041800c0c03007240c2e042240380d542c0610b22841401188407035070213650b59040002d4109900000c44050180d891b000300e41c0050600401040d5000941300c2e1981d0380803201c040140e00c1d0040d080f46c3c5002c4050820031106801148180ea0342080380140100c03480c20b203001d400406038007040301b91098400740c0b00c0130080c07000e040312001c418602c44480358155000920038000f41c80c0c6034082001c814070490488013202103000e04241080c818058114181002003a608442d20341c10341e00c41342c0d0074020b00d420040d245240d800140c01403250b42e030203031111071048111014481d540b6601141c00304619106a1400d0b9a442c002000b544607141e41260319030f000003c10001002c9010f0080450f8000701070400f85401c0450001c85030000c44820743d130065031501c00e2010382e2641c6c005085498414003000a041011210140590760000c1032640c440004001800301c2c150042102070308441c800380003342664840c004d0485034441c40d0000f0790f040c45480208000c102c000110a904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 477164523 1250 477163273 477163279
    0x1c1b08150909071a04060c1b08030a0816170c0903010b09010308070b06011b0b190c030f060e0105011d0f180406060b090105070b0c040f080a0b0106080c040306020919090b 75
    0xa5684c11100307207004e401a4002c3c0000603800c076030a031001c10f400366058070015550080044c070030b90752154190b1441d0301440004001c14074040800040c5203002c103005c015040542001c1207003002c5989103400e140b800801802e4099000b01d0510202d071400d50124500000c0038045019950b141e0811140c16001480f084130f0075620040010150351042803160a031040b41107201008012945e03036094441c20007805105421401e076000c40440842c1d000f901c4580c2c410f914001826190200c3e800195903698011901c2c1c806140010400351b644911000030808002105110001003540012014481118819400701081c0c4443c041c036092818014001d0348500820059656150036410260003010440340c041030060000c80c001c42c1112000702d82c8103180564540c078098640003c1d6a025a05812101d11a446a410b4404000c60440e445000d000745081c1100300b031900c24980c920b58480d03400028911900401d44c420b01c1d40f03811201e80b000c11035a0005c1000d10b900d82401c90300912103080c403548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 477165773 1250 477164523 477164549
    0x3070c0c05030a0c141f20060903160822050f0414190b09040602120106030513020402071b090e102a050708030405031c1b0815090907 59
    0x16203403070b0000726844025030114494504910700a0000307105120316807220340107040442c181076103544584000340ca4031038a1312940d030240824008444c00c84000c16041c075050340500c1c144801ca03100041610701c1c1590508150303072030b40e40616080b00c0b5405455420700c0c81c2d40c0400f14a12601600d405c00100396681520340d00c5a0008000800c01a165a0540d9200711800070001c60461000540d85105106030140e02040d8032103c0c0700032942c0400d0403035098801a6011034040c40300344807224414014a4585400d000358185500303421900407800500a104507800200c00042009040303841903241940c10500c0995955034915102034214200c400d0420701808401c00101c494074416421296400c00020b01407001600e035511700341c40b1240320b600610006002120010754070000840c070543c0700e07002942d11101d0000840d116001c160304541e201c90b0801d030014260810700302150040800318913020180b51204402181000301c102100c54004c0c40410400040c19000207031282201e82060701d541d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 477167023 1250 477165773 477165779
    0x60a050409150306230a0e07030b0a09030e090114060d0b060313020109150c080901030e0a0804150e13110c0102220501110d120f1b02120a090e0a0b0603070c0c 70
    0x1c42d150b0010b40d611170981d1075210104910400070f9101c694a400100120799074030340c890705c0315076258a003110010780d0281c856a040c030030581e01245440d9020010344a2040da5414030000c00388810080304864014007001c81c020a899285400c01d40c00550040c1055550742842c01d00b141d40940000c2d02a40820b20030a000200c41018440c1104203602617510b4000054460740d0300143da5020100e214101521900c5410710407000b07004481e043e40c8030303910703503661140b4021005980c100095400d10a00030790412081c460346992184441f50f4660000c00180083c1001d03e004032409244400c9099606c08141c0b020040f4603505d035450380110070044420060741e1030b40112003500c3d440d4031a04a64101d00d083e200750364064016000c0c00600c001c00403403165000201d003402c80d5113000d03c126104034150900c01d401601400750940b2a0404000c0c03514213143e07888050002c2c0003910860b4104e4601e02c002a0745001c0c69032103072900d07a000611055036810050b17401800e848200d41c042d54006e92840c000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 477168273 1250 477167023 477167051
    0x90f010c020304050a0501050903104d0c0106081006170c0a03021201090f0f110f030705151201061713020112020d09050703121b020d02060a050409150306 68
    0x1031411a00b0003070403070300664105801116140c121540303481d090710401102440d05641805401c001404014101e0cd52541d00c0031507405080c0914549000043e00161484080202e031030b40000004c0c208800d00e0707a0302d410501d51070043c60342b40e00c50038190003201d51402c0036241540009084408a088440d04224a01c880b251501d010340002540485512010130050a214a140c8903101c2c480c400054013807240e45602e1404030fa40c0750200c41980c00c001d210000c2120090301d02c812550140c80c00400c1c0d844c00404130355a490340b40102481400d2580c10103141204410884490b1a0403040410165a442601501403d100414400010f12050006022203011140702581e40d405a46000500c040114210002e5005124040500d511650320f00007099007005594002d510440c2e20300b900038824840100490101450802220318403003100300503a03900c144110328942c040b180180d03203510340001a41c1501c2640c0c442c4054900302100f001c2d1007102000c8500440c0e0003080207208080202e450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 477169523 1250 477168273 477168277
    0x50313170d0e0105100e0711060c07030f030207020a091d10020406020c1504261b030d11101107140601050a12031b140708010213090501030201050403031101090b090f010c0203 77
    0x81704000034200b10100900301d0a10515900700100e41003141860520390180c070b0501e94121840c48000301c001910000b050381c0100099444041841c0441c10050716034001181038520303201d4900c10316241c16089140f02d00d41d20300030314008602c0301200c568003268902c80d0041c1d0403501c202c00142c0110211842c0600342440d403040c0c04d040c0310108078501410034120000c80115040c02e0110300001426000700100c1c104032003803645800310701d803807500c8180c1ea04043c0351290400011080029104030754801e0180001c10180d40744d00607001050b55500d81004000b14040c444000d00034a07481c80744600b50384000300342c09050b10410b0311a10412501c0d0042e0b8401190311850080000b800c50795406023900c0c1c1c5000c0300a00521400e04042000c01c0c40c2d114034908000c60308243c80a07503000800341904155580701c00002c00d83d01005024561543c0c001034114025448080d0604c1000506e141d146c00083d4080054540e005e6901030603418406802070303840d402451224095881c10701c03810707480750002007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 477170773 1250 477169523 477169531
    0x3260103030c030c061803030f0c18230d1208130f0f0c090f0204091808041806080d03020a081e06120a0501050c1e0909040201050313170d0e0105 64
    0xb2450150590b590301100e405441c04415180541d8401c0f1021080d00c100000c40000342c0a66004105c412915080310201c400300d0a1203014031000c00520112505149545000c40e46100c0c81c52503201e0351503400c241a5484502c2041c2d01102d824901d40402000044141031180d1030358654480e0743e20321607141401c111000d03000e8100701c1c40940c1103001401018100f15024400c11791007180ca0fa0f14601d110644040914803000d56130085018003100c9000e1059854418800300130301011421504d9a840910450113004000407590041880318211038000100034585a000c07a2040c5000c000001c009400071652580041e03110008219040f200d42c0c400c50701010703410714419090300c030002041080694400c03405050700501d1080c0c00869400e105141c4114581051799580700794045280c05421981c40c0c08540400c000d12105d0300c42d0b2140c440c1590312540c2801c0c400d0b0f4a450700c80700c4525418081c0f000a100c41c0c8000c1c00c050340c04848002420b40051035007001e104c00c9845100c5103081c3c4204072 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 477172023 1250 477170773 477170777
    0x8010e06010c020d02182d0f070302032703130504020910121103090d09080307170708040510030605010e0303043515010f0e060306040f020f0d0326010303 68
    0x103260078054a000480b18542501c02480c10003100f01e501580b9210740d2081300d00c410403641c11f405a0400040150303992101c0c108042046401c1d10f00401d01252601000d41b55108041e400700003e520000411100f41cbc401d041e42030340c000d00001000321180e503a4800c00c032401c0d445800f8000040c050030940280d808283c0020300c800c0300e1174841002205c0400d0f441c0c0ca114141625035000d840302c908000011805641c0030005000c01d5901c1000140c000b911384e6000720340c1c9510400080340415100d100076449424020340059945503182840c0444e1301894029aa000324460520840945c0507404201243e900781c0340d244000341d0030820180c0700c1c0502c0c41958101500001c00d00c40c06030300700c003942c544800b200402e07521082d45113030654900242d0415070344102e003404c0018800045102000402441c0481411000c4c1c9031200102c0d031580d5018000801001c13148c1800011560b0703042c070302036040030060002010780401b030400400488880190320003880c3d00c510205800030f031100546042e00c0e095 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 477173273 1250 477172023 477172037
    0x5011505070f020112230108010e0c06030711100c0215090106050d0f020d0b0f040515150d061b020c040608010207050d110c04021207030c080412030c120f0c08010e0601 74
    0x2500150303444032901030308000175580c0b005429902600300d030310a08268020905a03995604000c03150742180c60504203110298016a0724285565450b0226980039103180f40c5055160400d0b4404c81c40e000e10711b01c1f4003076001e04003200603501aa00003040b5001c06040f0310200040d440d1b51110a00b2914540609500036502c000d1607808580482d15200c0c90500c05000d181d110420340d02d80c1480d2640c10307104a81c5071a00c900c10b01c0148001040280b80c0d0002440c0c00352150700f8401c05100c0e1740041001043d0150340c0c00080c43c01800580c3d80050030308096060001040600301000030f44034081c01480c0c1d44198604007010440440500c203a58000340c0c058007c3c80c1c1d0004114069070304000c44400151544078414200f08584c4960011b0007160b0b2030300e40101d01c00e090111015040d0313440f1000380360400400a00b017002113503425869204200340d6090014581c0c03030524040312960710712300100c1082401d1603000303451003890b03a10904058115555070001a600c0c2c2e0a040290030703041d901a40042c0f0a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 477174523 1250 477173273 477173303
    0x804020a1406070c090203010f0b0f04150e043611191703071103010212070e030307140304030c0b0a02030304021c39030b15010e060408010501150507 66
    0x1800a14a0216900800e058100081560344c0301c0807004580101c0030403500400100040c1c1420b00040c40608825801d850070003180441e20f100d280100d00c100c0740c1582140d03020001c954080c582d581c020b00381c050803d00444259042d500c1c0c60f0780c5000003214941d0704403100301d90b10540700ca00540f00c0da03178003440d1842c8448683c1d04100f4035460800d1582c0380c80e550281c00040402801c51201c42619400d00a540c40c1e151030f0810182841c4010480c90299004100082a4020b80310381540d0241d0242080e501101942c0c010a1550050541c010241000c001c000c0c40341507000000b4008403482a5400d4030030070b884009050700c80c01902400c07409640103201140041c03401e19040ca00f0301d41c2c1d014000c1d00340b00c010f403600c0030151084501c0056030040341303600e0b180e4030010240c09181003a110000e06216403840c0d440012049006054010ba10001c079201d0319140e104408100040500402007602c40751516019070003440c007032207003a01a030300c40c00b40003c1c0301d80140c06882d002600720f614008180c903 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 477175773 1250 477174523 477174539
    0xd17041a25030213050f010e0910060201061a0901031e090b01080d0e0312030702030f04060509120c1302030402040b06191d0a12031812060609150312030b031c0f0804020a 75
    0x10011b1502414055080852403664403001044c034400c00c06002c0f41c031041e03072038808041d0854405810040760754503202c0008200d1004c07242103842d1070703a007840d00140009d0901903a0018000c09842ca404e100d062000c00d6040c03106e015183d80c141e648880a0b65400030710040c00340c419281c0258a250942c1001180c2821942e284014513030044050040c0d078a455851030780650550300175001000862004200c1c2003450402d0142c1c904410030350001040741d859001c1c0040c4651090b291204503c0303030008006801c648640c1c000280c5c421025041c592100c0f110343c24004240000304280002a200c148a203180d142d08070007030602244060320501c000c0381000340040c0e9003018100e042e0300f40060b091089001e0548514070f200207200c0504210f04282c44c5280c00c10941d0507070b40c00910300c02e04080c2642d11489110400b2001c503540074030301c001000360080c0150081c1004041182e814010000b0345001c1c05035090f203c0d0a1488156502c280180816a0130b840ba070405880c0030b07400c00810807003480070310 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 477177023 1250 477175773 477175789
    0xf120612150f060609080c010c0503090f030c131d0105070503070806030c0307080c030111131401090b030114040c02010203090c010f02070308030421020d17041a2503021305 76
    0x104074408007181c2d885440c0c010710252100d0b54013000006440d801c0070040c03200144491400020b007460080d17264415511050360343e01407040301601c551803070496a68907035410001880301c1d69000d002c085016401601110040c42d0400182c000708207100d8001010940c1031251900c10510b80e00c58a083d0b071100c0c0030854000c000180140c5d014030498800501650302000400020507031000145850000d40c030506094845a025580c4500c20074448150054051501c02c41518076050340901d030000f0820040320b096013240e10112807407070000004540b5003c3e902c1d542c00c42d00d40c140e80500032118488801ca00303d10040b1416880c07600807c800f242e00d98400c00201542e02080d1040350045507ca4a03180000e5005860485aa000012140b0408009201c940501c2c54a5001502c520441c60760081c2405000c0008010340040d5907000038104002c0040341501110708416446a9141005448070f05903070110280484840c2c4849076200c0500c24000c4640280341004055441c0f4902802c1c00815 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 477178273 1250 477177023 477177053
    0x31209022b02010f02030c150402010c0c0803070c1a030f0c0d020f0c0c0a08100519060342090f210906020a350a0f120612 54
    0xc103070300015050700608448958807110402100c20060202288005000c031100004401c05642042c0208115188040742034546e211340015a07011503542c0c0c3c40101d940301e49068006020740c58200010600391000000762241c01e01c218405002651070300d4840d031607040009001c0380c1c0d00b0000c000145941c0008100c5542101c0030102ca60b0500451400380c0b001ea0f000020038030380840c00415800e075502c808000308480c147c0c2c261072016a103030403c01d400d074668101c049070612203070700c0b180400c00010302215100c42003c04190204400f5842c0d01d40b0082d51028904086400070f401e140c0560880c042724102009d041c071115921100c001303242c011002600041c9416901b0110104810020032000308909881031081000e0020309a20500c0c06017013a40c1d15081101154010146400000c1460504000c2c0e03901e1240980e09039201e00b81d50101c443c500948052000401061320802c0c80d8020000c1040d1214540355505410b00b4402c05000300c62140c8101c000c11040c48a000b00800c1700755074204c8074 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 477179523 1250 477178273 477178279
    0x130516030b070e0123180f0105030c070507031205030a05070e100309030903120e0306011a070303020c0a0203120a1211040614040b0301030b160309020d02090705220602160303120902 80
    0x30190300585c0c0c0211202c0c00f5002001a1040041e014801e15120500c00d09017060031031b80000c416090000003012404000d151740c50344400040c00206200040220200455105038483c040c0d05206c4001040c079041515450241c134201404600d90030b0042e06d050100300c81c05030192031420009803080300503048029068041c032180c40b0300440410f034404004030301e2020395150071401400c801c05040c6842d42c141d101030409012036a2034500200c0c0d0740100ca440342c0d01807501684804014001c141003d00b07210000750306115102d00b020307540c0002406005650030f551141c00c00e0035800000c840c10345120390722155882904000c10300105004040c642c0c4030000440d4450f0900d40c4400d90810140d00030380003510300420308002c03c121007103110301a12102c041c0d8501030080c0b5603554041481c048100750000e2140302420000740030b03d1720500036510203100b5626592101d001d6080c045c001c0c00258001c200060040922640684069404001c03c50380d15945141d000d60740c400c5220018030f01544101d0b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 477180773 1250 477179523 477179537
    0x2703120a0302070812012402070b1b03030a050f010f030201090504051503030a0207180908030414010f0903030f0617060a050a020403020a061e03050603030a110114130516030b070e01 80
    0x2010481d40c002503d417518021601420f41d5050007802c0c2841058002d845442e00c040300d0441c006980e020803c1d10454030700981003521404035a040d09545910386103180c2d83c1d844084204070b081d00c6e140d001240100401c001808445c0d80f1907800c148484a10b000c0079002c600e10b1841042030741031036070000e680b002c80050784002d0080c0d4000080d0541e806107000c003005902000041c8880d42d20030341c3e04610440600001c0101052558030300f04103000090000d4480c043d0000403420500302034006584880d40e40400308a601c0482c80c02400921444140740e54040c60000081584001e50f840c45410780b806134000e003615520300080c5409048010042a1000d8082c8000001602d4030301c85e074400b400d11134482c4040103c1d01c40504481940c0d003500d0104150801044c030145407030110488007211520b15040c0b0130043c02c1200385024044505000001d101840108001c0a5003440c0d400c0d000d0b803141c0c050f40c042c021200300c401c41c1600d250101400445004020880e00360246015401451041c14850 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 477182023 1250 477180773 477180787
    0x8010b03070e130c0b0309010f0204050a06180504023708040b090a0803040c060314240102031c050105010f052a0c1905030c01030608031e130801022703120a0302 71
    0x9400d5840002031007000b0040c4103061400b0300800364089e404141c1141800d20b8480000c0e21648244628420b102001c05400d90b50000c4a02c0f90000d0840a80250f686520038030204154004040084031943d1180304840e1a0071203642c0750714140b0242d50b4544003180c949480e40c041248000d0460b240c00d10448100100007494507000e0752140d4040e50032400098034125014013510490320000b00492341c1c080c100a00820b000b180380e4944140b106003004080104030050789181b10300c2c500c00b008000d400b2410619200305802180c140c070020b0341c80401c0d25111010a5403c1d002d0700b4010401c1d041d041202c940481912004040718002070710485400b98042130200e8100c019081d004521100d1061090156050401c001070100da1b0a00c1c081244910306805d00d0384130701503011007010150300c450388403820640420503980b004031000d0490040355a2856501e00039408118140100302c1c40c040382261074840c62040c0316440c000a0701030611000301c200e01c00032613407080d0088024598240008 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 477183273 1250 477182023 477182033
    0x30405151306020d0e09041a1f0f0611060705030109020a090306020a09080c122518060f120503071515030f141c030504050a1a04060608010b03070e13 66
    0x107100621164018002898109400501c14850a45168019109035040c4030000d400982c4008003100f0310a85a1610b4460040e00e1034407401b028080700302e40140810104061410a004e4011200541c9420f01d000000c2e04800d502c5460072250000450300030701c010421442c240d0010001c1041600c0d01c140c2c00e684030740d10702049820500b24000010312a071418071040300b08000326215490100c80b014590854445c000d03668004030365807007034061204250b10f00c0c0180440c0300b90340070700b409036001c1451300544180040141078500c110305110520a20014103240e41d06440b00c1100c3c0c0100c0910b00e042c0407070325079041d03000704e4104000d0f03800d90ba030101004090079440118003a52203162848c49491007814042042d00799000015256000b581001031031502c0351035500003078030ba00c0c00c0c0030407140d582d424403a0401406130740c00b500e08000703a40440c03104840080510301c03d41c441c9804002c0652070f001c010b42203400e03130901f694144d030040200344428002118a15800300d100c0400b000040c0c8c1c15038074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 477184523 1250 477183273 477183307
    0x702060d050609010f180f06120b0f1b0f0304020a090608030c0111030709060f0905042a02010e0c060702040e01020a0509010f050309190f17030613090503040515 71
    0x20800c00107544109020345854000076141c01003420625500142d820640040c1a804c1d000d100400714965540e2120540e070885e40280c0c0007402c60b40c003050104102402c0c11811401d0460340c000385d032a02003001078550008100302050481c01c0820300c60516035405880300c030701e40c4003078030581e8848803500001813000c0351070080e4000b23008a50041e64603110f41d9a1100d00303542c60f113511864421001e004018516510420303c0d01203a0b95860840003640e42e080064590710503130703040340350000c1c105455102d490002e4007054420b8105da0b40400101e0965a50403800c0358804504e00481e03400494440d04180303800c0e03000d0301030680018400554906080512401c9034040c003000c01c041903010440c1c802540c0c0142400740c000105040007841c501c5c0050001e62111116005050084244c1e0811001d021246c0000c0040a03070000444a48581034628504141c001302d52061190403d0442c2000503a01e5001759000c040d442002076003032030b04280070860301c00c40202c2c14441c80700f1300307112103140320300d428103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 477185773 1250 477184523 477184537
    0x70912060c030b131506080c2508030705041a0a120518030408070f0609140409110306040f02030f1605060a02030903190204150e1f09060807082b1103070206 69
    0x50015240d171901a0058591790507034005002d2200c254100b240032543c880481d1540c038a801c055459551404590b410030341083d9001808014000c002c0050803034109000303000766078001d080d81c000e82140c0140e10f480d510a0503418800034440644102441085400c825040b5000a0340c1085050386039280515541003603110007080d911074881080b075604440d01d0740002e4040340c60040142c82c10000640c4003c40450061400b90360b4850f084d905000d20110001c1c0324403802026601c060401d828070400c06100b050040e4400d0013180443c0c0480000020390307406d14551408601c825503d8001003011176001242c090040d400b007005844410340d000e2100c01c4656240c0c0c10030b2404401903005100440341140070801c01b0005c04042400181880716a1031380c0700000c000c916441110200d100420110a039014001250a00101084004021941005030345007542201c000032014652224060405e00c04005020940114103407020311501c142000083e0400449140072825404200c40741e100c80 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 477187023 1250 477185773 477185809
    0x402090f13180605180609070b0a02070302060313060614010e040b061e1903021e0a1403090a03080c160f06020f0d1a0109050a0b070507030209011d070912060c030b 72
    0x90420100268103140c005480310341704020005440c0503890f00750749a403207014108880c440400c0008040740308101d00f002466020740300c2516401c08030300800740002c025000302c4100341400740208880c024143c6007806044140d441d240741d000d2201c00c0c80024950151090f4001000704062203c18000061601a203450840c1e9281d842d00781d0321400142c006071441c41c00806004106102c00c480c1c056130b2802c0e00380e032880c454942ea070380100307070540e80744202c500d4040c0c2200000c4100b00450384041140344005000b030300c400d411980d03801c0c6104181d200d01c05d036045208041481f0f03900070900911850003254840c4a00501c4c2103075a4085680d2508100c00cc580e1590325406070590404480c040140c1809081c05c108140a09010001d0b410300c189000d40114040086400380500c20200460001160007918400c200d50315016420504046415a10280080440440d4855110340000d4085440e41e108010700102565144000382215000d6207041640303d80740c0001e07950300c045004020344d00d48 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 477188273 1250 477187023 477187031
    0x7050a0c06020f0c0108040803130c0303030c0e061207050a0c0501050f0115080907050603090c190e06060403051209040204031406060306182d1005150402090f131806 73
    0x205800925122248180c85050f402443c24500d4030b9030406c1c0c02a410543c00382c00c9540341d91ba05010003242000b50701c1c010f0107020159400106044e059072103100b040c01c1c503580d03260300c802ca400c09000d100d00c90000d44810058500c00000c410503c03440141c08689007a1501c0000c0140c0e64890700d01355801942e01a0884015000400802c1c2c001303402566a103040e4145a0b80a2600c0508940c490025101d40c6005a8001000412016040c048000728440051a03102500000e190520030700d0560b00450800e042d1400114407a8601042503804880e8400024042900c3c2c18110106541109404c46e8111740c080c80088001000031300d0003003a03040c8201c024406843e0001c01c051038880050f2022201c25071300741c00d09686500c040307002c81840a480b000c00710524484881c0c28038a070000113148155000305501800b042c820b07900000d0045100301e1440440c40b061404003c102d100c0c2c0e40d01785602a4070541070309240e051815003100405c01807032000075114056542014048070f91901219000e43d2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 477189523 1250 477188273 477188279
    0x405030a0806012a020f031005010504050105041401181b03021809091203060a090c02100b0108010e15030a02120a0b0906150d05011b1205060915060a0507050a0c 71
    0x12101ca80360b40700d242403034035004607100c140c2c001d400c103401110364039802c4496840c1c1c01c00f952584032034810405005000c032104011950903110040000380110307840340f4100000090306140500500f00b200c082c04590210507441c058a10b658503506140d0103840d0740c2c0b070f2020f54111889017202504160841c1d1070160b607961143c00040800458a854240708051040900030014000154a803420010304060340d641d03119000002c484005560242a90608204102407a03540c0802d05000c8421505403c5c07000d03280c0c00c801515011000d0040b00c00f801050740014044002102e07604041d120080c058400e00100d42c0c0200e08600c15181c59540c0c030394818490001003024040465511141c2d96000e08400d00304468101d07041d0082203102c61085207200c4501050107020340c030440c140041e58cd81541c1c0d610a2400180a95540710808002c02c0c0c41d013000a001c0b0300341100c58900c150007524200a001c0c00341c0e410400d02c2c4d0011034118040110138810704000500801481c80c00c2400f56150880c0245 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 477190773 1250 477189523 477189527
    0x40905041e0b06041a030109050718020319020a111203011e12020103050c040f0f050405010621020d0209042301120b0412030b0d0303060305060604021602120a0b0405030a 75
    0x2008110301d201d510580030100424810b0b4051604200c04071400700380111013422042190024a0303040b5410352801c4003010800400050800880340c007061561a550b0100f8280e400b02d0104907003208030140ba01940641450b150350082070078404a0034909650a40c08400703901e4407940b200c03040001000000103025a20001390318500d08003500074007002c102d00380380001060028031240203052541f21800310386006d0381c00c4103490241402214440c0c040d075980f00036054254441c401c640c05a4941300010804500c288007030f12008074507200c01080c0040d5041118004c1d03110300800a20b07141e00788608802c0b40c0d00d50140e070720110b01e100c0c403004600ad28400c0203060700106900800c000f110541c480300008018440b8990b10035041002e045e846040c13803006034040c1100c111503c0d440541d0014280c20550558019000ea81c000c1e0100e41c005d0380e9460601003203104401d0b079010700d803245420500040c900507a00800c47c0300840305440702001259204002210140c401b150550404035040c04803503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 477192023 1250 477190773 477190793
    0x1050f0a12050c16060207021c0f150209090f19020f0702030c180a02160b01060f0f030b130e03040909200907120518060c27010f0f020c0604090504 65
    0x750860245403400030036082c104c02d04010b6000040444c2d07008144c000656031707030700007070b04562180c030000d000031188515040804022003001214010f09240c240208402148291035080c00003070103003402521585017003440a00020908202100300300c1d0850a11003990000e00322003030003200c100751119103610400d82001e007007200060003410319140e0540c2244c18452404d41201e1400e000580d2061040300070380c0c40072540d6070003420b0060180c0000480d55030100c0d4002488100b03644807244005000070480c20368582c4412164090440300320200300c8019035010091920300c0e981140e25081e52036011800b5240c0105d030a6601c030380082810318058000c9c0070088903000d41100c86409a103070111024100354404e60340c40c0070300c503a9280060a035071088140b1002c65980742c0c08445d014030300122811a1a80410307884200e203207501e030108485400c0c0880008107800140c6440745501480c0c2011640c18684881480452140f451011010340324a40240060011500003040910b49402d2015203c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 477193273 1250 477192023 477192031
    0x9100c0905150c0d050a1106070918060f0603020d02091801030b01140d140a0f11030f030304050d0531030c0b090a0510020a2108060303030f040b0601050f0a1205 71
    0x4002e080220049405020800c844401c004d420210b81710018141d0444118a03c5020400980701d104148016140c0281501040f10341202e80041158017014220068481c1407040c098190311039007041c0f02d00342c003e4015000c2d0041c0d00c0c40050a01010400144141050b24000a0a1100c4600510a02c0305a8611a014000081000508008240c08150500b103034100151401c4203c1007101140c0c0000d1203d04c0c4020b0300510b403a1312180c2507042c06400705107803803150380c4248070304021041148804410340e40b0494100e00500490410504256001e40c00950110645000304035042a4600c04807250320310049400c10300d00c07515095140c03240b200c0c03810350407510101e84107108112140e6030b07400c5c001c0306494041e5030f4401d120f400b541041e80340456424006041c0300c214409028818a036160103140802c0c2d0340d07205129503c802d4241904c911007a910811164070160005020810341400b05800c40c0b018034045240c0315084040c00ca40c1c5c1c10206180000420b049211801903600d80200c2b40c01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 477194523 1250 477193273 477193309
    0x15030e0316030503040c2d080106030302030702090c0f0c011e0e060a0e011b0e03010c0504060813051212060a08033405070807030303060e010e060909100c0905 70
    0x18200034000d040310201d216220040030028000001010000003c268200a006c02c5603840e0002c501105050701c41e0108841181d1aa01440000a00410140146c4d01282d4041d0051032415515809015109000400ca0100408200a030105a464401c02031081807080c0c4000506c03506440f10005c90480c4104105001609189844e000b145d8082007083c0c0003a400c00c000201651030100c00344c0545005480405c1540d84078a40c03e41264000345440510f05045008218507100c07408107540f2800380d4040c8500041d085000502d2107081701340455682401001141c243c580382c07001103500fa51046080305268203885091084908010010201405250000d1824000580d400802d501c10650709050680080d2050b5000d23051441e54030284582c10406646a490b2a1803040d595165140700450010340b0b00302c000103070b0302c4591031100e05031928543c00750415103849040043c0401d007e0b040380300c0d034001c04401c4001210035200f07508491407079031120103c10b4a001c040000c0c00c09020800300c0e03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 477195773 1250 477194523 477194527
    0x51305030706082205330c0403020d140a030e19050102030d0902041b05031b04030f060b0301020d2c0a020607030f021005040b01231518090115030e03 66
    0x11154100e240c2913800012040c9041d4002d20300004040c20f0032070540082e00328020421a00c2149403175901038200311805003044119041c2000003a0340c140411034000361040c0b4107200610040c034000112172541d5010f4095021018591420b45060540c103010031000325000c0008030006003002e0700c0311110869058440300b005da1519001079101c1c4220700191440550b0380006408558840d0f1220501d101903078501a0320780034000014060b644181c0d28840c621030288540301c2500601001c4a00703032079012100151520301c40e074410014040742d0301b10740e5065409008083e20842103106016440300d10b44904004010308072141f507601c0d0070411500300150010a84000036071113010031503688030340c18030b8489190081074100f00d050103c4144400103e80c105401e01c0140301540c0b10030750503520f07010303003c421040040211502c000418402180c20005031403c03c240054404040c0c001c083c20000b40d004003d80e03100028800d00780c242c11140f80e10042c0900b10700c2c4107505100c0c406800da1003900540c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 477197023 1250 477195773 477195779
    0x70306111603142106030606092a04120f02010801051005120604060302060c0106050f010c0201021e010b030a061e02070f060f0b040203090d0806030303070906120209100513050307 79
    0xa504154020142c20301ca42000b43c150203000e584200ca0440c800c50140801240e10755035104e50205042e00e92034801d208490210740b05140c9800b00c14014002c0d40707041103400ca00c141d0328098401100440c0c1140301030a1100284160708101c600b10000c3c030031a1500c1e111915031001512440c010380207107004840d0400702940098010003243c10190300382d80e0b01d030070654400c2d00060191110f03030802500b248022481351803d0b441500443e090300c20845160b050381c2d48420046507021101100a4016842035500214603100e1043e0000350340c20b03413000880d03451011700100e40752003000f80040700d80e940d0740e29544801600b207412400345108488020f5240940d01e894842d0000c4854102610042d5510110350b0343e181030b0380c45a43c02d080007400554407450401c00954460080d40031200214010310006130241c50003004507442400c0341c1c4c0390380095074240801201d540b00c80802c070590090342003100803902d40c0d91501c41d41240942d551007503030fa0000d01e45070b42800d119503400a0b001c0c0d401080d0034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 477198273 1250 477197023 477197047
    0x3020c0315190b03161e060309020609090604140702030a030b040917160609060506010e010809061b0408010516021006060509040c051e0421121b05030c07030611 71
    0x41ea2000c84240404118101c0f4100000d05104900c01001140410100001200903001840301040c02c40c81c4000d4040583d980c20680031340300102c030000d6202c001081800744500e03061001e039400c16006800002c1c0603500707000c00500d83c901503c081c00503070b001051003685540c0c10300810305100c0085d5800c0c803102c1c229a03039013071004102d540d50225101022420003020000315121414240c0c000100b44494001c030309008005000c240d82039400100554211041540a08001ca0160783c841000341103603a0ba400e258414882c443d1069004040308110000780848240078141c007070840072610b02c401c000300c00d00203031411020014903500d00d414000100a00d0f03400400b501e1f0303910002e0794085000031001c07600f21014415040d280140c9140843d42c8242e04800341c01a1040d9404d42c104510032001181c514005491000c800400401014901402e41441980e034040882c4201aa03c44e50010680c0c4890031070300000c0c86031055a100e41410414450301e4001c500400101c1d0080324500383c946803030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 477199523 1250 477198273 477198301
    0x3240503060106031119261e07020a0501021308010b030604030f030b120a0606030b0606040e15030a200102073507080304060503010e15060412150903020c0315 70
    0x340d20038076903030b4a54220340e0f40c03405086421044009074014000e203a01c1402030300d025408400ca000030010b1941c0d007170314444845290323802200c0200704a00d0280d4042c00c0c520b590400140703407004500429006000065003400502000254410b038001106c0c20b002030700382116911090140300e41d211905101c00705c0e801051640b14402e451501240c0d9480c1c0c04082081030001a200011505c601b50905d403d010250380094252403140707a0849158032808208110b50085008482c071404010000c40da0f6040401c00380740d44054040d081d90000040b9071941203c1d4404005021121081e85055004175079043c40440080c28117440341c80d401504101003031038107081c10000c80300e809800e0000090b00380001c100d500014007a4404030b9a41c0da464200040c200d0300284181d045034100540411000d40c41c081049140100261a40d41045d207052140c0c480907650b402c082c2d80c20303000e0002c80002d989060007080a981c1c06030300107102d24564041031500d4003460000910f0702e801a081801007005210070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 477200773 1250 477199523 477199529
    0x6010501050f0d150602060702010506060f09120703020402030f010e01062f1608010b0405090c01020312040f02100c120807021b03030d141006090f260d032405030601 73
    0x3070344600f5981a0440180b140c140f000d454003104110018005500007040381c80f4000c1c9074001e010544604040c00020b006660a40c0ca804100340003000316410010144000c920441341140d54a03a607a0700854100da02c1911003958001e50305d401403180007a00800b5900400319403405040707019010404020311b012907120010945420640d807e10381104004e00101c018041604a860665490250b4003c240f22044607001e0750824001503240640407500b86c01840041e006113141c03030581c1d03800b214490001841110581e4242c40440056101c855601c480071401c1e441c0d806001840d8104071044c01406005d00d010003641600b00308445502140c801c001c4460320800b07840e20041030000174114050b1075a01e007002c0d85000011038440c200200094001d0200107100800c403529040201c1c0c1c0c0c0c0e025802205e03d4009040d400308107035016420640c1d00c0b5501d1040404409800c40300c0d0a040480300d21550000980b01d850400c100f180300200e00c8014284000c0103003032240b4010101b0b07103a84d0148 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 477202023 1250 477200773 477200797
    0x313050607090f2c071805010e0d0b06030709060305033402091b03041b0824070318050c0424090f022b0606030e10151d01030b090601050105 62
    0x404807000c8044d60110710960300754464080d40040c5024000280501c0d0340a02e5804c00c190b50070000070700c40d4050700500e003074075030f0203040d400c18220b071504d038a2110030029001d150184034401d000640340c40f16104190245200d8006075696003130f0808140c14094590800520f2440b0304c2012070f08002400d1401a05c143d41a208117640e070343c810040381c00481ca9500100c0b05000300000f00b004000d554201c014115900d070020f245d42d00d4550002603598a5000c24010203c600112102d47e29481811415402005441d0100d034031035441c07841440241117203d040326141d0141513000d075240380c44e000f003000c40e118612840551411848418a9156591040301c0e0196665000006481000d40403134020043c1c5180d010000d0006107890a2080b4403e050200303514600b2601081c00f503c45d0045104a500500080c561501100e5001009040c111241d40c1c00141010740090b02001c2c2290b260519400d036001146035601d5410207070200031000b8400c200941181c0010320140e80c2102c00d980c051004d10b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 477203273 1250 477202023 477202049
    0x60702090408040f0b040e09241f090b010201050c130b03040807020a0e07030f0501240210050106111209091b1324020f071701110313050607090f 64
    0x10b06021002e4812031300015103000056001103000c00d0404c0c0204126083c401105040756200c5850701c0d1602204420f0030280743d020184401d0421103c1601c5d504202116440c14050b0150341c01403040c6c0d0b903543e0140445030340742c0301044000d60302803207460381c030941c2c00002c07602d0a044080c005035035140c0c9014055020743e010001c10184502c24003a42c0c055030f07014102d90303445500e03416018105402281d031840005e04001a01041c1309181c018581242d10018030b10780031401c502d03501182d130b480024000c0114894510b22502d0a2814091907008050948076924180c164182c4941080300b84001d5080324601044111000e8541e4034000790f0004501c2d600314818009045612030314480e4645c04203111016950120b1b2181211040c00181c00b04000400c110380007816050743c542c141214441050780050404012170300d040744030f20100c010300100004191294041000280e04103440c1500405003074080c000800c641001401d070005000d0520208840c0303890240c0c8800e0929000d00500502d40c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 477204523 1250 477203273 477203281
    0xf0603060f2802130b030610091410020a0c150e190e10080604060501090509060411010e0d141c02033402100e13020909061c1b080d0e06070209 63
    0x31643c180c4020001d0846000f0166594842e505084d170000d43e03d19120b05882c10f804e80565000d503281d40c044034100c19514501101004c10410790b0340301040e205040d401184081c0c400a201103d0038400351178401070003c40d806000800a0002000c0d0343c0d5240030301035207a001a001080e15800104481000d860340c155035903110080040315602d50f0104859211318824401044a0354020034113032032407054200419518803000c0c550314501550702070040d8022144440071075110f4217010400420107084441442e4096441446a581203000c0b60015048103101c0005000d6161070010312a256100550814803005005500321000c4e507615a0400350f000000c0105000407075000034020740050141c0188500c2d848007500141d458034140b40320fa910324003002983d00c140d100f0396510300800380811110b5511b0009104404058005d1910200444244000001c428400594442c00c02c003c60300701103031030f200d940b900d004d445004c0e0005001a102d00c2200c40e840745002c4d13609854049941403017a403a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 477205773 1250 477204523 477204601
    0x702040506242d1206040605100c0b0c040f0608040201021005010902130e090c1c050f0a03030e01060513050a0605120309010e09011d0c0904050f0603060f 68
    0x1070b4611a000c800288140c10480039201c41024080c0a00000401c100c03884140404034600f0101c0c045505402c0d2040c0329414411101c540860f81c407110140c40050300507210340c005800d004510f8080c80c0003440c00d01c424000c000404a050341c214410315280303800c1030309211840000d04030706e0040e0720070041c1c40070001e02568030070131035054020b180020810465841d020180040d511128400740d28601354200043d880001c01170191003101804090b004c1010b4440c00c00030449010342021207040d448a540c0c002240040c001c441038400f0500051a41c00e01515016040e6104118080400e0b40b502c5000c024540724126400c484101c1c000f0009003c4c1d4880f0344060040a141c0c21441c5c000c04c1500c504c99000f0700000042000490988070725000c1140e0900f000031810003405018000d081c02e25943c8607202d203c4100c0303500038100e0f80d015400d00314904082070441d40b046580c41e1903c000f903020f02116090610a035900304c2d8503240b0074081403408920106d0103d8161501100440d85049070050b092 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 477207023 1250 477205773 477205789
    0x281a1c12031b030c0e09101a0d050108060f090708060711030c0601060806011d0d020d031202070602130602030c0a02010807091205031803031c09020d2a05150702040506 74
    0x1048101a0300941d601c902c002801803140e40f202c3c0e80401c01894403040c803890481e000074801c401040015000e1030406130140c2200d1041c120402d4940005d204032411002c190240f607019140c454010640c514110000120315500940b402c049030308520401e210081012502613403042e2a070030031401c00c8600c5200c0700d00e14400c41c0c184204900625002184aa0b4408800c5008400c01d0fa518505d42c41003080032000c0c207940d4406240e000301340111480050909107092a0905c8c001c1c02c1c071440703509a090715407050740c3c082c100c100d90f410380c0041c010403044429200240a40098030085081003020140b03641c0e520340fa0800a070500480b08000340c0c45621030ac50510160000950032001500b00e8581203a0381e405c003050740144420444d461a199007800808d880f9130040e41e400000c103038081500302000400e0200403c2c0d1b0000404030720100030070b020154844080d07049400a00c00804040c44104140e4000c0d00414030807040e6052110071255004141ca03038854044900140135281c80000401c48 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 477208273 1250 477207023 477207041
    0x405150705010c02060f06010f1d011403090102070318050d061104051507050f0c060301030b271f0204050a031502040909150605010906080f281a1c1203 67
    0x2d6081510740000b85501081c8a0b0180c45c0d450a000c400d9214130b40159900d8168284450000d00340002d5000350100c0f264074203100070781c10f040c5a44031000c07030480c460070350340201c400e26140d81d0001594000c00da8410b81200e03c04014404124071181072000094807039640f40f030068415902d9030196545440c000046a009040003807280c040d0b2414038060092a41003540c00b503c140c003650100d55502080441c4008007002c4c01080180b0b180e0a6595451850101a208030301c1030310307950914428582c02d034010400046a00e4000d040c000da400ba02d903504815403c02c560503460050008014503140e8a07400001d8076031000d580d0b0501100d15001e50024000d60744004045401d00da10b50083c026040000c24403400c070103000703000c80394442c1f0044d650500c9502c40c1c440001e41450004112010390700b50036400141034196583c031000c0761407280c072400a02080500380e481d52442070003804450144c0200c00118196403151111000004540c0e10140b50a00a4080c0001c1400340c88003d01c2940302c83c2003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 477209523 1250 477208273 477208283
    0x60f030b090a0818030718150504091a070201090b10051009080c280b2505030a0305130c090e01060e04021c030c06111207020615100c020d08031501110304051507 71
    0x20011001c411008e41540c03c0d203007111000322000402e0300d06260061612050300100103100604501c036208042640c020075840c2103560780d010100c00280c0381a04140507400d2001c11010407070801c020084282b01460098050140e20407082000c1800400d2090285604a80c200c0c402702c0c0060701100001c0001503a010021161381c0d0124108915401402c2d201600261501e0079040c050050038042e2041c2002520301e500078803040c00060f00c83e030000d0354400204544404205620341d995400700300c140d0011440f0342e071101408000c0900074800c041c024a6691410310b10383c20f00742c02184404514652040680c102c1460803403d16000e4502d4000f2164050810056040c08414040c0e03d40c000001c07000c0b2520001703001c80d00d59480021007038001d0628051065000815200f000342d003458000e403440600c5004842e01c4050b0b66601030b07607003926000324511a52441c0c404590f442d03948000000c00e0611180c44002c1d0200344000068074190f0b101505d23864400c6100c184003081602a1200081c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 477210773 1250 477209523 477209549
    0x40302130509123405120c06010b090f06122202150307140406180f140906040b041d060903041818021002010c080105010518090613060f030b090a08180307 68
    0x3400740078800e11041c4942c0a00c00303032007400c100a45802800c7c424007030182c40316448980180a00018500140300a8030020500b01c1051043c5000c160141c0220300010304a0710701404100c103440d0003140c334120008000d45d072203030200420342c0080c03480b425041441c904210b01100049102d4022042a10024809505c82c0e0310355681c0d802c0280825003501c0000090050004002a180c000451850580d034480200d840368540460500500140007408141d106840d555601031940761071140002d000b2070215800302c0e160140d0f880f41e181850180112030250f200304000c001c0315103040b0340000d0040b603040003c100a000c0c80c185c0030b910b0003084406580091003c4d0310110464055104203450640c58490035626a80c94006486031300407285c40e6800480760600c002c0080c68800782c440d0740400010b0482007504502d910120845202d80c00094160404440c14000d1125200b04560300081c110300810210030320355502481030141120406080c005038111134440c3d5024041500a0505400885 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 477212023 1250 477210773 477210847
    0x80c0a021203040f0f0b0a1103010b030a020d09080307111b060a1d06030c0301180516050a051b0706090e0402010c020f0f0d03020c01180e01120c080a060204030213050912 75
    0xc210003080c2e6040380400d180500a1801600d48c40c01c0e03034100c4d06c0201100c0d0460b0780e500c81c2c2c0c0019601154448503142d59400d1030000081490000c2c0d03008450356610940c0d0101c030640c60314900390700e02c408800c9070402400000e041d1354440d012624014060b00e4890b41c8030180e80314440703842c180035501c6a400341020040120070b00f11000518107d413000e03040e104020151080b060300707c170400e503000c9906200300500f0801c035034000d9004015450b1a443c09520f405810082035014500140b001c003819003181104004d155400f0407680040c050389801e8002c1d5041c00d40c000381c110507800301c0c005d000c1c0171070b95400120395440c0c45080070f40703050240c08200407085901c0c009482d00129402c0034041082c200700a941c02008468107410707905401c20702c001036424940e055402c80484d460407100c00544010200b4596400d11442c1c03c864807444001d6211415441007018480800301c083c802c5520b81000c2090b82c010014140361040803036001283e07620f01d42c6142c031041c024000311500b44145c0747d41d089 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 477213273 1250 477212023 477212033
    0x409140a12030b0f2805090103060b09010f12020919020a030c020d0918050912070c050301111801080702031303051c1e0f0e040f0903080c0a021203040f0f 68
    0x603944104075a0b4040041100b14810000114114102c1540010154202d100e0085840401e03e080e000c0904800110a40d00c10010301444005d800c01c030380654881907110b9840c145000d40f58094425402e0f4070015500741007140d840d0302c0d80560302034480c80b01000440c20301c41040c8401403844c00580c0003503503034a22001014000c0c1c2050b500050061040c250b048014a1048030004244c80d02e45100746081d0720400540c102410b8040c1010b41c4c075015000700000300645e1000240b000d5440b0340070315180d0520b0141010b085520103070100c01d4421082201a4065189200350300e00d480342401c000d90360707071103500e01240345000e040b0700015411509000481446400100030001214450349920100102e05d01150003100000c0070031080041002d501c26403c0c01010b611000d40000c0c07030304000500c00300d400a01580c12540b0744c03101d01ca03910342110081c0361f48101000c1e40b000c010500c19251102c2054000c1d40e07041c440300140d80c0401d0100100b020068920800101141c00c03044150844c4c0c001d0500c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 477214523 1250 477213273 477213293
    0x309150f0e070819080d0e07060206010303020613020a030803090111160c0510051e0d0c031a0a051f03110a020f1506010c15020d0606020705010e030307110409140a 72
    0xa404110b01c03400034009020b50700060400a6074400d01c07000706034500190749a0b104e50700b108007502089a2612075203040004200007000040203e0f50040499500d981400790401c040581004507162500c9595805a162404880101c83e801900940d881e40d408880d5401080e00d008801e00c451030000d0786440001494106890070f03030081c41005c0b50250348030104100c0c4101c10214a001c07130801e0185180b41140d0b103440c1d43c020300c4441620362910b280032010100b03c0310800d94103000b0a0303030f84001501c54048461072840c03c3d0b030140c0315012098203010000d200c0b0311900344218032034035200030b00803421340c880c0d0090b0020502800c1065100e080e05c90021391a03030b03c0401c010440c2c0c46207007d14007541b40c444640074004e00b0180c44000c412041c41d11a0f1554804010445111503000c1010103001e00303ca00c13543c1e004081d90303070190811030b007400700051150b08502e07903c5110354002d10540d800b103101024141c421410031200003481d40010710300701e84200311000105407180602d5960300700384a41c0d044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 477215773 1250 477214523 477214541
    0x30c1505040303021b0312060d0c0801020c0304030c0530030d141e042103021b15010501050403150902010c0203032106041b0804151806110c0d0309150f 67
    0x30001c6580c0f510500310982c1c80c0204091140101d10b440702223a01c2d41804d00000391041e00500e05503800a132140d0000b402e80c0c2c0312108040040c2c0c4002000c000340095003e40c80d000d030000b11003407003250703184148060601e0102c114840100b00240350941e00d0000c1001242e42484841406005600c441c413100d1900c50030403030b009140310b52004400c1d1000181001d86508c110390120003108500001509580700004003044042490350030402c1658403200d0b20003440d440141403006041118413841d0b00d00c0c86d448183d0105060041c05d101c103200007000911080c8841c05c0015002444a10500040b00c01c100075501c080e4140c00b000075055803500ca022108200c8408100e09443c0580b42d4405020441340e404071240d100141c0501e11035a554807400b07003660010300901c0410905402d86942c0c0e000c848c100080c03072035505010031055041080724002c0e40000400c1400542c00d154034205c1c1c40d616581280f04407000c06035a1200301c010042030b89d960740c46181c4542c0040008003885c5070242c1c02482060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 477217023 1250 477215773 477215797
    0x6130608070816121505090304050a121a0705070201030e070f0321020304140f0a03060c09051c170c0111120415051005130605090c03071701080604030c150504030302 73
    0xf00b001c180008180c6252000560100b1800c2c3c8404092185000500c40540200d44038003042100060035079038100b1813000703840442c1d1140c0088180f4503040c0f4440e1241c80c0c1c44051518010100450140c014040e40c85087d02806e001c110801d00c4014607062180980040440c00a1148040140402c080307144000e0003100f81031101c1c40c0008901a41e680c0911f2141002038411018070b40070038141201102c1110001034820200700b5101c2d41d607503040d40c104c203c2d180006007060008104928084240c021210308084034024900802c0d02d030054400c2d4040c00c5c501c620b10700080d5003140310030254441d1014148024a840c1c0b180a40203006c080c0030000e85003520300c000034010903010151746100b1540980140d002d4002e00301e14140034010407000d50050010042ea48031000692034603400082823252002c0310302541d40f45001071016020b41c0c1c0d02c80d503245120407100e005026450700001e034150096058100200c0700c40840c84c0c00c0f248503160b20500b00440e0f042500344001c264040e000352001122603 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 477218273 1250 477217023 477217063
    0xa03020c06010f050a140112110a020106060e090c09030f060f0f010602061504050c040e0103060203010e0906070219020a0819330b010c0203030a05040315050708061306080708 77
    0x840f802d100205940c021290300c54011001081446002c0080704008001030505104d1051080a058200d40c141c000401c40382000052040c0241d03420b124001c05000c90f4101118111002c4000c134591100c01084609200d80c00181503210b99400c02401a00b00c113118112800c614012144684825017aa03110010200c204001b2600d24008181c10f8480d1002c540c0344002c81c192a402c01010f0701001e0f0001032209030810001c110205107090b2140618080d01015035203500d8004400e943c03c0d0020700050140d00b168003440b00700380d03000c00c0386904440c81e050f120301c10011a0000a8411903980d0080f16248150a441c0f00c10b030000012aa0255000b036041c078400c03e20098407410751901c1c0c2001622040752100404100c0c4030b5a03400727240d126006241407400880c440c0e000c44e145510050b030356804a031020908004010090b188a100c0d218541c805016500b42072801a1070340c00081c0600e4865450480319440584866000000404498003201d88140d9281e205a440d44950a402c007020420 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 477219523 1250 477218273 477218279
    0x714070515091503040209150112022704060b04030f1e060b0310020405030d18090203011710090b040816020a1409150d1b090c030e010b030a0b0604200a03020c0601 72
    0x201040c4e0388200d4010380340c514182c3c0c072003000c1240031001101050600820b00c208507011036007072010b04019000103490101d581b0105400d69035010a090300d0510943c1040400d0000003a0401510f0880341e00814426070040b841c07601020b60440c1d1650000300a070000043c0042c441590401c03100004150207945c02040c401d103180c0300781c0c811030040d5030300343c0d12180384100321910442c00e01402861080c4610541c40d11001204140d90084e401510352004a10b40c042c6248030520200f80c032210041420171568130b03580e81d0103440c4480208040c28540d03000c20050707420311082c0c08032400d4a40c01020035240b01d0300c1300070507200514100e1842d40114401c000080c0004845110303035a03010381c01040219290050b0ba90031071620465122418403101c044400a81c1401500840314402c0ca103841c081006c411400c00c560071501070321081032280e03201442c0c40c8040340c400c542498010b40c050310045801c403407401c440704050409030704a000510b0006000442c055250b4040c1488442d0f58054030b009076030b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 477220773 1250 477219523 477219559
    0x1c0c0209100e0c0c01021303050106050909010c08060f06120108060a0e06040c0306050c2502090a0b090403030b01170f15100816090512161505071407051509 69
    0x840c01440d054442c2003011506071160303040603200031480d640015142a03402c02651214803842d510450301c0f130391650010b001500c1d10605440d4490303201c0008204142c90f99a00410005000e44440e009a0440f05d000040d602c070b07081128441241c136406403a455a444050320f03a2100115040c4100d40d2030907666281030207000c40d81c1f502481d0813009042d1314600b561103040c0280400b4040c403483d074908100364008040040c0b81c00c540500c00101440c81401c20340103011203014010b012800061502208000650790004020b0308507400d8500003ca01c0c91900050740d200c061502080c02a51000c6d04010310061000f5600c0d1107842d0440b800300c8694500390a00c41041c0d604102c100c080f804581c0018180d174201d0800410001103440c060700c00d960f4480210b07004011000b4400510340080581e1120140c0080c4510b005000070b82030382c0c440d9081400020440d000d042e800400e1500050401004d4003020080f8002401c40205074815420168000315040c2d8080c5400e030303006546860502c0c0d0038407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 477222023 1250 477220773 477220801
    0x40329090d02121c2d02030f0a050f07080703270c0503030f030f04021503011d0f070c39030309050301020403020604092d060e06240a021c0c0209 64
    0x41c03002e8002a01e0100250f081401510048003c1080004081c104145001c81c880d664170a8403101000144c1c2ca007007070b48010b244401300422100409040c003050020000300800000c6e804840da00d4142641e03140ea10701240503000450004d0039115100342d2000000a000b400156018451803c00030215906c0e0141a2030340580b0070b00821146081c0002294498032100740355000d07200904985003d0303113681c5c0303411150304280c10070348100000d0100741c100c1450280203281c0000d84d500e50b0a502d4541305000908645035524000c1000d00d04e860342400b94840300d030341d20301d44280000b054039156a8030310f040300024805100c2034001580341100054a41811320032030341900d4014000d180b0341403c187c144005061848154440c00e0601c20400340000f041c0801810960100c510115460340390a4200410f504003916580c030074036141103002040030320050b00340f80120890b03806c81d8481c25425416400c00c860074000c8410300d45401c110480450740705644940c424800c944020040d110101c0100c204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 477223273 1250 477222023 477222037
    0x90c05030117070504020a050a120e071e24121401030f020616060218090118090507080f030301090606080912090402040306180b07020a030203040329090d0212 70
    0x4944104018802100c041c5502c141e482071000484511560320300201c0c0c200c0c1e0002a2a80010f4008600c140f103490f8004031100355505171030000d01c1610403052405448035075074801d542d000324104030440006a01d0008010091103003041c080c810107868042800c4490802d500200051541e010000b00040c1a20030030030481c126038a000d005a0071603441955a200000c0103a070301140501540040005a00702d030740380c1c60300c141d0016807101c40c0d588801e43c42ca42207410940c03013140210018007214010050424600d003260501240301010f0342000340c10800c09802400050169038186040c1c481d001000758100c5102c40f074200b00207545c80c40c003101d0180081d1986031441d04001021a500b40408003d8040c112006000500d026900d560fa0001c4440c411044842ca02005050800f48840d010f160f0303501040e00e0010b804004403503a0000d40724442c0303002c0145a8803083e00c0f42581c10f00c5400c2d103038820700796895440210b402c0400c075003a91400c02d21078210041c4180400b68503001d549109031044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 477224523 1250 477223273 477223277
    0x31409060405011506080f0c07080315040f06030317060a050a060e0108060d080304060e0313030302071401051e0d06170a12050c0a03120906090803070e0409150e0a080310050a090c 79
    0x190b1f031209000820f901d840502014840c507000d01811000c0388402c0001d60255120301d10492032044148280710070740d082c50503014102481c044c4100017103500301c0858403840400c021002d055541f01c1d00068099035080d080540c1003448050007080c0300d41c21100c6074003800d0090301c5007011070f03031842c041100a40c1e5201c401801410144080390028286400c50103c0c22040c001b602e08ac58a198500102081cad0781e401a001a40001d40c2003003500c208103e4003000c8142841e00e14078140200302104450b4680d2260304803520710004501d00b0041041c1e003d0f202921707100020b4a61000001221546c5038071901c015511a58580c903c0040d06008408a403441040f10000d44202d0005403400c0e1043e100c2d044400413030030b88642c10400000c0d250b22441c0c0f52070307204001c945c1e1a818040700042006a03c5801e90b40103074901401c05d804200c4060382d07810301c8241c000c404580c1c0d030036a560160405405c2c0d07000400800003c0180402401162100d0382601c5043c1c8200e0f00d50b075550741400054614122000300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 477225773 1250 477224523 477224537
    0x1201050301110a030f0b040e0718060807061d030d030912021507030903033b03041a0a0e0915031207020a030209130804060302030a39031409060405011506 68
    0xc4614061781002c140c601c152500068004041404642030380d1001104c05c443d60051b000c14172014030114499000b882240404200581c140810969644414069882844144801c20440740c0150024104045010341903d08605a004001d80a01030040c000c5a0b80d0b540b02c20304a4640d840024068044c502040070070165448172582a00108100c4200b0740c10035484000f850306040c0500750b020800c00c4040340079408145c40f90f100004a1494441e2911290003c01c02001800d210308504131010b407480f6411a624200c200313066440c034a1032114a42c000584030100320090700c01201e449400070f4140c0507030740f0942c5542500007151103940c2000f903205952410500c09418048980e9520078000140c081c0e180d1f1083e240c0d0380f0b05401a92105000903000807c1041b85201401900300103420360250044841a0926501a407445c4a407031903900070000140c1c0f03045030b10980019043c01210062548a820405030098980c54103c2e81070340c4541c00c2c41c82844a440001c48400210742c900d81d9145 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 477227023 1250 477225773 477225787
    0x1506030e010b0307140a0f030309030305032502012007080301231e010f05030c03191d010e190c09020304081b060402030f03180f0a08060c120105030111 67
    0x260040c118000000e12965030780000d00c441d0340f0200302c42c0001d0940555804d00c01c0d001c9401304029000541c012580404003c181000040c1c0c0103c07a06003a00d5041c20402d03200d81c0e41d400032000a04d084440140810403e8411101081d0194061159006104140c0c2d00083c04900210030b17910490318020030020081004000000e6624200c0e00142c01442982e8a00d1080304001a40e008400a045030041d40150f02d0350300541c0c00402907247e0303090b141081030a41c5404148642c903408010001c1c00f0403000c000e09070881894643c407900c0203100c500001000507000e0b02040d802403c001031309040038480c0c0144121450b410a101f101b50591182e02000300c14200b00c2408040d410141c01102e803400c3c14000d8820140c91b050807000c048501100078a818502401003500d01003c0568840c4150420071070703000b2a0340d528510248002058501c20b003914001c00118a00d26420f503c0302604d8011201400240c104038402000c1c140c2d15000e121a1076600c0f00100742c22200600c1200b01600d50401440c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 477228273 1250 477227023 477227027
    0x15020705010e060c0304180b0907080610140313030314010302100c06110d090201021c1b03020a15020301050112060506070b190c050a0f0306050f1203040f150e0102011506 75
    0xc1d151807038043c1240742401d0f0000801d51458106400c9070303200e0340020038010b40d001031901c200d42c3c0030340b01100c00c3e5801e4103141c0005004294007500c4c10740106074a505c0b000020380161803945080400044056880c603200b9080301940090701d004400103810f20036040c2800c940052114141c0390020450300781c00c020310000740d9810b1402442202e03400d441358003102190034202e01030400420350000200f0114100c3c0300081c14007415070707258100c0f03171100b0400d01d40095201d00d5501c850702403482041e2440d205800d045c1c0c82e00c4802a8010320111102d600300e0b0000005802a50407a24207803240c54041c0310078503051017614110301807990003100c18080d04011514041520b90071141e14001645001c40c0f25500805841d410780145000c01c030000b501000c6268084c1442080340781c00e15041204a00788030010f134004007c20400d520460907840c0810f9078080501c1101d008180c1c0d00308000070199141c1405583c0441030b002c00b4082032108181c40d4880d4018000ca802d90206880048025400d061007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 477229523 1250 477228273 477228287
    0x11d0906060c0f0313090e01090c05130b060c1c050705101a030d02010501050306060d020f100e060a030e060109050f0718050607050709050109020a0206070804050114070c0501061502070501 83
    0x310060f803090050030700d06283e080c00141030542c61441c610060f00c0c1020f400c0f60603940965408002c0ba03140004550100e0540740e0004145e8400f100d044411100c1c0590003005820500200e540c401c03000166041103550002c0d84031621840f5503d5140401c80d0300005807240d00518001a201c1d4000c8030303040c41c41074050703448004805e214070074162841031948003180c61729442c0e003552000350390354500502403031904102c042d501250880e035201602d850381d40410225900c000381340e4020030703441c00c0d11940240981e0b03100c040324101070109038649000d001c00074043e00b0110320600c0c103030007074000101d40c0307031541d029162248002c4805c404803a02c034084d00302d8401e0200b0000340d00070f17900d22102160b40c1c1d40f1540101441e5005800901703074903091014200403910180e001420b980c2c4104550190030b500490495440080d42c02c00c942d0329981c0f820b0090244c05850b00302480b0300608410804007640044c0c0690240f40600e0080000940321510711030102805482180581e100303030810400b80d842032070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 477230773 1250 477229523 477229537
    0x6030312050601140307020d020708010b030309060c0c04090b0415020a0503042303040f0905100f120c0305011d100b0f0d240c0212040303050d0504051614011d090606 73
    0x5080200d000404c480481941c10541e815070040c2c12001d04180d20385d90402c40032002c0c10310ba500030401c103401c03030000a5a80c454070f803103240661008150382015017070074802c400c0d8802029100384010015850150000b0204035811181d003850300e0348000c5445540e10a543c16400280c9981340b0f140c540e44ca130500e02d1451010441c07800c1600c00c0890018030000e0000d40b004060a55140b04585d04020809042e0f400c001c241d43e41d412004201040182e4194541c60100c9602c500b80600c120010708005400d4a100d800c09003541d07003040c1c190341f0404c0340f814800c02490f004200703460310740c02034071000401c4c0d520251a40c0d520000400f10f0904510701205204406031042801c1d080c25a180c0c41d44582080b05140711141069507204007684042d014800c0c0c0c0350b14881f0f504a00d182c5421a034010f4894007035040c60300c03240d5030754000203010018200443c03120a80c0c5604000c078100e035503207074500b2840000400a0f000a02d224039031071800065081d420f0081d5402848507502d5580e00051006641100d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 477232023 1250 477230773 477230777
    0x7090e0624091302040c0305010609050d20060c0318010905061e0313061d0c0a0b120a021b06070e0307140f01230405150301080a17040b0f1c06030312050601 69
    0x3d101c00c00698603440f81c3d043c0c080c1c1c40c1c0c5000c00c140d890f0039009003d114095000500820080e19480d00051005104c0c0034070100d0b01340d4600c40c4400141c081165801510b2501c0071910000840b5111040c00604071103516409980b68080c4580342d40601280e0700503541200300b03c8414a1001001c429420b003c1c5520807041011107041c4100307910740c0700c169401401020a4150203944414030700c1c1d42802040c1c00c1e00300a07038141200c41e2605061104c248141c01e851200e01c00b0800204200d41d80b25012119030166900c24410507050359100d040d01e400082d0f07098800b042024541c04e840b03007400b00b5000c0c2103550b142d5105680892941c188000072800c640ca09041048400c4424158030400c1840c3d909104180c0045444a052500f03008400b01200300d0788117800750130b000400500000051602005610004d690f140814050303480c074088c0910b80003500902c0010410006070250034016000c055550800c2e286280d2000c00342d803086626902000c5c000401040490480e10000d40107190021018 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 477233273 1250 477232023 477232051
    0x50f010f0c020c10020c06040b07020f01030209060a030c1b060203161b0f0c080610090e0106210203070b030c07030212070c0302061b0307060209030c04060501090614040807090e062409 81
    0x504001400340d03208c0d400645016001041d42c5040d400c0c040758000306158282011868441c550380000c20302d0051a41c05c00c100764680031020245481f441041c0390b06040b520000d0800340f081e1070000c0c0690021508c0300848401c0d841510242c9200d20340040c80380a09081ca035454001c151960749100c440f001e001e0300c1042a00704000385c182002c019452180c1c2d00340c0028480b0324101089442036a00802000755540c0c1044420300540500c400e2060b020f002e000c40c1e07080d03c019240b000c64141200c3d54091a0f0f074a1020041021503460039000b855058820342c203440028480708c0400c2140d0242e0078000e403410b03041700402c0c401803c180b4001c0941c0401c0da445002c01900318110240b840c1d0045104132401c980114500d040c0741030130421041862402c450030300c030b0103044c1000200701c007400e0f00c203500400c1200503580c100c00d940d840480e4045d203d01c0007038a0f041c030744841d850405400f00c040c1601c0d803407060a00047c849a08c2d250340d200c1c40401e0b078062a4003818a042004240013003d4581c003805500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 477234523 1250 477233273 477233293
    0xd02131a060c0312010b07050601090b010315080c1206040809040e1e010906050604020703020c0405060409050a0503210c04154121040c08060103050f010f0c020c1002 73
    0x15240940100b4807028002c540c0c54098444134180c1c40c506a018400c401c600380304032400144046186415911800d20014070381d424140100c0181c00300c4110790143c200c41c48404100c160010840b80750022050324010395003500404050350340e040c2103c02400001c030902250380c60346040c0c0c00929070322911100f21400d00a807010140030201c480f110b4584a603644801000800c00c26005184e4400811074045046c40a039443c081e4030340d6941c1001620695840001807160b640e0f940c07060040c1500b0100301d4034601d02e1403400682d60b0b0302c006512007581040c02c030300e509100b10354110742d07100c1c04035a01d4039800c05240c500030016940b00400350704240034064400000320480c8003404004a800c0c00f031403084455600000103080c41d0804920802c0c0d034030400803c604403269800820000c102001100c130301e40c2c1d460078080f02c29186074000300200d018000c00007043c03200000b0002d4022441200800503001c4480c0d4020032520410b2111000d60412140c4554528080145032101c40c0c040c0165010604 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 477235773 1250 477234523 477234529
    0x403020708070f0602072102010806150a030207150516051e0a020d0906080621011b0f0206091902010507050718020a02011401210c08061503010b0d02131a 68
    0x495000800c500c3c0c41031404000c4c142e4100310080081400d48000359100b851016464001c21810502a0512082c01c1c085803294030f4040100d058809104e03091615400c2c0754a000b0301030f502044c01038441d00301030031503000d00d640c46108842c083c84a05160388100b13000c1c1d83c419181500400390309100501300301c40110201070320070018401c410907076014040185078418045c104500710740040f0200160b050402805840d1281e0701a050b04804000400340045001e400d03014140d07204507000c41c118114900358455401c1007401d041804942c013920541d03510b85502c00d6031280e0f68072441c1400da958585402c00740d4050700040024500070010356480729120074a20022000c14541d4043c050b9000400880b42c69080c4148100c003041c6030440d0400c0c1d490140c40280710402040044240c41000603800100300e506140100100810019220301c3d00c0c05034102507e210122420310f000b0350804041e190686014560300d04015030040007010741d84504968840180080d12403501040d910420f001c034169 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 477237023 1250 477235773 477235783
    0x13090206070605011d09120c0709021207110d05090f0112110306010908031204080a090f1e090902010c0b0709270b061e071104050a06060806010f02150403020708 71
    0xa409040d002c20154904003506820505640741d2428175424402070201c8003030007181c1090042814a1210789450704505000c1c1440d4055000340b480d584000380c10b44480d112400c6071407040290303466001a260340c0398800c80e100c000104010300040e40811100c0c5070b510308008503441326501898241c14402454078124101c541032a00c000780c0c983c01008102056034070030001405044200091414000c0c0860385c0305840101400003012120046500c1703030300c42d1090050381c2c0106046a04100c106d03075141070400e400b1408152110705c0c07510904000c6141d00d014002c044202c1d5042e56081c05e2800c1c0f54965400800e0701825030010801c6007100055000b540c1095841825800c4103801b44080018400108070752958003514002d10742440481402454001075541140d02e106680d07035203491034640442c40c1104880701c598024640014409101515400002550496124055039450f15401920218070403005c610040c1d200d00541e541c54050b001d40c268000f07200b80100e4512507103070f1215034141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 477238273 1250 477237023 477237037
    0xc110d0b01051c0b0606070f1b05190332010903021c0315030b09152409010b040b370f0507030906231603030b180613090206 55
    0x108116001071090f440c2c070516110f00444192000c0303c140c003256036000701e0a5001403103d0700c0303035802060003801d10080c0740c40d001000d5840500d08031100300d43c0d022142030300441c1c0541030050380d10042440241c12440524015241c10000c80200300c40c12850a1300032080741d4100849140390748491800100b401d0085001c0644660040d054641c038010300b03e802d01550012600c10541001118484020040013060a5a40040c3d082050b43c2c0c900d20340314a0700c5807070b000a0060001d21010020703070380509540004c00c2441000b8120140b103003a010820304403420301416030051802c1004222500d049001050f482c085912142204000300003550312013004032180d15526041c10a8903045658050040d09105045003401400c0246e240c030024070340c0041c1d014000501a040406a04040c804c107200b6000c510400e940968920100c02103100403402d00300c04501107420140c406a07a4a4032003014003100700a161803154550301d82007040400300c03c201454511aa6414041d40543c030360000900c1c00c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 477239523 1250 477238273 477238283
    0x40b04020d0b18070504030f14070e0105091b04090207170706142508070216090e160305100b24040303091e06031d0a060c030b011107060c110d 63
    0x210030940b802c1c00500000051109807040d4480d00b000841c90700300c810f48041d01d40100140c00c0781409481d110003100880303403410601e84201e400c0082d40c01d904000c1181690001d81c4c01400c20345410329800101c0320301c2d0084402502c0305000078001d000340c2d54081c0c0340040c01807201c9800c49400c004214403952000380f06449644d281c03412500e0001c0400c0b17900c0e40009601d00269520404c4a24407070b045249030104c00f04008d81580421445071080141d06c101e504c80c568003400d0305648807141d030010100d841340f440341ca02401d440350200e583c21154140c1140d420401415602c0325410b211002031060140035036104894105003131520000c0c101c90341c0b006600a545d42c1d5924150b00780a848034a1035440b0302c0c2c030f0f00f21560002400c00d05001c9082c007290741c40e06000c0360204660072080103c0001080d0704610740310b000300030018416075410070400c45595880400c40e40100e0401140d503100300803d084038540c48107034100f15840c828140c06d180702d40200c120300400e42600000440c0c030a60f607101610 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 477240773 1250 477239523 477239531
    0x307030b1609120f0b0a1407020604050c0102010911191502030904050a0203011d07030b0d1505060906010903031407020414041205180906030f01090c031403040f050f040b04020d 78
    0x501c01d9084040034000d8210072008070f103020780540c0c480380046070303a2100414403501e9401003007084041c0c2d0090952502400040182e5140c8020000d42c2c41c681207d041c4c41a2092104c0d44a840d401803180704a42d80d00506011914003a060901c03c7c1407801101c0350a0000e09200d0010b00c03803c40850111812160f94003035660740481008110554034050a40241d0600c1000100039111001caa04800c030010340c2080001c550f1000c0c4264020941540180c2d0000d00c2022000208100020040301302003003018204095101c490a028a801045801c1070104014000900109000b00342602650300101105440e11300680d0200d01900d1049280481c0018800c00303102c10490540b10034070403040c06140450500e002e00260110600c10404071078041c207130080c042142510280901c5850700702410003884941f82a18060900c24440c1c4000e0300d880340501064a0100b002004070b40860790b01540c0b03103695501785420045200e2885503070030b07030107541c5031803007119616280081e16503620440e034001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 477242023 1250 477240773 477240811
    0x70f17030702060a020f180316060c02090a05010e0f54030405040e15010807030209010608190b1807020106090b0f0306130804030b010b042c0103030e0307030b 70
    0xe03180c4403000c1c10341c81104c0d006000c20320514000405036944a6075560000c404c42181502003818240b000d00440c60380c05409c0c2001c200560040b50105601344240d55041455980549500413a4800c1c01f901044407010f40c0070842022200c201c00b60040504920f000403100110340e0f42e00d4040c0c03011100d040400c0164490702c0c0343e201d802a03a048288101201c02203002c45c0710403140c1c0768032131401a5481140e079041038400310942007101125110020b01415100d5840b41500340d9a0b04a07448120b1083c0550000070644a12501485018000070f00005013891704448601380a0700031201c09a4210500700e21000207400291485809403030190000034100342440c44403010755a25194003809140303904903140c15501d000500039804034501c20f44401c8151a0302e0301424501c030fa0390010b040c1905400c000f0840f80c04160003007040700c004500480281e5200c00d60303458003c1100702d070540c9600d501001040841e000e241d214000c201d00406843c205130700c0e90740c1c036980c0e0041a90440300c40c5090100e95 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 477243273 1250 477242023 477242027
    0x60402010f030e07180b060c030c010501050612012112030b03060105061c0e0c06040b04180905030a031d16050a060c05121c020d0c12020a090902070f170307 69
    0x8441c101503510303040c402c8400078048669180400e1141c010041850038070b003000b020640d80180c006203c010507242d641d040c8004015030740e400c5055061a84c1d4030302000010f003807400c40126082031448201028543c4e01c1d140300b40050b90034071348003190840c0306126140000b43c0e5107001c548444c0400d450020300d01c02e4034010b1501d0203c0581249000b40303010000002a1034842901e80c134034600452002c00d034164042480c3e8101404603c4190b007000c0007040100b01401d900014205840100711400048a01c07003020b80f003521416140a040d43c0c1081082d15003052107a006503150505c50402d0341c05445401507490b2a058070510b05000d4408820428066494480b0061000b4019482c103886040004d444180c3c440c0d51003424032003a00d40c0010183c0c5c00c90306904021030f003c0e040c01411502c03100440d4150303003e40703224080d14002484104044c01c01150520a403403465006584032040c440c01e0114440c025404183c007030b90340c0d00000b400d5a000940d400700c000e120101c100c5c2c030180c0740e060000d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 477244523 1250 477243273 477243287
    0x10303050c060a200306040e060c0d0b03011107020613170109150506010912031106161b08090118030b27191e051519060509070e0303040905070206040201 68
    0x41441c843d424502030b2294000c48580894131810440441c1e0303982d03110500040c00820f9003981629407802104104050010b0400150015409081b414030155039048200740c2210641540800400d000384181c801606248000d0509502c00800d212252521004802001c035070103c014910344e91035a0100c130400c24040103107054200303001c0007800a82000b200107800300f10305015503112898035aa03141c0174148661030030302c18420030310169241410b0042c0581e540400382004107021030149103940800500301a452500560001c04841c03c00a20000440b81501c02543c0000e1443c510031010020840b0510f0309401804c881c050042c00e1040201820a04540248050050381051609600303011440341420b680c90340c824500c0340380d0080055203c100a030042c202030042d1003400400da1503650708002031409111074034440d90711060740381156020b5a442c0e0203010f0b04034400c07401240109000c0c5d01c1e04034480000034203807030520761078a4007081260401c4a404c40142d010b0010f100a42d600700e0340f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 477245773 1250 477244523 477244531
    0x20904150b0301090507051c051008060702061b09040e010c180f092d0c0806060c030d02030a02070b0c1321030f12060605040e100501020604121205010303050c06 71
    0x4180039a945002036000c1c841c00140704403e0280d40790b90000d29924807520444407802929005c0414482c164031414006000032100c45240040400001c40e9600d0005011403048000707600500c0e035590303881c60f00d2951200000703070800d0040c0300340414403990b5154010702e40024044000080c3c07050300000010800507400d0302e0b07101020000001400500d90103201402522180480401c22820014028540520003c040701c60656503242c0502803642a0b082813481c001c042d5980c20b4140c54030740400808d48103044664410354410084c203030342440160059503104510000040c2418007030340b120107410004a460f025950000107424203503030100c040900240034140f14610700350414603034000300d0507080c560103818403010b815100c003520320034456800d200183c540103003e4651f4484014120750020302900e040071054a00080d01c48821075000400c80b0416401850103480d0342e01c4240b404a00203d004041020b00f54180c0300d0480e8900445001b180b0a9480d240e48900b105500c5007850b101030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 477247023 1250 477245773 477245801
    0x90b0103020702030a06202d030405150601020a02061b0601170703110607020301150f080102090d03121d070302130905060c0703050d140601020d02070510140c07031b1d1305030d0906020904 83
    0xc014000805c90008533104641000d5000d10301c607844920060385407040503440258489000100c0d03691026400400324020140d200443d206641c03a13500c0b120341400d071040307081c038950310810b82003010800d004c41e001c080c1c4201070f200619040c4250042801d4412000c1e100000b422424010003030501100d030300e08010500500214200005040051b0028030207140c043c08000c94483c80c060480c40360741c080c40c1200340111a0b0109d003810340ba5000c2d19090306d840240d102e10100c84150f80c3c624134a000700c1d0709007a03000c00a803041d5682d4462801184d00034103019801c011050250f922040e4042c41084c0c6c00703040c1c1c1d001f0842e20340707040e9000a1414040741440e6013150001c0350b082080380c4445080205030041d508220f03003003403240c2c1c6030a0b81c40d00401400a005200d0304400200307118910000e0b816805001d03070488909626050440205102141681c814034014800200300d1b981c0410070700b25080c4182c00b600c0c542841040e446040e10115181038600b1030740006d0086080c0b030144140c40e0070384801 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 477248273 1250 477247023 477247027
    0x3020a14031b060c0a03121a0a0605070311010f05160f09050405060105070b010e010515131e081c030f06140f01050f04030b01090b0103020702030a06202d 68
    0x402103070721070000c03034852004014120910062950f0300825200005071460460350b070b08802e424000c204e4501c0141c0c0e0820a0319212080c1e800d000c01030103d00da000c002805511099247c45400c99182d40240310035400c002c004800034842030300030f00480c0201d003121b09002c1010301741074000d040300c400c030041228140300c0e0030003010481c07541001d0514100d800031100082c265882c1001a1400d103e0302d50001c0c200380300c0000121b0514040704101d8141c50b019102110210a1a40c03070039018403c030000450800320f4070000b08240740d04045d401d440019042c652107491507507610346038901503044034110314404ca00c0019000d966031510031440320340380d02007003402003515140c1c01381c2c0c1c00310030f1307024160083c0c00780000308155034094400c0784c1c00310f194166841da842e56070382408000c404080c0180f502e00c504203120075425601c00e0007a6503000e07030000e0160140301059551307680200414501200610700d0880e00c041c1440d00b260141c010b00c0f00c0308050060410304000380221480540300100002402 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 477249523 1250 477248273 477248309
    0x203131403060c03070c0b06060913140c04032f0d050606150313021504080607020604120203040b16060b060a0f030b04090b07080c040f0b0901080a06230a030b040c03020a 75
    0x101044008640d03030803087d030302d4060700d034000441d00e01d1240352030039038100c10300c5140d004481490b54400740507441e82c1e8a107a151501d490841d25900c2c800e500c40a000205000d4a4a090782c140f8840c45070080701d04012000c3d84c510403404170700074441100054074a5001714082081c40d0a090481c00c0005072103015052845c40d00b44c2007669030021000010303000d409200c110800342040401164050900c0d8011204035142240c07000790b88400480b021a03462950317010a0031001e0002040d2000e84164a00e2141003241c804c0000d500d0741e61011060342c0694a80e550904203494410080442104079650203048900074000981038a8040300c00c00d02580c5408071090103c0c8400503100c0d0442c6003032031706440c5030325036440c1c0b176605008903000210039451101001410044620003094030110a0b22001035030359446048808503019449408506c2290140090040d083c0148210448100500e0f07030a03074580380e0302d0307065008108441c100e92891005d01e0074010b61800c2c542d842c00910174540072024000d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 477250773 1250 477249523 477249527
    0x113a030902100f0c020301020d1e05071e02010b040905061008061003060510030507060203040306061d1504090f0c0807080a050c0603060a0e040f12140403020609010203131403060c0307 81
    0x1100b0900c4004100c0102900d031081c030320a440a44c0340b190001e001f5500c075080160904014200c18030800007900c030415030083c0049543c0106840b809440d21102012000c102081a0005c0d203540c440e8210356071100c00754010780d42c6200741d01150780180000d04541c030b02040d4110600246810501480d80031604000c01400d02001c054140c0f60b2000b0082941d88804c92407490600e0b40e90030052180c0244a0041a65a800400740044074060341080c04050350b02c02400d1403c60f5141c000d4041299104001a45080c17184000100504003500c0020010503a4840c1c200203c0c01c24800c0f1130380341d280c2c582006035210402120020384811000b800060081d55126075a521050b1405130042d0004000191b96507600070000c4002c05040c10030501614043c5405100850f11507070841780d035000503441c0c0c1c940720b2041041140207207076890800d207030a0075030b000c200e11504004d49140c11880100108040b018900e8030140090120f09400d280c10340e1041c04140c18541c00414400c5140d4040c010069056 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 477252023 1250 477250773 477250789
    0x906031603080a050714210c0c010c030207090c020705190608130c0b0706020309070603060f050409170403080a0306080312011520030d060b030103050607113a030902 73
    0x941c00b0400b940e4903641c0440c02e0321940a0881c0c09054070390080e05000e801c240c042500301d1141d848220a48010b0609250010f180c043c0c881d85103003590080020450a50003002c0034200940030303004540c0e8255a40d8003072001d50358021444030040e00543e504000301d08100c0000c1c00c01d00c00d00f203164548a8101031000700002e00050500302039030450060001800118824840640001c810456403202e0505003e0080d60040d5013540c01072060780400601c0511900c121380550f40e4134408045038074034060422001e401c42600550315600c482c42c581e9004807614000344011445542900e072110481702d009411a42c0c6a0b002047d6500300700203e0b84c0004031041500d054803045100289007100e2030804a0300c0550000c40140c80e000c41d0300b203c00210314008050590390b00c5940c42440303001e45815042d440b50200b0f200c0285180e000300d01285005006210070444030413580c00300d900f101c07120010005c1094100003030f10b040b080703c00103070070300f0840d04840c40c0040c145604050140d4078560780410260 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 477253273 1250 477252023 477252029
    0x7090c1b060f020a0903020f0306150103020f0c1b090a0b060319020c1617150a0203092104090e030304121107050d080301090506030a21050c0f070509060316 69
    0x800d5400d02035800c1200c5a4400c94010808207011074940340060806400903242e800300b644249007000b034641c07103441c002444500c141403000d0030344c41c00e40c2c0003001503020b034010104c1441c18100904c00c4003001c01007007103166114520300c41e6544c080c61084080c0f2903200409051019030320304052040c495034403120102c80e0000c0d400198a500c0c0a1503d240c00002d0052a01e444110f000341400d800b400c022100071031040da40c1d5905051000180442c41a030344074030f02d98883c03040d6006400000c411808981c090750348010300e1000d40d131104c4c040d03d101c0d80014070122010205d40c540401c042c4800406849140b41000700800150302e14245070300c5400279505403000c5101040302100c241f07034441c4010b01002c40140009001c000d0050030610380f60500c0d400c00d001d1400b0840c6080c3c00110517180000303903640e4198100042e101405101e88041100ea12411560001c0c44000c00500006020801499403d104550050000642400e0030001700510140c12540320342e0044101f2544034500803841421 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 477254523 1250 477253273 477253307
    0x1b0804020d0614152701090207020604030b0117010c030902030a1709120c040b010c210c0b0a020735280807020d14030a050603010f1d07090c 62
    0xa0709181d00d01000500900c509220003181ca40c018421014206500703400f5550085a8280c407410b030aa4810b000d01aa440100070401a0440100705040842d40103001603400605031301d04d41512500c8502245400380d1103403c8207440c40e2002004400300f0301c101105003119181c20b2100003095000a55a20403040016200e000d90608aa180c0038014003241c08014000d851401044041c10030b050300d030102100c0c1c44d40a01d0502d005c1361144d6124402038441c05600c030178610390351100640780c190300da0641052101840391070410007004c07541d0401104d00c00d0310710b04d50150380c44010b0710786502c41c82006c0d03103080c620b088405100c3c1025501665036492410400e2111032303d07070900b060404104021b141010f9851110005008280d81e80281420311500d0181c0071030f60706c44101d1008441c406050300c142c5000340c10a00c0402c10f07800071a00141c0e08043d0040010a44241d0200c0740ea04907083c032500340d0144c4001d01d0501e06055402c0c800780c0c0090003a400104101c402c1c03072a02921101180b044550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 477255773 1250 477254523 477254539
    0x1a180a020f1306080105132603010b0c120d0204030614040b062e0f1103040b0702060d0b121c0c0f1704030602030a0606030e0f2d010510091b080402 65
    0x40b00318040d92210300200b411000900c001c3c01c1c510917100c29011844d1050f6048000c0e2010030320401030504405141c580e2805000f880c60b8642200c000158020030019002030003054541083d820305500030300841c00440e0401640d60386103240540454501400c02c1007200d222100300004500100582c59000c002500e00c4c3c595101100320204c026280b02107a001c05642d0a00e0300403825910504c0e150182039035441d40590310443d5075500b6564010340c4203050700f114007080454010705000c1d0203030040c40b60001d404240c24668000041010070036442ca80000d0f0700c10319004010b541c00900980414005003800d48401e0344944403080f0540000c94090000410103c0701c2076906004421a801190417070411516400c00e0740b43c0c1009001e06200d01380c00a81400340c04031540c08045240301c2c032202000020101001c60f4036200916400544140c2c0300c0303a50700c098080c0c8084086c001d20b0b200c0d448403046080f00324180483c2c5801c848070011030807002d0041c1da00041d001707500608a02d40064049500d14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 477257023 1250 477255773 477255799
    0x703031101060b04090b010e03120702060708190329090a050903070209070801052e2003160213021603050f07020a0602011e02030702031b01091a180a020f 68
    0x1d0140050342d111800040c8000360014041a09038020550035009a8404000e00b4a102c1015980c4151070110b920020040001074018074010000f0204144901c49a6007050405c00d54041c2041c81d1302c003081d0100307448c2c2044200c2d40650001c00741e48045e6401041064802c80c0020491040d401412066100d68400c0402d2841d80c00b0000d680c4201c1c0e009085a005181a0300300819070402845580d008014007062202c920b01d00030340d603144410164222000350444034508030384429005032010116403251003c1100c07010244000d02200c0c0c58904002e004030035910600c00715414021007941000c0c0306201c0d04580c085500105440319401d4608283c450070003140d102040e106030f480081d4000c80301c07000080c8880d019002340a0810101214010440114003114264441240e0010058000304140402024043d102100c4803144400000e10450103984040b5010a01c5001ba19000448410065a000b04d00b50070340460740b045029088142190380841e03e508003800c40b141c03182002038400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 477258273 1250 477257023 477257057
    0x140f090d110901030f0b0f01030305030c0a0903080f070b1003020a0506220e090c0114030a0c020c100302090907030b0a05040f0902130e0f0601120b280f0b12070303 72
    0x70240c0302000030b061102c01c0d6580e1800c0c101802405004403060702070ba90001e28462540603002c0d040b01d0b096100c0a103155101281400654007245000090102250000c80450468400b0300f20640c04074021030f956150ae4144002d5071440201803410301c00c2030200030310050300c88100583c00c4603000e950780c0c0d8440500c01c0044000101c00c0215000030107108400140d4030b080881424040da55032802d4500350328011004640611203210541001141000450641d00d502d5100c2c00e0343d60014810f07543ca042503078000506002501c0f0310700d00002c0e00031810607103c1c9804120280c01083c0c43c14100f100745241e001003014a106842960700c2240d444a01c40700740b0a03950000818242e000388000144881d450b107190040c03001070841415442914140c004a07200085c00380d05a070990b107840c00200300560341e004840c1030300800d003000c070315425003c0309040040c1c0390b00c400030812a0350020a803a001c1110800c01c07902c98004442c4144012204080004008240181504e41500d00281c10703821000d84 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 477259523 1250 477258273 477258293
    0x81c1a04021e0a0c030906030207111212070b06010216060c060c0e0d0308100b040509010302040c050c030301151b08031501090b0711120102070201080c07031b03050a140f090d 77
    0x60011410b0300150002036168000402030b0468802d0b16080d0351300d511090100e08a016280c4010720721411100499040e10b829025203804402c0341c0d040b00c20201240303180501c66000b100c01103614103544014407896680500506a000c561003221243c21480d010000b8402c4050b4074000d03003145d55901144501c644690541008850060220280c00200d0b190040001d203040f106401118144100420612101d03012a001c907400103115807426400c6400300801020411a10020300504009200c0b00000c1800518000c1100804905c0b031424094005450000c6a00101000109072106080010903000070740c0c0e0807440084d951424200c1d0f4078016a41900c01d0b81115000600100d40354007003050001c0400d40d50001a120785130700007080d0404034248e0298080080c041800540003840800140f0003070450f880c02494010030401c0c1c0303070003107000c81f001d4140183c0008000043c2c0144039504615405460103244900741c3c64207081261101240c015490181e01c200703c0c407030105043c0461041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 477260773 1250 477259523 477259567
    0x2070f0e04050f01110706050a0906050c040609050118030f0c0905090723010f120b1306061745010203011a0403200d0f081c1a0402 58
    0x66006448038a500c58403481201c00b1501846a900b1a1075450010700030034050407088082181054165030354500900802003d222070655641900c2c404251180200da000d0a680642d25a880d410702074001c00c0580341d904820306010704540c3e840c0d41a48a034230708101310307a0050000c28041c03a4070300d0203106100d59a4481720409040070148400301038003040d80c0b000c5690000d581e02819a5508240d01c1410008014a020403880402000e01c94001e021855486882c000009416224580000e441400e403450440b482c0d640d56406004480d000f0103004240600030190302664540b0600b5030f0040c2040c0000303212580384581d205032445051000030780144111505a9451840c516025030007034200744a410340e0101909070b02032810003640119002d1300e0304013640c410032000d0034041042005501c0c00c2c040c1c01004407004003011508480c9004041340c400c440c400c0d52410802c8030030525036403400d211040246014040c036510005081920b03403080043d100582c1f9851080244061600b000c0313 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 477262023 1250 477260773 477260789
    0x6070b040803090d020c180709091a0f0103051b0906090a08010b0907091520030c0a060506030102040506160609050604050307020108010611030304172a010c02060f0a05070207 77
    0x501041100d0700c80036610030450740c03044688000d6683d200301d039290113003032005800208100c0c82c00a810005a407090f4801c9117801d0407150265a4203a070fa00f05d546951071112826a80c3c0b07613070320207458010407a5512100c2440e05100608203118104401040759627100340c403d6001400002640740e10060300c4812130000c1c500c0c40031695070040540a07145101c1076603c1003402d030002512440c080c0d8202c070151441c04402d000d55000b4000d0540e00c2e01c0b094020102c102c40c03094201e41c402c1108000501008580c907016111110085c540350041d140098010b0748a40d00600091215132209004d444000e0901c1f00070207000c500d24280003006080030070001e440d5000c2d0302c0401091040000007041002e100fa603d260b126a40e4500c105d071505101c900005007500100082004038014250810090b00e410703110910380040a0304032031280905a800c2440500c100c0c44400690703400380f1a41071400342a0002c4c1c001460301c500700c43c45036100100644401139460000c035070218402c200080190200c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 477263273 1250 477262023 477262043
    0x1119090e03071a0f180c040608030a0201060603230a0e010c0c11190b210106030e0c060f0a18050402030a02090909010c0f27060e0102070806070c060b0607 68
    0x103640e00c641c890344000000d070b5081a40541d00709200c292507500610480c0810b01000041e02c801e0303500c180c0941c02a404d20114400e1601d00c2d10960394610400005040c1d00700110754070021040007a007552611341c484414103107030040850703400d0009412240d56034079034a200c000b16520b000101c1f00600b40141042415860100081103107038000489010581c01100c0f451381ea104214100040c00358054000c44034407031703500010000b40c030304000602040d00141b10aa00032842540c0f001501e10400d922081c00a616104050700c203000a014240d8030b5441650031526020b21000480603901c190442603081003c2c09040c050960309006040003c2c03d4010400d55490070020541400b07500a0488148a4080d00b400f09861182c144600c0d00140c18031344445c0c1441d090683d040d200e030510300c592010086000d4902c10258454280c0820180825071100d10082042034002441e080350303504210917a501c100f052100654000500c00400c50340040c002c200b50740300e000812500d0046c010010465000307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 477264523 1250 477263273 477263291
    0x615030608060f01150e271e100605300a0f020306010e1e120f0f032803091a0603010e010209150a020a08070302030408060f04111909 59
    0x85900840c007201e810380c1c219002c1c1e44507240310704003107030003031007010b001c00001c0e26400c13a40c5000d19030144809800518a861560f030a407460750241c50141c005960301000c000421032000c00382d915030000c0c1803160070346801d10300d060760b040405803046019920500101040c00b221201c40b0303103400e0480e40655400328140c0307010394425a0540c0000c0d0b83d510001801c101b4444121180741c0700b41c0748540b605940e40045240341d04280207203411001c9080c0070f000c0316040e0580450311200031a40b1b203c120100104a454100d0000c18101a0700c02600c2c4000e4004010100d02c919050309804080000c21003000309044510105074000d000b5aa0700070700082c10000b000720b512404490007803244006800034818448001011401c070320640c1051580401b05800c1c0e01c3d030003c1c00c40042c0c40719161a004179002e080e283e880d4018580c2020b8001c500590000800707110444062140940107280404010400c2c1890358541d000c100c26604894002c01110f201c1e008081b9104807044020000341c1c20030401040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 477265773 1250 477264523 477264527
    0xe13020a0e06090705210601030f020f0301170d02120d0f0e0a0507050301050105010c0605040f0c2d050a03020d031421010537030501020a09140306010b0a050a030615 73
    0x3600b1124148140100000900c0c91401502142c0c400c1309121410703a1168414031205c140781c075000d8003080c101a943d100094000075240b008060645100c80d10548070740c5006a03000d0316500d0710034405819040030f140340105980015a09070b88022070035100c5e40350391030b107002d0720010700030074404015050901d68080358000d1701045078013245000d8000d49141c10f44440078142a1502840b81c140080c03d00581280820401e500503904240b0801c0f403411906c441c0c0d03c54014548064005888504410500118040380b00c0000800c4210b8030703650101044c13914001824104140c84007900400240b0090010103100350320105100301908003040c1c599406007518806d00c25140420031001c200007002140134900100415107460121102c42c601c0c16803900c82150402c440500640f4034000c61070b01000081080c0040d0034110b0260f540c1c209154601081d0f05851852043e180e0b010740c0004006100070000390046640c21080c50401c2ca94407101388800700d009080560140c0003040840c00c000000313039 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 477267023 1250 477265773 477265799
    0x1a280906021504030206010909050f060403030212160c0803061c0b190605030a11120a0b0f1302030c0f0111030705032101150c060b0904050607030501090c090e13020a 73
    0x1545075030031120724019a0780501c00407081a5000b902691040b070040100f200039410010215100e981550800d103140701c801494442d080d182100400e40101e2030558050303240c1d041035030081304141d0417039a0880c200c070060844401d42c00e020700004800400507001c4c0d2a4208004150340040180703140003411400c14461400050314583c1c0010842482002c4040b0300f0701480003a10300080160044409590712800030000400c200c81e006000c0c100e407a50001701c01d0003100310b81401050880380520f4441800d0446400c01000680c3d010601c0d0203203c056140002d12200100d001d941c2d248401e40002d0040e112403031704582c070710300500c00003914400b00039010000d010038034803524007421000264a004400300009001c0e40d00c40403010f1104104080c8144442400c542c042d16002505010050125507182002c035020343d0b09a101a0070703c41031641c144034181c0104084a810450061302c2c9030000c0408a6034440d0f00419000c0c0340c04100101c100d007a072003002513070042103e40d0040c0c2e1601c00c00040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 477268273 1250 477267023 477267029
    0x311030915090f07170f0303090703030e0402040b181f030e010507082203030b0a090e070504021305060c12070f2a0308390c0a1a2809 59
    0x9030026074040385503000001061184212941e000c0d081040c244400c01d41080010036151000d8440e203a40800c40d10070500017035000b01001d038090310000c1d0540c100070303181110045100340078a1040104104204103642038561710f480c2c810340d01e0b0100d1003d80001c0e0921450070130200720b4103290348290301555055400040260f40040091015507104082514a040c04940d241043c050758003c046003955141e030000802c6101c1d00740064902c110070042407080c10a03030810598280d888114140a807001c00020000300401c0f2800d500cac0080c0740c42d0880700d5000d180b0a1030300584001c20030013a848405c1c0000407a508910100c651554564244051346c0620250152a0b6042c1c166a2410100c6a001848092100d107030f2161902851031747c42c56400d510880e030038034210300b0811505607540700c0c0740f41c0e0840c08041411264000182152070600b440907803a429842038102d81400c008000212040440e25420001c0203a116408000034000300d84840001ca901280c1180440882503000800f810075 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 477269523 1250 477268273 477268303
    0x5040f0501020334020a1416120203160609050d020d120804021e01050a1214010807060908030405031002030709090e0307140604020328151a0d0308070c0303110309 72
    0x10a04941c2030180f03050b00800b0b40d5070040c6c002c0d02054001c9405c0e0a8a0075004160104590030100410044003000001d03030441d400d2001106001025460b0800005000380200c82440010500e0f088005e48200d6162064500881c044080c84096503a280c6a01541a4100c620458050102d01700100041000c44003203209480d18908040000d0448500c04071208068490714a00951002e05907291b8003207501c0c6410003519004510f031202c40400c002802000c0100050a01506101d409811040b460700854010f0b40305000401c460f60303000072581644d02ca0548016600e0702d40c0c0c42c04603041065034010541c0b0f41c0c2072000d501140d200010042401030702540c0f280624444021049490714029580079515600411038280b04040150300c034003c1002409000d1b01c41040e0703903a8011880321002e81c500c15180c2d11004515440d00210111841500c101c58503203c1c05416600a80095009040e6401b003001501003a010075002e9030110720300d015040d01c4551607190217100b10750344141c3d944820b40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 477270773 1250 477269523 477269581
    0x1005090c0f03100515190516140a02120f07030204110c07061e0c021806040605120303091c0801030b1f150216050a12050a02360c0d05040f05010203 65
    0x2070a5030601706940010518100300310b4164001e1904030783d15040700945004090f840180c01c80012003c0c5400e13100c0511a101600d00d413401130042010048414000100c4c03608100d07049170607520045485000c1e207504980004031841d100201143c03602800c0d8483d400e9104140000c980c25410003900c0e03c0e19207078644d003003d5070070122004464455081100070741082132480038408001414684a5100c68082c20005540c0c0d600c0d0005110002803042c0300340180c00002c00c0c007102440c1885119090030b412149007031041c0e802c02c0010300720b120510000d46407001c5d2002258400300303003010060a081d0945d80c601006c603100c0c0c02c800892600c0b480888054460250301ea071140b001c5080c1142250402400b10b25850320300b0761450440018400121500c1c003038118007100580c2c82d126010400510041c00c110050074049124010b121168500e1000c1c9410408100300c2030020000c0303a04103025048045035030b441d18a0000300803450288014481d50022042003650a0071805800145100c006508 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 477272023 1250 477270773 477270799
    0x51801090510050d140c13020717030f06010c051213080d020c03070b0a1b050c03060c130314030c010c120609090c05240c0303011406031005090c0f031005 68
    0x101108854410f0980008840c541100440c81c1161841d4500041d0000e4600340c5810a0000d45d180700026a401c0405a020030010140071000142020111285252a141d03045c1043e1b195681e5500805443c1003105150f003040030018144030028110300141100c90b103410103c03518082105941c081c41c526031154a13103d011089c4000740b2042d48110180180c80e06a04001d00015150b0003042c03068280065802c51001a4603440a50929140104054142c40f1684e41c201410a18042c0c545951041f0070f2002c2182c0310b40c9a048241241c3d4450810b404010343d0030301081c15401140c1a05540c5d500c2d00c0d00820a80303400912402c481e8800c10b80030400161181c6d140021141100030250411451000078003a0f811700d40310701084040b4022030324414030600482002640d011101c80a07031904040010022591483c0761001c030b8a104840381d504600e02200c1c69000800e00c0d110312880303130703d001002c100c20424081c1207440c2c0042c1000050b5481c50402410743c9124251b01c107807401615882d05c04 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 477273273 1250 477272023 477272041
    0x70f03031e0f20030c120a23040519030b130203061023060c0f030a0917060708190213031203061d04020316080a15051006030f060518010905 62
    0xe00c00c46419403108007031903140540c1401c0d0840410f4400030944020010495034010410080700300c1c040760448555030341d5507554010881040081a40d8809111b008a011200c05403401c0e00c01303403841a00c42c03054000c140001041400c1e01039201410350f101e0300c0d05000d81c40c06006112a071860017642154990f031544e4800100f072514502c119181310460000c032601401060800c1c4001410007888242441d8180402768280800c822800d40c0592001a5254000c0e4018040b140200000d44032460020266605a40c07100d2000b0210000c003d418000150380001c800350482046c1b800b60411500c601c030369011101c4100107030105503000311714241004030f5030b482405640c050b00e00180b4038041d86000c40d02d4108000c18040e00880c1d00d07000e1165886c14940a1751001e2004041a200410901c25141400311844074040b0101840e1b07400c2004100c0f4507400c4441c280110340f014600050301107054606d071401001c41d60807140c2d2002c500d0b12407103002e502c0740282034140d4045c29020407c41d00d4240413 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 477274523 1250 477273273 477273287
    0x50f01060c110301140106051819060f090b0c030d0f05100e0403090e04060b010305090109020306010506220b030f07030204120201081e01080610050904050304030209040203070f03031e 81
    0x4180c001403207140404000b0700c5101803007184250150011038401d000258000e104142601b06100003800031940880c81607080e24034200200c8141e03200d0416a85040c42d400c02031541c0d0182906100340601c0951025101e00703180c000402924002d42c5c3c4807182d1a0b00d4903225807045c90720318045400d119807408044d00ba441094020700d00c5030b03003d10f503251804880049202000300103900784000b420f000070b00135480361241c0384139030310941c40000c03d000c4603070025080700e6000d06103544030b030700d003140c8000184c40000d0140e064030b00464000c1d0b10341058080c0e100741c1c6402410040c0b882d0700e241c01d00280000c4000e019600622410000346900d80d07a01d4000c030102e004900c159590032400445101c0035502444040f030308001843c4d10a50403030031048202c0300e003d03801c0c0d120321081e40c041010864400840a480405840e0407292030015041c1601c48960b00d014900000e4070804a040104046617820812040200202040b2081d4107980e81009803070701e45c26076403521440c14000e00c0200c40c41c0c41540 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 477275773 1250 477274523 477274529
    0xf0501090b090d05070306140711030307020d0e030a080f07260405130920030c04020c1b011e020c0109120f03030e070504060f08010c030501080d030b0f09150301050f01 74
    0x1c001410000301e082044000016281d0907101401480c20101c0810703d00e0240d142c0300c0360001181159406d010340f0003000105082001d070141d400500a00800c039030b020480500c201c0003841c0840c406404040081e050049014004050761000518880c3c13540480c005040200e000300120001140044841e064400d14004409065241000240028a131101c0c0348a45a00c41c408005642c801a07559404260114119a60f06000d684510a641d28080041c000e8031001070302c096080c5080c8004442e51410442e600c5503070200111840c820a034814600001200d40c989484e0f120140e40d004082d403905104c68003140000d0381c041c0e010403510035680143d848250f1181c2007809059803500e04800070060b00707400c03008901407000b0026440e5100c0c09845c0141c4031480c0d012090b239241c01489400c40310b0000808080c18103040040004c4040460090690000b074140419400400400915804d41d00ca10031a4480034910500217925000d50b0a0411058150020051600c45245045441200744 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 477277023 1250 477275773 477275789
    0x1030504080d0c090e0103050109151803030506060c01060608010608070e011704030909020f0a0806100816090816090e1c051c02041205190203030904020a020313030501060f050109 79
    0x406800200950101c56112200d16000d074410b03459001017891180c0c01c0c0e1042d1a160b44800c5000180030001403400480755201070104801003030329000d940700d55401d00c170143c24180d40310001034042d1141c20480310007030f44000c000c005454950350050111202806140b000820040019040e507004500420a4040c16110f08100300f0314024903200c042d000901c110f0421150a100069810150001e000070700450351241da110440b1103401030450000034045807185100103481c0e00d81c65000414260000850201110008202007040c0c43d9284550700a025074402c0c82030100002000100600036111142d405210900008280a60760030003241c01a111070500000100c0c1d0703902800081805000c224001c54081c0002103508007241c0040c5e200ca403420400013411002c205051260b402c640e00c220400a00345201c0c2d4010035130300d00901400751301840d80026941c1942c1d00804c1916100c850b403000340e000071071701ca03c0c00c603018001e50b103d2840c440820002c003045541c098400703182602c01302 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 477278273 1250 477277023 477277027
    0x706290105120a1b020c15040f03030507020d05070905010e01090c0e1903062301050303191d031c0f090e130204020421120e091503010e0d090f050103050408 69
    0x40e21020b070308200584034504075503440c0100f081e03081e0501400000651280c0140c4030142e400c01c02c2c000d034a1009612005040c2c4100320a021036080c2c2105201607030307050710b0120344031622440421000000a80c0c050454442d0700b0300014002c036285c208a06031850080c40701d05690340c0f2100c2d403059401c030b001c0d00341c04969522180c5101e8100040c001040d00340542d656842203a80352102022602d55a80c01c0b0500281200035042291004011030b004003001d600940c60701c0d011004002c1704c880f03841c03198401c00c085004045100c0000003a0001c540100038260785090620010150105007403003502004a01e41c610360b0310500b401401c0b10380881c0c0e030030241f4901c10b590703e104c0110301060790001264025401e020110b25806100d2100003800600700c03494001c2c80d5603040801d0b81c030414800302400c21a8508000302d035a250500071300d8201201070040000ca808460020340506110b415200481c841d9080c43c2d80071076480205001224580240c0b4564640c07203000440981d001194080e08000c81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 477279523 1250 477278273 477278287
    0xf1602011e171911130f0302010c080a09090204080d08091603020d14010c0801140904020d140715050703080f0702071e0b0703030e06060405040c1502010209060706290105 75
    0x400d10b015607010314040c3d0a802c4942c0b112000d18101c40095694192144c00403842c041c603460000340750000703090b0207000030141902c0d60f400248104030381c2c2c000a060340c05c0407e1079192980140420005080c0d1290305540b51900d841c82c1c242d445902c101d04600041101010480d404800309041100c1d410600341c044540d4110307020700041d801f000d1400c95240001801280c00c1034000e00c5091620a0306030340d165455458442c0d01d210338003503070007141d2058803102c040c40010780c0c0b0b582c3c5d0903186640c884012005850405201418118243e0107180c503441901410b100c440d03409402004003622a0316042e0151b00d82c6010944c3d805001c840c10400b40c2d020140c14003140a481d900f0741d200382c180310741460070307180c54441d802003903003000700200d000ca516400e0340310b401e140a00036554810410380f4104036605c3c264440340002c0c4210703c100c00e84d203084205c03492a124401c0d0101d9000440240c48140da45182e85000e10040036000c0c041c506200303d1f40c1c009a000c2501014079068403005139680c07810411 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 477280773 1250 477279523 477279557
    0x607030b0d080a030c26070815040903020102040504110304050601031103030d15051f020703080a0309020307032307080a021905090702062202060409020a02030f1602011e 75
    0x30034034118036805107800802400040c140401411010100d90700455030509810001d400c051004811a01d02c040e503006a00301d98891603801c5a00620038906008192600c1c20401c003a59940c12100350480d0500c8072000505070150010320480d9020340382045522a047c00d140b079075010945005141c2d421071001000440e40e1252150070301c1c0c40c02400d481c40c1540f130002c004200c1d0b201d01d5443d140440d9116040042d4039144202c2c5110b010500301c1c2850b51042340400a45488039400b00074a051030208020032254032aa2180f031603203134007078210303036280b0349030300b1b11050010398041d124403081224941090080c81c0454004c04403040c0380000c0003070980960801000380e00410b8261528800342800203150790ba03082d138190003000c494010740190b0510048455918140c4108007070302261410306c100040e250f2208890840f401c00b540103803108002c82c030032821845035104041001101241499148994420b40403005100b43c0315800f045501c040d081410807410100e2001041e01e011071111454 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 477282023 1250 477280773 477280781
    0x71202090f06030a0204120b0601020606040204060e0928090c150c11030a08030406020304020a1e06031a031204081015030b06030a0b070e1903050706050c0c0a0611160503060703 78
    0x46080380d030250030517407101350072011f00340410b40955256481201340030040d6014028182c01807c04c1e6410362416040030f01c00b500b050709100140307001e68001800a0810a40c85c1c9942e16544c2c210400c03001d0f844000d00202014211082c000d8842d11464500040c046c10304980440c0f280440c2c0d1502d001140c00c42e16852400b0207074560300c940601070710030804001620240214800c80c0b080c1300040c0c40f81094014440d00340c82c2500a14102107400600da052540c05680400884003280f0b0f020400c3c14002681036080600760280c030f50184154407400c264032000901030015030b14100c00311015208450803040651324401030214012414510030300100d5641c01c1c81c00d0f030103240a011540700320b51560302c41d40c080c0c0c021521440011844242c48070b10385818016250040a260b108a4030340e81140ca0b0305445d51078511821041c020001100310b584007061240400a400c002c00c800500707592543d01400ea10306009028050f4011031400011205040e10b01e00c05607040980240420740d242c050030f80c018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 477283273 1250 477282023 477282031
    0x8060718090510031406250e03070e1b030708070c02030f0d050301150306030b071b0f0f150912120f0e0304050312031303030b0a0e040b071202090f0603 67
    0xc00c010001094030941805101d0180000004414005245003040791803542520074070301881d0011000e100c3c5c500b0300002d501040c0303180358500b140041080c000545150600c03c1c4a540c060003680c40c0044da00000043e024410740303801c1a040800154005805900d00c802c03990403010901a40104089a10071040f11001610207800c4884002440c1401c0b860242d010341c400b03000500003c018800c400e4000000a16142d084c01c1c2400390b01d003141d0b188038001c0001458902000700c60342c001d040204001c1c000c525110340002c10511140801c0c281800742664000041c1c07004400440c01c441103103810f2041c440140d400a034244d001e104a40412110400f402495448d401e85960440e002c890048c440c03089450000d00c000c6589038a0041454104120684a0b02d000141401040b0402e07203035110303009207698145400511b078440440010700701c0700180c201e00c14894080c010402048001d81c0c001e4001e442c40e88039001560510b002c0b1000703a00c038640415801c009000d40007140b900b00f0a001d1500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 477284523 1250 477283273 477283307
    0x9031e020604090509010506030f01140f101a220503030d05360105062409041803030c200d12092103111e0a0309080a110c0a080607 58
    0x350590303c02140c400d03918269070300c804595454007804050b150420100c00c000d1550f400030301c400400f81040e8884198014591004418400d00198408040310101e8005d400400d1020081c2c0000c00c100d01c00030707048880000e8044141c054001419910340401c2d404444000f4000e41c80c02e6603403288440540005001054068401d1004100c820700440110181d1160541c0d5000307500c222001441c255171000d070001303004892a802c5107580c180201d440816440c0070ba6a180e6492401d10301050040500710800500b040b8080c004900301541604003001c2021070b40c2e01d103104022881d00c100081c030700f50b035030740b44040e0b0002c00407080890081000c8002450b800c1070010303401c039242d150080907880d600d400d13541103607882c00c030b048409415200300380941603441841e50400807181c00140c448000110b54511a040114148007a01d100f81c100d1401240d0007480f10f07880704940783c0d014101662400740030100340503000d040c3ca481d0034202d00340c80440e02d040000b0401d68950300f409840080c095004191 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 477285773 1250 477284523 477284527
    0x3050903091507140f0a1709011b08040305062502070506090d02040e0a1a070e0109060311070f060218041401050907140418050108030c070905060a080709020c01050709031e0206 78
    0x9548805d01000d41c0c8001c145001e0304600c4001c0c5031220010741c040c001009050300622810406076070115186286031811230004036a00c0c0142002003003401540c0c401015031080f403040041c458040c16981c06101d49412070b162140100d02c88c141e840c2c1160740112a0031240078000201030345012245041524000351002691140d80d00045003004a042d009a6481d042202d1032a2002c001d1ba80c041c1d441206031034025408070546000070940c00e01d078404c000400d52150500d0310f00281140031100e581c0d031310001d070071a982103c0c0f0740076020703400c101141d50361209015044811810a0701889803600c40200048901e0781c200000c01c030480b80007410002c10440382ea0b003160b40401e42a80140090b02002c041d03001442c1d42482100c0036190b058000d103500350802c2c00080d003025400243c07101580c040c040041200d80d40c08011411104440d8022100c501c208200050500c07400c6e40180006640c200c028801552891020385508005100c000d0406c0400142a800c000155400380c21803803004040c14 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 477287023 1250 477285773 477285803
    0x50907020a1e050703050303070f020d020606060a122306031938060a050a05060d0b010e03011107050c0402190e13050702060601090f080d050c03070219030303050903091507 76
    0x44c03034090340740c0048480c0d900000030301c100300c0c6d0080c3d00c540382a4194801810594001c400c000d440c0c0c0350140a40d0b0103003202048885140e401500920054031900c0d000308400061440301160f807180741607039051298003e40100340f441c14007092880e03038040f81192201d0040590364130302028400e204419510b0b5409003d0108000c0307080300000070094410455500c44e41441400c0000800311984602c0c8038517186181040b013521502d00b6038083c1401ca0800044180c4d02100507030341021151035050b49035280c01c8000e5545281040038002c0140601d04032080881100d0512080344503424840d081818122101071b000382c400e9021803c0b210010b81210310840c0b9100f0710009542c03054502d600075810540806c1182c0d41d008a8480081c030031099030411440c68014190b485071070b580c4804081140014039071201450400072030721080d40c0500810b2a2800212084565003158002103000034106400318446540c0001510f9002c03100a144440c201c150204202c03850740420001c403000b8440034210 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 477288273 1250 477287023 477287033
    0x40b180a091401031403070215090d02061306020c04020a05070b1032010f12150305060405010203190630060e07050415030b0f130501020309030702010306050907020a1e 74
    0xd41c000042c0c0e4015032199419441d1418002180c4107074004558003d1102c1310150303580c40300341034003000c00e0fa101d980e450201101103042c62450210281d00110005260281c0701801811074048030000d500355810360a04008010030f910545100384c0c0050740500c4128003040240309810b0704823550f101c0078400c041e40c5821002c00c2400c00c50101180c00249600102c65240c90046e180c980d0030246405015142e4000f0042c0c035036007190f400c006100d5503c581704004141810468406540c2281c21100c1d18074242ca081c502035882101d00c07014001c0381c03018100e91143c89006000c01d6403114003030801d180c40340c542c1c0891003414803110420709030850900400403640a01c12a07141000303540140c01118102000c1c40b080d2222410030006941000c282000803910540d44182c0010941d4107081a0792107822042d041d480715818007420300d5100000b8040406d2000004043e094806c2c0c0703051006e035036a03008015500320700700d40c04001760308090000d200207589150b808140300b030390042c5134000001d0380d00c031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 477289523 1250 477288273 477288281
    0x618020c151003021003021c0209030a020306190b0d0b070f030b060a0801030c060c0f020402030a1e050601080c120f0402060c0304090603020a0f0302130e070512031905040b180a09 79
    0x88940c841c2c41400c400d106504151601221101ca91b04042d8500b40380d030281d1802c0451102c6108426690200e4003a009075001d0204428080d00203044907820304140515484403e084000400c034646486240d9a503402e2905140344040d4100c00c68070310550303984401740e60208401303030f441c4d080580d581034040e223030b964600290103640203581d100c56180d8194502005071450136080401408840d4000b0000980b041c0711541901c1e82c16180940c4949624031940060601400d200306503042454010078500255480244a00c000b641c60244a417622810342d00e65105041402c002040c810380002c4540d1500c1090580040c805010580742800c2c1c4410642540c01c1900030300801902c8540410643c0f038001c83c01c0c0040c08540741c6c16044a4510b500040e40c202c50348010a03255131300d9440443c3e5400f424048580245400b8050500000111f9202d5807264030440b01020342c0c041c4051001a150711601c00d0724140c03889801d940740b80441d0244404d240e10505000303107500c009024070204124407640030b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 477290773 1250 477289523 477289531
    0x307031107120e0406081b0a0306050405030705100b0604060c14071e1706071b0501060e011706040201080c30040c06140a030e240702010b040618020c15 67
    0x71440c0c007603200c034a5008012824186800340f190782460300c248045d407001f040d01c400100880072400d08110406002c6404001d140d4070140c105884c1400704014410302000405456100b8070540d240c4032104021202141c018038a0a82c00c28000d010921885006a00350312846000d40b480709502845a00f03090b02d03040c0c40c2d40181c42c080c114090240c128a540340904006024070711070421640440c400611303034810000f440101001903003003a0940c2c0f04442c0e02070141d4030b41c10100a00c989516070040034100c1c1000e100d0954445540d0302c00b804400d101250441c051981690b07000201d45039040c90207001e40000240c500700401101200010003001d00c600c82c20886020000b00c5203240c5130410075180751565100e08244106444842c1c150075190302140d246a1443c1000903013140b0b10003500780f8014010360101028482420319403242d401801e11203114074000c1e40288819441e24080c00140ca11b2403081c4101441956403401618032541c001c1e1011480c0030040310750968281154540000c4203071 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 477292023 1250 477290773 477290783
    0xd02090d121412040b10030f081905070f0b06040f020315210d030203100b160b060a0b0904020930010f05070e040e030d0207060209040e07050d080307031107 69
    0x180d29800907002c0c9145866103101034185515000c280c88400f00c024002031400c4026400981d201a2001080003e5904402c5044485e1041c0c9407800390b0f0791103d0311618007190400c1d09010050710a03400c854070702e0b5101c2040da003c1d0324640d403980364114000c2c0116501c142c8801540300c03032402910103103100308000340814048289902c01d029540a00141243c0e0082c0362032100b29440100068190007001c503490300603525a950010300038200543d0304155172450000602240c0342c0c082c04001c0481501a0b000340c0c10903200c94081090003101440b90701a0300c2403e1155003014a040e81c00350000784405440a0303400400c80005079038140d01d41500f003500003101d51030000210000d1042107828031980108100c1420b103180302400000d0b00c011040d00c200c0c1c4404180560710010303c1607800c1450850f0042d5291012803501c14060340002d03000c2d81c012854032180d03488a040026520f002c90708050840c003000801e0781c540040d00e910013010001416180c55520140700f503003c0080054500070 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 477293273 1250 477292023 477292043
    0x402041e02180405040218040206090409051e03040501022503020907080912130b0a030e030310052b021306150e030f0f1c030b04060f1809030e060d02090d 68
    0x1542c40c1c1c40c0303046075041510340039624101c00c0000503120b521011280c8618203031152820781c0c0307a1001502034032600068a0b00700b810076108200b000030014601600c503030952a41b2035a00451002c1980d00c0c0254810240107912560080a14954841a02c540001801c0e883c60340c654403500407030440031042d501600090303051020400c850205001c000950f08003185030528100789803494003052195030261507461800040c841d50400d000780d1094101442483c00e4039124038100c881c0020702c14051154a000e1150200914240c040e419010506541240c2c4803042c009203a400b48406188015080bc011666490010501f0310700b0000580104100d9900c00300c85000340c00c141820310021900d411015030015104412040380464010b1a0744803090300c2c1482e20036400c1c4110050010428012340080c5488804107004081c442020261201c0d081130a60520070419504103c90501c14081c001400c09141c00c0c400d440c100004003200c0780025000760400020800003054413002c076204890951507 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 477294523 1250 477293273 477293287
    0x50a05030a080109060b0714010e0f01051005060c251e0303090e06010e0621010f15140f1303021c021309032007030503030109020403030909060501050d050402041e02 73
    0x201a8102c0d000d03024080301400326a191074880410781c060f800780141000e1180940c009041003d40c41410345120f01d40c2150001440c40c0002c50003020161a50002800085070208480c1082c208840f01201a01c0c014080c2c404501c5503a90000d101c680f000c04210b0b0003140000e000c0000e4409804051141d02c0c40030b6045280d450003425202c140c0d4000011f401183c0100081c60380c2103040c0c05951002074071200c0d51034801300741400e41003180f0864800c003a8042e5001040d408912107002c01600d000000b40e114030b0038003441c140c8138005d01c0c0d210140c200e001000f100b10329441d40805000101c512898455055480703070700003075000f921404900d020b00003500c0c0000a5241408070300a00c0b61300041d04012240158174003c0c1030071a66140c4000f8104c043e24040e41506042005000940c0c002d000d0300e0312541c450000e64040c0d48944010307800070340802c07000b10384042d85228650854005031241450020b11500315009040010010781c1d01c00c1e0740b16010581c041842e50103030303800040c4500c0142d907844 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 477295773 1250 477294523 477294527
    0x6040507060e10120f1d0c0f120604080a0215090a0501140106020c010503060d06050720070e0a0c030f150609140a050904060603020d080909070e13110403050a05030a 73
    0x207125601d0070b120f00c10900e40342840c3c40d0040c1c84101c07058503080c00882e070410360b114000054460030501803213841c0d10102e000f200324408104c3c4000603c046480b407031000c000d503040002100f620281c042130f540001d008078002402240080c200014103006032100040100140795000c142120100d0003a00170304050001c00c40280308204d051003440c0380910b11941000002507481c01790500302818400004041a4243e8444034081074181e40301074280200d10700305000406c1e49148401101d200041c4414030300c8100030118658090b680e11601e410001d0750b030b046c6418007800c1001000c0d000c1c15581c440401e48065180035144400c40c0d10f60700d805003c2c0c64048010000042c2ea030080c0030103d000e1200c14413660b03400810030101ca81c01c44082c2010784031410f05100501d810380c4000d502200810781d0400304001b242c06800c0114040303c08a1b1255540d4000303440581c246101a0f620403041d02c550844003c1580c0404101075102900303505043d269a1128601104042c050340d1070303400842c113038500c40e13 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 477297023 1250 477295773 477295787
    0x311030a09030f030e1f06050303030c0a230708030a0912050a0f0801290f030406090b01050303120c1e03010e01090c05040812092e0206090a0c0302040b120604050706 73
    0x203e40780c503003003054103404403440d0703110b000742524410304507100c020030142c507501da0300000064840101541d50380d007046410700d10503501400c115400300341c5031400460054080351601a216051003031591900e4207694403101070b6400103140790301c0169110409004a81d41042c2c1a03140c00440d207502c1d03540d505461000d4688460141c2c01c00c05c10040000500040311204400c0c0398442040c20300b4041d40301c0c1a800400a400740e000f02c4a4003c00c0441000180229901f110860034040c40d8800c1c12030342c03140141072f01c0384201840d0440702d02414000c1401745501c1c2000f00100380000c1c04200865003e001d042c4901c0d072084c4d020b110880365400040c40940784912442042400a08104d880d00d49044141520ba168401c96100388590200e021070242e10f96040602c0028031103060311240420540c440741c00710b00c2e4096884014490000050f004800000d0f0300c142e95608141083c0c18949540c0c2004060024030420755080140c213803c440004104001c1ca9000d80e01c2071014180c99828118010144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 477298273 1250 477297023 477297047
    0x24150a080114010e060427060617061f03330623030c03150c2a0106300503090616110a0303080a18021903030801090510150311030a0903 60
    0x1b01d180012100c00d418082c0007417071046000f00f405e81c2400032a410312900409a590203100000403410a0030080d00d004511a407041004240e8107000380119001591038254a0000519007403c0240e14030302c03110044041181b143c06561441c045110b4281090140c7d071240d8040404c541c01d12032220362003a40a04c0110000303a0980c0200021090b04002954550100100300102c058400100d500450090708440002c00d0001d03280701c2943c0451118041d88003002d030500301e207501e170000208010743d5000300c81142d004092901c4420861a0a2288541c0161141112603200c108209030154807090094541e03040c420000f55103007000750030008900e134070044c1a540b0864261400b4000260418460b40c1c0028440c3c2c00011422054a641c0030060020000a54000101d000a03600070350411400c01c140c034403903558480b059981e920303070900ba24000e81710031032a480d2454042c48800c44644030310701ca0345081e01c0c0114264480590301c0d02642d0050350a82c81c4152070740807010a15411075510401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 477299523 1250 477298273 477298279
    0xc080d0f0f1a0f1905120f190624090e10060b030103050706020307030203070809190b04080f2107020d0602120105010e010c0c03030e0102030c0102030f01050324150a080114010e06 79
    0x1400810400e0344c203000142c0510f46c41407411418102005004100591905080404860080600000c0c0c08030f10099039400f141c082d41080d080309209c2d05078102d285128032510210702d035114140759202d0b0140940f0504101a8454010a1141c000c814010310008051440d100c0380e9950550401a00b00300c000e82100c000d41d40200a2503000035400030885030110b81000300541c07980d618000185400310460041e25041008202c00300d045500040284100c4081d201120301400200f04401d468205020700101c0102d401900c83e22041c11143c0140580d5100801c44650105150f980750121b81004000400451448005106a582084095500b10030900b08162665140e90784c9686070602804010208880d482c0c1c903150300d174002c00580e5460b41507030380250340720328003030221440721b04091050314828899580d40c0150038601150306114036003980320705c4c502e540d145210700d81e40d400389500ca15000064900001101c2000388035140b03001009070700d0b070016075140c110199030002c006440148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 477300773 1250 477299523 477299539
    0x928030e0114071509050f010c03270b070203090d03020c03060604060b0304020d17070305190513030b09070324050c0c0a030c021c1a070c080d0f0f1a0f 67
    0x40142014260f40c0080ea0242c502403004003c0061000500805403004000380304140075048071a0040d0440c0040caa2955400c002d040c0c800c450500b107003840c105020b100071801848201c00b19540c0c42076240d00444600489180070451070104030b00302e0440d07000f600148c0000340110814603007480041e07000942140d0a0101c02e04011281c401407002410003442049181400020001e14a8441d03210040e450078180c0c581070715050141041c2d22045803102c0c002d04008207208142d000381c1c20f54421071100b40d04401140c6c1556a80c40f1555000b82c0031180d01e2145200001c00280a5205002030369140c000d81e4034802e0408000000307841003e4140301c0384000900004d042c80d071002031916a202d4061800081e0303000f80703002050396410703031812011410f0390403a0907909200105414a0341c04c9414039920300d00e55100c039800c071b424902240c1c00403d454801c1000e83d42c0382445400011850342207100015060005841400803101104a0503001c00f88400030180c091070200a0011000801d0307441c11 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 477302023 1250 477300773 477300797
    0x20d031103070e0f09130c0b120f070201090b18010f05011a16080d090507080c0a030605180a030207050f12030d09080712020604060e03070b0f0928030e01 68
    0x10316030000070012010481402e4800d90035a54050010201a41c0034191072024140843c0c4210f108401020030780701403001070300009003072880c00200d8000100103050080162035640c40b1a54800d805402d20045640701d50f0100701013002c0c1c4140724020342000c00c4801d003541c08522101c0c00d45100d5483c0798042480d08004110400d001040d4000381c604081801e507032030301c0328201489072201d0391030082c0041d4408940c4a400145507488205200c4c000d604076000c540c0c1d44e024030b07507813511400d142035081103100c1c42c10030008205401c074640006100302841c002609000c200343c5402c0045100b5030050b885984204540d0038400d02401550318140c40c031a4040c035200c2c2c101a034074818150b0156583d42d8904105040c421000290b0380e40d180d000300c00035041007640c20001e6685205890035900740f89408400c2103403550000444120550041c603502c42581c1c2d080030f0b440c4268000348042414000e1003c6900342c00c44a201c04103205031005103001c0f410107075080090188100d11718060511038014807031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 477303273 1250 477302023 477302051
    0x60f272401090e0a020c010e03040306060e07092615060411090d11010201020c0d0507030f0804050a1106091903140703261603020d030b03010c09091d0703030f020d03 73
    0xc80c03e4424402d07900c249070b00d030303100000d00a204074100c05d040781d4031700b01900350300800c0030004004130380c040c0005010158844580e116001000d980807070114100040801c8002d5034058440b510f004040b050703c850502100e41681460940c03000c003055050701c001082114503141c0300300e040910704141d041d0305003045440410f405420404020300141950502d09125a2007501140c1280122006441c01e00866002c00b4007150060201107021880410508032080c1c8a13001081c420341d000700041c00c0005813078580071001200074031059040b00081042d413003d41c8030341c0f503162440c02c2205001c4001ca851428400c204c07205c2700c6d01e0b0035403540001c00100046102c0e404028052030844224120030716424890140900c55681e10000194034003c0c1d007400c2c581c004c10f40d4010290aa20103110080307141e4105422201c6600084010417480c0d40c0c140001c149642c403032910300300c290391200d11002d0504a0346140c20031940c030450001d0044018402400e6041c002c2a0200d1514202401780040031800 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 477304523 1250 477303273 477303287
    0x9070e06010c0219030206040f090507020313050105091503011e0b03090706140415080a0c091518120f170c060c09031608010c02010c050c0303060f272401 68
    0x191141890903003848078091300001040065034024920741e134603903035a43c81d46130003500d91251344140d81c5000001a440d0380003004892a12400409850b20703141440010349140d0054601c00b900040540c180110880d201e0300118082c01410001401541640d030030440450119041040c00c1142481803140703210000440707409a07905030810107100a403220352000d55000c2d99001c0340815905400c04401290014002030007911460801e000c5941250010b6889205522860f4000e440d5a0040c2140034401d81c00d08140a403814034400c0d01c944c4c0c8401e00c401c140f501d082c043d1b550f5000c00503803008105254000e048500c2c06441000e003855850030410b6103640000348800502030340001c094180c0c1e81c085c8035824031605d040070790a4031a612448654024600712100901643c82c0500c2d85000c40c0c0200151681c04080c140150300e9a6540018044a101f144940642001950100058081803408500310390a40c800d12603100d4603068101d200c80c0400c40c1801d1030344072003502d17a443c034590340004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 477305773 1250 477304523 477304547
    0x51e011e0203060102031903020a090e040209010e180a0602210c091c021f18030b01290a030c091d161b08032406030a090c030204050f09070e0601 64
    0x8010b84075a00c810050f81144611610950364a441c9030050703c2c1684c141c3e006c1c00b804602540d42c0b4410f40d855500b0140d489001b45e502960180d01c45004021072810120015400300203048075039100704060103814a00820140110303251500420b40d603545a014480d1768801d000190702d050351a040900941c141d510810005030f0150300b85014132203912500411462000317030b014200c185440c000300890101742e405454017000103a041c200c110f0071010786290020030b5980152400b2007591800740042019160203800e480991582d1240081d17900720000609a00b800740d0300c0c04260b0040c40f450090042035071750440d461000d80c802e80e19450410190300c0c11342c8607140c10b40304480003810290075101030103007049010144294011003010081014040d42c081d01405111a0074500035070520400000d000400c141c2000c0d0138400911150065080200854090010480242d48036004281920002c440d14555a080e80043c080c00a90400c128001011061150002410b01500003001040294 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 477307023 1250 477305773 477305831
    0x50f04170102130b0c0c10120504021534030f0305071e030606180302090408070602040801060f053c0f040603030e0913020a05151303051e01 62
    0x3156030400900354103e60398100003442c0c61224a0341e450750324070540e02028000d0b00f20701414429030040c2c20b00d079040034091681612440035441003040d07074000030040140240c5c1d010441c2ca036940b02008024000309000810702140d668a101c90030705a01648101c00c0206000c484003181c00b0000c0f9600450b0011081003510300800c6544414030221440048000407d074080159a40014050303016400760b001c4407026101c0f130701030120a0344081c3d1501d02c3d034400a034100100c040040d0004100100600d00d8500c03030702c001410715488412040c2141d0068100c03d1140d951100180300310f107400c04c0501d0001520310820941c9009001c4a611032032081c0c422004d0301c02d01c00c0150140f0b0341d15030100c0c1000040c042d00422140b0b6032400c000b00180000708000d406050b11501040e5440211817900001d5a0041c050700c60852030141802000321240c0311036480318106201e01180c40b500c0c11000341c002c50080000f0710302c60560002c484c1c45a0112034418445030b00d4881d0107510541800480c5800400d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 477308273 1250 477307023 477307049
    0xf0503090102070606060203090f040e0a1e0605040f1502070314161e0b010b0708031f03060c0c03270b0a030605030313030605060111061915080a050607050f04 70
    0x3600c01940a80290800140445d040000115a81c1e42c000058010540304403282c11885805609000c111000c44d50403078050b400c240711207004103810825000540340ca030f0321031110018158954804135002030314202c44031096046404148032110213151000713a80508114542910f0351f401410390350801020032403500c0b000c220103c180704400c0103208210b8104c5028070021a09640784050080c1d0307803104039a80d0440c00008902d46407803605581c000d950000c40d140c91358a814a180305507201e00140c0c1c0c01580011217000c0300080107401090003900030303629101101300e02c510300a8032002d59551054200c41110586000c4a403010304044122248030112913035400301c41d1800c4000d0140c5801c0316030944000a004030459695556400c11039002d02401c210b1525100d0044891010704034481040e64051004074184a0019203250402070210500061041c00c551511076002c2c1a50310054003600015030792300c14400e0510003107074070004903e89145801d000e42004000340c003803801444070285034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 477309523 1250 477308273 477308281
    0x201020c0402030f0424110309070b0703050f0d0908040801020909060f030a031b08040e01090b040912110a120f031a10080403020708072705010302090604090206090607050c0a0806070f0503 83
    0x8899070040c03241d010351047c00300c60464041c8103ca0390081c1e0340800c0500c81da01d4005013208811050f074500d1307680350b96014940003100381a1902600100840390140c2d5542d459000003072102401403009000c150005629903019900700b201042c1c0c0140458007070344080b0b0644c0c42d00d81d40450320560036585414080c2c0b8029603008040e040c41000040103001800004011030050303031841007581250b541031414400d803000d020620007698cd201000403d0381101e00c2c0d003070740d2042c0070b03240003003803c01070f001101c401c0c1c41541c4540f400440306c00712640c045208005500201e0b0f505024845104a1800706410103503052b0001c10120130800d0b601d00100901400402c0c2014828002d040003002510110303440a5103d200c440d00b034544110358500400807000e118034000600c0d001c0d5504803900102044081c2e03880c0e0342404090706420004a030312030030822844a0554178403000d23110090281c001020b1900002c4180201e14586401030551a8040d0082001803503202c0350715003400d61185011903e80e11 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 477310773 1250 477309523 477309563
    0x15010f170a0510051006050a1205130f0606050f0604032109090908090406060e1014120a02070645050a0b100510050f0c190602070201020c0402030f04 66
    0xd0540340003000e50290301c0c43e04003d22150b80100c0c0c05280c082c08180300d4156203e50030740c2d5602c212044600454402004000200300345c2d4801e5520401104d80040040c1e40d950b81d00801940c0100201d80c0141e5800c1d05000358207004454400003401039680c80e251906580b103500c0d4403c50070203ca41010039030720150b80f030300d4440c6071040c0050104500c20301240c0654901b0740d0320781d04403180c82c17030103217103400070010b21984142020040804040c00140d40f0104500b011204d480c4102ca00010b0b0000400002080d5a8186442c900c9803074070071001a1030380003604c2d10b80103540c0c5a030184c2a12041410303114400300242d1450004601c04904c40035600359090003000c00003121088060040d00901c2420424010702c0101e407407080300710703500c200943c6441e0002c120f0f180d100740048000043e400e000c1180d04645444c02011602110320031280480c405441130400304600a00c01c032592500400c4240455070100030126410a003201d0540c214940305103285d250120082014040200c0042001e158003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 477312023 1250 477310773 477310783
    0x5010f0506030f030405130b0a062d0e091b040b2106060a03020c01090f0f03120e030f0c07081207060c0305011805040c0e070207080c0303031003080a02030f07060e15010f17 76
    0x40c3c4027030284003144c1d9513480f0140c40700d43c0c814041d079240c115121064046a41c0103031000081c1600e40c82e40e4040040310003d100300d40d103000b44a20904040300c4011091003030000007170401010701204880d5100b28000102031620382a0b10440c0c0c00d18058010300c10545e841000b034a80148241c900140c0300c02c2c500003014050441e402001e403041c6800ca18500c140040307410303480c0c8514080e4544001c0e00c4080038002c8112440003004171341c00d400500c020400001810002c009400d07080c8100e80c500380d01c41e20000d0405a1030190350340c520030300195076020403038107014000e4010400e0500308607941c50840c004102c2041c1d010741c1c0e10003d0340d603400501000214103200c3c000d4288441c1c5076907986404c24000e99921124059407030144161280760070545400011688100030540341d402d00f0030728654174220743c2d4219119100039070005004914104500c1c1c4041c00d89540108004184c0c00c1c44030151605001c240342c6046282d51282d80184194100c03191680c003240c0d04800740c000c010003903088060400d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 477313273 1250 477312023 477312041
    0x15080c0d050103080a0e090c0d0b041b0203070c150509040e031c02041d0417130b0309100b120a1203020403020d0c06030c05030907121e05010f0506030f03040513 71
    0x45141c0310022040c0036005002d06000011a191703070b1404000300b810810600401c50f062250120100400a1440c409801440c0401d10141c000f00f22110220900c104031024541d000005a00c007085290034081c5e03488182c00140021260000100c4036124010500e00c101021503004030b44174200c01c8072102c0c0800445a5401869120030080c81d860040700019610070b100381c070f105401482459032410515244240601e52081680b0f018210b45100303900075070031292820200304c5201c0000216000b42c20015441648400080c02290900f213418004036280e07140c0d1a80582514a03c0d40718810740003602d58542604401c01c1b00403420074000c00c40c064407a6800094124841071840b80c100555a203040c01078601a072410b01c160203100314111490b00040b19039407001d030f1055800f005201c241c0c00300c0d0066070340519080c9100341c5007202001070a600c00301d800c840c66956001101d07035003990380c45441c0e00460218003500f8a921001c14980c2c0c0c0340505d004252041d401e11502c0c5680400d80e900c41000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 477314523 1250 477313273 477313297
    0xe12071e09050702010902010909060602190c2106181214091e100c030c0b0601021e1b060a02100b03010b03010603030c030206060a0f060806010e060c1b040615080c 72
    0xf8504004000c0c040c000f401000c0f80403030a024030100d40b8082e036004000680f0590740c0249110f841d840522104509420000d9030034103000c190200341d001c907080030115540c400090780d00b52605149408411110f8110220000600400c00e0400094245071340c02c0c5002000c1c981410b000c0d0800c640d0101d18483c0b43c070f00650002e0b8070381981884209440f04d403002004c0440e0504007000d052403095429a51030030001300003442c05400b60300043d56235510181c0080c410310440320100642d0301c4801840c800811200841d902c81c80c0001440b105c130500094405e5800d81c1c14500748030445102a50307a01412000000d61034a030201c90025490035030000181450041c0284011952800c01030f002100501040d001402228001500d90400d03800030130841d040e59100c0000a81b0789181141e406101030415810000ea840e0b01462941e02d550181a01030700040282907074501901140003106491550031340102d003044030400000b512180800202145030500c00c03103603520140d031000d0506c40c0c1503150741 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 477315773 1250 477314523 477314531
    0x607140d0f03061e0b07030504030c0609090f11091011031b16060509010c08070b0f060f09041e080403143319060b030c0a0e12071e09 59
    0x8155104581c2203140030180c4080005a440b14143c1103036030b41580071600c031030350500d00400c0b00590040052110324082d14242c1d0400f5225521201c4002c80c0d94003040c002501010f0910505c5080e2250a074064801b85d010080800d400204805074010302c0b481500c90072092102c482554000c138880c4c51640e10302416a81d6924000003441e0041c401c0c465020a0b501c41e05451482107a03031840c008041c0c1d4100c1c0c503541e0800f00c03c2801100c3c008510542119154018450740d0006502c000109014181140d20303100d51b0b160070340522034803000740c0fa040f611a030b0404090001041e460074580b104080788640c140003040f0f4908022910788500d074030041240540124030310071040c0101d1310612280c0481b00076032000011491526841130301116841c00d1007000c8011965034148100032076551071808401007116540e0f902551500c2e0001c40d100e61040c10002014150103030300600a104c2c0300c0341181c001c1c13041928500d20907651075490041d0009807e1074000015500c205c0b4401e40020180d0b014244 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 477317023 1250 477315773 477315793
    0x62b0203010e030d0b0d030207090c1110060612020f1b010b061323030318040f02070b060907090806011a070c060e0f060a05090402130e07200d080402060714 69
    0x543da644030b0010010118645500c0010520384400b01e070000a4056004107466420b00c10008020003c41c200b03c010711110300700d943d50509003440040031010f40785d040090380c0d0380f070060068982211075802c1c40e4000e104001d460f0b000d0000005075080030240382d404801241945030241e004000070a030301d0b58080b40105842c600b0a180c0040f0100340c400124a01503e8030908031081100f888510b14940e2640092110303154000c0001d034032502e4041d00401c0414a821411440b40032a813120b641600c074089a802000041c0c00e2400125410140515103040121700e04003200d0b458803018018180208200302c081106414401d0550f0241da40114000750582d41e10390f4003511403030003a0401801464615048415442d01c20180ca203030250300d450b50f600e419030450411000394032005505d140084401c9000c5280290182c44510400300d075103c54410198202079010025510030301110a0ba0102c10b08001a99100381c1c040c1d00598195840c0342c43d07484e10315185070200782c03140300d00b0054414990700da = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 477318273 1250 477317023 477317051
    0x1050607151413120c11060a170109060806250c030207030812040203010506011106060f010c05010603030302130f0302010c12110f010b0f0f0904030e0613090221062b020301 76
    0x703401c402c2d1054070005110919a1000e0310028144000500b8861b8001010511401e00900500c9292a0381c506050312054807100c0c0b2183c1003082e00311404c92982d60209002d80c0b4000c220083d0807076410b01c00401071550a1041080103103100c180b0324104000400c0c10010580200008409503a120302c1190300d030301a1903942a00084101c0707090740329608040210b925540942c1d0313003810098407500546110790b00d40080c842007807140e0301c0c002c4c104000d00b0120804200207204a2014500c640e80141e603484180e40c10140c500e0941d040300c5184000241c003040103030b8201c0e04040c440b0b5400540216044d889040c00d0760326005101c801c051901448180380803082041d4003000742284110b5144901100b035070240a0075a04034a4000e07001403200f004140424007a02c80700303141c030b0b000410f0b10b417400c5040507004150104550288000580205524071514980702c00120583e1820055420501e050301c00210103100076540c00000c0c007844200d80c0d54080e091219842801c3e000b8000707010321b013928502c1d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 477319523 1250 477318273 477318301
    0x623130f0303030f0c17040209060111150906060907020303011a0705010213030c090b0f090a090f050f101a0904021309080d0e0604050303013302030a03060905010506071514 76
    0x1002000300e02d00035200d045d02d40100090365209529486100c41595150b00340040b5a04c0030b803101c0c0c148003102c4401c8a494004220035055401822a040740a0401c480410702c1c12a01900840c0300d40211410461000e82c00010389045440e4111840e80442807000f0700f280e10310502c01e01411950000a18219030030441d190740046038440d010304001c65a45408010803503041640e6142e0140340313480000c40a1074180d06054000e83c00410000716200c0560b246800501010800c44440c0c01945140e403811070306010300015031002500520024440c2035030b2010038074043c0201403094203100045015900c48240e01c0c00341e0742c0222401c000300e20791428100082c0e0000030598a01c1c504000c0ea0580400004c40e185008690001c011825a400e102114150b04082d48803d10880c803030902c40ea0b81103a4041114108002e10b4010315503d036030003003000701595025004a14800d0504004025580314030f000c80780c0154210803490a40d07000a04400d01520700b00300c0c40d81000800030103001e500030b11104 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 477320773 1250 477319523 477319541
    0x71b080304030f080108120403060e0c36070509010c0c0906090b12030c120f07080d090501050a060f0627080606030d080103020102030d0e0f0a05160623130f030303 72
    0x50380c1106a0340c1c1d034641c87d6900a20580120462000c2c03000300001071850300000c1103248040e0541f500e13001504040f88050448000c1d007100d1010120b0708a1240d0384001e001541c12005410001142c6444000a04140704282d415810044101131502c00d010b10540000e0103412004801d120250352425646d02a15200346800e11917040040c241c9035a62000003295180b00c2c918000d403500c0c00e0380510090340c6800c45450131460713035400c00c600000981c4a00003002c07000002e4a000a80440500b0441e00f111001480b10780424900700041c4401901003545004603103031445c00003405840c50f04001180c030501c88001240440340680802d00070070102e00103118200c180c0c1203c5440318010310031501e2180a20010f40580c108000d16020a45290441c014071424401203134426400c0340c1c121407030000c0c40c0c001502c50f03400c44640c80c40159001c081c0803004001902c1c1c10300e451341c11001303105000042c0050110320810002140c454007000c0700803000c001c00301e501490814070b60303d00300600030b081c0d004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 477322023 1250 477320773 477320777
    0x9190207060c1239020703051501060914090c0f070c0323150c07060216060c0809120d0207111f020105180d0e1507030302070c060c0209071b080304030f 67
    0x250302c5021140d520080104c0f0f031180000d280196a02007152603401803e842c100c000318041c0340703400f2012a604101c0d010300306403482003141045d0b01d0440014a0414583c00400c510f201c100304600c2c86645070500319411914022080c0c1d61040384980000c424800d108004155450203070000040c0245404960007445080501da65070034803485956441c1c2c0394503a01c8004250310352002c125015500f0010341251445814018500300100620108400a5a9003241c42c5501c43e50310900240d0b101d1000342d04803d40034010005105041550503882c026400b0385100c8036400300b02641880100b402c0c0c040480f03030103003114400414041044880d5030811540001542c03d01c404203864148100d0711045074a140c0003d40311483c03480d2003c941140c2c005d0189070307118060a601e022103006420041000306c0c441e450040e581e0740107140440801515921100500c110200040056100c911026038403102d1481e2000c01d07009218260003a41d0300761314000c0c145403000f10403c0201354200d0102c0c0790b009066 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 477323273 1250 477322023 477322031
    0x405010506090310112809081b09060a0506301506030a06030c140f0312031b0706051305060612030a0c170c07050a0608040209190207060c12 62
    0x80e014441c1500c2001d440d00d4140e807205001c8914225298007a1410b84421150240303490503000030504902c0444070048881c0c240351000355629900000b85000070440c981c0980401d0300102000c2680c0c0350441401800351040c0e5002800360741e24224010050072009001d9511b9003078100d00744030000d03403a020b106100f6980003807000200c48640c0d541803144900080c0f02c5200708114043c44000e82014040207881a254003000c0001030a0840403000740484070070407507043c0709402c100050310134030f07164040c040e0b004034186003c8982e802c0e040341c3d8014644c00d401040380c02d94407040352884c4210391002d000d8514040600a004610b814102c41c214050300448259858007410442c502510903030310f0344079070320410001c20000d0051f0020103a6030f0040100a20b000c5842000c2c0c42198064845580550800d4800340254a04a98503e025010b43c0c03814844600e403550100c0c0c161000a010400100622944001600c0c0b00d40c04999060341d00540501541224420142c0900200144022004d00f8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 477324523 1250 477323273 477323279
    0x5040b0f0103053408010509210a05070201051314120d020703030f121409060f090601030f3e0f0120070806070c030e120c010807030f140105040501 65
    0x10144050582c1e401c1400780400600140c0f0014500b10602c002c06203c100780904000000415941d000c000c00f1004004240c91402888460504030b16006042440780d90908042a0011100a80300c0220032801c00d10741c2d80140d8001070b6014003c000c80401d4180d802100030070350709480700c180c1c80301e483e045d0f544508070700080f240c09440e0400b51081a0042c0d0000c401000480d10981983e420030705282040c96004542449070029a0751800c000d100840414080c00b10b420020002668048600d90a408d4036080201c109512800d0622014220041003844482031100440a0070a9440b402a03041c06e4000c5403400e044401d00c42045031500302813209080711003400c0150905014034016981c40c5010f03030300500e001244050421304c01c03001e0303c584940031981a0b403c0159070300500407130b00c03a03040303144107454010504403481c00054003901030700d060305808020006000f52101e000342000d4a0644d19403408800404030301e800004c183c0e080c0003000052003141d200c05816602d094a06011580c1c07 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 477325773 1250 477324523 477324541
    0xc1407150c09030b24040c0215070201060303081801140f07110102030105180c0903030301060512090d0503071d09010f051c080f07081606060603050601020a0203071703090a0905040b 80
    0x5000e203c081c00c1c0c12105000100e419001c083e00030310403081001c1007540d00955001140844010110301005a40900031443e5404100d4480560013105440240710303281c259600104804400f4000e408490880041e200401d00b0139040203154078041e01c84400b113854070b03602d01c6000000649144001ca0004403942c0702000042c0202c0c0e05035880600b0900b204011541e04640d00100200390304c1d0080d0040c4a260001c1c4d40c103000660080000c1d41d541510b0702c03e1003046e049144009010510303a5441440c070342040540102c25a07501c12854141070804003043c0d00c6c0d50070040303003c50100307500c00380e044000304100c601c000506040e550f040d03508054030681c000c18101d19003030040c0040c0c0003103c1800b14030080801c0b0300003890003610035005030f41804031000040320b0b03c0460120450f0b0503900c070f580c14403105516115a5600810134401440210010303004261500c0260240d000e0005085010403a646400c10860f646240d01410300e15041c0d80c0c0301c079410b001340801c4e9800c880b404600400725001030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 477327023 1250 477325773 477325787
    0x30806040c05030114060903030f130f0e0c09030a05070e07020139090312050d0509061b090a050a0803190c050c100e04020c2107030c060c1407150c 65
    0x103107494640d01e16507420130030101c0e4031413440d08005900c6007007040544826202400603204428821042a44940c8409203800c00c92425401c00c44410701952020880c1e94101e003016500622200281036170f0b000ca031808039090141e1400c02404500c2800800a2a243d250354100e10131000e035402009000803d190b9400c5400544a81d040c50100042c070440301699561044000610941051490a079a85e0750720400e003e411020704c0017183c008140715007181d01078021346510103a07034800303040f840c80c00c00516a0050011000c0d0b5043d00310100d4444915100c20140e2805000c00400300115a9650104217607240c0c403184080300b02c422011007181d0340714000e0301c80c444a141e120b80500451075400c0148130a243d21a84c0c00010800d110b910166103403220310007170440c11803040160021107590514100001c401c00c101150300d0404200700000702f41e200c1084440ca036405000400d04801d078007811074004d4884102240d080000150701403c0241e4010741e02151904032005022428078190107480307034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 477328273 1250 477327023 477327041
    0x72001020a0c031401020c070b03160c030c03030e0f0109050109050f011107030c3801050303030c0904050c1213050c01020304060504031407030813080c060403050705060a03230403080604 82
    0x15054200500000e1100c03014120713424112030005081608a80ca038074640400340c1e0040000c0c0000000b8440c150713480c0321160b2a030039224280341c0300030300050307900901c8040c180d0000750030559240c40d0000c0031081401004490521030b0020f2241ca040740c10039138000d000004c400c0f80c0314410214100e00019040c022541d0744030301a000d085c2000c0103601c05483c08402031404684040d00f5100c1001c003010203000c040041c00c0018040d0001810f1943c071400d100c9411f0300b080740b013a4800c1c420480d03200c0c1180221140200b0036100405c0b26120407a80502c80c1c010600104842800a0104890030008001000000d0b000300b0071958403045100069840b80b00328041c100010b13000300720a02c040b071071f4002880300c0012001c0c121110750360b480e00d400455800ca0b2444001d01020040200400b8a04011081d980001116203a02d42071569403015580c02c0d061051034081c850102c2c0c181112406648130a01c00718100d904160100116200d0b9200c0b04000c603800c8001c80c0f81480464101d0410384110360748 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 477329523 1250 477328273 477328283
    0x5090103020d120e030a0b0429010909050a05010c030e120c03181c06020a1d1003150b0c101a0a170703080408100c1b0609030504030206072001020a 65
    0x44480540302d040c440030160f54642c013407140004104003141c508000c01841c1038061108400c050600c0d1400480f2102c02072103030b040f07500108819558a100c1041c280d41101c0341c8074000101042d80e403508500b005900c03100603016510b41005548c945416030130040c510b0500400f44d07400c6400e0801006014041c0742144016540180440c9034040345104c0a000619402040200d00c640195400c44031103800c0c01c400c9640d6600400c0707804030290410010f00c030f00270b00c40001103418074109003c1703250080205030f00340415440e03044240c011080702d003840000d0f20387c0e0300c2103603035460000d012996600410303000b844007545400d221500c0341012200811149500605140300e40e0300e0240d8480e0789069004d1001014010030100200040614004000800b400006420f10103031301d5a4103411940c51300c40e40000d00c00f00c1c902450b03100320b0040044000941c401c0c400281c03244941002ca0300c0f4000c40e000203401403070000c1c00006000400300f8016854040350410398207204490012030701d86424170700043c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 477330773 1250 477329523 477329539
    0x10b030f0705150f0711090702191b0503060a0905060f04080304260c160605030405060c0d0b061602040c03061a0702060d050412021204060f0c03030b040e15010509010302 75
    0x4443d10b05007074100881e4208505003810b0406003840c07100581e111000c226404141008107200701d05080b202294010a1030020701240000345003d00910a45401d00618103880c0c03608940c00e45111004000182c040034080f11850316000e6013190041500240035505480340500048440340500c5003d0321903075000d901e85003161200e540307001c0301a02c8092032503c0ca00710400c0417400360301050041c4c1008003965006000215510762205641c28a40d00302d0005c00c00704000f04004100000740b131541000920020703d517202c2418429600810f0003a020701e612204c00180e00781000e6490640c00c40b142c0c007c60b0300b0440d031061548290210360a42c480c1c000c4650f004103200c00c04030800400350011900140c00e540c40c1c201a40005401c0b15811502105c05854096a03445040d40c10401ca085800012404c1440c040c10071308083e14607140c000b00e100070400417011030020035110390007241400d2000f42c01400220320b080b032119144e44614050f8818015240300004161801c2e0040300e0499030040d01180f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 477332023 1250 477330773 477330779
    0x216090b21071512050f040f03230d1a1f230408010630020f03100906051603020712050f070f050715020102030631020c070503010b030f07 61
    0x70228054115076214010305400240150b20508a0300c41c10680c3d980304030002c020b10142c1401c0399000707000240b640490604000014290030004440b80741c040c00d1408009241400070404040c141d80c3c8100d04a40c04180354020340d846070044c030603400c8044056513007043c0b01014041c9040303aa150300180210401c980880d4180200410340598a071861b1401c810a40400740000a03070059002d4400e0382e641c2c54007081203e0700c800702c5031000c019050b1640c031407804880845845a903481c2e4040e20407400c80f003141e070f49a60b00300000d05090012a90903c111401810400002c0408a540d0420802c0215001d40440e2091085a40c0f241d4401481c1a402440400441e050b810082007005c031400108030203c0441c9003c0140592948034038000c1c83c081c0d0820f40140041c1c1b000c404843c0c25a0300504c18021a0358038108500d286018044117180d0000d5450010448106230b2500c120910748001740d9003400820224400060b22030980007030280c1c5203c0300615a903006450616a45900107030001c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 477333273 1250 477332023 477332059
    0x10b0111010504110402310302090106080106052a0a0f0b01080a0f061d070f0906090b18040204020f0a090f0608040b070f05040e01060203130b0a02150406020c0d0216090b 75
    0x3800405070314034201c428440d01100f64800c1442c0c40c0900461f20110b402080007145402d50005014052034500700c0607552500b80050503d008400070b00005003c00c240035680c00c001ca42c0030b42440300401c012030300f607030b4658101110702c01c1a604040d601070044000109070f1020009240d03041641c00101e00d20344002c00d4440301c00804002440d121904164502010340382d90400500c4080c00c00607001002c564a00001c8030b00b1906d41c2e500401641e130034801881c00d1582c2e0005022104200c185c1c070501c041d551480010b00070310901d19280040d400100301c0030702d119400036500041e540070400340001242c883c00c007641c11600441e4001c0080108038001424103208003030155600701c060800508003611441104a401c0d030036004507005074170200f805d180700c011b20900c540090201c6440245003120701180291140000040e846056525001050400200f80d040720034a0380540c09031031a440000344002c1d100c034081c0c4d041ea070b04403c8032000070961500920074402c49010003080700d81c1007a440104 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 477334523 1250 477333273 477333277
    0x40b012102031506031006090807050f010e04110f0711030a020307061407020402030c090907030b010f030b01090305070905071404060912030c0b0c3001031b17010b0111010504110402 80
    0x242100e1100340c1c43c4900e030641c0b6490061401144140000c6001500b0004010594030a981c8282030030380c4840010403c0340c0320100b62450340082031902e44c81d40344400c804103028100725014510302d01d1000030031907014001613000d002618403034a8683c1c1f41c00000750400d40d640c00d5060001e5410381040c1d00030000c0f14082c1c03070004581181948943e00308845500050101e030411a09554840fa00040300040c500d06040600e5010005040401c6a10540780008027202c03210407445c01456a01c5102051980c0100203140c000d6030300c001144c0174507032500201030243c1825110000800c0c2301f603450b61300800e061000c2da0240c0d840c41e40c0711090a464004080d80d50444080301750180181481144003041503064024403a4002e40502ca9450a9805100d540c514500c0c0312064184104c001f00265900c8403118241100e0700002c6003460010307007200060010169900002c19900713004031151a11206401400040c0c40c2600c0350f840710300003500501d00b80d4004490040c540c8116009138099031400c2e81c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 477335773 1250 477334523 477334531
    0x20d0503012402150f01031109090a03050a11030d0b210d03020304021f08070f0504080712062301060311280513030c080610080a081c0507030902040b01210203 70
    0x41251145035202c000c0b50b0384004e041d240d0f8503a1800c25401401842a00158104204015103d82001b40b5200030080c3d00c1c0c1070a954000c040050004806032407074800d809a81404440b4001e403a40c800c008000078005198103184207000705140c05040c00c44c45000d04407134881540380c0010384140703901c680c006c60003540001c008a910610364245070f184400c10508140c0c1e4008151a26810703801c00482c00b0384030f1211100303080b0030007600b004280b127001d401241040445403d114144c00341c0400c1d103000c00140540d925420b14002c03141d15204410b040d0020341301d048801c1c40e24100041070400f80311003031521410a040c1011704544004455240d0081c120003282c0802d0316211342881c007103210680704940c01707038010b80c0c41123510704041c400d5210038801d0035001101e600008022a02d407800861f150308481070094a008000f00b0640100c00014403c0b5524944161041002e4038150b000070703005205007442680150b00d030400c403c82c10b5010758100a200080c1c80160070071809880613080180d44014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 477337023 1250 477335773 477335777
    0x307060f18081c0c0e120c1005030a050a230417030a0204060e030c0102060402060717030f01090b01020a0804140310052d100306020c1f0c020d05030124 67
    0x4940078068a9108581192181c8103420003680c620003446a120320f50310079401604441e142040300001c681d04802c81d400d9110302600c15a081828a6200608040d4220306080e049900800208105030b448401184240c2817181c0400854494520326800c80f21800e901e0402600d034482c000a168070108542c43c3e05c10f2160700310041b4030302d0b01c000380c0c4104d800c16510704810b01d40204040c0121130f08514000382858007a401003c4d800394003c0001d64600010300040c0c020f80c40007900c081800b203e011032140e01070303a1480c4140d49041520440c800702400b4429580c8541c50600b0003000c5620104503072010039082401941460704002e02c0e8009200650320040d8140f041092140030851180201440f94a40541449401944c2491106551602c0c00e043d49030f0308810703080002030700c5100840d03c1502d401400040e20340c1030701022145000159102590b02d0031106280c0500084560045015611184d083d03902c1c00a81e1881074455020a01070303d044425031001d9480050180500c2c507040104038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 477338129 1106 477337023 477337031
    0x7060f140301060822051f231e0f07110703080a030903030f091103071a160c050d03080f0705040303050a110c030f0319050702030307060f 61
    0x14090142408180404500001d101000042503002d210b880c4400b004070030f0a00568605c0c1061041510100c012031441c2d2041f8503024000c00c0311381c05841101c80e0301c040d800b00302d82800028009035581c1c10302c0400c0034101d0340b1141810b01505101181050030700300124010030802401781100d081c0d50211004100090445040380e05c0b00000e8640001d03c007441c0e1a0403000760542840c400c5015007020f040f00244a940c41041034016001c50842d8280d5955a883c2502440c1c4076200316445c1d803080c010350b03031079031065501c402c04035105124201007240c071a000150f4a0302104010780000c0c5000d410040407113402c0e01e40315000320541c1011410a4650b540040c098850310030b11408001920741c040050400402c1180ea42581c020142c0d01c040001241143c1d82e0381000d003071700c40d800309846803414005010310103e90b813441d00500174601d4040151181030141c03003401e580c0840c00348d031 = true := by decide +kernel

theorem cover : BRFrame.Cov 477158273 477338129 := by
  have h0 := BRFrame.cov_init 477158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 477158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 477158273 ≤ n) (h2 : n < 477338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
