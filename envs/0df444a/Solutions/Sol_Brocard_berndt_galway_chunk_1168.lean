-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:33:55.903677+00:00
-- url     : https://prove2.me/submissions/6621a73f-fe96-4e67-8081-774370ea8fb4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 209892086 ≤ n < 210071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 209893336 1250 209892086 209892097
    0x2210a060612090204090b07050a2705101101090b060114030f04030f090302090c120606160b04020111030304060504031d0a05060c070b1201090c08090312100b0a02210403020306010306020a0e04050a02 88
    0x22f844034082d07803408210a99030000e0451150002c22081c5004020790b04001c40f00007502c4907141000100030744945845400c440406805607542a05401441003e58200350f2012105c0038125103607144d4980f4004001810b10b0140c03009003001011400c0c42d10251152202e100034681c0103260541909003c14030094076000410740414120105010070118603280f4121010400c1d0600d48656403041c5888644081d4401001607050140203070340c0c8007103000140300461103140b08140000d4241481d0a00a0448004500d80940441c0341c1a252803e544c2e0083e042080701c004941d050b0343c5400c01d25050f8100400c5500c50301c040d06000c01c0502064120b498028103071114213400700000e04c00c03200100d0711110280c0c0d042d03030f880d0010000b50240301c0400d0209175000908090712400c01c1e42e00c2000e50065440b00001c41c0c01a04501c00c0509900c103140710480490082a401604040c1140c0001e41c41d40d906100080005a0000709060340e40e002c0c0b4444107006000510402c940e2902c42204000b81d8407130b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 209894586 1250 209893336 209893357
    0x203070507050409030906050d0906020c010e01290603090c0907110105090a0b130c0503060c0717030405060c130503010c0e131a010c020d02030102210a060612090204090b0705 77
    0x10640c0c0400c2d2400c01d845100c0c2c603241c1641c1d80b000f48518100301541c0b10b41c003034a5a200d40d240c40c0c1036150b01054860000b0202e0404890000800e4150f103e071140c2100e0b40641900401800060150340d03000c20b0350384180000c602126880d6894544861151429a4840700c103070304207101d001009001500040c403031f200090030800034016991400c00300c988907260501700902940703e07100403406110041403034100700d500c241d007400405916400040d1802e4412030384010501740024082e01004000c940402051400d14205811414590350b000d854120041042040c04000300b61b0141140146100f90002d1802038000c0242100c040c3c00100894034030082c0741e0042c03607645030b60411460184102180c2010030900044056044c800441d10032501da01c003640d00020286103680946c2d400e100414044100b0300c03c190304051010450b0b040000002c0050790345904c1c04000300f0180e038000c1d100c040a000840d000292503051440010000c1c070340c2c00c00240401c040b40c401c101d84a030300031004250b0a0038 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 209895836 1250 209894586 209894593
    0x61c0507080f0115080103030c020105070501050103060e0f01051902031315020703030c021b0108062101020403020f06030405072c1e060402070804090b0607380915040206040b0a02030705 82
    0xb01c0301d950700110242d480044c0f0001d608a0700400c04240308952250301d40b403051402d28075140c0d240e2101403d4072800c0e0011340351540d603401011500201041422400401d20f0024080c5280032060066450000660316182075000000a8403040c80c002580f15420350001c1c031800c0351000e00000c80000d4100d000c084010900e004250320400d80006221111944500900000075001100448600102900558005000c03a0b201d0806801d0203101a090151030300005032038910354010420100104c2036101c0c005d201c200240000f00324003085510540b0001d241d039100c03c00700c0c00a1407907001c0c5036440460841400707900b800b03038010220b0003040010081c401711003541d480764410030013203102346040180b042c4810003040065102980250130800030041441c1c0c07c0c000c11b40c54103007400d42c074008100700c0d03100b44600554060304400242c0711500009200c1a00600c1d10000c2a9a54000c0c500c030f000321255018001802c56480342d049078050226920500c0c0c80380c01c0311502941e6908006008c41702c500 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 209897086 1250 209895836 209895839
    0x705030a080f01050f0d06020c010609022203021f05070f03020d180f1707050402040609180b0604140f031c14071e03090f030b04030813030e061c0507080f01 69
    0x40b9000110390580c2d6000f005042141241010803401e440d0070101141d140e9001d2010071000e54007132142c5002005003150141c0e8910100050f448680785264505403211925002070001d0389841c1d1100755a00360542c41100100b1009406a40034052444014990320107000305004056012400d030780d51140076100c1a560f100c55480c150f0002c2c450f40180041444420010808200841d01240c142640320003581d0915840d88085000d81c2c0c015002040407a00d246030421074020f20940c1d00500b1a1050b130108481c40103080010402c1c82a4850a9070111803401e45500c99980d80400c03480c10308004080342c2070a20811514100001180000da001c101c0b0b59038100c95408115044a886036400503a43d01c48821050b407042000c3c0001c00150b003040f0103050049440c901000000f0050743c0501c6980849107064a00185824002400302c00348640d8054407100094000385000d4030201c04503004c035144d400013011042c01c200c08145031031840f0300385410301680030b4115204134081c550f0110b00c02041c0c2e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 209898336 1250 209897086 209897101
    0x31d01020609100c03060b03180d0305090c06030a020909010e0a0c0c0506010e090a050f01051602011509020a0c080d05070315030b011215020a0801170c0603040807060209060705030a08 81
    0x507102280d00c841c454001d08002100d000260b03000112007401c81c00c0005106403034910a00c1c05400844000c104c003525102501404007040110154100d1a49800c1c0500e25000001c992900800b0301d000d4003a490102c040342d86812544c05440001c01c01600030b00c603e41c2e40c0c2c42c40702c081840507648100303c00d02e064064a212445a04144c20b281d030040b00600207a4031300850b6450084004005144034002c90644800248090200000303080c02c0d00d0012076035083c944000821040300d401500d0540e8903010854814068030345651003115040540162076078207214081c1c3e01034144150040c40c8000008034032036000703084c1d0304c000d000b0a42948c04001c8071801c1e081c3c0b005602168000501000407030801081600c04500080480c2d034840c0c1c1103581d45081c24031000060b600314802d044081000310006101c03001060f0b20008509485400a04910400380c020503010312010700050181000000c0d03107401d01c0015011500c070300b00041d150a030380d201c15041c0f161f1a80c019401e8a80002d01c0b04012600d01c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 209899586 1250 209898336 209898343
    0x2090324070c02010c020607020604050d03020a11010503060907121e14012907030509060a0816090f090504020d050d02071404050c0a0c05160f0302090c040e0c0a02030d0504031d0102 80
    0x50b641e042c0c64214016125408118440d0440782040380e00520400020482c0e031104071150301d44601c25001803114060b503103004090b00380d44801041c1001814410440d0540c0d98080b100c0d001085400c3c0000029503848205014080d00352451622183e100500c500d90680e41d800395404815403002940c86907210307285c101c48078041d5582c0220054400081e4108480030000800581c1c4c401c2c1012807400951401040d40d5401412414000c1003100c0100004001c80c0c012483c41c075042da1412505443c140300341c00d10340c096540039034034205a4640001e800c5440d1640c0305a41c9540150440718a4007005800950350360341340c0076038074050600c1180d0160a00705406851300a0f01506442828a520400d080710b03850b9035402e00382e443c1c0c07143e000000710000c035248000740035111761840302d00780d2411401803107980040034107590242c060402040101303010628042c0c2d0000740300f01c2c0190356940c82e0740c0100e2640c06628082c12740030b8078103001c0c481015041300c030000508c00905002ca40102080c001643ca = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 209900836 1250 209899586 209899607
    0xb0a060302100828020403060e0a02011d0a050315160c030203041203210507020d05130501080c070816151b03020903010905100507080112080904050a0209032407 71
    0x40160911600303400480c0591800e5134012036984000e05a418003134051111480b91001510071268001001d1050003031a019407e02240700c40000c07c812985680000d24080c0d508101401c00348030021003003000d5845803007190051a0080c12039074107c4820210501032101524a0341028000c005050f2080340a40c601a10b866056000b850500d46401e030b011260b650210400c404202ca50406035450511090b20050128680c641c002054586018041d1401c51141c0942c001d00c5400d105c1c62240039840304841055580030302e0426050785400d0086000c500403044010b00904000c03401c10314040d501c4880d0140c2c2d40c0514082c8031414007640110044841d650440b03004407102d02d2500d011140a40c00411030900050000210b0b0301740c40d00e85904110302041c0c002480398503581030089080d03102192034050b24600282524000e015a148106441751150060003207403120000f840303451503641501c072404405406e480c1c0c08400003001e0144845290030b6200256904004101c403144940008007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 209902086 1250 209900836 209900839
    0xb19080c031f050a02160c08190b0c09030a0804090515010305010b0d152304110901020607080415110a030501060201020301060914060c010207081e1c0c0e06160b0a060302 75
    0x92200e0381140e0b0005020014410003480750200804443c2e02d80303031030302001d51034002c40142010509050041c1d0600d00360980f006169010b00d40712001140c4904003164200324050900341d51140310401083c11301086800140007458085400154261560481c520071010381da000004049010019000c4890030700440d5a003010038060b0020200050380402c070583d00240403142040d5452449c15140700781030b5240091100c51b440c40c080300d41082d003e210301c1c0b900341054490910421400003562440c0003080c0204102da0140441c040c0040200c1c05010700807005818428000744001c640d8141e1700000341c203400240340c0000060400d02c10300c203803070503a181503a0b59031816280c841d001103c440714500145d4091010049204070800900c001e01c401441015443d440d902d881e803584500403100010802842d00821090204840181c00c0144091040740c000400240d1040119082c910206034035801900001c0c183c83c0840d0700065035a00756100f00c140c00c5081d91004070200a070b403028070009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 209903336 1250 209902086 209902123
    0x5010503011a0108092a130612020105030411210d022802030114070c02011101090b0c18210705010c05030a0c051c0302180f220b19080c03 61
    0x10869036115100c1c16410102185c00c884000c0010400100c1e0340c00794050003031155280404001c0b1905083d810302c207405000c0201008241d250030406122000300e554002e04200c0000002010080c20501040300c0c01805070040c4070b40e03802c80324001511032005250300320034420000c9100220788005124400d01804205290034541c4401c40c1071419060400704a0303140d500c03011071014112134070714101c0c0708000030b6a41d86103100050001501c180e02008141840d81d04200052010134002002c0e00c3d0000f846112150b62541c44240303d60044070f81d581e00580c0b054a040380c030440020034501c454021402c1c001969a6181e41d040191021440d5078402000b94009000540c0e180d8015025072031124002c00907130314002c80c8000c0b2019462070800d546d4010940c0895408507542c0d48404184000d0400d5822140098941001a100c80100301c2c0c1e41c83d60039844001451150308030342154075040000b500145a01d0116580000d50b003115000e5414a03100310003540c00103260000700300500801040c0340 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 209904586 1250 209903336 209903381
    0xb0d12050a020111160308072a0f0204020c0606042306041d070b0706060f0605030613020c0a08090f0411070803070207030b0103030c0c050306070512060319150501050301 75
    0x1a2081d03040103080c1019556900c20248911011400600d2164030314032001000598501d0050f181c4c41004c0c02040c00c0040c1c420400e00f0300c2004034080c200c602c200c0120032580e04483d140c00b004c1c90305078010080d0402d00224000080c2540000c4450040d4000c8800340300c141e500715001020040c074080c1d8109640c03440c0011071a5401d140c0d1040003140c201d00800b01d80140c070083d00300e107410800c4c6c1c018144860002407200070b0024520810014144032280d00d2000c40c03400d000103041e4000034242900c078041864401803002d8030313541143c91a81c03016045c0d0740340004c94100361182e83c000c000e1031800341480c00301c6802a443c052164015400d071084066041081c1c44d1186030840d0001088601540715000c00400450f840c546054001c5200c0c0d40d03000134561a81c81c1440c1452204d43c4000d0099208506000105801c0341c10b03104060101d03060014513a48500c0080e00e071030550f000d45800c1c4460281040b041c00f0103090400c102c0701d80020140400e903600c605150880d60540c0b161007007040d075035a9 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 209905836 1250 209904586 209904623
    0x102030c0c061602060703270e060105030a140a020406090909021810031a0a0f06030c1238100e01030206030a0f051f050303030108100507140408060a0b0d 68
    0x360003142000304900004401560210b0040e46c412070041d00841c94400504138200700340d080391501c03105000050007006280a14a60340351801801d51814010084000b4444400641c001258080440700c0d840d50340c2049000c0c07400a51050041900141c200c1c600462810381c1030068150080d409403254a01c420894004d1501032000360180e04020040800040403412f14040d44054180c0169110130a00780410f8504c201e4000a003030807402c42c1021400c201103400c2007501021120301c00700b400c07503c1d0124906203d4080320159a03020580c1d40c0a40103202200103440b02d9091086040315206541b15074800783c0f1032561a101c0d082e410010400148018181038018581010030300700e0104503e0308482a45099901c2182c108201741c500015039805400c89425190061405a016520b1941401c0c000c1c0d440b110020f540044c040e44079408a03148074810510b8152500c841e0420302e8603591100e0072240c650344c05595240d155030034420b0000252804c1403007000c0a41d403000010101407500c08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 209907086 1250 209905836 209905849
    0x111070f0918140c0a1706010603051801050f01030302070e0114240d0b03010c051206060304021206040524011202010f031d0c0907020109052a0a0b0309010b0102030c0c 74
    0x1504007980121198070040010160703003491941e4048100a40040131071038003030292804559011400c0700703210300515031a0300b40214555054598615000c90390b45d0f074200c0319041d07004c181c2c1151181c0751710f844100918060140b541e541070b40d200341d0079903035210303500c03540fa44e200182802011035030190520351080c18540011043e03194071521038a44030601060520b442c4582141d80800c1c05292200d500981d64038081c407446188860700e040c16410240307500e1030134241b64001820f42e40210000400701d415540e4026451030483c0c0540e00304d50b0145400e01e0703c6074440001d04400d05001ca0310800d080744041541ca4030a050314001c40312500000e40c290011100588881521014507540704401c000da0b040c2c010510701d040244400a10000070740c202800009a0004e00c0700c800c692602c004000002ca02190710307610305030120071010b8415001001101c41c4032280600b0744e802002900e000071280c40c0f62018520840c1c541c3c0c000c1013805286001641c40e032203600080f00c0b1036004251141024580305 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 209908336 1250 209907086 209907101
    0x40207050712031202190f031a0607050a08070807050d0905060f0d0e1207030e0307050a031202070503101a0f130e01020903010f0b0312070503071e200111070f09 71
    0x2494001031001300b440c038400072070b40030030028011441200713070707440c100c9400012070001c48105140812403985820701040341c020310000e50701c2c0b2901001401c001800400c01000c3c1040d0b8100544560392011407a0124260b80a00b900302c8150194180014171070740141c05101c21500701409842c500460400c8052082c2d1020880fa0a503e43e2071558000c2008108904110643c00c08001070380c0e08502c1c24040c1c10f5041d4100300900c258441e000601c1252203007610070089941c82402c0c99a06207506909900384201d44e044075030144641000000d0009aa81256141760100000007503a4481942800035448840304490341100d614884252034060701d62007400591810b070001820140140700190942d40c501425400c0243c0703805003404079180c10b000c2c003140080103401d400c3c948100d5a803090740303900907800c001d0003541450a503001142034103502d05d001586d00030304205244103010754101c0c048418510045c0003d0b0300b801c5d5010083c000040e0704054880d0315120208443c40e00008a01603c41c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 209909586 1250 209908336 209908343
    0x8010e0403110f03090328030c021311030411010e031e011104030c060e0d030f0c020f061c05130b040f02030c03030705010b090a0908090d020f120109020f040207050712 74
    0x120030302c240e1054070501c100802168031a010356500c01c80b0608051410000001381d10b90b410030301040b541d051000059065070180d141c1003155200c071207800001e11107101d5421030302c240c44c209000c81c0b2081480c40029031042d441601c1c81414103a608004503007500c00e140d11581c040e8001d00c45025080c4d180d40b290240c0850110001c61020701c403101c20301003500726a008907869026030405101c0c4a40101e080650b04205407100014410147c40040419820700401030920006c1400c2c1c0d81551030361070044405950107000207555219101d46440c5480c8295118000d261170003012582c1066514141900c654003c83c030000f241d100c0d6110418086980441240d02d4818211002490307141030015281590243e00001a500301000600c55100c0d8010500070405150480300c0001804800680c1e040b0700c400d44000545c0502c61002c00d0800d910101d090360b00100600e071109548405400c00940c0c3c82c404d031800c840c3c2d0712007042404268000e680700101141c1080409004070319440c0d000c103a02c40d00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 209910836 1250 209909586 209909597
    0xa03030b120706030e06011d420a0602060c0403080d062601140613020a031d010903260117010902040603030305070215010b0a03020a020309060f040501090801050708010e0403 77
    0x1181001c907203801d032540e020b000401c0d01e4800542c04100e0034403a1500600540b07400c00380c424580f0740d08039407020340140032007140e0082038069800c41d40304001c141010004402e00108030400c800040c0001a072403060f0034070501aa12010413500d101141442c020038403100141c1c02c01c0c1c1160b842c012540c01c048584110503035a2000000d400c0201a00c0e00b02c012005400600383c2004408500d081d601c1d00e0101500130948041400060b403140785072141010214080103880da0b120b00821805000c0e03a80409103500140c0849031220101036000b10003030761103a203c6131108030103100310400c2e020304862604d004001d0b00004008040303508000301500d82504e4000145c003100c0e40e0000d03048400c960001c2d40000c0e0384504104426404222001d043c40301400d56016940c5030404a0000303114100c44881096004034644107074600070016070f8003500c40200195104e0031005006101e9403c00d1190300d00080240743d00042e0000103110310b42c06070440d41c4c2e41c020342c1d80c20041d841d0814000030f0412000c100c1d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 209912086 1250 209910836 209910859
    0xd02010c0203250906030213050a09020a06020f0c240304031205040f030e09090a02040b060702090408130b0f04030303091406190b0303040f17241905090a03030b 71
    0x342c0c14040056807001c00946400d607002c80f64a042c001c0e80e000e41000b000103191400500150703840441c4003451004d503000200b081d59440c0c0e032804c00740070ba211009400551600d80442d401d5004a42c80c06031007130071003c4030b899208940801001c00c04181020510207441c9a05801b1410410002d41e8400c0c041e04000d0989094000b01900b00c0300103c40556400c1000c0ca24141059400f62401203444401c880110740c40c200081c90f1902c4a03c4a02c00a102c1c0e603480000f100a038031102c041d510301c0764000308482c3c0c3c04d1400f402e203c1120361003488144d4021a0114010580b110305101752000c0903150200d560070135056603803e070000c1800b00001e49039068400e000000d09542080060321440d20000240e4941c480c5281410940300d2640000d403094009200522a1104500710303041215074281100703a03820205410036042c004621400f1070081940601c1c00702081d00900707814011100480240b44110103665120304440341546c01200340e421011803000130038403c0d0068803510200500000c8001c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 209913336 1250 209912086 209912089
    0x30213021303050a03080601082710090c170303040b0103080c07050d0311060c0f0a051c0e0a0c0f060f050706061502011415090708070e04110d150b0301050d02010c02 73
    0x2600603442152184c0c812074007181090f40c45134400d030708880203080403549400e26a03502c0c042440d40510204618403600c0d4240c412210801801c5140012180e04002da22028140040040c02c5809002e09602c45800500508003001049a210ba40c012100c10382c0c6074256034841d0f00380d9005201d140079503c55040046002c3e60f404480c0c8a0151080e12609600030b01841130504001009140b440510010300c11907071452100003c4404103809460090b41d2220244001c0e0f04030810342480d845100d16014452416075000602c4222090245403490541969424081002c0e5100c2c018600011508a40c08080c070b80508060008144201070101b00e403625403244100c0d00c40c1740100100140e45808000841e084c0c0b8041468100703c4400c2075421301d10400000c65981407024042c0410454500001003920384604d400c042440b030b000304140580d4080743c8081d6059046a038200c0703031490bc0c100501800c065406201400c0710f40c4010854190781c03a0504019141007641c10990600c03145044941c0103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 209914586 1250 209913336 209913367
    0x8100b0307030e010c02010516050a0921050601080f0d0f0c02030a0b060f060702030d2102030103030818030702030d05030a02040e0f011502030c0615180403020105041b0501050403021302 82
    0x8070625078000034200c2e07101c0c00d501e00b90f40d581090402564036103010f101e50380303101d542e200c19081071508180740d6984003114101c900d450315500400a00000e60310320700d03150280c1c91070000824000c004440c2140d885548580c4c584242c000090002d0b44090890380301d89002d180c0ca00c0c0d408085041460742e100e0203230042810090a614100e504040590411415141044182d09604010764095080201590100e661000741d042c00c28180100380025011b41d91065184540c4803032900e02c00e6480396981c1ca005000a94152521501d4041180a5a151107400010748010640090043c0791a0005500607070b001c1c0d201810940085400300008900c0c812888081c900403002e043c14401c441d03140c5903000c0c0c80c2c2c0120254400454004010424020a0024105401c01d800b2030400c007090b102e20340000d4000142c82e26444910740a4010001410f40640c0024443d6004e1410b001c00468003089501c80034036107005241c0810b009000500260a12072020341c02d0b400700440044c500700c59031500b00703034 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 209915836 1250 209914586 209914591
    0x606041419092c03040506030c1b07090207020123070f140a050c1807020d08070c0c0b0304150b010c0b0916030f060c020c0901030201050702040f020a0306030c080d050a08100b03 78
    0x5004000d089206101c2c10b0380c025143c00000d42c006141850305160000d0365611020381001d40b02a00480c0790145584440da980a1000d219400c840c402c039a5580d4070000794200040c00e07404034482c041d846c9000c0c03808060100c450003d583c4542c0c6004e0060b928040417014054003900c01a1181d000d4501034501080303025556401a030040c9400170f042c204020300a0054189002140b010809101c209900050b181c55a0005420300300000d0352001c10803107c1120703102c000b03844001c082a0000300069071400560246000d1100100506140001002911039801403180004c20042544001c140c59441e496006801e0100340e42d0074501055108261034500d401c19200d200d00c46040f6010031240740710340396186809001408200402d03100181a4008c148006814808001280d0085590301d61118809030030703d201c1152901c809103401402013030708c2e000c100c0305c4804450000c9071094000070100c40070180ea94816183c807040100488003d0000741041d2640600d914005c02c014424401852 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 209917086 1250 209915836 209915861
    0x90302012c2d0414071d1e03100606050a18050a0f061206050a0330020d030b0d05060106050906041211010801060e010905010815210105060604141909 66
    0x6014050010580d40c0100c01d2402880c41249440e101684100c01c0031100342e4005d0003810040f03050780c6180901005c055820b007031194058070468407804001c07084902c012200300306600f21400859401c40359822904c040c0240305c08108180140b490321885081e408540d041c541404079485950364001c168142d003243c105030038441c2c2d040001d014240e44407004910011809105110861a0030b021500c00405400060016001000b6105e0701502c03449141c03000001d50010041040701642c0029104c2054042d1100060b00b412000b490783e03e07044906400d02600070010305280d03441d0040c107565a13840384c06041c0e0403200c00e00c0005081405105014441406002e05045024a413000100382c840142c000109110082d0078041ca941d910001d08001c0e03030020709140c6001e80720821150307107004501c41600c4d4041e4900502800c80000001e080f4110b500880080c09140c45410400150703008901500c1c40000d0352201a040720324101c421280030800341030341e41d10910740b102030072030650f000b003007120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 209918336 1250 209917086 209917129
    0x31201031214040905060103141e100e06040902030a0203120703180b0a11031312020a06140f070f02061803070509070c0803040501060807061d01090302012c 69
    0x410070700000d0310001d0008452480e2602c500d46030222490b00500542c0a22010590703a1000240664043e40c00003100300c42070074400c0740c1450000b20046050500b0761440a080f4044004101001440c0410800351400e400c0784100a50720501880001c181041c81642d1510880e080e440168505000f80107800c0700f00c032660b55030f405d00c82c20003a2040540342d140b401024000001086101d14000a0320904011071400062040341020700741d01c0e40c0504000403103480082000055a08052864080200e10030380e0b04401840c4e0b01e040a840d004039881044000c2c24040007407520130307810a001041e401344540e45180403903250740c01090640c1c001010349109024081c1d03020742031746400c107d11001040101d68006031840c0418000302620300e80320000b80b03580004000315080007000e40158014081c20401c850686684000061841d550010500384101e400c050a80700382d4811035202c0140c0b501030710f5044080c440b41c1001070707441c0b94040c018010a5140d844000160f40c17800a5500580e2000015 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 209919586 1250 209918336 209918339
    0x804080904060f14060a171009020a02010c021207030903020108130503030a05190501080c040914030a021e070e0f0411030d0905010f02010b0d0209090a080f041412071406040305031201 81
    0xa12900c0014514a846040c003801b014400c2c079404100914081c400c52018942600ea0209148102c0301d9504103000490011942d01442d43e030541c08041281c3c030981c201e6000c2c4111040f849407074841c8000103800a08084414009940140c40903900060b943c980000d0f100160380b541415074006550201c005a2038006005001c43e41c800210342007512000100203a526010000e56202000c40c000c070300658a804c07806082c070445a90307030000e0480801c207a070b903585200180251180e501a1541c1e5160056141c00d2070f140100003030038010f8400c0b18400fa01991540380c002c0b180d03960024000c48400d04a500e102d00c41e40c40c240422807a000b000d031201d20806080c000054040c4040c411000304580c54200c1400f040e0366175819410030070750165078003c40740e00c0d800c010a04244c4042c4002c0c00441c00021846541c0704140b0040049420102d0f02d0f01d0149241e80400002c144030142c00003c075848014184001400c4c40c214080d140b000401c9a0319050b80d85da51a810340e041100201e10929480c0300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 209920836 1250 209919586 209919599
    0x1080a060b12032a030c10200706020a090e070c0303110c01090f02100201180204020a180b030402092d062404030c0501050703090e090a0b09010e07061e0804080904060f 74
    0x30904d20600240f4051402c2050400ca410342e0b6140c1030b4000b10307840b038583d0b101000341c44000a40003c13490794012074a585e01130f0781c1402c001a42c0700c403403c60001100e620300041d22406001e070440c0941c10a58641ca02034469460403805044072400a080201d0704218840f5800424450029420b100d10f40c010b1144055004010060b110851880190390409070741d840440d2004000c01181c0d030341140c6c016111121880d0482c2c2001a0341c406040c003210b180c502040000300300c40a0762180e4421204000039a0b82c0c0d01030895a894080441c507040b09000c040980e0190710740013032603071100d00a042250305800e004180c841036013036165116822080002c05005000c080f51050015107020300f046464101c0315a8000c100844c03030b20803804c010b503080b004240365a000f440384903100e40d00160300260768201409418002c0c01441040f80e6540315000c000501d59004081c10f0a4400d082c1e1101980c402c00520700303840544000700100d030703070309820891514144e4a5102e4a400750411221914965080c4078 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 209922086 1250 209920836 209920897
    0x60301030b1806161b051f060f03080427020f18040501080303180705060f0406030b2e17070905031e03190203070507030b060406090501080a060b1203 66
    0x500702d0101d50050400c2004400207101c240b1440907003442c000d0a101d40f4021560441c610250380249180540000b6000301b020a500d112541c00d01d01808110480c0d0f105800b41c00300190344801005040140000c000743d03141140d85004107840b0403800c4000c1200e000f0000e00302d138854401200010f50100d40303440400c1c082903003d24038031419502080709504000d40780e640c0e80801048000213080d903082e07940d0b140f00240301c03032001040c02a03c0540c81c2c1b40f103120b02070411f030014000c1e03c00082c505075081c81c1c03900e40120310a114141814031524080e034400d409500001045281e0702c1880145001500c403411034400c007910480072644d40d9030869090001f018141051880c80d134959100030502c03c9203143c80031040340c0b400d03881d01060012854165030140d0a5000d42d90018002d402440300002c00c1c00703120803071540328010481d01002030340e8851040030100e903001c1c060080594004110b500006070710741d100500c43c45000b088030b00303c10041301c0f0b41e504c0d5610500c405601c7d42d00d6841d400495030f5641c0d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 209923336 1250 209922086 209922121
    0x1150807060e0312071101021005090c15031006030c03240f0b0304210e090a1a04110f070314040803090a05180621031b0601060302041a0315060301030b 67
    0x8401410021036031400010385405020b9010b480031b41c415107082016802001216581690720300180f042e440c0c0308410b1510746403280300580c01004207045500500e600b03c002c9902c900b40c165400d0300380a042941c124014610200e103607040c969125100403503021b00341c12806400b00c413407010029080c205104040b9050340790740080101101881800001000300b091065510300d0401c0e45044c00c08039860444480c01075100352070304020103c041c0241148a900581c42e10310700c408000401e500400705000c2294001107007006486420f01400c00060b8005d4000c002d400c0c0030b0301d0501080d12800c89030483e0380c2c0c0141d220056076800010b24420500748035441c2c000411003250040d20881c0791304000d00c25280000d10441c41654200c019042d07110300d215032115440c901e801225204d480d0000030400120304100c0410303503031250300000200c84d0300c20f008503406e84241c1e682c1d00da030000e8120540105a04042d15001107054802d0003540b00d52203445c081c0d0b000710302612110020b4107000c5680031344c04810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 209924586 1250 209923336 209923339
    0x9020c0c031f020d02041215060e0702070b0f0f0f07050105010b030f16140d061a07050d050a0219030f0f0905060405011409061603080901090b07030e01150807060e 72
    0x1455414008898480044010842e4409a07484000612a2009104642091302c0006403c00e40505019902c03c50800d081c00c10501040840d44500b50204921421282c05d03005900284013071019600440152840b85034481000e8282804042464402e420500d003031041ea420216141c02841003d00416004203c00004280b07581000c800342241500c3c010424145030300c09204c4101001d1051250030b029011000d4515100d0950340e4107100a0030701071181d051400c0e003d0080d503400254800c00c882d0000d03446000ac20700c0c1c541203402906e041d00040300c4407055011306035a041789101d551101781a0a4426510b00c136883c4090013001c1c041004c2c3d8408078040203100c000501260725450221003c0da01d003401e1501d910f01040113601220700c201212184c00c02004103801d00382070414140c403d175032841307500d8600d071507035511400741c5c06c841c0305440c0604080210307000320b8240f17400703544900070341401a000491140070014030440d03995032540c00701c88554082e460400c10991f00680c8240640320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 209925836 1250 209924586 209924593
    0xc0916171f06092402030d061806060215040f02030f030c0a030801060507110f0607080c0d0207080f03030411210c0109050a0f090c030605030a06060e07030b180613020409020c0c03 79
    0x204101041414281e0404e000600000c502004115000f0420b989901e0340820003030040540f2048008400b0001503042070071241030800101d40f05002151401c040c01d40c030003180e819650740d07840d09000b500c0420000e9805008101c082c0030190b200b8030003040c03a2042c040007006900301a03c0c001308502016845202048024841c210014035126420b82a101c0300b01e658230b054aa91500040c107d102d845002800d5580019003441d103000007040400320700e610380c2c0a450040341c3d50341c0c8003500c0344035403070801810740c01c00c100107000260a440d41074034500000d00a4a80584900c10031420800003255007452580100b144240540c0d000441101a007030a0b1030300c140c050320f02138040c50f02c184640505000591144403000401d80b09501c403000401c0c000b8112140355010b030030070350003c2c04180510140c00784408000f43c4003500a000320302d42003c000c0c20b029043d07065110261210100680840d07803201c0810708080f0f842c0514005400a049441e5005a03980f183d040982d1034861040c030741038003e40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 209927086 1250 209925836 209925839
    0xb070b010f05060a270303111006030803190f0203090a02091602030d0b030309040908040608010f1d0711060114031603030e060a0e0d060903030e0c0916171f0609 71
    0x1c8540040c3d544e40c180a0801820148045070040c030954048864004c054440d00c00000034190b012052640e40700703c641c15030b80c1d042140443d60080d100240005452041c0810100700b0b60f10300020140302200e403d83c0f0014682c100d000b03900703007030303910a40d42410594000300041096140a1102c1d6130000044604609a00d04082d0040d403280101d1101c0b41e0303620b0b5500088811910140101c030041c0c034004008124901c800d280c800090b40050040000050341c0c8030012455481211044040d0b074000b2038090710710340086a0304224010300130000c6040012845000180c1d035010408c0c28041c0000703007104110401d8003c00c0c107141c108021403455032006810b1003000807070703001005400c00540a5807501c0d0b0f6100c000009850b5004421601a00103055102c180180500743d4008001c680c07107642c0c144041d80060030f12940e140c0d1855041944601003c011400310f221600c4041c06034107841c01e180880c0d1001160350385040b1011a800c8000c000c002107106902034501c0c42c0711002d00804e050680c3d03181d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 209928336 1250 209927086 209927089
    0x303110105062407020d020604030623060d0602030915180d020c13111201260c0108060f0a0f0b070b060307060c03050702181618050f04180206040b070b010f05 70
    0x41d02c09aa111580c00d0f000446409640300d200002c01469000341010740d5941d80e074541b500080424903580456031140c50045507010710300c5032016004070350046c0804038898a40e120071000b544081c0c90850244600b10740e0f4a080400c12030014824000e60a21001500312808118200001604440210b4200065440c000da59a19891000c009031480014014489440b00f2405d4410305401c904c04145c0400005650f00d0822542610800060343c20360011032007c1e04a6900c1c0300401c2c1c00e90210b848480000c02d1828110000340c40c00e100248402c1c0d0b100d43d14611010b90501507000684038500005030b0301305114482200c00d0704818207030000c0108a02c3c00c18001c201d0515441c0050803c0304c0021080150b5503000d84c480b20310a0b603c04688003c1c149078446d42c10304140303040042c0204427084200e00b809030f280c400c4641181e402401411003031016a04120085c800070700c00c44c2800180c2c02081d030158603080090005030540503081c907035a2416007011501c03400140c2c00040300394254041484036 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 209929586 1250 209928336 209928379
    0x60406081602120f0406030b060c030a0806150c061509040507030f05100c08100b040609050d0f0b04120306080106030210030213090c0207060908030307020307141204030311010506 79
    0x2060444a5040503100c0801c0220704099145800703030342d204000b09141d10a210314070300601c01c42d12140c0b01002400406001e0240500405480c1f2216030014881d40700b00601039101d06900400090498124040d6251881119003001041c010140c1c0600308001c81d28201128040d007954045600da030151400b0703135030151307544610300000307118860311400c80c82000300c00c001060401c00c02c01c80a000d00030210100501000c0112605418500d40940000300e10345604102c3c0e050b14825510030551504000a100304440003440450700c4500c0d0203e94400301d8034143c1410301940c410f00c1110190800b1001c005e05071703442c68202401c90b0345403d800b00016a170728401b011400e1618100540c40d92400d60020368440c0a0303038048d0242d10300b0583c0d03c210465011600400750f80c13098031041d4406840b40022540c901080340c2c84000344c1e0040003a000032a840f4000340d0100c074992012195100b02d40c441d07880300b581023903100b1004035040500652400c0360a000350360340300700241c2d403001c150003030440145038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 209930836 1250 209929586 209929591
    0x151205060a060c051203010e04051b010e150d0501090204080d0906080f15040f0b1c1205091f02070501030c02010b0306010b031003050601080604110307060503040b18060403030b0a0506040608 84
    0x40c08010143e0100708103052288100120300b0190450b00c9603502d0220b24580c420440e8121800d0184109a6030706c036480c80103660120006941e241003a0801c1814400c0c41110f120074407134091014450b00202242c03500485010f0030b100b01001d6210740c035007043c480c500f0301e02e5107202050116401c014080f0342d610102d0284d0003642c0d0f103042101521007004e030002034a24a14030b503130013604101c501d45007510290450814050300340c030840c482c480084e00e04c07400041890b8004188503031088048a03400c1c45180540148800249844880544c80c5181c2142c283c002500c1d00260301305070b004000640e050311855500340303120300003401407041c04800651141c0050042840c040c44c007201140140590494103000f9581c4072007102d1071542c4450b482c03aa1040100c40031540d101c0900ba1004180c280070a15104031082c5031038603170964407696501015900001c200030094001c0d20002e44110004001142c0100c0c00f070344001441c10194411b1040f41c141039040b45000360001c210402c0030640c0403a5141c1d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 209932086 1250 209930836 209930849
    0x801180c03020f12060306060f03060a11090904030c05100207110d080d0c030b09090307030906050c01020d05010b0c010608031815130b04091401030f0609050a0c151205060a 76
    0xd80200041419070090189284004101002060310b4858441801c41140548400ca085442c50703a83c12042200e034030b070804003494241d00000c002c10440911500300ca0459040d014030141880e030454080b40d4501c00031181030700012007500307510007400410b200010384101071b580250b1424003203032140204a100c00e49818020100d5203080005d1000841c191900031984220500140d0301c1e000c0000c0c064020b69060070300c02c032000e401240e0b01c04030020445400c1d07030341364560301c03078051801c4030980c0c854200395448a1155000c00040d007800b0300754820640a010701030441c0f6215600f40303580f60708494941e08480041d40c03040005000245090b010040030f1001100c81c440c411501c0c124220042c000d14070340000e4020140360209000d85200040c00030783c1c419000410044584200700c000114081c8009800c111000c030807440030501e1500940b00303880c080c1d07045424406072551012408043d80c0d200340d042052419500c1d0080d584014070128411080c041400103052000c0059124070042c03141c0c5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 209933336 1250 209932086 209932091
    0x120801090b0d0b061522090204141e04020a08010e0a0b03120a050f040f0501140901080c0f0c100c02010e0c0901054005060603040c03080313061d0706080118 69
    0xc2e01c641e6588040a0141303000c01c07031180c80b0004501032401900206d900703a00c0341800d01b04040358411492081e04d040b0781a15031108402c0d00e0b92002e01c140060071071040900c1d444c0d2100c0301c140c0c0751268001400c030500395680b540002c0d898010340c0444900d026045074a49810140142c80030364001601e000744840540c0700f076a6503208858103980c18442c40c8100e020346000440c00190301898240340c0000c8901c2a254287c00714807400c0584210f101e0107a40c1070100e48040d0108520850b0740b009040b10076070002003240380444d020105843e1003003069210204d10745403c000c04400b6420300440c500e081d606002005840d410388001354654034140280342c00388a00400e10110709202c50070080c131480c007200005c0510800c20a110034100d0540e0b811441260030900810224145030b000c8a100700d401680340480f040c11950398210702c0e80301904464110340417000c00c0c00403502e80e00c5005041030138203406694802c9010100b03418481e4660185007807000001c010008142044c03111081000c840400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 209934586 1250 209933336 209933341
    0x1803050a0203070b01081c02030a090b090a17010f06050301020705070506090105070b1302030610060c0213060b0a0c06050609220302070b0a230c0c060702031009120801090b0d0b 78
    0x700c2c99400f501401a200700344003000001c440c40301052000f140103200c0c25000d4000001c200036a41e138425904801c0000b200c0714001c000d00880c490240007039041c003c0003484c8441c1d481d41c07a6906000300080c01d0240d650b64800c04040320f178082c4103c0000b00b9059000b5410b1051644545427160300910415018070000583c0b0312040e0b2180c0c0c102d41000c0e600050401d154248501c0098103071900c0c5504901130320824000ca20450004014035044a406648400755980140c0c01e0002d044500d83c031500c0c00c0d80d11188045a123040e05406880019070641c1ca2140340c5029041807000c0c0d81c4064112030142c44180c06000300010425007800e0320356031605201d84104580d00d4100d1030000c83e0f901440040c44080303904008554007220f0044141c148003640e01580b6454031102d101e503c41d00203c41d800764418240080b0305d050400180c2241400141981e0460394040c400206a8840d108112600d0003614070142e042c6130405101ca002d0082888108014100c05011469610131450007402c0c0d09540d500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 209935836 1250 209934586 209934607
    0x4051015080304090b060421150212010b07030309120f02070e090a020d0507150f0f0f02100e030c01060f0e010b030f010308160f0b0702121303080a0c06111309180305 73
    0xc0324001e00c04060201103d00c648855800e41c01400c810031105009c040c0140801c0ca105c500031b0340d0003070320141580c8542d646854107503070f4141c0c0b12030022408d240c3c843c141980420034650680d10050700700e442e04d0301400d645400080c100360660f008085188910402c2c4100181c00040b030810180d03042d22060045ca44a082542c60281d469101625101d241c01d001c00a0b168403a103c0a102d000b80c0d102c1a40e0000005415a501103581c280d000060748072402c016070403001c41d0866414100c00030152844d00070309902a0b403e40340190444512404050f00c10040e0008100038940102a00c010035400c0d810201c404400c00c0d04d0601c00a0500140030070114814120929100140d9070300204070504c9008030f15025049000880b181405406a001120032002240f004c50b000f000b098a020310050341160303039000e46904503503204010868181d144034001440e034442c00c3d000000780c149881d200c0281c0c417403200707010b6015040f001c880d80c01c04400e0b003501882ca0031204402030381402c0c11034484881030f0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 209937086 1250 209935836 209935849
    0x110306061b01110d0f0c021c110114041703010f060c080c0307031101060504060303080c0c340b07030f0c020127090e0105060a06030903021504051015080304090b 71
    0x2091844551a000444030144050f00c000c007003131400e0b0f580c1408202030b03500300c4000700c43c141c1e002071015800500e580045101144101841001c481c10041044003901c03510508440b4004204490005240248814001500700400c400da181401d89451503041a40080401c0343c640b09400c02d1003c015103240821070724070141c5042114000481c5e894010341d0400410100340506a6a0b19501e4460b000c20681024061f03801600e806454075103c5031603c0000d05025070110052040c03c2c001c2c5113060381c2c032000c540f003180955201400d08910350002d801c650100c0b080b050344504500d650400100002070b0300489846003808030b904280169520b01e0005990030700741c80841c044100500c80e40203050411490002040c2c0d6003a0004100710781000d64401d08940080e1452a44405000b808106581c4039030040c040e00c91003881503810314981400010f800c05c2068034205e5094011000010316500e15104070fa0f01c0100000860390307000d00e403844094991081d809807103a02070b10303881100c0c2152a1034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 209938336 1250 209937086 209937127
    0x619240207211b060207060806060d0606020a05010b0901030308060909010b06030702030403060b06070803041b0306090c05010e011404180b0d05030c0d030e030406030e0114151311030606 82
    0xa4200c04941214501840080b2102002102d4182250b40d6080741c011801a001d400d5680d03980040106a040c01c2c002d81d1180c0005044950084c010001c4400b40032840c00380e000280300d107800605070b8281610b4075a00751424070340c945001307000040041001c40d0b8040c1500c0c2e08218180c40c40c042d40e460300303d4500d003d801e00f44480c0781c10080000910504680c004010001c4a02501c0d082122190520400209201e01c0c000646444010300200e00410500700b0b042e44c418002003200d1294560700c0d611707507040d901d003114156103a8100d0030b404c01032035800c240e51050794442403900481d8600202070114003801180a0030401500035018505418600d50220301d1214009126804411552601d0341d50b0768001c84903003801e8040c486240c903010303010780500e11040070024050360030a81000310440003031a070000c130040c9035921290608482c216040e801401419200b030101280340340c1c58240704940203941d406600440c0303071081d02005148001d040c0da8204074121003032907070f449401da85001400c229 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 209939586 1250 209938336 209938349
    0x30322021206090c131122150306050a05030607120b030c030a050106090b060a02151003021801140105070c12240203010905060a080c01080a1803080619240207 70
    0x204010b00c02c3d048400074403030031006411242821482107100e110b4003600c0c1d501c40c1c105480c9005001c0e00702e59115510150818013078101d0240c110356620991102c034513414180110105c0e655038014085400d1100700d40014240c290020191800c28400040101c0c82c841e10942000c0e68a094002e196034050042130b40e01d14000b012111150f0090400c0b42c028074003441504140c500e410210358050404c0f0040c1e400e1001150050230440c58040c07030908041c0b41c000e12209040500329804001641c401c04034040350340725480b0f000c03000d40c140b1040078041107401001505011051120100040848020100703032001c030008680710703a507075107050840d603060452004a001600042c101c41220381d503020b1412900c8201062140380ca40100f1311212100500a8101c185c110210020940d400f583c5a1b54101d01007000c0020080700645058400003240107044000420380c4042c4000340c0340c0602c2c1090400c030b0300c100d00c040841c541901091000c290712a007c0c0041c40c009800c0100300e00034040c0300d00034100b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 209940836 1250 209939586 209939593
    0xa051f0804170a0503180c060f0c120d090506150a05060d11030712060b07122102160209010b0309030712033c1a010e0301060f09020307110303220212 66
    0x100f000040c010b40c00440b00ca10103078000380180b030742c02200050030a05106003c0c00c241d2410103848100c1c05030764840124034410344a000208400c9203036a100814041400240004107681d407031078040c1c20040050190400001032064654040d0348000301c403030464004070b03001d03a44c841c141e08455000e40048c0603841940500841004034564000f4484c118940d440201000000d80b1b55948400602400c003010785491900246c443ca01400f070207400394460019045501540300781070a44040c0e07801505440400458080d11800f18144041d49a015060803c005420340c0740c107000c0355071790b4000d0001c00340034509000c3c100303404140a540202d8040070011006030020705428a03076000600c0c81e030b8490710a10740860000503403c1c0c4d948564040c085800500c1c150100c0c51000444106211028840c1d16550750704000484664810004000704a030450141c1c40389414203010b805001d0381c5000c1c40d6990070400400829081c0e040070b4418403c0320803904003c0d46400d00201e103043c00f0203407140f1076611 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 209942086 1250 209940836 209940847
    0x10080c060c0f01151e030f02042a03060f05060301080d050a050409060b0318010c02060402010e1809010608010b01050c1f021902150711060408160c090b0a051f080417 73
    0x148184a4143d803021542ca0154110070380030903802898901c4041c0044404811f800e00510706608180c0c070040000c2040747d801d07200100201289d10024040b40b0109540c1c0000300b101810110b400380090070101c44090840d07142642c910788468800740b17400204540001c04040e2207006030241c0e401f918644104000080e21080703003054641c01520800c00110000032500518141405940d0b440c0c580e96010f1700c41c039203403a8010f650581000ba0703825844124400c104650800500080f0711408503c0300100d174191902d0140303405c48a160b00d280d410000c08211400070b00c0303400103e00d00c080d2109101d0030b0110603002a802c0080c080c0f0b043c0b14881c441c1c00c90400d0303c0154000f5507003464817515040b0070081e4680c4042640c04044044589806400450014010400100241c0b0750f42c0380c213209007148844255242560070130b25030000d1120a95620302410340307041000c0d80c03802410003a2001141503c0710b00403001e426851020704020002d010700080c00300008442d151112012070f100550304d13207 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 209943336 1250 209942086 209942111
    0xa06090503040b0d0207111c170c0d020105040b0f0105150a020715020a0302070506030603120304020402070507081e011112130c06030b0f0603070e01080403020127020910080c060c0f01 81
    0xa60042d1019207105040030b08221142c50083c640d004a14103001034210f01780e4155030707120040c009c5041c0c4000b050070140400b0788011408e20098005002030b900005d101d240500d89010b0321000502041c1d424840700005204a4840c4e402c81c0300300154800c052a19111065003c03883c0c05401d410401c1d5042007a120901401c0e0005552410244250250b42c0d6240d118024001140000c42e803181c4d03da40002900261050000c00440e00a80050009842c20160340c87c3c0c00e18000c0c81c2da110032a03a0f80100016400300c1641ca550704d2108030410002d01010b00001d07140540341c0074040402c200440c28002242241d2415803010740041d51080c0300da46c2d0716503602c0e0007a0041c40100f400501480310412100000d00d08503040b280300340c001c0e03120b103092140c08800445035910300520031001c0d07658401000d0140624510400040302d41403203880c000e20705034818403d0565000e0084074a10104680074803201002080714940f41c81c00703444498032101c980c1401c40c904000070403801c17141c1d40381c0420710811 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 209944586 1250 209943336 209943341
    0x90b4006050a0902060a0c020307090626060c070b1503060403050a030608120706050711120306120a030f08090a0c0b1305010206040312020904090204020c0610060c03020a06090503040b0d 82
    0x2058000c150402256a07a41c03640401c0d200041d50080d8401410000c4007061401480300711001d030b00113011258000d8a40b060380049414981040616034000702203004404001030401031404240f8000d41420b003090091050729001d110300c001c150720380d1400010704440520804c01e0010b80028100c2c3e010742031134200070f4041c0d406807000400103030400501060248002444104070303409440200e25003c401e49810009000c05490441000760740401000404070802c0f0000c40c03040411003403940c4c1e081540030031800301d0702000c0e40025500140200c02c04a50000000174511855051001d001d80e0b4000c202030030f0590045000741910384071070010803103030300c04000381c4a0703910b521320968100350b00e94005a07600c8008450080029182e03003801d5130021a1074002d4004031202410120b4030a0b4943d0018040e60080c810510043d03000800300514881c07914807a00081107a0705240803400c071152002034a070030312884080c001a880b190031350100b000c10022680144000c580681d1901d8000454a01 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 209945836 1250 209944586 209944711
    0x7021309060f0506061303061d1203151503070f020f150f01050a081905070e09150a0b03070504050619030308191404060e0115120510090b 61
    0x40043c40d0200140c8541071140c02c0303d159146c3c09811008161070340c0d503110094036081250035a100c0742c0c06ca520703d040c4c90402420301c24110220090340c4a290110910740c0560003441501e1150340340040d2407102e220600200ca8002c002841c190602c9255003405900c0e04034200625101c622075903c200e0303403400e00c2c1800380d0302491000550800c0c0366030b40c0e01005112740352800b8102c50f58105003d1401812400d540c83c051251080e01611860b03070351900d990302d6a01045072004e03580e400c10b8103c0d10359429031148280d803080084400700b081003540b9002c40d6450300540503030350103160b6070070100d20117645040c150a0700f859140541e40849440385802461241c0030f0340e44c451300064005500075141e40d14001e800c07903c0ca07650100340c025a280d40756540580020828000e055503035032110401d8000f20705d00300005d01080e01c0b060101b00201c0c9402403a10300c0f8401d03030700c00d030a1500041e9000500300d1a41960445d200303480211481007400c4030404a06400c41104454030304c00d030341e0340c0d100e480840340c0fa04 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 209947086 1250 209945836 209945861
    0x20106051008133e031c0e03060c18120d12060302041a0306071e0e01030f0c0302040807050102060108460b090f1203071209110f0a0f0302060702130906 67
    0x1080403486030500030044c81546055850b03041811004031200304131200000490790f07450008881c040c6800400c0c1000001d03a00b19407034500008017659040c1c4a1445001c009005540c40031420322800380c025285c9544903540c90402c0b0b01450105070485081e00194040e43c0c0040080141500380002c12080000246146000740158400100510f0090000504078030901142300d46001e4007107011a000f10103a181107061543c0c0303a840000f21030191180c821706490603180143d80300d041c850785915100050740241d046600900041c08a00004940c1111403002007000340c001c0307100c01100c4168240c00c80b0111611040180e04d20a41c03404440d544149640601c0c000b40c1c035a00c07115032079074845031080a40111580006000241002090002d551201c414a0640c04040c480101031090700c000d6401980d00e2007404c0700c005caa916003198012441c94007141d0722280c332031402c450000710658074031000c4c2c030680004c5105025503c49406c203103c04888a402004100c40c64070b008130040c0101c1c078090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 209948336 1250 209947086 209947163
    0x100f1215030515040818120609010e1608120904140c04061421040204150b0306030d02030a080a0b0103021c1d0c0303160c03020616050105060102010605100813 70
    0x1100c000044203c40c011500050220f1810b480c80044800f080322810f01260491200d260f203035034004007480080d00030700c031600021401c4044400c016281400e0510107400301c0000e950201b24580001030f000a2091441c40119110b80e034240014000382003003020081c40780c1050f41040307124618040108203503000360b10b6010604842c3d10302404280a4818404d814503407009030b000b0003d031608011684544014404070324410080c00c121140c284543c03088c0100c04010060041d5860b0901a1070000192403008600b4203c000388000c040d803901400500000e03035100044042d59110f03070100e502c64030307034500f00355a0700d0b001480301c5005143d100e441c824008607808442c1c020a0300820b4514031100000c8c029410b040c000944411a05051314089800f442004000001070700c401000e40780e00c41c002860001181e1860805500350f600081030241107900d8400140030968602032405030400180c54140034075034075460007010b0410051030180003801c0e4181000d11490b40c0b107010683c0704800d803058 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 209949586 1250 209948336 209948353
    0xc03070c171605010e0f03010218031507080c07051617010b030705150c010e07030506091608100c0210090c05030f0303010e130c210201030b0d02100f12150305 70
    0x107140c55102680994980c12003412041202c0d42c812010b0124014000300110140881e03100041c1c00c991114400c4042d000001d040c5d10041d06d003d000c0d44102581c038840b000a203192440d8010a00000181080c140c2e240c0841c9801c20320500b00a10445080d0700d90046611540300c00e02181c00c5d020551503c1c03015800c28a940c03d181c03e01240460803110b001c5c017a0f92408400c4880c4440a80024162810540d40e500c1400410b00041000c0401540107002030001d078108034007607a0802000c0c0300d415480c0403003c04204406803000551b0b0f0740f90021014005002c50b40d541e4202e01780381d12180d1581180b81029a40301c241f00c040030301c1800f242c42c102c040310090448400100c3c0c590009114134640c0360f0b51000020030143c0080440c4011038414091504401d0700e881c580e441204558501034400503241c0ca05008558140c4079003200000102d44078a410304090340001c07040c00c146c01c0580300f0420070802400403c1d01a00c004031143c150304070180114002c081100c00000c42520040e0341c14031402c3e95 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 209950836 1250 209949586 209949629
    0x6100f0504090b0712020906160201081303020d030b06090907020f0706030c020c0f0303040302060a17060607050c0f040e0d2c06041518031202070605030c0406030506060c03070c 78
    0x65903440e50b40701440f540f442d600c001056a5868035602440c1130140c00b048490420782d107403001000c0f8540c1011955010004600004085840017804071901042d404070744008039800040541d201025490080341014030319000c034070746014280700b40f9000308021050220f071980100c0e1440608020408444400f42d5800040b030513104801070b8140540c014481c0072078182014081145800406000c42e841c10f81d4075400300b00d440d4021102140000c071008900c0300700b201070006043d0040300480301d1500303114a984506465601c050480741c42050701c00030705065500c1350340002d004c10401c003050b54215440c80034040c02c060b4119250f04500301c0c000c281c690608082141d02d05840002400403814181040d1912650401940062062090001c1040d124412060701d0724003441c41521400706051609102a1070402130b03030000c0007445028000c00c8600081e00041c0d908594080c030b40400c840c4c6603180800c1262094005800e41800b00041040510401c4d0000604039a9100292030f08000f2009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 209952086 1250 209950836 209950841
    0x3090201020307111309030f1e0c080924190216050613030b150a050d080304080a110307080a120515190902071b0f060819020904060e220b130503070506100f0504 71
    0x206440415078582b4a000895440c4000d4140c108010707021185642e24544840107001c0c25000c501d115240c002544c00c101072240d0041031440a0b203000130401034229450881d1100780d94002d503401844003240c0c4034100e200340b60003840219008040b400c0d00d8140791040203107140302c040308240101d2994800058604004110301200c45e0002540c80c255119950382410036440804880b04000ca003109103c0c07240d0042c001054600d04c155007407555104170000140c001c2d07124000c800d0701949844100f00613650080355191420600f01c944210229004070503041c00d580310340004154510100f01d4408000030a001d05190328904540303a01195514940441100064090140003c0001d00420004116004d6891907080824009400c0554031008a011214690300c81141916400c06100b4201400c5400300054440050045015074854030b546910290140458104061460303000040c4031040c82074030b1213240d0000a503031032414074000410554419002c0c10b92500c1c04018001002e01d06031 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 209953336 1250 209952086 209952137
    0x160b0906031f030615090c030203091e030d02070b06150301060f1b0503032802090d0b0709120503040306060b0a0e0f030f070306050901050703090201020307111309030f 74
    0x50955265980c0c2c50301c00200394007108000e000702c5107207540100003c3e440b0301410180100e040954110549011054410340d055243c41005061040062201e03104001c5885402c0303030000c0301880101c0d200c5010756403075441101241d81000788042082c0b003c200e261802d041c040c1004070748058164130b000b065140f4521080c41804040b41c65810251669030241d009241d980e1034040f0105480d001a80b80c03241160b104035410600d404009a110400d503400b00c40210144040c0102181030600c0700020034601c0500700005091707045400c00040316180b1079a10800a44003485d00c094600410b450156a2900030b40002c552190905102044035017200c000d85080f043d90740c1d1804003181c41c90080c070082c1700c0107440c2c254041c00303001e0300700424038010000440158402c030000585032822104240c215900545140e04040c28200b904016030790000a80e800360390405100c1e2184610b4a0020f0b40206900c000c0c12502400c0070070100c00e0580000c00704118030201d403612000a1000005079a484041 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 209954586 1250 209953336 209953339
    0x405040519031817070f1d04050a0605090c01030f050714030406060f0803040f050103020304020105040b1308031b0c1005030f0a02070f120e090103150207030c1b0f0e07020303010b03130f0302160b09 87
    0x103d2620960420205200c8d4010780504c040d204a03180030f07114082555002c8800708182c0e800503a440e003445d6030620903504900f080c40e0b001c11007420402c900410410708a4550007820728040041424001140d000034000c0403e200a01c1003107598205007030300c07600310740308292403007800c0c032000036843d40a4003c59100d5a8165544c925207402e0042000481d0440103030300c6886000c107030000c0340b004420401010a9071008910304a202c80521802d8a0810041440384c0075146070410001d4154000782503030381040300001c0142c0686c3d540030008000307000707203100074010008681c01d5409102d104401c8100f42e00740e43d500c02c2c248160000510407401000c3c070004161141c207424510030401680d0140c000c0510900c1c08548007a2540c0702c4c001081c1134003c107440041240d48040220109100c0c10368010420081c10f0702103441c000102a407280014403881d0480e0600000155100c409069880c2c810360340101406500c840f5420003d650341d1711862814481500c1c00d0000c988910300605480d0700c243d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 209955836 1250 209954586 209954609
    0x40501050306010507060207020a090b0310110910020f0d050a08010e1501080a02090406031109010e040b0103022103030f070315080703020d0609050d05180405040519031817070f 78
    0x2d800004545a0340900020342e651b590074010034005130b80321601c140040510041c0421001d184404050030000441c19044101c1e103040c0c5a9280000d038501510110141182c10a4410101c0c6c88160308216002805501c1e42c01840c0c084241260000c015042d00c40340ba5503502002d03078031210101700355001614610803c104100f000186903110716620381c0d00c0900390101509054490010070700f0b54100d600101c5034080c1940d000c0080e404c01c41403181c01001507203551520f07400c060729800b150402c1800060f006003074804183c041410800c0102d298441d1543c200c076a2440c0c0007032201d1001105071080f800107410104402c100321024903429059a603880054040c2d140307940d00f045a6007001c4403080306c0194840412001161040c400c40410312442d894840c1c0d80da6125000e900380f170803d410072038441c41c505000e00c40450000034070018001882107005040784074505042d00d0b41210010700c44078075074060002245c1c454014441e0b01c0082420800c8402054440070021f039003416034001c14001c2807 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 209957086 1250 209955836 209955841
    0x50f010507060e1c120b04140a0903020106030206120403090e07141b01182916020f060a060509060607120503041506090504290703090804080a0b060112020405010503 73
    0xc2d0786900c1110040d00081c2107812001080050907003080c2204010000714a92812181c0c54007520701071184071190440b01080f19824414010b014880027401d020089a81c035a50181010b000f540044080c680040590b9214800d80340740c4100c2400440c1c0440c00940c0c4142c00049220406c80e9241c0299031a854120b41981c0c7c0c00c04e450b070550003280e015604036040c500b20422814003841012103106c600e004454224810b4281071144a5184070742001c01c15001c141000100303d0814490b8010103c880b07000d00082c00000101e290100b8200c1007c0d5134003c1c1d400348420340350b180d480101120b0701a42c0c8d800d2159a0035042000c50701802401911300340d071442100c01c0c158442d80c0150b9210307100f510126a072480303c642c2e0100312100c6030032803100e15a48406100c180204c00c01d030024890380201c101036446911800403c0700301000303800c40d8103050b204c1412a08005400040e0380150a80c0b00886030031a10905105250440c160740e140e0104030f007a003e110558090380216410f807503044c4c65491464 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 209958336 1250 209957086 209957093
    0x1030b150a03050c0d031701030803090d021c050f070209090c03010b0f030c040902030a0c0906090b030a021005160b0901061a03011409040212010f0e0c0f0a1a040b0a0c0309050f010507 81
    0x10303011708004500304180f18000f9442c4407245072509000c0e40c020010b01d13859141c004596031405010a40f44800d43d88182c0c1000f402c840000c80d40e07100c1e055a8035100380c03a401d1071138080c0707200d0040c1c0364002d5002d0700324400c00041d845e001540d06054403088000b4042140c91005200d9050b0748050003a030590400305504d000c0341003580041110510185c2100c00d0448180c440c08400e40d080d8020300750702a101c80c0708009026541c00b486011020480150034801160340c0001d9004040c00c0c200e40c180a80441c40040c8420640b00711803929801801e00c80281c035000c20158000d00c81401900354a02080700245803000c004016281a10400200381c40c0f42c0d2550320404c001000c00170400c980c1300152003030031040c83c0000e0042d0280c03510307901404107410702880d40050a000790b20103542e0099290391100441c0e5618202200b04580c082070741590f0300c801071007204940748646d400001d085040010a07405e00c80d070194940c000503000c3d54a0014184d115020400003500c42500503000403014003028010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 209959586 1250 209958336 209958349
    0x40302040209011106040501050f060a12140c041d0105150d0b0a0f020c010b0a06030e070b07060b060703170a09080d18050106060504050102060f0903031315020301030b150a03050c 79
    0x1840d4141030004c078880412400d10700e40001114102c070380c1d035100d0302800403496003a039200c0d40100c411520f07205074906100030f49170103441d40c03040942620032505034180201801d1126003400c40014000380002c0801b030103843c29150b0b0300c0c0603c40007913103040d000542c4c500074003006640d10080101807011028460b160f0540d4003402070b180c2d4080381c2d92030007084846510b500c004c104400e1144000700d84400c80f082000041d6031103070302000038141030039460317a0343c0c10000c02d05805440842c0150307a15403e8070704000f0028901d458640b43c203c40000784880505030041b04424500c03a105130500b42940d501050f00065a107244070003070113200284020740c1c04c030103160002186841d080050f13100d1420140c540e54203455180d1300140118200080a2059580c1131044950210034001e1515040c2407087c200f69a070b110080c1140380d080c0c1e44021000030803110401c2804031503204074042d0b48a50312030521041e8004107503503080000d03200081c108894107001d01d403101160741007409840031000304130900c00d2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 209960836 1250 209959586 209959597
    0x1140907030b1309050d0e0310090305070807052a0f0607030e0d06051b03091b13050a2306031203060d02030102041401030509070b03071404090e0a0302010c140403020402 75
    0x625490b52221201c036107807042c1c1220300d01c91200002c12020b030789007461803e00c0c0e00d549040f41080072500e10080c00303072000210040f03644840303440020003144505003200d00d4051008001c0007500000384030307c1800700004090f401004c0e004e00c03010b4040000075080c040135601500382600034034840c1c0303214007900d403203c050000a03011741420115108084009111420380c0d03a02141c603181d4500510003034000c0c0d91425104600841789403460b600b84221015951030307804d000c4410252548403846040e4407001580110b800c00d02009122504141c2c403840042c0c20748240c1c0300d06c04c50021400ca000c42400780801801000050041c00c2151441031505900707510042815800c021039500c20001070302d00344010401064244100d6940341031000005041d0358015107510100c0d48181010720855403008212078100003641070003034600010380310200b81170086500058440d03181c001942c10782d070b101054100c20203100b40d000f00481549210103a407080d081c003e0b2005001014001840103003420b900411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 209962086 1250 209960836 209960851
    0x6090807060806120d020f0c04060b070b060105120901050405190b06040903030b1002060a0f1e0b0a0512030d0f0216020d1a07050d0605010c08032202060d150e011409 73
    0xa000134042c07015860469200340450042e8010f00300c00340149001d02010520100803034007400181e1400c1c0ca841120301802d40007030040382c5040b02248050b8051412100103590107a0030840700d1038001d003481e000303180403101502c003409403114440358109400c50b0011025405004c02e250b6841d04410700c4020300e21100110141039454031089180d9032442d0008491106950041c036103441c01c40e055005132014502140f42c034070304100d000201c4880981049002c0814020001101c245120000b0004c1006500c40b07604101030a014550003034001c4002c00918031174040c1444080045001d00b0101d00c54144072200c0c8281c0d030700841005140594920300854051503c0e14118201c0e40d6417140840300c103994001c00320301b00203a0326044140030b00802d001000e0900704501b0504440c2c550341c4252000401c0840070300d03284942c00c3d041c1c2c081d07482e090001540185c11142c9484140c42c05400034200c0400d8007100000f503000010300c1d560384c0d41d0020b069503039038043c01e003140f200241407040101c030182c00034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 209963336 1250 209962086 209962099
    0x506010821041e03020a08100b060a020a02011419030614010c050706050d110301080307030207060302090609010e0607140d09080f0a062d02130918021c0203100608060106090807060806 81
    0x151b038070f0021354400341c0b007080c0150030a41c038a08001011039060382c0400d03006640500c611010290049a454003076902030030000350042d0391880240a0748901e5265081032800d603480801c0031030341980082c054510801003e4001e04080c0c0c015101401000001042a804040c0c240314880c891009065968403a40000c41c0c0361400c240c1c40c071040c1c2c000346c010005903480820700d4002e0680c1004030000810b214101185450004400300300f45108400707180341400040904560f980d11510200d420b11a044a4000c20031200ba07221941c640c0c020350038084c00280000340c0481d003940c000c1500340c0840d910f803000303086c20106640e132100502625101c1c160740f030301d00c000b0280d1004042000611000c032036000040c0d80390881d084c1c01c030142000d030704072982881c0b604500e40c0b03881c024584403660254040b00c4030274a0140c1c4d0030100000700c0f044180290140070b02c4205421120342c54120201f80c5586606a03492070780ca8180c03c076071079069032003140b07026403290504201c2180201403480d008031020307042 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 209964586 1250 209963336 209963339
    0x70b0103031d46120201200106050a05060f030f04030315180c2f0102090d20012a03021c05030406050106020c0a0902090316030506010821041e 63
    0x10310101c18009800312200c00310b1149044440060101d22000c84908001c2500341181040c071243d8002680035503000305a002401d101903a00402694500c5a00b403006c542c114008182d0302030282283e48102e03401009281004151450008203035151020310f00700b81400c541d04c580c2c1380b295800d0040d0094080c16a180700041d005040039030001c016240c500c0c00103a11004a002c00b404503200c03d40d042e804c02041e02c0599071059046005001c2030310f00b2820410004000c079940f98028485e0100441e8441410480e500800c074030019855441d0944200074403266000000554480000c00e00031801101d82c2041621010084640102021300a1045845210001d41541d0759603821444020100300040100410440b003401900c1c0074207094406000c0b00d41d061400705512001038014485440d8003c07690103540e40f010070080c01520142d040300b9000580d00c1c2420781d106e0381c00380030b004014000d11403050150100c203540d6004142e2600405490245002980c0050320700c0c0d51840140320b161043e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 209965836 1250 209964586 209964589
    0x2915030c09090f180a0b01030212070906120303060902090307030f0c0e0f06041805030d0e030c0a080910021f0504022d040b0f091609080102130e0705070b0103031d 72
    0x45043c440c00b01e43c070542041d030030040102100c030024400203500c240d101d85060380c00a04035018036411668141c64010400010140c05030800002d50007021a46182283c0020008054039102041c2402600c0030050f45464017440001c2e442503011458040c1e02480003000054000340c20b044c00c02c2c1c015207414414030340b1018810700441c425104486019062028813410307160521411001c107038864882c9101c58055030380c0d0b03500c0303019101e07010b89444d9890900361803220703043c000c4030011103000302074481c00211071512000d07030f4001c225418010000d0110010030907000107040c00110b00d1000c1c0d03101001c5107441d840c2e4007401c03000308100e0f04407405903a014140d091100e12a000840d07000707800003052145809100c12150f5070b449161080419440218450300c903c0000c5400440d01500301005a41c188415503010206500191807903100182800350a0381044001c1d054400203424149103840754542210140105200506840680c9004000082c001c80070214120380d890300001e40c0130704150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 209967086 1250 209965836 209965849
    0x30d050406021b01090f03050a0203072114040b04150c05010f060503010c0903030e09040606030b010e070206010611300c03071a0c0403110f10032915030c09 69
    0xc0341255881d80102e03d14011100348003109864021040080103c03074080c0d00c0c0c0c14005403980401406000002070004001407081c0115016150460408840013820485c80c030144420b080c0014005802c8050754180c03a503101044030304803680c1c081c100341001d0400b00d41c54032443c075060000080c808801025000070b8820f0007840940c0311500c0d4001030661825080c1030a680d814071403003040240381c0c54140000ba0304008401c0c0c070400203a0341e03c04680c1d40c9242c450002e084a401c0506914500d00000503050031240301c59224071419800c1d0303109640d90b910150341031010700d0385000c240d8009000a1040020300442001800345407880c07802c5500341400000c0c411f901c03600780049140c20024075401444054403074000e114100c0c83c0c5180451034840101e607418010f900000746034604070200341c1f0007503440c0034008000450040407080300e0700350200058001c1185d0b00e407581020090745495020742c1891081c2e640f60000140c40c110701000701040c1000c0c10303807006140214040c4140424512904c0700c5 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 209968336 1250 209967086 209967091
    0x5031b06041d0709080c010f081005060c061801060e04020d0c05060c01141501080c030403030209090f1509240604081b01080c13050603060f030a06060f2411030d05 72
    0x30b00690250502900050001a0a8000403d03540c03000041040c241d0380502210100940d51501d4201070b215802c2400402c0841e9100c1540810049088465501c0106109010b400c400b82c6035001d128010400c40e0a950316441503c1c8041c88100005001d41030800c40704042c0c03071040c82e0b05080c003501c41000654a07003081c91400b1007607545540003101940035030707555034100c0e2200400c0b5240c14103e20008100b15001811402d0500740440030400f01400b0f50180e4411b80001002d0013410b142000903688910383c110b500e21041c00b140c0d1499502030030303c01c009170b001c4c1c00307040c403084040e1541100b411001600c0800e11900322100300000125840240802c00e40804012120044104030100060540c9000b62002c10a104104001005e01100040c10822280152012a143d60301d07000000e01c401c0003100b1454050144c5203a4100f0802182e01c4041901c0c1d885100030724040d249c0c1e6810083c000c0d0b00d01401c800b0a424000034084e14007403c4004200c031103810407a45400584c039500340030b8580a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 209969586 1250 209968336 209968379
    0x60408090310060b0415050f0d020a02330a0b0f100c0c170f0f0a020904060204031b06030c030902010e041a18090d1403070e0111030f030402090c030105031b0604 71
    0x10901b40003081e0040703034481d01c01034a403030501c0c1856960390400703400740b08464080031016800192245403500901c0440030307190045d21028010010204681502d0000e80d00200600f10355070300240711f5200a1090524410010b00302500036100760040c0300110710a030f180801031002c5001008002480129007034043d00d00300042d45000c4400c1c1500038138010103550046110703086200d40e8401000d00184c818206901218403210603115803c04800901c199000508030034449940c003049840040c500a003180d950f50f500f00903845881070128100c6d00350030070081c0000d4103140d00341407520b0250081030440140441a601207079034100000c0000c01c0030b101c0081444040800c00c19081c070140600ca440700c825040106030b8241c0303540003506c036100003404002440000405118264410141556400058003c0b203617030700c0104030301c0359540d0000c5034100c0c89610417600007400d40040b40d0580e4103c80e0007500405407034401d44c3e4410347c805408071070325421640600001580484003030800003813254 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 209970836 1250 209969586 209969609
    0x1526071701090203190f060c180b07050f010b18040203100e060403020607080f270106090e120405060f1c06030c0e0a0608100c020a14030a110d0206040809031006 71
    0x202032042c90f08002c0c48501c05c0d00d000d0302c000c643e0004102c0010b000e02c80c55510070000621105c0d003000540d000d82408100d600340950102000c12128001d800400880b400b41080f03d001c0424032414030f0030307184c0c40c113103964002a184c1c004408549100c161650010720003001d0350440800b88400408403401002040c12540c0201c082c0003c4c15014040c40d0f0704081c41d854880002e144c40003410941400142101e2074403180d600401030124800808503500310300c40700082c00290b85d5641c00c0720240c103000c106070846000e400155890380b05010308484c00c441000d4415070400d500d0050200c074517040074025450074018402c003408144650710a0034061445101d4003030460b414590310407540c04004000110a9180c81020b00c500c1c05d000030010251203207050302082819001d2412400e15002c1d0900906649162028070365221010000c3c0200102c0c0e030356180d003076190500e0550742d00c1c8940e011850158204402090210700380400401c160070b800703800c07181403581c1c1814170350403110607a12031719283c41d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 209972086 1250 209970836 209970851
    0x30708030f010b040303020c010509220c0f1805010c0c170a030e1903110a03020a080102041703041a18030a050a0203010c050c1f090b01090506041526071701 69
    0xa4448401d903024200ea4414607052074110b5502a50b030302c480009040c103010f8049040885540d039404c06030b84204a540b40c03201c80c40b90341c008030340107030400060703d034003081c0304039020042c56120b45180081c0021600392044014034250066500c0106038005036801108400302040c00c41c105148034060404250041422003201d05000f041c154500107024410711528040303140038040d0000c6407081e0398001031507a0041b80640000b4150001652000b03403c6010540300049000041d40075004035420700d50b0207200c0c4400016800d4a91240c2d01032410b4014070545600382000c81740c0094841160045881040c840c0c0b180002498a1b03002d0f10b0071141d581c0300b0307014041142800c0c003c0f10450410340c20480d080444400640d83c60f1207101c003110303190784520f2003545850907072908031a0031140c00900d40c2c0da25585074528034024000440d40b00b402242400040f1882181e140400c80403a4000c442c050024950007040030070a002d030300308681c0b0510422401042c80c00940346031a0a030ba40d09800002c100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 209973336 1250 209972086 209972101
    0x30c07060e0d0206120903041505090a0f03081215060408032208150a0b0409120807020303041502031e0a02071106030115120e01060b0d050a0b28030503070803 70
    0x14404910701e405540312810800c01616030200f40c5000400e044080c0a0340da0700c1c414901e2540c0101e80c010030300303402200004200b59802c04018020a4429540c3da10110388507214608191500c2c80700500740c5204001d82048001c40c50200e40e00031700303000c0d030f04000301c501d4500190150700a500001925000040c008107403601e85c0594003401802d09540e909001e14000c1010b0f1102440580c40b454400841c001600f03881e459400340c4150034004004001000702800c9c1064480c0a00c000103002c82c10707500200351010b000005692082c0d03031000e07000c8200d00c0d02c208480d0280d040980307450240038080e070866028820700d60015104400c41c1d5801a10303000103061400041c170102c0c8a07140a610b00308018000a810072001040440c0f035428410000b80b4420404c4000b000c464118110329480c2240210300c50204e41c0040444000c81c2d0001e210701e1315114103110031110120b1110307038007003030361f80ca000c803211002c400401d020820781d813028150941e02e440e0f50341907510541d400c8404035400001c101c0031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 209974586 1250 209973336 209973347
    0xe07030b010207150c1a090102070b0106020615120c09070206090709091a130c0e01060f0f0903030f0504090608010e010c0804030206040204050a060b071103011a01020a0b07020f030c0706 82
    0x20580c01d02c0140003d5240110100300540341050b00c0040200c0c0380c001e079050102000d1010081c1d4507150701c900d490302e00912a10300035003010ac41100e003818940c0002a8691000490354064000e40c00c0144d0b111030702d441000410140e1048581c07050040c021030150581d03d40d0070540c80380181d90081c1c81146842d008060425026800081030070b8945864140424509045208081140300c44040261102002c040c80d900712010010030101101c41c010038808566a90319049401c2d0f0384a1030300b00301c54004166008205800f507000040e900740750070000700b485040c0c150042049810b0071403410fa00c1c0d80c098800c2d00c03501d8003c0c2035503079103489021000300f00c24441c031035038100b051138141c595080a980007511040080c00207071049031141d000c80d00710401c82d0300640c0184004080306071380b80d003e881c103c00300c2600c00d02194440d500c0d28414924501f40780a4801100405034094445403115607a14100a07401030701c00c1301103104e41008100c200c90100000c0840c04005c20080111038a8003c0c010304 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 209975836 1250 209974586 209974601
    0x30a050a0b0909211e03130c0b07030f03050f060f060903071e120503030a110d02031906080102041214030904110d110f040909030c02060a0918111b0109020a0e0703 72
    0x140c50401043d0300c0c0026010005c020003888481465803911048504002420104409822200341150009001103e0001030500a1007a1130f5160880301c000c20039401c4403001c40b110600086080c0018a140c6081d103001943c0380e1000b002c00b410400c0400210303241c403080d1b41100c440325600d29400b0f41100728603100c0000a08403d2192801d002c0f030307583d60399180d000c0500796003056074403802c40c4a82c004514003503800218074410b0031174032894800d48001d8003d6075071220303030841c2d40380c00c0e4085052074044c002c80d03040c0c0e903120000030600c12082c0c0c0d500d4040038900c0241c41079800b0a11240303c9580c0c0d03d008201c502604a101c5603207403902e904d1460300311303020815519040d9108208400f02c00340301c0c4058a04803010300c2c0d400641542c06040a440101040c40002e522010004400031001d4100c1c0484059a00800c1140080c2810301c140310122a0484e400307140c40ea0040c408014007a6032485040d0903100d4000c00452500700c9a4081050600e8030740081d25a905980c04200392294580304144 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 209977086 1250 209975836 209975893
    0x4111b06090307081b0307050a0b071b050c0f010e04020a0e091302032806050709170105010b0304020d020307150f08090c010c12051e070c08070308030a050a0b0909 72
    0x10300c0c040030f503644d41d102840b801c207903200030074000351240030400c000740f0558074029000b50541d15403600c41e2a28421040e0300315040004603c1d074006488403c075500c400240d11507840001011010251010004241c22a000c2a410010f15100324000b0740c80d240040d040d44107175030f102d580031620240c0810810700001001c414803034148840710405a600000d40326500c0b64200700c0300c06120b0b20100b07080083c85200d800513185905004c1071100c4203500c141c0311070454a1355a800c02c4d80d4400034501070b00ba9403083c0f042d490a030000307001003400352400d110300364601c03803004003202c1240741c2c1c0c0c5241c00d419586c0a040ba42c04030361307106c5400140d150010001c56200011401620010b4018400644004500314004d031210140780380c001c030300c036001d4000c8851440242c00c6920511076000c444d05010350000f44100e540213101d00000400b1000041d48006803540211001e040d903484144001c0204002810140a1501e8204000040c1c884000103400b5007a0040542000017441080039106145d030302d00032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 209978336 1250 209977086 209977093
    0x90a0e0603070b25030c0f03090806070203070c05060f0919090b0d02010c030332180c011d0a030c0303051e0408100e070509070804030807091208070204111b0609 71
    0x50540d1144135021400041c0004000c90441c00d00782011181058880380013404000034800c80400d054101d5100c1044810301c90881d01c0e81c2d626400100e80781e0203038800c01040030110010501072842c1c018080e146016842c11102e0030602c0c85800109100300c2110007545000300207806000e51001800b43c000141002c0c0c3c1d00c03e06801043d40001d00c2c02092803000740802d039807466402c00000d50301150020700320204244140c04605035108a84550083e40c40030080d81c041100e2103180e08021030481d4015005031607480b00402c113a01040c0b0040040c01e00189d0050f0003440200004c0c10800b02c440246000e03940b41c0391103c030481e407d8062074000307071340380034002d00c06200070000401e00143c000b242c105056004075a600d9280ca00c145003070116000345a100d10b0007400c0124403503024840d2407250780a540c54400c65180e107201580d907103000340640070490a40c4012240454045401400a28409031000882e20000000b0a44507040804000803164015043d42003480b000c12443d0340205941014 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 209979586 1250 209978336 209978347
    0x290105070b06010507260901022407260a020910021204090b0f0303030a1b0c1101080c09030a03030209040e010204050901090903091503020901091401140f090a0e0603070b 75
    0x81d10001d1400501c6541008800601c640800c241c1c50f2000540d840e128042078186d050f84841411503070064009280140b20789001604140017580c1010840035600c0000400741d181c0c3c00701202c0e00c8540014a143d1001da040d042c1c0301c042109480e0b50b10031111038100580300d0042808200d2070480711961001150b110520304a201403000b82214110742d204440003d0341046000450200d0f411800710543c18000881041003010700d03500b01c007a1801c06460003424101c2e11003410703640b2500e40400900200c3c2d0303004501368594080c0d021103400c8459020900e0070030079040002803030142c056208400290300401c000d1110308150080856518010000394100360404c0301050201d50b0502c41c4c0c0a10586601c40082854080c082000142400e800c0c0b040e01e0303110600f0050044d5101006660014040c0000094150b0385036104078507414050707440d496421106455070304c06e5086889880c0d4110707001c014020780f65849006103030040940365000c0714940f601600305410701403194006080f61000304035 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 209980836 1250 209979586 209979593
    0x140a20031609020928050406080a05030a18030f030c210203090d0201140d0902030705010305060f0d0c1707081203072106050604030506040506010501032f070629010507 74
    0x15010252400020010b80b03132403808001070251800c50b00c4c0c0a0700006504908a481d2040f00d9400d8103581017a60140003c69032100e41701d6440e91074000213400c5400c28003841c01054842c800078940c0f02d05c43c0304405420b07603e0391035030301c800e09c0202e40c11408204021072075400c1000a06c4d541c00d441040c5000c445442e400704501a4481c810080c460340b145043d403101d241160702410320400c1200d000d0400d1511410000c800341c1c010816500107174800c1c82148000942ca62081c050700c2e1252034003800c403019529407002400040074481400f102c02e1300c0f451001107140c2c0907100044142443c0c99000b00107041c40c14110609040c071000c64000c1481d01041006901c0343c02200c0d6410300e00980c2810800640f46044000042c281038101c1c030b90000c40000c0000a000c00015402e0155000d0010344406903611001581103401146100820283c0003107101c1e140305800c00c4000001401c0402140361104c19030b0307020120780c081e580b50582c1c0c00210980440d501040e84d0221242c8030213080080c90030b4480c1c1c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 209982086 1250 209980836 209980873
    0x30c0a060e0d0b090607140906070f020f040203130303060e01080c0603070318060933020d0f090503041d01030201090b0306010c050703031101110f04050607140a2003 73
    0x3441041c0711000303601c030115441d0100c0c415005900072650b1103007400d00451564861200741c0d503003070024040350856032102121804485020310024850341c41c003609551802d02020b01c00106030f038403130300451003007080ba2034078001103114010400d02d401c440030240c0340c0641110003070f0300850354a0310030341c006021010001030840d46100302101c050380c90303541d4400b0840180c101e104056100305815420a01000303070a80046990394410f14284411250300608480d603c415008500d00705508880c0d84d0b100060580d0080039109081c0e2404510030303600d4011031090f103d054200310340540c0006010810f00c2c81040d091520360840803284091545950002004401180a40b0440b03010000200d0030702ea00949589180035400826940c456540c0e041c0904210760244001c0c506508004000080c0c10242044800e12085c44641904150508090003090b4025007002c80e909030752503800c1d560001040152004440c032071001c003049100d10080542c01e02d80d4100303415020750b0100300703503804503002003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 209983336 1250 209982086 209982089
    0x180307050c0409140111070201030c1e0f02010902030a0b040c080703080d18020d12030f110f0a0302220f090c020316020102120a0305060f0a0b12130803090307060506030c0a 76
    0x1200c010450750b9250511281320446600110b42c29842c091141c510910644041c0000701d000341ca0421603160b92000c2a0f030781541c100340e81c6640521504241070a070b4003c106006403e2454800041c7ea07441a9010030300d00151803a0503070711204110100000c0205025081b000303081400c003e0100d13141b85513112040e5001e405508a80395403680d0300307081c001043c0c10040683c1a0003e003600624010f5040500c4115180e0101c0400070741000701c2051400b407140034a420042c0d506454624000060100d40c09a40102503800c0070541c0810070020020320480c403528030350000e04203094906142841c00010482e0a90010358450300304051007020316008010b480c6501d8500175400507560321840102d003001c2c80c24149010f100300102d8580d405070b506601a500c942030a4401640940d1420200008402c0030302c241031740031808200c1e00501c52000080203401c0784400a608010221030b95032030080380c104464140c16030713001080300e030103200040c011290410410343c082d081c1c03000c1c840081588607025 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 209984586 1250 209983336 209983339
    0x10606050a081302041a040e01060b0427020403140c0f011403060d120e010215040c06120f0906140a09021e060712030e0d0203040b040e040302010b100503180307050c 73
    0xb0001403088043e0702101d40b5029070040c0100070030701c54841d004244902002102d40100c2c80c07d40d0200300e05005115500a0710300c2040c841e800d0500d804880e00b07040b0324084080c0103d030310310245180c0805450001d00003862040d401d00c2e1458850140040c40c04d443c1802203481805080500c007040d98201c0310203440c603900c0d5551255a80d03580400305440c1c616021000b004803851164244040e50f20039040311031114240c0c2a00ca80d02036959001b085600b05841c05080360407000c0302002414020009104e8604003080c020500c09411249041100d070030403c107076207a46d100d0040210201c14124021340c0850350001c00c000103082a0045888620409a43d1103d650440b809003525a80c010a072170704660310604144220210075001009002c6034101e0311003c0c440d03100815040e600200c103450584003042d41782401d151a202140540c00000381054003036540e101c4845a15841b19200040301049035110f8613540d09050101c01da060a040c81401d400d900284507240000d040418442d800000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 209985836 1250 209984586 209984597
    0x241505010c0807170c01141608070c08070b151e060d060e0408190507030c06111b0c010906020a0308010513110a110c1e010807020f011517010606050a 66
    0xc0ca03040b0700c68450200c020703040c20801c81041c10910440001429030880c680000e0100b148850380d0112000800d9483d0216018441c003c8903440d0701c501c1503954000d01d24035004001c00e000b83c581000d00d0b400000c3c01d91700f2000710010000d007010345442a452030007013929401c4071182c800341014004105148260300c43d0000140f40048040e0765089980603001002c0c502ca40e90829103801d2826a000c000000c421145010002c0c400e2406035044c0d030459501503c81114401c1190782e414010202803d552082075000c4c406140701d0b40590101d41e0200e41d4078002055500584070014004500c147d20540441d48012060800294858460f60450f80d0640300c2c0400c6000f5881020084d02d850307817422031000408140342e041d2543c043d080f201c1540c4020144c40c07074865810305105090100300710040154090320b000c016954030904000c0d07030000603032040d20803031500d030108a0b0030350390000b00045108440300e006000341e9028481204091020100810031107280c10300c003401c54080c0c42c0440b4284030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 209987086 1250 209985836 209985857
    0x160308120a0f02040909150207030801030b1003080c01020703020111040b0a0503090f01020c07090b0f0d0f06110c010c170f01060c170d0f182103020408010924150501 73
    0x4440b500410700b000d512650654071580c40d040c00c2d10041c80204029a4014851003100f140c82920340b0880d007599403d99141e91b0030340c3c216211042c801030040c01d440d101020410001000c2040ea0001e0300c060b140c0c50002680c0e0302d138182002401e40f0f640032814951007004200402c4100c80c440212096601c150811940ba940c41c0000385041419184800f511540000741c40c0c4080e10002c619481aa001c402040080c59542004c0c0480c4458141110b034003e0480e0701c00801140d01254103c412501c110390102e064500000c1d180c40e1a0001072001025a4540c1c0190b100341d03403c40c240c2c805003800d110b00001549460320502e0510301040c071441c8144203039198130341c05111160103001d01c00e00f020300c1c2050390b450324a019000103044c10140701c2012468049a100c449582600c040d10286c1c00401b5024181d55402c200c480f26944c00c03c1420603d5070800000600c81d10038003824581e0341c0107054101c4001da0308408015518805d142c2c03110100d25111651f00d1022180f02030200b6030341d080c80d0804066 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 209988336 1250 209987086 209987101
    0x42616020406050a030b0115080702070b2208071802030c04051203040b030c0a0f03020702130506041509090506161d010c05010510080c0402042d0e041416030812 71
    0xc01c040d401c1950484c9600201006010150408038101d40b421075401d4424030b2404011100c04509480300303001600500c0c4200a2881007102a02c148224000d81d65416242c960544030704007040d5002c00d0594200301405c00402d9060f114204000200304800c1d803071440c0090b01e4040610840c0140391152150941c0300142103c108180c0340540510701540d42e0b00d0a10101181158020004074400601043c1c501d41c0d40600c207000784c0312076642c090801150300704094a00e00c09458020109600207036182048100c41500c40c04010090084500c00604a00c4906160307052041c010329004805ca507007a05880080d0380206a0101011441f184511440034a001294001c50300f80014001d0360031700c018018070104080700e08084420890848811014030805d0105030701540c8941d61010010030201a03288003442c0c400b050b0b030075910004986068407500201d08074036003a581520600d0786c5960400d0b51140c1084007030290172240c00b0203014903103141c1d5541058030461100c45203807403e010108458 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 209989586 1250 209988336 209988341
    0x1d040f03020a050a050a050c010e03060a0c2c10110604030c05030f0c06150301050c0d110c0a1a01080109150c170c09041401060807051606020708030426160204 70
    0x3100c0d4890244c604e981c3c0241400783d0b0744e05143c2d006950a01656800c0d040031f40c09000503505150002e030250440f51340341590600102103907a0898184003c100c19403d8455100000b0801c1d15070420001d2180c20040c028404034a00420240050210f9000f00381c01101c00061456806a85440c1102031b9210500e002819400340c011001000c500208550300703100c502184d41e030b00c2000040448042c140500b000c050a80e201036a209007001810042c0c0c0700a0107207500300c00e01d1700400b40101c6140a2060082c1d914215076460103450381006401940d40000c1c01003a02401403401d40000e001080d00740d00d502c500d00740f054080110199030b80300619034640c0201502c0f10b0074290329001241c945031100b02001c27103034041c0208910440c80d200102e45c05180d404807090585110343c3d59502c00765128401aa0554404946500c640e400225048005800d80c001050210f100300ca0454880c1402c5c0b801c1140e4060020181d00120b84140d00300002c09011010b076910aa0342a075031810b0f65041b070010400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 209990836 1250 209989586 209989603
    0x418180f02120a1a06011d090114010915030b01090906030b0a0507030f05090d030b010c0c05100c050102030c07060b2d0d0b04051c090305061f051f03061d040f0302 72
    0x40c0b80b0100c1c049030204e010034000c0310310521081c0c030f444040090200c803041e080d400e81851b00d503014441100622800b00c0865040800c00e0040c10824012500d071114a0101035680104200198a07801c0602c803031f5070300051a50060005060600c4003c2c00c566440c60b601c40002c05603549269100005410300748070b40c00c044080d0710400b17070400c41810504000c645462021308041d003c80c1c00d00320000401e500c9510421401034006401d010b500f42040108030f03014220003004001c000c140030482011401c20300c020350080382194205030b69156145003200c10348100310b40c1c0600c078146410182407010560200303903c015142c0e121008050401c50300040350750044500240180500404100c10400000703040c141505014040281b14944448100c800c803103503010090654124a010030300280080d01420000b943c054139800c2d08035103440210351101b88035031103841590f0048003e65a01900f40c03040002501c0306001c412210040c4030078500240c40090002024086888043c4050510901c502034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 209992086 1250 209990836 209990843
    0x40501020717120325080406050c120a051518010e1003030203030a05040c1503020d0b0a03081c09020405070c2609060c0102070c0617090601060c020d0302120418180f02120a 76
    0x40785c081e8030810050202401700c40407115185800c000c5200988050309603101d1072084d000000c0785645501245024200103090180044d08401c00020965540010014003140080a118581d854820b411400040c094111031800400810602c0070a6010044079031003001088007103150303151441c000350802901e604c1040e1003582d00884c0385004c1c0d4590001c0c05c50343c10b4440b0a2009400290070002010b04510004001038410001c1c240301015130390b0800c41390138003183c000680000d960042800c0d5441203c0040001e00c40e44807010400500c5c840e007052400701d8204080103100704a441ca80700c0d03c506d03241244034010101d10985004030940440f84a154005486501c155640c040a4080c802000100207485c419200040d045c0c0300c0010914103d071515940d80401e034565400380411150150340039403c40c000c900d5840c0c4581207510062004009500500c180380c51b00c0444402198a60342e11500d24841d91a40e542c08214143d1210381d0700c81e011a00c000b038004c00c0001c554030b040d41d0340000030b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 209993336 1250 209992086 209992141
    0xe1005120c030d05180a050315040c08010c0504060f03090203060c0c010f0c0207051002010c0206071b0b0114040f0b090a1d07030c0e0a09031d010207080102030c0405010207171203 79
    0x1c45140c3d43c844082c0480c0485e02400748050501c02080021246040c01401d400d544044480b41b1003404400304250001c0c0544c0e44000d074162110750f280d0a4918100202c1d011034030014040015540c080c000210480f19071a040081185942c00a501c41d4000741140541d41000304004900000130350048100303440f0007004201d180980070019417501c8407885840c2c890f294103e8840d50490040c042c8641d800500d074041c0c511551418030541d403a54059161094031100300655400051048180700d000c0c01c02c00b425074050038018001c00c415074004000c2004074a050401c0710304030391500c51216802041f601c2011415210742c2d00c00c01007a42541d9154190f600c50714600005002c815840d040590311107600552041e0381303c004490990301c510b0302c01000038450542d8a41c1d1107085589400724000144103035980c3d04d503034401c10b6081e60400d4038405400c03400002c080000750780410003280240103004902d518940319200b825190081c1c602c102d4410600040025040e02500300030f40f00ca00800c20a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 209994586 1250 209993336 209993353
    0x203010f03050c0a140103150b0d050105090907030b0414011811040507080723091801140d030203030c0a0e09090f0606031b0103020c0102070602030c130e1005120c03 73
    0x111034100c180c0d2005a805000c1c00d5041401c81c00c0035442c100948904c10285100c0110080045004100240011254a86403100400d05500d6a0700500303031480d80f0200858154101410440e141c01d010700080ba0341d5101890800006010703a502a0b0f1281c2c004a504018a800210450141402030000300c00c010608032000d04100011b04002226501682d0420459561020a680c40c0000b03443c1d140c0428020700d08a51aa240801c211400101c3c503141c0e1420121248041032900c01e0740d40380e00a6010340100140441c8120745901000d60070200d4520501c1142e544000e52a44000382004000401c0004c2d0900d04034020380c65110603e001404058040c54481c001c15100c00351400c000140d4001d44000c10420321780000c081c1c46501140d160a0281c600940040d002940240c580380c03d0303035400744506400310b04544080c512800524100c2640c49500050b0291142ca194101d040107003000e1041c0003482c8055580e240589500b40c13043c07090f08980d12085440c00f6000c2450903818400c401c030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 209995836 1250 209994586 209994599
    0x10e040b0409050f010c020c0f0616060606030c020c0402131e180e0c03010603080d02070c090c0203091009140913170a090b07050604230a080406081e01051e0301020301 74
    0x1600104d10100d20000c100340810410100e0301c400d480e074a4607900101e1002c11580c0d038900f90340100044d02c070b49100c10720818000d5a85405803507141d4403142c0426030710002d070060a901481183c070200021101141781c82c1c8411203203903012609008d44101845d8a80300d154400700201075850250421081c8541081c101c0c00095000d428104c0007042c0c5801303141e42d034140909050080b41c00352640280940c0c1030148230103c550007900004000d582000c3e030180b001a402642d8490b50490031001c0e8059039a031028002440031f130841061141080001003c0104004c000c81c0c940048090022250180540c4403000c0490a032028600d0241210300c007400355180100525009004003101900c03000b04040d5201c138801214050444007412503040b0a001400180c241003c2e80e0702424480c814042caa814580401e01d0465050700c21100400000b4080c40040d81003101b01e40e01030040f001c0681e800f02046407040300b0320018441c0c0b502540c07040003903140200082d0482c100722b1001900841d00ca61f034501 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 209997086 1250 209995836 209995843
    0x30408030711040c09090b040209041103010f0807060804030e041103070c06050c2a0a0b010f1802030c0d0c05041d0114010512070f171f08010c0905010e040b040905 72
    0x103008a40d0b000052040c080c903820240541503a070102602c072250300914000d1450060102c0c0700a6a0388142d0800010100d6903a40c854050700e000c6001080da00ca6040c1180b001c44005a504110500c0c0d203d2981006403da10000c1c4035406689440c20300b43c090b00840114010302440c00ea440d450580c0401000340b0158480ca040c1c211178003640c4203100f0354a41040100c064424a061a811500c00008600c1100c145241c0c028141c07031008212114070b0419282c02003007000070b802405100a200a00b0071030403000c00c084d8022145802421880c1d8105001c0150311343c0f103900041a80c80342c50380ca0506560b4011802c3e10010540e010359000c000100c00303140c0c0b12038042401114045801d40080c40c456500c160240c407000444c02640481544030160103880c4122a20b50b07100030848045210016040007155440c015001004d0010ba203a00d6001c0100d03001101c0d400c007203020fa2504c2200341700140c3c04007419044a00a007410407a445c070f20300214007c6e0009c2240f080d081810705142004104002 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 209998336 1250 209997086 209997097
    0x9010c0c08010903092102090c090d030203190318021905120d1103030f010e0a060306020703050a0f0c02061c06230a1a0a03020a0e0405090d020d09030b0c031803040803 74
    0x20303900d0030401038441341c442d01c1050b102070821600c0a00005818014208230a40a07001480ba208040c1401e10b8000041d0080720740c0c00084005070070100303544c907200065029441c0b00410300d080500524950100801410b82a4040030f84103921003c07461686034604c2a80602030f244c080c0c0313030007001030181846c03607644c0c19017040e03400010300102c4c030503141c0b2070303002c000d6030b00442c0031a41817122a442c2c0700111b2080440502880040c0303075201d800000040c140c2c401402d400e80b003511071586038044071401504583d43c0010f0b0700301344480d0a0020300146d881c0d00c1219008100d20300c0a0012006600d440001003405801a26202c0c403400410420b400740005000d807a038034120380d0210b1040c3c40b41000c8468003c0c042d000e000c154030030321281d030080303001ea0041d00d032070b000341d203400244c03844801d00182c2600c9050351010030b1504001c0381e405d0715036410300c00b022004900381800400e0920f5941c0e44080c0c1c1c07000170300401d0b4400021001c83c12500300c12112945090309002100d4440e5114184507890344e106 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 209999586 1250 209998336 209998343
    0x50c011a0a0603150312020f031810080412080a1508071e06120506040f021206010f020a030c0f030c05060a02030702010b0406050d20210c0a0e070509010c0c080109 72
    0x1141c600203103080c071074081d04036104202480003281a00d0340d42c4180d9134a48445103241940580090400306070030800140c00e00094604840f042c51801c5c41c18002c810703103070949034001c100020003008080b4400310001c10b0030078103c2c03400b983c0d10313550410300200425815419086003c10300500160701c420006032a003c4d95001d8545010807500c20340c2141c0c1064540c8544004690650424421154030f0b621190381b0920240001c258800d200300c0c0001240d00c988030b8001c4c40000202440195640f1099034099240c0340d0000b0b14107000326440150003141034800c01041000c0f894110001c2502c43d0039804c0c5a02c0e40a000c9510700d0401c0c02050000c0e40007102c41c01c00562912844445031300e0203010b84002c03580050b2240310160300c40d0b00c84d00711080c240e06016400443c0507d80f0300294607114040740c9020912007440c102007458a0f072260811b0080d24403548114030110b424090034014000701608102c1c64180142c0c0d9410100058030020904140a0540500c81c0f00008160354190445e03502c2511 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210000836 1250 209999586 209999599
    0x21905010f060b091906020607030903120f14060105130306090503121608060306010302010c12091e1406070c050d170a0c030f031b0f02010204030203060112021509010e0f01050c011a 80
    0x52140340e00d20349513018030440e40141e12031808940b05502951040084be4013074034108103400c0060481c0307415608180c0e4520387e82582e030f080c0700c1c5000c441c00c401681c00031802d2807c01d00e80035801c156540d02075082d00000c1c09483e80c408240e01041400c00c112840440121a008002c0c90910a030450300b180350107481000c50940c600240f0030323180100f00903068940c140c4405005407816100d070700c00381d032024420a09000c103400c0c1c0406c859040d1401c207403020032f5030000071280605180b0280b8404455510107405441c090000d440002c02401405040d204184d5000203000c0081c142512040710300d0f40e00421124000078a0720186030710540700f941141c02500c81c9040c0c034010030401c4044515100c4903000c170145040280c0d1420f80308081c86d80702000c05100140c00c082d204c1c4c00080c10041c0c20b910082800090410300001c50422456000740c41401c2d01c00345080040000001c1c21030345040350040c3c4980d1481d9518981c5030300030310640e010000c2c880000c1140c14680c00031381030000240704a0300d00c80c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210002086 1250 210000836 210000859
    0x30b0a0602073b04051b0306130f050703150f050106110601060e0112050a050603010608070b0a0f0c050a060902041a0a030b04080708030f0402180601021905010f060b09 74
    0x40c0001041c20460360b0494050600740d100159207541031142004040342d61550306512443c0d012003c05850080340510003402e1860440113140b00c0700c00600156038000d0b04200d040040d0b0701c50f1003100060598200c0041d03081810140342041c00c0c4200d64000802c09110320825408860003a4401c82c1442500c41c0100300e16600c0326001d0351030030307039120080d8a2a0300260044c0002403194010645088060500d400b101d4441145c030400d4070f02c202c4400800e6a9240300b042403502d03090003a200180f0020010b4a903060078180001d40310710030000510240003060040071020752052340541d002503082001c3d0b822010052030103201400307040170240d22880c10610700180311003124410000507040101a000b025255a6501207030700380c0248150362111080c0038501c0812903200c011441441c5014074001380e850548100411004c0c49000c0740c8034000011304020183e47c0004000802c035401c6840040c94003c14a0720342c0c0540740003d05260400d0500200003082220b04014000010040302c80c802100f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210003336 1250 210002086 210002099
    0x7030b0613060f0e0f150f070f0b0c0316030c050d060303020102031014030c0112020c0601030c030b0c1911070f061d03191e0b0f060316060906050903070510030b0a 72
    0x541300c54207110f038040c001680614442c0b0301141c0c19403800c0d28030460742e4100031880044180da5000580140c50006c003400e000c0c000c00480f111409c0d400441902e142d803c500700010f0140c012810000807200381662010f0001d20580030703809075180d180307040d03000340211500c1c3e00d4028080d400541c1c00c2e00c1c2242d101d00010a2100070302c580a441c06101030700802500490a00445403d0200c110603021b00c1c1c2d082002a400325018000c16019600814101600074030303600c3e0542090f50010804c2d00c4260040c49168180311a01d148810810305c1c0b49010700400b00c510f4482800c101190b40205903919400100288813030308a0254050700184011911500b41600d040c15140c2c81d548645030198410320301c0307101c000340c00f00301c4040c0c0201c001c0c4445031100c840c90b61901c8038840140c1d207401116813240100300c013914080041007900400c1d4045254020300e0050082c0918a45001e200107000300850000c409440400810008001c010b08100d4580c170184009801403000741c850a01803402542c010502c3e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210004586 1250 210003336 210003347
    0x528020312190f0f18030b090a140303090c0d1b090506040e030705070504020a09090609050a0c0c0b041e17030105030c0d0506060609060c0f0c090105011803060507030b0613060f 78
    0x2640315501c0c4e200340c1c016124000c075884542a50f030220306515010011001c00c208180b040e10a1a04c0e00c0103044038812401c000b80759030710a548041c001d038010810002111404545003130301c44001c0e104c1d000c943e41d0500e0300b02c00d80c0340d190b4425090f01c5040400014a010150012801280103403030405c0b010100300c803059200d101c0e060025085a1007084204a58105940108014451407030803030030f82610b9544078410b03241141d10500740a0744030740502400b0f80c014411000c9a003c17500f401800c50a141d80c454501a100900250040d505201940c130203805400c1c140303004542c481d160b4000c85c0c1034041020714540083c01428060b2298045480c030f00e00340501d0000f8580e070050010509640c580b01004110741c044100701d230b0444800e0000e100790346e5013040100014800d0308050065589110300788078440105900c140c0c1081088900c044490405005840c20b8a42103480420203070341e0541c055015088510750180c11140c00600c180d001c3d14000d03030306001d503001a6211081c040000170105ca6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210005836 1250 210004586 210004607
    0x3060e0f031c090f0609050106060918050a0f15080c0a060816030b060309030304261c1401062102030c030610030605040606030b030118052802031219 66
    0x5a5078400c0200c1800c0d0700301c906a0070400c07540310901103035800c100e40d520b00300701c0f03a140001c640803034031050900d04102d0280140c4000e03100c20f24041200e0b6203403903501258583c4140051401603070b07a1000c80c42c0351905402000711070b04218000c0c400707117110020f6102d00801078070a004250040d00841890340c50b0500d0024101c9240d40d0742c1403501d031511041074415051207017003c1c00740340e507800c80a065521090069486000c400002d56203a00d46420500350740080c40820640403850511101c4241600e2000e43e0b448170341d149014040c1c2174890941c10002c100e6054103440d1030102a00000366254003071940113110314030a003c6400c003207190b5102d0081e40016142403107404030510020300340b402d00020103015503560740740c08181c03d552040460308a411b290020000a43c450300030912609003400340014a44150001c0000144103880d141d8468a80240c0024415009801801c10200003403480f85001e8004003540c0040c495a82d0303517034a543c8406280e003802e500f07450084034818042d01e040403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210007086 1250 210005836 210005863
    0x150e04020c031b151006031b09090f020f070602030603122b1b08060103150806040311150c030403170f04020105030c040b0408010213051518010c0209040c03060e 71
    0x10308010403408100d826000d45159100c0c6131040a0008210001d9a40003502503480340760389000c51801c0410050a0343e030948014260203100d110000100703a488189907007142c10f0351000140710442c0c09010b8020740f04204030940b0b134040101c1c248061008035801180121011003c80d040e50340c2d01c4501c80300c0d0b4083c880110f405082c039a07464440500c900c40c0d10002c3d48005180008079103482014002091030100400000901c1c00c0d0204411560903208042da42c1d178011845500244c03400340c3c601e41c0d90340014002020850348820a9149000c200803036049095030406160300341c40d00682541c000c0d001240c09900003480581018501e80300b40380b030140122000d000040f656962034005446a500281c5004807141c81004005469901c02021304041c04000001603518402071070a2070000c011600000d110300719040d040e4482780704031021207900e40004249151042e0780c040050300c01040d031078006074101400404000c1005402c0a18005907072061104100c2c600c2440c029550368400c070350810 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210008336 1250 210007086 210007093
    0xe0d09120803060d030e0907030506033f0708180a090209090402010c03020c04091b14060d0b04060e07170108030f0901030504020f060a020d020c0301051303030209030c0a150e04020c 80
    0x600d05043c01e004e1545081d009041905418200b680462800e0904036020030000380d440d0305000d03091030217104102c210a04c0c81d41000820350141c000a0845110312401880700e2078651400e00c545d61124180c589560300004078540350701623000c41142450345640e940b0f101e04581000414403030745900c01e860410501901d8905551380e075a00649159244c0207066040d4820512a00c0a41e615030040140081c800e000d52060b016031000d0b07540d0400c015800945881a803840303146507076190801510b5568a906d03002042d014500e00105000305415000120103600d080b04000341076400030203407408410301d22030580d516a41d40c1d0980751640544c21902300d11000c00c200405180d0309ca40c00960300b0600040000702000440c2c00002c2880d481142c4050141e00100ca90480c0c0d03a4042c4442c07a4917000560090104d0720780361103030030074510940320010305240d0702190304056603c003000100c00728075000e05030201041d02c0307001c0702e400b001103645140006002030410f4010390410b8025a15440501c0c0000c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210009586 1250 210008336 210008341
    0x7080a0b010b070f021f20120319020a09150c030203030c0f13080a050706090501080a0c05090411090312130909020102100f02040905010b03090d050307020a02040e0d09120803 77
    0x1040b0340c551240784107135141c000309114440960f40f2500a904040f03003080c006104903155980c05080f074410500408220442d800042403501d0021030903481e02c0300450740c2c2c030317569036212500001070320252410f20065501c0807902c0001150001128002c2d141600090724141e00300b03000403601d1031890000200107030003c1c404162051403e00c040c0403c0500303200c20a05050000c41e154a481034140d0013070b2100e03842800343c0d10502c001400002d01070b049038a811000181032500103000d002004d402c0d99a00c0ba078814060030aa07120f00151821190b00510504c030400501807030003c0c0d41c00214070b03940b09005004044041c1d04000040b10700040c03c888503400b240e442c20606100829100400ba41540207907032040b40805440c1c801c5140c803500300800183c446040908110481d4016000bc07012101e081080c40948500040c00c01003c652520f40b02c0d5480e941c9080481c203002c507090000390060308180440d2404c82007c200018010466034442000580d190352080c1c010341d09410207403c0d403a04002 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210010836 1250 210009586 210009599
    0x703090b09011e050a0209032a0306010b1c1d0624031e150a06080106050604060e090a0e120403060506060a12020315210105090d09050d110a031407080a0b01 69
    0xc030707507844001000c0041c101034640012a0404500003a035008274040c140300e45e120811210440700243d0800d600420066040800a50280c8100789801d600e0012640300c64101800c0d0350448900410f16034030318465140d0000c00c0ba80c0d15030f420f40b4824019801e0302d06040d0803209043c0d03402c089001c010014058400030030b0700d468280032003880b11407440c05034074080c4051000300403215000740120640081c0f614980f036441ea003100e810303810072885a8010030003040304a504c4641021200300c12990003040391980e404c801300400402c440c54080f806078403440041891100b0240044030f00a0106000c40e60720441000082e01c503070303d80b01000c00e0303035050803050440059001c0c581c803c0400130200c0105041c1400100d0305c1c3d408a504c2c107420344809480c8041c1c051300303009043e0051a000014084604601c4024280800500841c0c0c040c00d9064030303407000d1240c002d440003800c070005001a03075501d4823424401e000e548250b0002c1c0051040c80070007e28203400041d4204400e4008a40007a96400c100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210012086 1250 210010836 210010841
    0x20f0f0303220c090608101b08150a090608010b030106050d022d09040f0203010f09020f12070905040501020703080c0309030409020903010e01060603021801110c0d0213050703090b09011e 82
    0x2c00c10345401c0302000b00480c00308420b102da007000d08003940c000d24042030b10300c0b040d070180c80c0321108103d2041000700c0c503c052150004600368120103150306115810465102060115007940d102c2c0303040c80d09001c0001600c24042d80700d2072500805400074010aa00e810600009803280c03032000b034020510403246c1003820910402955149072081d9129011298240028103102c02a1401d5542108038043c1100310b10b024480c40c01104a81d007418041c4107250b4000900031b0011442440c0a101412a00c0c0c100480600034400600000e00007003045080901b0800e000b500248001c9000c504980081651000c0c1042506e1082c0f503200300440c0f034182000611006900300f500403d0f019034813424580c04d60300007030203039401416880e0340050b100c5019141c500c40080700f224640b814849003030781c0295042008101c280c0c0024054446031851841e0b4404200c48540f40301c852484036290000340f1040d6507040d00000301e0180500321024254807104040f60894051038104409520382c4c0502e50034503806038 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210013336 1250 210012086 210012151
    0x2102090d0b06011b0803010e07081302150403050610050f010512041b030807120201050703020a0c08030606040b070615090c080a05041707080d062106020f041203020f0f0303 76
    0x40c90580c008000024950414100b21001145c0c03d040200050101e180f252016540c000918a01900b0300e0a10710324082c548280408040e000e2060182d8900000c2e01d1b20085070011a8003508030340a41c5050404003064104a002e202c2c403644101522901942c4154182e80c0801c0301121110500e40301d9540b00700701c410043c1e0091240910b1150b000000c150204040c04540b4001e40c20348003503030102d0a000b03003140c200521003800d0610500409800503409580302402d6540460003650325100c41000035558007442e409610f07540400039001c0200803194211100c450010301c0401205515540070000b56a40c40138035200081510340024800f0b903113500027540042c0501881e40038060200d191000e25403200ca8250741c012000100d90007000c10b9881544001c084c15041c0342d44d0100c9140595410254581c006800e107a00404ca041040c0a64000c0754000c1802181500881c00c03107140181d00d410001c80e501d403407400f440304000b08038240401101c1c070424202c0030b604035100e1100007004402000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210014586 1250 210013336 210013339
    0x61a0d05090a02060d1d07150c0c2705371b030b0306062e0e1e010f0804020a06030f0e030a02010504050607092303010b030109032102090d0b06 63
    0x103075006003002da100d100051105c4c01c5515401b10740324080030100701444045201c034107815809082c2c20040304010f400300b042e80460751701e444051a4203504140710581541e4010340b915802012a04119070318015251301203003d0510103101c1940c440c821100040b00914000a4a401c03d0b41090b4500406003d880e084101404002841c0c15901071914403014002c07440c4030200c0c0d9076142c0c2c1c861502d002c001007607001e5001c031034001049041201c2200d10041668000c000c03526507954080d001c0b03004025040780414054007107418614800c0301c1d807a500022402c02c42c0410740030b42000720b029118111661195402030800003044e1318042d0308030002c007680014095255a62000c4820b00001440100400501503002203400d040c03d0409900b8180040c05400c14000220400c11014407440c03407001390500e50300c050b4045910701c140031070f0161424954090f815442d125410040581044200c041203005024000000b503011118000724440c00f502b599105d80d030010704074000b5002c0d4803c04e40c417600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210015836 1250 210014586 210014593
    0x210020a0606030605090115030809060c0f060c0d0507020a170901030b0a090e1509060106081008010e150106020a080d0504020607140c0405060d02091f0803040801020c01061a0d0509 80
    0x60079140d080c12122581c0080f56603d46a80510507200024080d1440204580001107122882d41da9400c0309441584100c0707008150225150b201d206060146656051450050725428070b031586100c0441c0d403000342480031141c60728020650b004c0c4002038040788203900070f00e40e1041c4048100a0050340d00100c252904240e15201c907074a89032150300b810740c010300c0c40f8403010070803d00c45486a0308022080c031744030300507004000421815440018001d8111091030404803000e855210f140c2d07903206019001031501c2c0d130800055050f501030020b20a030700103940303419101142c0d80b1000304a0b1504841840a8200e00c0e06110680022185622a0360132520040c5010f1902c07000340e07103002803141c24140300300c4240c200c0c50000142c0d050a000c0c0030703071011040320505000c0b96194005013483d00003030301d01c050760010b811480c82c00c02d108903504400313044800c040b00d03101d0f03a5604005010b588900d03146503442d424098006400494806580034001c01d5450443c140480c0c4442c203401424002e002c9041340c072 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210017086 1250 210015836 210015853
    0x706051012170d090c09050906060622120b070f02070f0306241205060a0203010510030203040510020408010c02070b0c0304060513090f05060f030d0f12150b0304051b0607021002 78
    0x1400d40b003039401300c41c80341c0c43c03100c80c41e450145801d0881300014110f02281e0800130400c040740d5982e0040300d4005040592902504a28495800c1c184a681d0011071f0104051101c6505025107105a64400d0307005545a0b11201001e100881e1205070602c5841d001080e06c3c5002d0000a000e6041905195040c8548500501d0a124030307014182c07142d8004000c0c00b10044808091000030311460340e00c030b10075100c01c2d85103501d03040101da000400c0071a030354105540030021404200003409070403083c45c5034190640d215a141c40030a07000781003a0a00c400580b03d48800011030755061415116220b0440c0041c6003040d141400c06d0b6801d44c806421074064039500c04010a00429a204100d03803046034900c002894902401408100139003600134501c2a8000200101030f9179201c22080103640380f40c070740f1482c04542c039510303200500105101602154180e0b0300100301c0002078405184258003603007ca807074840c03205c21084002c98690040070340040e010882c1a0240c01c00207101425140148100d07240c01c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210018336 1250 210017086 210017107
    0x60501082415030403090b0403031b03050904050c041401111e03040902031512010e060406020906040305070e041208091504030909150305100c12050a18030302070605101217 76
    0x10180180b40d003548020100620092660000a0002605148400302d10b4541152006440d01c40d20b5082402d00d40d0070b0f41a40000c01d4401e070b00b83c0e45141d43c050b000f407005041c614001415500540140342420344e40c541c0f4225951f1007001113240e04030300314001e00000c0e901c480b007440c410488020302a00500c01000002600710240c8011407052411511030840268040d041000307441c0f008044a15503814000805800c0c20049078080c1c00552003240140c3e614031030008504903001d158005045e501030380381d00080c4ca42340da20a051183e4811480801410010401510031038070540301e41882e5071100c400e00160480a01c2100c1c0c1250003810311040a56980c92000180c030030110030803040c030844480800811200300000c1440d954080c40500c03a0a0301704030010f003c40c4645400103541d54580c0003107a4200480d6018401c403060240c1d140055131401e04001d40070354486201221074500d40400241d034400c0d540c2c0100c050301c00c0d42095000e480c50070b40f40c800c00484c940d031900d43c03088400c02c00f02034071 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210019586 1250 210018336 210018349
    0x1021b0915030f0102030906010f0b27040207060203090d1b0f0609150c02070902031e0c0d05040507230a092c0c031506030c010f030603020306011d0a0605010824 71
    0xd01c0f4015001503502e1801c403034060300303104060344003000740604c80f0000d00c6904032543c00d881e1290303800c0d05040307210000280c40885130b8800c0c00c14507800c144000b8601c0b05004240c0c00940c40b91040c4022500507880c0381c81c00320f0b40850004c840815002d06d096165000500c0c1d0a00350b01198083c00b4081140044c540314050f0004c0414a111400ca5964640e100039036018004000204214482103080d4234210300031101c6400b4690811003015089000100616650f5054800b803000c007a81c2040f45150900d0000d940d030380035005640040d4221000c1d50712460a21107000e00214000c0c0042082070702d040f0072031003e0801000059014003821541150390388a02a00300c1400c20120014501a0540001d050501c003901d03403420410303681442000003035240050350b650443d03400e20f001079550a126000b2401013142e6040250300d402500300014042c02c0e405044010402e0983c1c51310b4690300c6000c046e00c00c4031254410103011440e450005115000341a125211510038a0100244151000e000950303 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210020836 1250 210019586 210019603
    0x1020904110c0606100f0c050307050a1218050a03030302070f02041406010e04050f0408090109090509071a1207140412060f0501060903050a170c012901021b091503 72
    0x10061001c0303090700c42c0031000c0007640e4100e070b0107440c455150180340780300600400005100c1800d02220220b0201004400c1084540041d001826910315414501e061a1911100b4a401000540c0c04543c03103445040e4042c8141116402031244030b280b46541c0c0c00303401075048014103551800506180b100980c43d0350240004200301405044d82c50f02e400b100240800a112040c1030299141030200b18003819a0901c0304d4015801c90405511a01000c004a03509080c5401941040e0f04040505c0008000020003105030703800260072081d0808094403c9076180034a030b040c86000d610384004162454061120344c600101b200c83d034607117410740760404081b8408501034102d9205580380da40b261895228403900340035083d00e142200e561465612015550300502c2000341c01d4102130100c454032080002c3c100d4180c0000900280144880000e400c0318054000707440c0031404460384000199580b004c1103615030540b252030903590b031110403018030503481c500501e403180d103042d001080314150b07508101851 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210022086 1250 210020836 210020861
    0x71508130f0c03121b0611070c23090705160213020c030301090509030423060d091101031401052b0203060f100909020603040b0406060b0a1d0d050a120201020904 71
    0x78280d20b5403030100c4c1c401054400356410800320030b442c0040302419400031a4583e40091000c103800303404025010451180b040c0c001c0c0428070405000401107103402c0340c02010441d01c141c107034005514038284800000202c60300b1001820800034410001c2001d1181682c05001426800c07a202840606000301c0e4071071000d4011075440400100035102c0136000b00390b40005004059400c007440c0048007004000e0480640840c0d042c0001d030b40c0d1203603d40f00c05981001c01a0b2100740301d61903032402c044040c030143c01120307800a4201080380c0c0e06d101d071140545048070307400381c480040b0035400d1560072141d444012000030703401010030400016139001c110880c0140c2c0e10244030b0440f814039000000340c0052a900c004400c030b007400c0c0c100d0f01594802090b80e500c80c4c0c010f0251812540c43c0d203401c00007403a10b50007000844402240c0340d4031013648440e468005d0038031062501c82d003c80440400c00d42c1401d54a004020350700106e2040e0002c0d00c1c031200e241e04c100300c5000142c10116102c00140a90313907207000c0718 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210023336 1250 210022086 210022103
    0x1090309060305070c050f1b030109030c02090a0e030a110c0406050109171c020601050a060e01091716090209010f02010509030d020a1404080d0f08191104051507020405010602071508130f 82
    0x5030340341490f80231481d48120308500800000e0155980035250240301c18020b40702e1445803000076424102500450590100784c4140c0360342e00d00b0a0400340000b40c206504240500c50a1111000c2d41042d1150b603081c0e540584030006902c0c500481c2144020101124510380c2c02000001c1c1d03d0f4250b105c4051043d40303c5900030707040d650705000c00e020445c1d040d40d1000b0108800007a4105186e600488800305840070750310030501049440f0a2a80b0b4014500c402525a443d00040050703140d440307a0151134458800d03600c00b02c0850b240b031000ca0984d4000d507030240079600100101c0183c80c8540e4000c00d0003100c0d0313003040d14000c407485c60806980e400070b510081140e0401405100280d80c00481c54028260b5400c11031507600f4074008180880310610200c51205507102c01d90701300704011320291001090f00a25425420114252040d02c90f001043c04a00941c100b40012075007500110f4124180c0745010071070000140040021540781d003004c0e018003500c449400100e0003240c0c0c61121500e1031402094903 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210024586 1250 210023336 210023353
    0x105070b1311010f050f030c040509070903060e15061201140403020d03061a090d02040b19031202190b040f21120606050414030c040912020601050301090309060305070c050f 76
    0x10300704090410030b03040c10001c80644114480d0b40040541d00c4441c0103520b03140d00d0b9515040c0fa40031074811500100d502000701020000c205900600d0032040c0c0c2e01c602c00500c10404c40304001580c900709006045503026003500050554280204440c2140a110001007503007d06e08103d440e407058190340941c0160887c40d1450840307500350140b00c004010f2100c40d10301d0b4206400700b5a60b40d0150321030041c80b41200c1204507080d5540e9801c00c03100400000c0c00c0c103003032101c0b48962680024651004513011802284400c0035980040b0311400c4510b400a0012001d0505035191001c980005204507894180c401c5048046030300e0509100020292143d00585100c0c07620300a80590041d1007150495800c000c0188115948502a03c0071508143d02d01c003046c3c10700c9030000303060140c01c0703055540151420820764213000c1c03c0103843d90540202d800355442640c030cc4c01072600b80d602c4408044c0114444401c200b01d40d03072095015540c400107600d800c2c0d40d1054165149810100c890a0800311507000121 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210025836 1250 210024586 210024593
    0x20a0c05060c04060e0f0307090513110d03090303050c0304150c050c09100504230901091b050a03080304030302120c091810030b0603030f0c0106090c03050912090105070b13 76
    0x75254109501844050a041ca007410050403005c2d0704000d6801040c00c1d50050300799803001c000b05000307000845000d001900e440610300e200803a55020688500d403900780c2140c00390a16200c44120035401d5980c645080f800c0d91002d4940340c1c04610034034164401004002240800444100b0440442c1d50352041145010308026140c44203000003240b2540030801480044401401400210341003030b1004034a946000e10482c45c1c162800a80700e0090b400802000650103043d8068034800e40b10b10a02e40ca502030526268000840d2030103407a4005040d204140003081114001c2d40d84a0b1091034003610b000300c40500c4180b010000d440c0e82083c5800410410460300c0c114001100081c1440d41084092605218240003c40d0a10000d090118078501040f4292410f000b20f40005800001e8540c0e50700c0802e40090081850744191082c0701d00d0002c0070903c0034030901400e0302a007a0403000f030264a0904000c10150b5101e18445070520108221980000c3ca2051905120300d6851440d20f16010b40c604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210027086 1250 210025836 210025843
    0x60c1b060906082d0a090b01081c090b0304020d0f080d0906060b0702091303090503031b07060906023408010203090c181308130b0306030c0406060e090a0f020a0c05 72
    0x205081d044c02d80100140c08090500d10080329207080000450300981c6820b54568014260118040d00150000d0004030387ca950004100d08103404096640500085021080b5442030707072030059604030a420000702d405803400082508400d400b440100c400701d2130640d143e40960340003600c404850340e00c1e04403480900c2014452000142180801c1070701c0c00b0050384c00100d003040000c04110005031a078405005152241c10100302404000d0222969106c914294003095a00c8480014242c40358000c0492094801d090040494000742c004201c43d011411403100c01c0300c42c040c0c0038200408010504580c5080c01e410510081034074600043e524100010b9407030070600042007142c0121190300703000301070104e881c2000f0307884190884100c41d05400c0d441c1859031445000306441c2070080504d804140010103100941c05035008500711140d402142d0144003d8071010300c00e4070045410319510501a00f840f043c80ca51001e0813842c0010b03240c0c01c0e8203c00382203030001c5260200007095440c522003040803c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210028336 1250 210027086 210027091
    0xa0b180406080c030d230f030a0605010e060403060906111308070b2529061c020105041505091507020a090501180b060c0109050d020c0a0e01060c1b06090608 69
    0x200082e2107074150b0940482e580307422105d001810040c00390410150711a0202620310716000020750296140218151000250429100e0342c0b982864540005050360051480a0305040c01810b101d040603d103490f100300034031040209030780254842c12604a50f190701001801c40c0d541d000d5104200600700a0303618904030184e00f2103240000100300c2c0b00c490b4078040c4c054a4036104030031802c140354082c1e85042101c050a030002d500d1040c07096040c41c0c030324400c00040180f2551060390304400d441c1401d2103407455003e48040c0640800c50403c030a1042c5280b520a4444080ba1414510b160451900110f00c1284040c05582c4200c00049004000c5203020568680100031000c010b00030b0754104810810508040140320b04503665403000d02d02640c455800b990700036550b11303000700800509820007a0302d83d0680c048880050141c0c0d140c4641c1480c0040614003610351003116007015a0800d50140e82d4828640700656032902000c81070101c00001401303010182c030b81940e0f44810103107003030030181400740c01 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210029586 1250 210028336 210028349
    0x30702010614130c0c050607051c0209090f071106102d0612091b03031b1a0408040b07080901020115080a020f06040816080f0708070608060a0b180406 66
    0xb560b2001400ba900e604004041e600e050360006041c0400c01002d82d410380714121300601d640211020400c1c19500700c0040d11000384084203112080e00c00e088031000300d1041100941c2e0140008010804071b44065041036070002003800c208160b181300b120740916000c401c4940a0281d0120320b0300344581c07a22a80d030b61807000c1d0382038001d0035030503a4038400140003e9a4000c02d0108216103c00c500c0c00c107001c1e000440c0e951381040c6051aa40c2441e0480b032816a01e5010030380100d4015003d02d09215880e00241c140b064110040007201d40242191081c0d850300030b00203440c0804144004141c00500100806002d40b1503c00385a03664600c0002a00355003242e000101306d10440001000078001c044ad00b668040c0c0e04907030200146807000001500d50203560421400c0d4800c1c500c04003401c841d6002d2103025503c0040480307600c1420159100e5585061b07000d107864907007002c003041013114050481580c0040c40105100c4038151100c598140e82d41003103a01c0c882410300c150310b00e20079050500c1100003600a = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210030836 1250 210029586 210029609
    0x270305010902120c0904080705031204080a030b01090b091306090213031103071a090a0315020c0c0931020405040b0f0a090507061d120d080a1a1011120307020106 71
    0x80e4200103a01c05c140204087d103901c1000444a00304030041c41111003001a4146245035400d0034101104960060028000860302d0300c2c505503d60b41c0614884012152540142c41c50440d29038107005003c1e411800d8450b99584070200070a41038490b00180c01007821081c100c1c442c00c1d2960800d4821948070b840d0150003a080785c0010300181c0000c000f003540c00d0381d01065550b80d83c40410041a035a12150303202425020101c04070760344403280f03900105003891845013143c48000301700d0108103403903400b0344908181ca500020400340c4c0400c2981c012911040425950340910100d40200742650011103049644080490800110283d0501c4d21a0043e00d02c1c4001c02002c01240e4480342d4030305140c0a4030051019209180e185d42d8a0702c000c130b04103090090031100580c003400d40b0855403201b00841101c003045040000509103100b900c60a00781c030b150401c05c100311081e140103002d50308c401c01010760204015004500452041006900304640c0b01c0382600703642e0320305414000d08640c02600308005084 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210032086 1250 210030836 210030853
    0x2909070302210612060115022e05060d1e0c06020c030c0114040909150b0d26070f050703020906040b011403090327010f0f0c0327030501090212 63
    0x42c6401c8038078950110408107081c00e840c1d40c00042e88480e2480081d51445c460b040000c40c1d161262010460588a150200c4002501c46981402803103080c80c142482e02041d0000c001030003601da04041c0c0c00410141061007250034a841b445a0b06800c42e00f1030072403504c0400158108080b191a0000a25151020704510b014400c00251501e443c49a030b40d041104070420a0051401300c0210381c020302514000f00402c450514140e000c15500050f605826482c01c500c0c0c1a11b420180040125940d00c10300c448080c1402204026134080000038000800005202d00703400a0b420300c01d50503050707004034001c01c005072031803041004041000b84100e02440c1054494081c40c0d8206078498600348120720642d0300c0c0c1d0f840300c0010b4598095420a0203034000c400d940e40d0000401d400810620103800e070380314901720b4030b107410a0394500d0140305c0c800005038803100b00e0782c0842d20821242c0e4500318040c5034851484040c0d0505034224089410175245070350f46150542c1145090002c05408040d02006041000d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210033336 1250 210032086 210032107
    0x30203180a0e06090a0b030a060501030c0e0103030807030e030412260c0a080306060f070c14090103120302070501090b1608060405040507060f05070615050103200307122909070302 79
    0xb8040030300110b01a1684001013007507080302c1e4000504c881c00c0581200d0283d4400e040100244c1828807096500060011001c9250cc100702c3c001c074141ca4040d101c50496895464003100180140000c0480c0e5004c10b01c400300302061002c00000c2401d0195600350310020400c002d0304941c00988020b03000e00842085184003010340403940308141c42d003080c0034a442e50359040200d0140c2c400c4403075078440d401d40018050b0401c80e841c4608010342c0c20203078007005100c140b80107000080c0800e00029105c4c100c2031208806281c800c1c1c00801c01c10348918000300e2100c100ba41e90507c1d20f034040d01c440f510030714440e10404031a58807540d129400181120148120b00300350302c50ba07071200868051300c810000310643d41e10b50680a0785c100d43d10542d11010030024000003180f041e812403014020240000d0905d0210503c402d0383c1c3c0c0b0152805031850000a246840b0b2404c10782c0c09101a000c0920120388920200481286400760040d0945415104141d019007034002c202004000805140600d84180a0007210 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210034586 1250 210033336 210033359
    0x90603112d270403020607080c0306040b030c040e0c030d180605030711031204120c030e01120603060203010801060503010b06030906010b03060d0203010504051612020634030203180a 80
    0x1e600980141c0c00c0c00301841004240260340d050380380241509a441a440300c841c041442d1407085000c3c1c0c1c00e0f0341007911000c500b242c0041301590544130070881480401d88a01d041c1d0b10007001024010219500c410b0030401180030764a01d02587d800c1508001004845410140803030010300d1f000b4030340b100005021034416026015940220010000b0210000c2c070064040c8a1400441100c40304a03a26219140c840b940b03d41b00c1228101e803812902e02000c104a802008081e5419900d500c61106038800070380111451402983c006034807688a003400008119a84001e41c041c01c0780c5400030514a061105060958080c000042e01807201081005903207140070230800e06444582401c0c0d542d0340c0358000060300c140c000348030280d415441e15040c403081081c00240d001c842c50420030040d40080d581c00b824542c01840b90b1010390450410002d4500520342c0d054251403450300f111a0454800700040044111406504201c01607840043c0310b045000400e21034016070b9404580c41052141003045107103a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210035836 1250 210034586 210034639
    0x6011406030a11041806090f0e031c151e0b070b1609030209070804030801050a0b090906040608010603050307050f03030105131a031b09010812030403080406060f09060311 75
    0x101035491811a0001c1441d204580040102e120001702008078010060010401807084004d59894003411502158050081040d842c540c7d001560030300780403044041c202410303c9032800500da0f440742044000d02c44000545c010b0a072440d03614507400c11001c2c0392805c00a0340d0700b000b205a44148400c1000513840300c1c406602006144800a42c000103900c01e071050703409074100030740c0000380b1b00800204581c0800a1482140255100b4485036610414802004a18080c500340120200a180481d081c904c000a801410140001901c255220440d60845080f078100700d5142d08000395003000d125003041840300022100d1f0245281d0b500d02000542d4480c0004915403443c2d0f00e803040c014004519901049a1100c05401c0e104c014a9175418040b02450f64950725114102000c00840d40c2031000038070300c8248807082c00c01c0385140c42d1506d0513034903040e00800c2220700309d4961034040703800c80325603812000804141d20041086400d51a05080348142410f07028081d01141600e2004103048020180c0e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210037086 1250 210035836 210035851
    0x302060316170c1911060411010f030b010e040c09081516030e15091501060503060109060c05031624091401050411041d030c0304030b06010203070f0219260601140603 73
    0x2150700d0100d009035140140207040c5e9603180166020001401185e01b03403c00c40c000241e03180c03641a4a81e00041d0115686540018001200020403034094245544080c28906440c07c01c001c42d40d0741e8640c070300d20b040d15061950800e445030500b0301a541c2141c2400112055550405004695072030034125602d002100000c0c4449660340c0110f41c00c10030910142542a001c41d540c90515030711030070082d00c1c0d0360084d40c8941c00207031403243c00501c40703204d109600d070220740c0000a103203880c0704164100408000a034041e503000403022280100c601200000080070902d503100814082800d081c8492210750b142e00c0354031940d06010421002507a410400908800101c600140c0c204440c1081ca81e48020b503108000580306c002482a2030240000162040700d2040707444179a581da55000482e220700a16500030208601c1c400e0000040c946840d004140c4038615980400c1513603103200302009a13100b034a2600420f11000650b2002070b9050200300d0241c4040741e106842c0d0780411000c5981d5101c003d200c0c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210038336 1250 210037086 210037117
    0x60105090f04031407060c020616030e06060f01052502040f06060c02040e0709061403011518230403050c06010e13060e1204080319080105010917070302060316170c 72
    0x129815213600654010903040607080040322240b1801a517100001e0b40c5441614007254003140180d4464041c4035001c48040c8080c004170b4880350284840e01c8403083c05103050080910000425102c0d5201da4000090501a880001c01c210b005010446200000e40a41141000741c140803441c0c0207180da0b06101d50684000401c038044640140c1451900c0e081001928203140c0d001400c400101c001c2d0303083d460118001c120282c070b00e44250030f090300903114a98840340010540c05c5451519840302c0602d04100000d01c10b01001c401580c18101d41c201e4088010640204194226003000c20040c0c1c054034604814810b203040c01c5c10041442c134884207009259030346501040700c20b80400d0180110020301104c100f0340702d688420300a83c0b290018401c4074241000c40c0000201035200d6600207040300e806031116130005003000c0041204103143c1c2a0643d05c0e10854500000607180c640003103200701c103440c6c4002c1080c1407404000703101c007d2003140460390002101c14080303030004100071a07605851040b400c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210039586 1250 210038336 210038357
    0x3c0106140d061b0201020a1202130b2b02071104060e0112050705120c13110301330f0306080102040b0d020a110d030606030606021c0f020c13020c060105090f0403 71
    0x41c00240081c0018003030300726040f96403000b115130150090300c408a1140c544140c100803004041d8109c1c0200c905840d03041100c00d004210405a2000400c00c41000d081c3e4a00004200209004860a04c165426900f0703070000b8400b05101000003803120042c0101c2d4107108061600300040003800d410300581484107041d109800c20032504004242c0180b90260400103592a411141c540315020341c444980079540d0490804055503051251041c1c2900c021691420742c1d0820940c852400d081044401321400c2c1340c14843c01c945207084042c40d070308006940e0290849400c2c0d000500780c626903405000307580c1c0107000c24003e0f80300f008161440c20303040241c0162107a95020040310342d00c1c0341066503440c0c2e000d11964211700c40d81c540c20036002c1da8a01e44051003510354484003242e41c2c880c4a02c00f01052000038140d199242c0c41620422480c0703144e4412548415a1000007484420310800a05051135002404400c0b0740e005000350390060504540561552a000303010000c4004000c05c01810019081d80c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210040836 1250 210039586 210039593
    0xf0f1602070906090203010e10080d12091a0907060f02030711012102040f0506090906040e160810050c0a14070602120c030601090b03060d030c053c0106140d 69
    0x201000600d95010300f0f000c41591488144001c1d402030143e6543c2803807800c001005192804506412200040000e24143d8905401121b070b0700341800480f4511500e03003103d08041074181c10f4080095804d01500541e5050a411031751401d01c2940c0400280300042e0f5030000e5003500032096520003074001c041540480f04280041301c1c240c0e00d141307080c0714095400d01054201400d0758050000d5a81126600c00f0081d10340b005c201d001d014070b80344a40c1c0324442800060340d905058100302070400c100c0044502600305180f555520085503080282c2e954061103130304500b102ca038015260440034008500346041d910307400050039083c085540607a03810000900a0401881761b04a0700c0c848500b50740030f04203080c02101ca5080da130040e140760340001d10900c004200380003d401283d0040c0300082080600798015901079480c0740d80d40b00265424001d45010590304040715a61181807681c0083c1041007010b19020f2460060b19003503903021584c58404144480c0011980b60a48a441203504001c400c51902c1c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210042086 1250 210040836 210040843
    0x402030a0803010b180a0f0b09040f020d1413032007090510030b15010e121002030403050702280303112a01090e0f0a0b030f1902090f0f1602 62
    0x3900500710100000009003848149001c3c040c44d002030525900712403001d0003006024049409424000c04500d8800c1107800740307501c02049800e41c041c1c030116030803080d800d4440484c1c102e000d103031481d640c0311800c02c90418054030200340d002800351200f440345a45510020f0000d007200103541540303800c20000002c07020040007054010108004d0074002032404c5122100140e44502c0111a400c00d8517011950312040711022110f1032206079030b085408010340041114040840301e112205004210000300400b006000031880345001c0d4803031540d01ea44a2060185090141e810700c1407902d451a003411440b414004400d040344d40524000800042d4541c8040c04d000c404103c549042079021092022101a0803050008130f009803071301070826564082c032804503072040380c911680145240000e1003034121940182110344001d42100c00d41515107618030300c0c000600030100341c0d01c2c0e502507091003145003080c0056406034a10121900c18208000c030f440e1790200107014801040031039214002200e00c00c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210043336 1250 210042086 210042103
    0xc030507050d02030406120203060310110702090a0212010f0311041a06190908070501050f1e04120c140906010c03050903010f06050306061f031e09031d010807020d08040203 76
    0x100603a150400c1c2c014019540340c1c0184140008a60301c5401e140c2518103510030b1703900c103a0300a00500f00c0380549540c0080180f20f403100061000c9028020400940c8400c6000c81c41040c2c0c50780c005980303041c401e0300c00c070207110305038013401071059610002d00000b58900d0580c120554165000b050030038049403200350035804144401c0c2c03c044041242400503210002c103100d00900c940f1401e90103034880444035154132042c042d1f01e0100e07204001c81c40d0401380113401031082d0300b10300410310351042d144c44d100352841e885648034421814018443d00c1c20b0140d1114000f004101740364038002c00059400c0890604100201501d052120a003032000503d80036800b207aa00010080003008070710683c0784504010013003406024000d200f1360700003519a0410690707452100c0925030940d245184000c00c100c000d040c01d021800c1001030341c6102c0d101c00490500904070340e11301c40d40350301040221500c0310845040e1a01c84480c1004411810b0150854010840000c00301e02403070300310095951800420b1506000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210044586 1250 210043336 210043343
    0x80c040902070812450d090602010510060c020f0f10050d061706010b03070e03030f030703230112110604031a0c070506130f0b010305011508031303030c030507 70
    0xb4200080243c080c008001a80701ca01c16401145c030b0712a00040c4080c5004a50508465102c1c0740e4120704001c10003903403800c030340c00561403189521030405900341300309400d894000c51024103091013480d80a004055100c0c0340442d581c2d4a00749080001843c005050001074040c41c400c41c83c5401e542c46000007600000c0e0082c0c0030111801310102d0080c0035a201700302404503c0d20b0442d010600c94090314406400d554a00b00904844e42004107840c0c0e02d0740040c0045090100444d40205140c4080c800ba0411031a030850342c40e05e03454280c038041d041c0d071098605e62150f0a142d10400300f452102800013410b444066050240c3c04005180a100241c65000703065481803000c0740000402c2080b5010b81e0704000701800c1c8154035281c91103074412600070960001d0154003d00001203542d052006520b410300d0148500309c0c8101500d0b00d588030702410a0300261950703519840c403030002000d005802d40c002d00d0321200a610304150b402c0c4a40c000160b901008080002d420809014144200d042c0d803a1a500b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210045836 1250 210044586 210044591
    0x50f0c0109031d030303040528120903031d240702120a05070e0702070603180204090c05010e011d0d0812190b0402120f0c13080106141906080c0409 65
    0x112402c0203001c504400d084040e4404907500c050b00e283c100030041c1da00845e4880000c0041c410321002d490988070780b1a000c2c5400002402c600c0300401ca003843e104000c0e2016072503032407903035044d400c1c01800c1d14464445142046100002410103441d00d0210300c6441001c80b5a8401f11010410020243c0c81201000783d40100c040b2220110810080342ca04200da10440c11910310301c3e6100a55040d13010b04a552102503009400100803481c00394124500384115451640802900350707000404030384a8003c2520504440b4034144140d507001942c81d0b403182000d0811400151000c40e00c2c80c0086210b80c2410300030000300e140801080301d46030596125859889074040946022540c10084c1d0308940d01e0207551908101c0d141006062510803505000445001c0c620682d50310a10021107160107400300c040508108607072001c80440d070300d040025062202c0040f400300c0c0780031000d0f620b45c40c002c1d401c648120501443c02c510121080001c1080395100c2c204500c3c81d07035032a040c3c150507016941c84a02802d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210047086 1250 210045836 210045851
    0x91603150b0c0715020601060503180309100518090108030703030e0109050a1a0f10030b060f040e010b03061e16020a08070308180105040809010507050106030512040e01210201050f0c01 81
    0x51011603c0b40680e2460001d0413841c0222803c126036618080c032420011400420100340c402044900c2070390207100420031603140008260100d41507203035814405000036004a102c540e8030003180c8200c1c05000c000c9603010708950400703440711b071a4814140f00905240d505c54001c01400029009201e0781c981080c10303500880c006040c280b407100d1440c00002a081c5d200e500103106460f0b0780740a14040c15408003445041030842e034030741c491540c024100d0340c1c1c0170b4041c18041005030344901031814034030704030750001c0745000b9000306051420102810032881c10110801100d64200c00520031940101c5540c01c481c2d2000c04201d042e420075520320340140c0101400260041072580201d0300a0045c5034001030310340540380c01d000081c01c0b69801d43d8000d00c0140c0030424010035612460180403280e000b5800060000e540360b8031207151500c0e49080198101e0040350401c2440c503440c00d07031030042042d15024410318800020f22001d0455269000341440400b00302c0131170700c12007941502c1810000900820411 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210048336 1250 210047086 210047107
    0x2070803030c03040b01170a0f020103180503180607020d1209030807080a1d0d1b1d0402040b121207030c0b0a0e0f0304060504090908090901060509030c091603150b 72
    0xf90701c00c440a40e01006000c00025800d01400000452801d8401c00f8240030700e0160b82d41101c501305810203134101070f2200303071220b418400c05c00b5001c041ca2040004580c0e03100c0740164203c0c04138442c00120b115590034499031015841c0c060715a90601d0703000660400100c0014805d031052140c0d5040600115004510308003003040000044c8280a942e480300c040b06909080c44c030710104030348007440c0e40181d0b411584c2d8001900207141c2d04009100003510000607516034400f0450380042c40784a00c20454020305006c03d60406d0710542c00003950545566200c0500a042d00742c2d941c80b84a891001d03608001003c909052042141d50355151b072010743c00c3c480e4204601a00054442000000d12a01848201d148050f0300001245c04490540d04c607a4242803810b501c0c003004002c09981620406410444d014050396102405800791080ba101c05840d40c10074414146021082e01c0300902a520000502801545a030b180008031000c619000c100041100e4540d00807003865800a00c4800d804078040e00503 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210049586 1250 210048336 210048361
    0x1090e061c080d0b09070f080c0f270a080a0f02010318050105090606040c12020904060b0a02030a091e05092a0901080903251a0103030c05100905060a0c0207080303 72
    0x3030b49a9100f05020f90b8025204001843d4000d982560100e00540c01c61544203010b00c60030381e84003a0300e2a045040000c40804441594403000c198001e000c2510050b07010000c540d2281152041c05030385d40c0d1030460034402c0701955440000005002d02070900702003821a0b119420100300d100e41c5604001002000d8079080d03010303020541d02042103019940014441e42054881c24450580c10382c1c6140c002d109001d6014000c1d809a002d030398026856400100d0141c260030300905c4008000d03801980d071001420402040001141c005110f01c030000078000d500504100c440c8030039500c00715405250703500d0b08011602c03446490500d10400001c003402808064100740043d005012080c0c80d9603041e40d0f81c1c0b000d207070b80301d20403402030a90018a20150455500141c3c1e44a41654410320f000b28070042d40c51000d000041c1d01f64000c50024013074500744070070003005000c803031a980b80c003034014441d90b9141e5649603142c00e0014140c0542076600d0192054a51080181200600685c0f0980340c0d2414908002e018 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210050836 1250 210049586 210049597
    0x3090a1203110a02060a0c0807080c06010608101203050f0706050a0c1d180705040918020a091401060518041e0e0708032205060a090503010f020901090e061c08 70
    0x81014058100d07031208000c20f6481010307900400c034528021540c02c09407802d201c800400e60702c030001481000300280d9a0030090480e112014000c100640c0340200050511500074401041110f01c0001008031814185031403e9850b4142441c544607002420101d0050140c0c20340900414100307400d12103182000d81c0301c0d8600d10139541d4ad014485c01c1038010380c00200d2840070701c613401408211a40d00811102540380341c12450b1403038550302d032aa45001d100159130308176841a02009d4030401d00d030210301c4d1201941e030003440500018840309141c10b105d980b80c0901403150310180711001805406c0c1c154443c160803a46040240300b0060328404455002c2d802c04802c1e4035a40c002d243c005000644a400140002120312070001186803c500070008030a004851144181120001c000030034a5a191405803100c2055135549250781450601010b00351030403140004800c0388100034091041e6880894101030701d488403035441c51529160040755048884810b04002004482042020010520028074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210052086 1250 210050836 210050843
    0xd0b10030e0d18030b1b030907050108100608060405060a0f080c04050a0e21040e150103050c031006110f01240603050601080a0b121c090b0a05040509040503090a12 72
    0x5031510001142583c0e40111042000c1a059110354108000741c103000d4016800750907120280000038117082101120b8000f42d458900c95008040140482e5912000c400e510040c1034011f03181480c68420003420047d0040d003001c0c02070b80c5880003d00d80c0e07112004001c0040000301c8115030080e58408078151500c0c81106020300c65400c00c0040b848201c9a4041d4480101d030403405400c624405d07850300013000742d407840c0103000008240400140e5041e078001e10340c441d11056455480c0c40c10384100040c1214001007440f9801c480500c00c0c03080e10020302c0502c60a880181c10401e841810070200300780303406581d0317152030159070a1040301203450351007114281c040201c80d00c0c82a130303807072b1141c01c00d40a40703800301c0e41c03180059442d400294003206203402420244a0280c08560100c080007500f80c100042e132003400500c401c031001c420030b41d40c0e800444d00c4000c0030001b1240703040240c4d40a00800c94800ca10480d48a1003101000ca002d014050044418103c00240040081d0f0b0380c4541e04054103040c100103a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210053336 1250 210052086 210052093
    0x408010606021c090e18060406020306010201180309050f010504091803020d0504032f04090303020c0c04050103020907030e0f1902040507180e090c04140103020f0312040303050d0b10030e 82
    0x501100039161040410800c2d1280c0c0902c90800c684a000e01740010510407550b00e550107400e0040303506000c094015405a0400741c0c0e2481d0a0002900f9a4100c4070540c80742d1081000020205c0d5120503400140c034000c41c0d04c98007124080c00121001e015503041111a689850071241e889840443c07622111407080d02a1036005c5d540400555107401184801380841890090940b400059a0141c5200040c8415041a10310500000c00d01300c0c0c00e81d49007100403030381c002400c5141e250100b2618040c1e000031201484190b0566020402c08000a400582030680340c1200d990800f4040c40240803c0382c607042141d019602d0054480701d03201d010035003a40030324a05004110b545100c0d40d50f1003038002200607a0304e9460b203031500300d00300c03000c0081003260749001d4021001c01540d20b82c001c0d1840400901c070015620750450042051700386074031003a244280c0c0442c6040c041450f4000647e001c40b0340504169407220740555410018118034404c46a2005014201c1300c4201d8041d44126052809241203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210054586 1250 210053336 210053353
    0xc181c140f061605040905150103050604060311040b010203090915010f0912030c03022e050609040f1101020a0b0405011a040501052202071b1409070503150d08040801060602 76
    0x241c0300c0c91208090451a00700d080000d5a250030b14100c00803850365480c0c03851601d6a6408480300b1640151441d04120340c9281455040750703418065950814422241000710307510310b40e51803811000d01400207001d203407141581e13a082c1e8020710a0340c14a010142203e1050319180c50b079540440a81481c5901040703098100480e9036200304e00c460291a040915941d03a4030343c948007a14000e404440460451260000d80004112004144009080394a200801c0c1040200310030041e42c1c0018200b60140949204210109105038142005103410040380c030100c2c0e140e000101c3c1020b1030004090301282c0304109100030010154032100508030503000c4c01000b200c005c4100300640d070f002c0c880d840d4002c01c00b14210f8855458032b829241901daa0050041c40c4c48401c0d075032113140020800342440240c3c50074404000401e50311100b46107a440444081ca56071500c82405001804090021404029805162826601c500d54013500e42a004014140c55543e83d01c261030103004180252401802000c07003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210055836 1250 210054586 210054623
    0x90809031203011e14061e040b04030510020a171905010308070b131101050d06080d0e1f082205161a090604170a0c06080402011b05060c181c 62
    0x503070815100c0d117840042841c442442001150340115607051031545801c0300364020660400c004100620503601c420742c459286050140c10032014425030383c10b4500402c6181122a40455005604c0c0e154500e400d030300703031100740d10815003084544d86041414a840e0022040c001da86010741603080c071a0041c001c140c2d6a040c00110000c3e403010004290844102d0302c96490740c00351001c0c01c00580b494800080c110342d0380b5501841c00105000010218400742d00986103410f00b80c0044038803280059180d000320302d50000082c800f50300102801c140e580c0610803c0300514220441d00c090130740080440701c00740003c51180e150090107118401001802c0ea48001c03d0034600304c162441101c0040001d414186000e00c002d01030781c58003d10b041b0381d0044460321030008050841101c040e24980e650840c5d186010f1001510202081c0039590402101341c0291000807800075005900204030030764191610008a0702215401900c42010351200b26098008021350311008081846409608175603d01e00006d0f0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210057086 1250 210055836 210055889
    0x30907180209010f12020c070e060102010c0221090d02130b310c0216090614010903050d140906120405061501050403110613060e03060603010213050409080903120301 73
    0x501140850440c08013111064002c0c10141019248402c01601d000c155500240c01c240c4180c21242c00c5010389401e00c1a0b0f56030900c1840540079071030000305100c816102c000480c036088811600c01803900000d100340552541507040c0c40c00b59000e0072601006c40e0303280f80350001d01542581d0500a08603030400b071038848694408410064969030f041266090003919420207411140c01d03c0b000d510801c040341c0412140071502d1801010000c82c001003075814580e0528024400502180c10050510000c0c000301e600822000d030302600d41e041202c88175414280d40115405a40e803501c2d4400703000b0401d6001034404c124400d1040b40f145c070075140c40b503460041070f03015000325458a40c0050410303c014800107003031007921020380c44018034150500000c848e400700d002140d42c2003003001414400c0c4000b128101001025040700c012002503003000e41409410a02c0b0354140b003090310481d15142c2d0780f0b0900c0254021143c04110143c2511004489903134000e0380b82c1e2013886680080c1c112804c80c00d151280b481c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210058336 1250 210057086 210057097
    0x6040807061e0926070809040b060a050703091e05130b0406080304030606050301090f0b1032010c03021c090b0f04030b1312030b010e030d0801060f180605070f06020309071802 77
    0x850224140381756525540101d4000c4952580c1103a0703540d070100000c0d41d0306c0c1c010f89030701d035a80d50300d036940c1d14054034005101000355407103c44101c0554058801040f820580142034900a5420060011030035078282c015113905520300760010301c1c1210105012101000601c1520b0007400c00341302665640042c18226203d00001408410403c050f9a00045600400d0390300130480c1d04101c10102d403500285096410a0130706005201d0351014505646042d0201c60382c103c400c2401d055441800c2610f010351070303003500a0100c0003440300c0703459002d50b50b00601240024004e0080440c0c2c883c10040c0030b00741d01e940140415201b02540717400103940e84001e407507000c00045d8004490440c2850100040e00a00003002c91141400a40b8086403030300d4504011204104150344d40c0c10f0665450710700d02034400c2022601da00200440c005011181100c0c0000380300450f10b840c41c0c01036650030541040d0b06440c10400005000e0b41c00007003802486000019200d05135225021904001c8040c440000124803a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210059586 1250 210058336 210058403
    0x1e01200c03160b030a111905070b06030607081504110301030f0302070b040b0403020f13150e010815041202030c0a05010203060f0103020c0d03051f0305070e0c0c06040807061e09 78
    0x2000022407405c06600b041541100c003c400504140c40b42c4401c910200f6140c02c20700004001040b01c005001c6100e68141c0c04c1201903015015a0918402c000c105a1000744031100d018004160840152269400039100000303007180c16880c0e5843e071030080681b2400d400180d0040c4120f10f4086103608400c02160104c400d41423306150500d16800e0060502d6031146080e4403100950300d000b01c034a5140107400c0c00021060070502c0190034035548411202040e04841000c0d0321420b00343c00c000c05600e52030b540080d040301000c141c0c81d030403a20803131075407183c50b10103a500e00a1281d803004102054001e180100000c840e00c04000320b44000443c01c901a103400e200a41d4061302e0038251580c003076401150460240846001c5074001101c1112400c2d206901c2110240c0c4064420030178a81640e80741380c2c00c21410306106143c61034900c0e41580e103810251000d0a075a40014004c010000507a001d4501c0349010050f200504503801c0072440208048441601d011081d10307200c207040c2d80e50301207030341d0040030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210060836 1250 210059586 210059609
    0x60106090e0f070504170f06090c0a03080c190b150f090106050a0c0c0b0406020106090b0f1002010b090f010303020d020a03022109040f0606110105061e01200c0316 72
    0x4800b2004416400094102c00c2404000c00004c9012504502c2c1c0c0a894000d05006040c1036150003402460000014039051a58210300040420b9130f071581150300031a90040040f9481d40c94000c0300c1400c00340c130b64100300702c1d801800c14070504110240b04110f21802041240d210780300d100400344049a01940f820a80c842d007905d00600c000ea010368050f29401c1c82c1b51912000020250b601c0342c41a180b150062510400007040800009909001c1c0d0f102a100c00d880034040300b10b54002240c0e61014011480b4401c41c070841070410500d10035405040b4061005001b0440c505100103002c2a08000b030000342c0040c0030702002e4105035400022251030311640b581c000e0440c11000081485210b880104004651004001c0f400803a982c60041b0300d552a9901c0300051424034000b000703401c0c1c201003800d5440300e03410f000800507181d541c00c208a007004d20b91030390a01d042101e10012550b4600140d20500c030800380c200c801ca035032000000d4180c04d2840580448280c031180009030f0340b140141e8403d03000c4128 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210062086 1250 210060836 210060841
    0x6090d0503070c050a0308180106120602031e0a06050f01031505010f0207080102040b04062015040f02040f06030201030b0307080a12110609010c030f020f0904051b0c030c060106090e 80
    0x61080000390b6111070540f8003800106100da41d81410090155030580c00038000200384080b8060f0118041c80c00904640208200741c500500c041d1a0440c1c08800350903d82d010001540c10800310044203803115018143d9607051030600008801000507028081c0912116001344216502070303c00c0d03003028142004103501d1146032a00446d080f0303103440e60783c1d0214002e0143c0050380c80001d0015102401c101d004041d22030b41041001171042c00e2400061010b00c41903104030100c02004a0030407081c03040313401c0c0b08000d0b170355a0501440385030030140001e4215180c004c00b410420314a40c001c1c2d054038801d81e006d025000906040541c0d0785918091200f40d41c0252a180700002c0b100303500703040d14241c6070800c032503023001c080d81c4142441003c403840030060b51610607019040d5032500c00d1300c9004903e0042141000c4e49240002d81e18014020b54078025503840700070500d520111154140780c84802d41400751fa65064940c815143d0b00080e104d0002841a04000704805019920b4041928030840c00341c06140d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210063336 1250 210062086 210062113
    0xb030402040c030e010e07170601030308041e020d03110d03020301050f012a030c11060f030c0a0c14031b0c0f090a0b04230a0b100507060204050d030905030f0609 71
    0x1080500c82c48414107541d4400003e06800a002e08903000303040f08040c0c4201890300c82508814085855484100d400c810014400070b5004080030350003a8201d503405200c805110148860041d000c60040d6010416140000c1015803000d03100001000140c2a078161b00d00015041e41a400300f0f018035030b072200c19800c14000c6944152542003000460122441007603400240900201c51032400650020b140c01c181071040c1314880b0300066104900765807961401c05600d0b004841d038000981000d100c0c5d400000c0c8401101d11a0101040302c6d0340041d80d003a482464203403020f81e80d500001c0d04441c0c511100510096010000ca0154650f030f20107840c0240070415501008071114000744400011640c9070108a0030ba1900d101e000c1d5005100f031094a080c803650351070310094460082494101c14200314400040343c1f503080101c030a0301100e0616603142d1200c0c1c54200c01902558000a400419040081061542c40441e80c011aa0190155901400d030341580d25154078044901e8072240e403000030601c801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210064586 1250 210063336 210063341
    0x19110409020402161a090303131707051f06090219032301080d03050c031501181a0912061003031218121d01080a0c030e0f0d080a0203010b03040204 65
    0x1248002d000500d080002201e092024140d80782c00d0b03a1140c00c560b41c201c02c1d81d0240c0041908001004025421403800d44a14224146a040020143c000300350190400d801d84000783d4040c01c0d4004284d90446420801031507050210080030080c03281003070800140041d40b031003103540325900300d501e0645102d031411003580035201c0c003008001a81d03002039512140884022002e40079204602c0a06070b480840c040c01000c2d6280503040740075001c030800502540068903502d4147c000400e081c45c1c01c1403e400508900142c1460b801540a000c411a8111035503108400800598400712940c030100f004038080e10743c0d0343c1411240700c540d07503040c61418004207001d01404c0d00c02500c1c0e000040341c5602d495640c288240700c0c60b0000c9540a0640c41e0b00811190040300640c461803141d000b0074425400700340001c3c224000900401c0115a40d490641c0c0001c1c800e81102c0d215071400400c85040d010502c03c11980c0300841c0d0b0f1342c80001889040414001030305030003264100c03017403c1c038201d08545440c0c081000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210065836 1250 210064586 210064601
    0x70f050f031302060c010f0510052d060a030509070e010303080a020d0f020c0a03030e0d05040b13080f0604050d0305161206031712060a12080a03060812040602191104 73
    0x40b1400602e01200603a00c0200424103c1400c8001140c0061b032041c40e2000d85401500300c84616807100310612458885036584600f846c1902c500160601c44210598401d9418200c100e4101600103601c100741500368100500400e5600704441c03102c1e5507000260443ca40a0000030001504540801c1d2501c280350090074182003106000290846d8402001c4102da001c010f00452580081c846081407581600c42d295070000514023415150741280002400c0b4815806100c0103494080741e09400d04140301024030180002c202260000d00401c0c1449503258000c84080312180314a012105001d840b90003080e016403d000c2c815001101a004103659101000309004685982c1c0c540000116140d0000300782c4030b08815121680d07d00301c0c015520407001c8010034890042d89100c00800c20100e01e1a82000110340010145484000440045003d0550f40e07000d000305214517160218020411030040c8203c0b5401d40841d00c1102004450001c0130409081c06002c0b08a401c81d004000d04040e0040d88 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210067086 1250 210065836 210065851
    0x8011a09060315091b25080f0301030213180807031e080a0b010206040209040305070c230108150102100507030f0510030b0603070b0306100516060e06070f050f03 71
    0x181800400c0000c51001d0300200c0b400c00c0c0f00c0340100c5100f00c031800e009a049030450080a00842441c00500d40d0300d000344210740c204510003101c0032903003510000d144076580d0b1055006109603601d4140d2004801d40c0c1c0c0080c04240e111b0103c0080f100303a100402d00c0340301e0240e00e65130046c4161a21070344420711030303400010b070542c03d0010f881c259003c0c0e01d100c405044090032041c0c40d1000203042c078490300411104c0144100e4150360004003807101599400c042687d11640c5450a66030301c1d0340e6403a08805141103640400c1c500c072810710558a490303066030041c0360041001c0c0e0301c100707840d5100d040211030a0224025240560000c41c0d1103440c26241e5002207a2000f507506002c80d0035030b610140c200441d541100d8455a10080e82d405008002c00e00768166041502240201031070307810841e8806040c800909420320805210041c0000c440c020410785110039060708040c9154052402c3c900d0180c80030304490a0301e4003c640001d000c00e80105103d40c18001665202030810354000c0c002032141d48080d0055 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210068336 1250 210067086 210067139
    0x9020412020120191104050a0905060c0406120911030a030504180504020607151b0e15190507020a0302130f05070203270d0209130506070801030f0602030604060e15010e100801 77
    0x80c00c9a16607024841c00380300c41e00f48c0041d5000960402a04040019010002110b0304020401c40c895000e42040500c2a210301e0004240105e1b103002c810308a0b1046440b5098010540000141070304040a0400c84041034241000d100c240042d8070204c510450b0002d5200302c2c188070100100d5481001085801d03056100001d295543e813840c0031048045d101c42400242020b1042042c0703007051f85c0301518101810002e14284903490b584d605222050740d01c80003c018001c10000255951182e041c0f004540191100321022500c903140d00141a2502203604904e0401e0041050300748004121114001d00911000029260791001203418034000c4102c6d41c0708102450590141e542c050449008a407010f12079101052113142c010300b0044024090400d2010540040001c41e54140c44a02920341c8100016529580e102c0014024170b00340e0040c0201c407105504003c0e00c44202006584040001d0300d503e03040e001c0640810203168000b120500000b120b41c1d0040040042c52800b5107108408801413 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210069586 1250 210068336 210068363
    0xe04060923010e16050d031101022223060a0518130516030c05030402060319060b04090e01110f03090a081309050601080609071101060902041202012019 67
    0x809182600840c40c000640c3d54900601d91030107800c11408100d40081008203006500d81400200403100652016051000300516a84400001e504803000e200008405541c501003080c200d01410101d4018030410040007007106540c041884560351b201030f40180803500c0d041c0000c00454a43e00f1100c40c1903081104000341141c83e640d01071040160000346000000d440c5082490f890700c1052410040042c5860a04e2034407410f98080222507101c2c3c1c058468550b02e460b0100a90107400812800c00c1c0e55034035060f0082060048000100115043d0b00ea00340301c3c03031409201c1142218001480808103080811950a170f1603150300286511003103140075200700e0b2045407607040c5146d01406910000081c0104103100309440c6104480d040710003031038a00c45902e000d2010551001d801350a020910045200e001c01d0800709410040107000405010b40d2074bc0d40d6600c020444650409040340403501c04400d54124502850b10900c1104006009040e004040700e01d540000200d080296401c0c0005c604 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210070836 1250 210069586 210069623
    0x501030c180801020909010e0f0105010305182d010213120204020f040f05041808092b0305070611070c060509030c0a080309030d1805040b0604030c0e0f060a0e040609 73
    0x74001003000c0400541d660b0114410045d05140503004001c1d2001480b041c0030495080402240c1500e13000e0a0008080e240d0211786106004000310204c007620a048900c0d5208120043e21740c100200c5800011101a031801514240c0c013072481c5540800018a50412045010f0f62007500c0040c0040d00040c42c0c265621410742e1117030700540045070002d207440c2c07040119003064030984030503007150b280c840b681c10016500d032003180c403491b03900e076106883c2c1e0a0b018100003501102840100c03409040380c2101001843e0260480e00a45801d546840c03411131b10044600d01300040f81c5025622200b114982414400141c8041d001050700982500c00d1041403040c0b51900002d03000502502002035488140700c208040c07a051002c0050b5080100b007030b1442c3e940c1602c00340c003903060b05c00444002c929a050708010541901460f0b03c0600724840340365002400c00c070800780d01c0d070045030300c40e445c41c0d02030340c0d54420b01600700060301c141003050a8200010f0b000c524142e212140f207078031428014802a030f6420 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210071942 1106 210070836 210070877
    0x6050c0c0d1202211605250c090608100e0a0b040f1a1e0a060b03061203071502090907050415050d0e0a0507051806090a02031816060806040203040c0501030c 69
    0x94087d0421030203d400001170b00d91f402d0308220041e0344020003656254604110005140342080354080c0d00e00203d80d000c40d0725000f8805090545842d56007008648a52400341c41c2d020601405088000182d45194020010003241d156044030342c00180449090103040c024685280100c10041d201400c01a42c2c2d102c20100c541e0b04000d041030410300d095100f1444001c01c072001c4440203c0d202d68459014101c102c40940c1c21541d541c0d955030054031603204602400340520b0030388942c0f204142c03241000f800700b01e20403000450100a8031a46514014880c3c50450300d9401c50302c824000d074181810003243e40c0300322a503c1c60540c20041d021443c0e40002802c1211440e0700000002c2030615036044110032800258100c8a20356903400d642080c12610780600800180d054000c034546d85030500a403030080e50055602c0d501c85d403031b09005400030000403840c541817190810704030300c542640c0c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 209892086 210071942 := by
  have h0 := BRFrame.cov_init 209892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 209892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 209892086 ≤ n) (h2 : n < 210071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
