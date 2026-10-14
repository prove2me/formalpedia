-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2836
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:53:11.367703+00:00
-- url     : https://prove2.me/submissions/2ce5982e-ca44-4374-a13e-4c83d5b40801

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 509892086 ≤ n < 510071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 509893336 1250 509892086 509892091
    0x4140a0b12030406020708070905190903050c07030303022505070603020906040e0106020a0b1f14060c0a1a130503070303091403070311011803090512150906012615 72
    0x50710300c01110160200c11403440c0d2140d8480c20042c0c20000042c0100001032101c00000c04546000740010704000300441d03d891030100d6005606540c5020210030103000300240c0d2240b900000550703810740c0d940d003000340107540000c0ac0058034548800c103203a43c018202c0a2001e03100d8101c40203103070f0079081000a4009601c026a010f40c07203030040c04000741c0c5095000e60300d030103058a03a000e49600c80c0701d458101854034010b00f1100303010039100b142840030104a0366040885000e1240324422035103080100f074103071045000300e41d41e60080643c0802031101c40031034604003007661707024808150b58680d041c909000302c015006010f500104030a10100e403203504002c031141d0003900744401050300c890546103103500c014011404604a0140021058028407802c40c401d41101e03024080640705940040c0240704034000e6911807000034400c6903081504201031408400c070380c89203441a080002145589400901c14a0500c451079801e1101c02c4030305540704400b021040e001403401801511740c401748840300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 509894586 1250 509893336 509893339
    0x10c030804200d080717090d02371502060106090605090a0e09060f010e0c04260d050c0d1b0f0201030e100204260d12200d0b04140a0b 59
    0x107400040b02c065555104200c0102e20410310203070780d1042d034640b01e1408030303401c14100980c107004d1203042040c1c1c035001510001c00b94125180d50071861311411205069560340280348606000101c50008007420200c0791042e649646400310310301010f40380c200da4500c400d001d09000104800000c0183f280101d01400b6038000060160040c03544408060a031040c04485104803944502d0602030b198000c0c4551038058003a0500a40300d40c81c040001003024480c611604500040c5084214030703000011441c0201622084103681c016014004000c20302e410800c00c02110780156408010b000d405882d04071a9400c011140f08007143d81030720b070340003026528582a4141343d12621201d00c2c0c0791050199500309181c5100c0141c9403424500e480aa224000581c3c440800c10003650303040d08a00003600103504401e0340750400c0c10540d032a149402038040f4080940c5901400c500941c50f212100c0040d200700395082c0c00401c4880e81c64405c000c00d40d01803450079407880903e800403030b240606030340001c410f0500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 509895836 1250 509894586 509894633
    0x703020702040507031d0a020a12020f0a03110915090105210703084f080f0d0806011b03030b0105131e12031d0d06020a120506010c030804 61
    0x480c1e4010500340d40c021501840082d5a403100140305054030124000200c15000c01492121031039800300340c4841490252071018040000c4150440d901d81c882c0e07803045100074011000e00340c0e0fa480c11690b0300d110354040e2480f942d0300e10300003008601203e0710640320340c800820005850f440c1c001401406075005444d1111800c3c040303c1d21a07203800c1040300c2e071f00075842500c602d640c030000108054441d1180a9519003900140c81d084504001c481c451100000303011200f4226801000485204c04226030f07114800d140100d500b010b811800100b10447e00e49412f4550141a40e580801100c41d03c81e125090740c5184404c5c032005000c239119a1082a00b494107043c0f044c988120b0705503400804420340e010290a03212100c051141d41800508100248440e04004076444500d503805000b02c044190728000c81c0301c02001105035a5213046000e00340d00c0e0046021542c07030a000e14000c1406d0314121489201509002c0411840d500c11b84c100d0300d2840c2c041e92945419111941d0b00100440000c145002016 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 509897086 1250 509895836 509895847
    0x607060218030f07030c031e0f0b06030601090507051b0304120818010e01091a040b0703050702120f10050901020c1c18050a060507021923060a17070302 67
    0x514910081041204082040d5000340c1c40804040ca001d104043e5038000b500405001c02c00100420b000c00b05070307035201c8406988914044a40720b900120702c10040c2c0300b00a0000380c60180080404440d0080c0030a03800e590705a0389400c3c400099400c1541c0d01d4000910070002880c0340c0d00e02545203146a01180c0030f032458a40d8804040e000906000c906841030480003405184180e040c102c80500c820080c03d1480c1540346513030002e80380003428130a601d11154420040c003410005042280c025060420300e45032204c0c100c0c00d001340350f900022000c1340107002c2c041100926500014042411a44c860010010098005c4042003d42405021b640d081d64080c0030782422000280b00c840c41c140402ea400b40c01e600154200146004c0c8503500ca03c19003650044c0501c801d4490045840075603805003441aa5070407640b0208040c2d010076180f1240c0e1019000b0301140d01c01c5501541b252410100b02c14a080781d003000f0030071141c0e1150707100302400716400d80c0c19100380681c0c50341d0740c56008486007401400c1a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 509898336 1250 509897086 509897093
    0x1a0120010603020918011b021f090206130306151406090102120406031e06210f150e1b06030a0504021203030106081006020d140f1b030406170907060804020607 70
    0x20000d658034000c0360f40c0c548038802c12005c01d2249614410b80d0120a42140c0389401d00039448604080d541405541c0e409940202c1000d207800c40d500d9103a000d0704c542d0707030381e01003a0341000e4111490008031405800e040c00200003034134a106000c00d84000e0030300261b907454079408000d4540e00117a04070341540690740c041000d129000b00504001c1405440c0440d000c0c2101c0003d1192004c090708148426190031014800c50500345200f02d45003004090b4540d40351001e003001141036007802c000410199024045011300401e40d0449801078a400c5c0468500d000721103030080607144200ca2843d00304d0400d00003d01c00d02c00ca500426000360001c0c0c0f0781242c803c4030010840c1994004d0704880041452803040c002441c0300f00701ca24000344502c1c409022010b0341c0c5c840046c00b07844404100c041c2d581000c074020349550101c20465104903444002a4420315144218230f0b103c0d0004d10405010031014a04080d0b4045158002ca108403944c10103000c1980c10000140c03420310380070340181e030000805c3c060340f07002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 509899586 1250 509898336 509898349
    0xf0f030d0e1207030501021207090803040501080a0f020c0c0a120305091e0603090102070318120b0c090301140916181a040501060206040b06042009030c04140a1a012001060302 77
    0x9180117400269541030943d9010f501c111018000e4410005680e10030005c50030044255002e4400c01d01e440491a221041c004000d009060a07171040180700103400da01c0944001501002aa030596251000700d170390b21516854903402600c0600412810003c07800d16240008403409580e880700c80d45000e40ca403000109000d03070000c46610340f49a41c0010600b09041d0400d48010486a03804540299141842c2c1840400412850018084003000012807950403400c0191296042d029001b0014403490701c1c1e01e905141429201050180203c84086001103050f081d440140c94045510102406486d940f50000380320000e42f4500c2a110307070348007081c2c543c1d96000e11802491079600904241c10542044110000f0242a084c819440c3c520070b22400203844076560004a80c0b0841c0a446440c0b80c40841c0c14124600c5e001540035240010000c00c0c41203031905c4500a0360b030f83c21b0420111400d43d40500304810a03544003808116103840400d074800800031040141800c040020482e40e1352a80030030039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 509900836 1250 509899586 509899589
    0x3090b030702120903120403081e030124020c3105040804060507061e060501020d0206070207050f0109050d080a12020403020303030105041a0a0311010e0d0f0212150709050f0f030d0e1207 82
    0x20320541c00200c1c0702940b66101c1c0c0166906a032864102d244cd4500840281c034032003203800c0c590a02c0030f45000311100c5d5000b48112240c4150103419004040c081030141e10000c0901c0c41a05003660300400082c070240e005204441c071895000091515080c2440401c3d50507411030041191030946408840e02c203046a1402c415042c0c0002e0801301e04a4240000681081c004148240465004400301300a136903001130410104c1300c081d500c048040e01d4540040307810088942203107030411200c444201c100980c5a0007020380d4802541c4d201c14440f006012007059103d5884042e50580c014401840b080c6002d602620300318000410413030340184200c0c0030030102d070045d0340280d5110101d00203584103540c000140008261045a140300e42800350356440c0181d007180c5402030b0282820504d01040500f04010a040130151024044103601e8248801000c50409000b51802103c501002c1e490314140685042641034005015040c0d900c1020000c80e403200e51801d51940c40050000400903030300050010030b0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 509902086 1250 509900836 509900843
    0x1209060f0d18061a1e030106170f0106050910061805030a030807020118200301020c030403050a0507050405010b1c180606090501140d1103160e0403090b030702120903120403 76
    0x220340d452410700404994100350740d450401c1c40c4501e100865039840440c15417140100100c1c1c0100d44812011a0041c401500042c2a000924a210b84000c000154044131030060100a00c0301700c0e105d000f40694664103855940000c4010002408440e0065008408441c40350034101192075403480003d02e00121040b0540110300e001003403000380c3d582802a000f0092030f031500014414415070310100c8034401c000420750405540103001c00b0341d950a4040701d0107a140501201c3d00e681d00d904140341c58030a049000c0310640300714580028141464004c2a04a41902e83c0a60400140b60180a2403040d0b80e05055011036603003460452031114110380c241c4a174080c0600041150405441c101104d1068104044503034403184034034003c2e5a5905091582036101c50b02c24010101c0001084c82c00340800540198400711046c04960000c61182c010301c9035009a42e00001c480c1da6a41443c040d12007507419000607045004d06600e031001c0c80c0b001346401000a0308841c2d17003221070240020a5006500101c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 509903336 1250 509902086 509902121
    0x3070309120807020703020d080f070c09061d01030605180601080c0a1d070c0c0e070804021f0912020d0501050705031e090304050411070b04031e021209060f0d 70
    0x180140199240c881e20060031038200400c00b400c1422019582d0003603844000e1040710070540c0201048400e000ba212816000b441c440d413500c00781d1401c1e0720701d180203005403d021480e003d00020b40c012003c135550b0b03c4409081d03d044159003980c0f5010060f0600401004a80d50411b44400f29050200001802800c4c45030107481201034240412407000a5948424180c0314000066031041652005168205245080019803a0300e54605003002c4d101380d600c541940c00300d040400982a81050403540325074821142d0300300890090500d046600c0100c0550301c0020400f0005000c80424020651803481c0010141ca0580c1d805070384d02e07800e46000311188400079901001748507451480c0c1004420400412004001234030342076a0b0300d0340c0c2e4007441c400d10b8411a02d0345182c041801102c8200c6540d603400040980e030602d018100034010400c240a000820b030210141c16024510104007070b1200588069072614021003001042541c2d082916075000390707507041000b085842d809101d285103c400b4158003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 509904586 1250 509903336 509903351
    0x300c080106080c18061201020d02030105011b0b070806060d06030f02030f07060e0906010306090e0c150f03010e0c0c060114010210060608070c060b04021b0601050111061515030703 79
    0x4090075a8400e52007038206501c55540e014455075504083c50942da500c18011510795260030014502e2070340028021082d510028925030700d5401d98004606a403404e072114103507110b01a000d007030005c080e094007400c1d400580000c1075125100303078041900224010103503414030300070004100c100c0d0b1460f401200c044e0094030352041181018448c100d83e0000c0000506045840c05002030001420351140754030843e07919000071b031260702039031200016010182042108041074a0b0099884035480003045c86503c80540c18003000206034216820102c0d000c4c0d03000e0450b4a00840000c081801420b400400c040070f12180174003401c100b001600800d101001612041200000a03003070101170070712503080358204541030003042c7d0440c1b0915002581450951802086030078013a00078130030011043e034402d00000381c01c141d6020360796140302c220889000b0350380140da0790801590155800e0700580301903002000000c2c001261007a022026200c098030b841c4002100b04802060f9a0084030010301090f90341a1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 509905836 1250 509904586 509904599
    0x30d0f090b2703060c190c0f2a140607080708030c04030b09150f04140d032c0703080d0f0903050c060a11270a2705070801300c 56
    0x10140707994010740180401d404e1141c203904040c8242c001c00c00c020764008007440419032280c540d0b5002607030441003101c034a5245150064603044200c41c6407850618075807270715200c0b2010000d000103c4036240d51240154030400144811074000d00b50582e070041d014031048010076204001144140000c2c2c0d03000740d4541c15403a1620910700090b1003100c0c141d00c6084900b10042e25229115002a11302000f0219039549240c40218402030518903040c5002c1d500b51810040c0d0141c04ca0b08104800420300104c00d000c0991204084185008110f503a03031080c0c0080011502980003070034940e40d061404688407201001d0801a203003110741c00c900240002131340d41003a40c401e02000d0b80103110420103204240714180c85105a0007a2000080000940c5140c8a54004c440b404006442d0300500b030203801c03a5440321800c400c0e0306110a0820142ca8440450843c0c0140780318013440349440744c0316080c159003464000712a1710049101d040c1030b580240000c09000e04d592a800b800310b842501d25514240c01e003070 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 509907086 1250 509905836 509905897
    0x1b0702060a02061918080f13060305070f031109040c020709060608100b070f030f020312010e010e18031903060e0a05150102030c0a06090c03020d030915050702030d0f090b 75
    0x50100c00080c45c0100300d400f01c0e00d00c00c4800c01d040fa005100c0c25107948226441010300c0c07141c504410400c10260704002440c0e03801d60402d80c426103443d100d0b540074101c885800c3c8c0688207521406e011042c03080000d08040d03d850387c000414042e01d4411070700f585440340d000e04111012034024501203010541041101c0c1010740400001e0008070711540e08201059031010400c00901300000c00f03118440c1403c81ea524420410750303066019450204403103596542580001003028062080b03810f40e6400080c4225078840c201ca0024030b52480210f10700344088410725159250052000b040503290b0000062003a40301c1c890b54047c45081c00000744c01d0819a4980b007000c101170141c1410754006003c2c82c203070007901160007002c83d038010304086250b40480c50150300821540d08003d501502481202c410b0640c8080307120280c8a03140d0f610110518403010548240c05480c0b002541680403140d048910f500c0341f018004445101e040030104591592000b0916400280b101c0c41e803601042e551406952119 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 509908336 1250 509907086 509907121
    0xe01050405071707030b041113050f01030b01090e10090c020609070e0709030f02040b0604030f050c030c0906061c0e160909030c02100221030a050f060105031b0702060a0206 76
    0x1401c0441c1e00c1c5000410400d80180f008180790140b595079820882c40741c0b11030b040007000d1716255054594450302510003c001080a008442c0210112400c03003805502910460004146c1616803410051601c1402d10308000001c000002c122a1300900281071031103809a1840c20b02280c000c1c20291500c2e1510f00d250a40f9039020610082d0904c4c04d00074456003050300141a6508107403003c00d010224000704000c0d01501c80c100e0380000c000a000001c3c0500043c08105043c411410383c0c0c101c140305410107a03074100e0300c90303000c1d848200301d0302051007807070310000401c5070005586000300050324501006040b02e00c810310604032500208580a11031007040b0300d08026280b694030400071001c058038014140180316500900580394550b500e0600c07402040a0089004a40c0141c200c035080300584408541050391900103550402c00400c6848600d48503d9101d404180c0d103050440d9030b9140c040d0704040c3d4400c00d02800c041e0801c032a80140e2128001070501400320b4000f002142040c40100c074909010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 509909586 1250 509908336 509908351
    0x40c08061c0305030705070c0e09070303120207030212090d17030109060b16080f0c060a060e0924061c080c12030c0a0c020103110c100507030c17040317010e01050405 73
    0x516188800280c0003401e1381e400c90342a18245488401a10b0040c4000103190866a02d003080720b0200320080d400015507200f524440c0e03580d41948080b544c13508003030307001d114002800350300910482206d0b0070114003e8086070340e0041c03451920a50b40c0d101c90b00c0088500a00c20b01c1044000014803a0803c2802000010400c3c14401840c21260340e03c2c03010060307040e100003445e01000155000c0d4040500c0c0945102c03000c5403084d203400d420003041d040010510780c42403810800460300080c240c4540031850300603c842c0c00490540d403000780c014a003081782004006c81e91001c0b1924903221030022100d0781140003842192141d948030340c08418180703811040304090310401d00c03c00c204001c10381200256200c3e01c00c1030914030345c00c4045100590180c02410040d1416810121300c01da107421001407508840365082c007080149031071320002102900d104c2814040131410100e0079600769509175100741e0740b050092800100c201d00c24050b4090454080c0c0c8801c4450700c8a40040c000c625103480b60b40d800c26074 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 509910836 1250 509909586 509909629
    0x40804180f0b1819021b0105010f05010903030e010e03010608121b16060302030703180f020f040c09030206031003020d0503040e0106051e0d0b13020d06050909190f02040c0806 77
    0x10b0f110600c0c0c50001d401020611118014100c0b0f0502000680690b0707507015024080c010404038020780329000706400d2281120104940c040003860b54029840310040d01e4240c0d075440e2038040030070b0040d2441000304128030b401d5907031040000741100c01480300c800c141d5071b0031819a540e1025001c0710304404c00d0340d14810b000340c0c00001c0a400b000f141e0501d03080803a40c41c0c2c1001b5031a82e403001e40030350040a0408071102d45034003542e08070003002aa00e48000e06903200315202290040700d40140404ca800e0a1035a001144404400b800549012800b443e030000000346600300d80c9031650f002c105516000c1c1011181d944c030120307007403105c4040740000502401a618009051000d1110f0b0800342d102c00540400e4141c5001440e8210b52455070022280c4050250140c50102d8410300001c0c025400764820340b014514000300401c8070f141c015401401a00100f001300740c1000441c12030b125807004468100e540c1d590913501c10780103840300d0145101c4d21040b43c40b100348500d006801c0c0710810541c048100b03407008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 509912086 1250 509910836 509910859
    0x30311090a0e040614070c02011e0801090b0301061505040302180c161a09030a020c0109050a05010e0d060f0902090a091a07020708100509010c091401030203040804180f0b 75
    0x40701c00700000100d84900525240c15140c50034142d00400c0c0305024440103801c0c0720200202d41d600004003a070100d100b030340c42c4240c161480003a0301d402e44040c40034000003100500108805455a00207280100000380009441595450210407055450051102140d00400c04105600d084507141e0001102c0003900100c40c6081074404516100f82e82c00c403404445403120307110612910b07101c010f02003844540d00186d0b0781000400c144d665000010301e100148a00b07140d440055100b8070200044480241c11442d02c2401c050040d602d1028140031079410a101d1298100802c03c1400703111498010f450b000107004400340144200300000a0021082c1ca05100d9081c00003401190b8050781400600d82000c5c0c0c648603520101d0038650140d010306114841c00100d0200d044d15a40118020041140200441ca004c03082c00e81d01030016108079a100c640c2d0403c1c4486550281d001564814801e4191520b030580300c0000ca8844200007111040a80d03552107103040d040c940d88100340c007044044400e0b54000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 509913336 1250 509912086 509912089
    0x1502010b03030f070204050a09061409010c0309031e050f04180b101e05040803130509010e0402092e080303090d14041a0f03040b0403090603020f0a08090a0204110703031109 76
    0x500c55004e0090007555103000084500d440783e4010703800715a2040040c440c004004c0c2030880c084d01c00b0365001001c0e501e00098845030078021322900703400f650300d610380306202185050703482c810343e80b640030751000e00504001c0351a10949110090014000a0782d10302145c592648021080b81c4464145901658003803d811001540021890188119a0b0118005502c170148101d03a140202d80c40b00301c451102003110007032113110455070f4041c0c80b8156480070441c5e80e03c05130780b01c400909640103900700c24440045481c60f1030600c0902c03003900048154954100742c225007684c00219641c0701070b01c5504040140500800d0900101c9807111080c070f080b1542000c40c0c40354203540d10885c8030b41c110501e015010300c00e0304030000301540c514810510501f40c407445c0905140391500c608840840000304000c4010640318060b2090360300d09418641e61909121142205a98041000d4042c111501c100510341d80143d0301e50140c0690300141d80c1d80c2d543c0350005894040c040d610040007024030100b0505c0000c086 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 509914586 1250 509913336 509913367
    0x5101709060f0103021e1905040506030705210c060406090e1003050d030b0109030602040801140f150d0f02150405130218040207030c0605040b0609070c03020a11040f061502010b0303 80
    0x19240c048801c0300340104001482032210030070031081504594031030340c0d6171082006604031004440c8c084d1014001765982d24100741d1105111f000b0b00c3c2d0300c489009043c070703140501020300c0102003840400300c5580900c0c0d000003c0c016005684000002800380e0001d1200810000542e50000c094030324005a0b0381c00c50707803003948135543d010443c4100342d516a86512141c0c070410803600255000441156615296444540608081981241d103030120304041041c83c00e100500780e210303425003502003200396500410404c5000c6184400e5071890079420240002d683c4900c0700c18540d0815907c1140d0300c601d07007000c0c000c1214030f4240c80d03240244140401040950094102407184400301c50040e80c9500620f004e4031030541c3c0300782c0a80307618074000c00c000c204101d01d03d82c0c50280400712014140e035a00d4020454a940005c100200140c021404c2d840015458800005081000400201e9500302e000d218104803101588003200c1c10315209490015941c080c440d000c42c0c0072040d80170750302d442003940c4800c90 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 509915836 1250 509914586 509914589
    0x3140f0601050c0c060c0c010f050a1407020a270c020c06030115050c0a1104050a0207150c030e0d1806020f070e06130c051c0b1309080405101709060f01 67
    0x5102d030009203858810010700820781210340041107151510304c2c0c04400c3e03541c0c0740500546404550420103c043d00c0e4041c03420b03503854890307d0381c1e0760001000311000b02c10290041d9504070780181404101040044044203e41c03210341c0e00400d040d400341203128511094030191038011003990002180c0d07e000340c48250031241511010820703035100300041d5601715a603200303814103090340d80540e8015208120b2001c0609081b2001210103002c1601ea0008070000c03072080c40c100034440f641d4401e0140100c115074108407401e106c5070400107580003230500e813107051101c079419110004850741c10568140044141040c0034260500c003c0544601d00403181d40c1e108403a000c0c0020b408516800030700c46076603100c01d6418102c9a91414071100c0d01c01030010342150400c0d540c800300051244900b03003461803544143c8549420050500c40e1600551109100600c084882915522030422004c030341d0740c990005a1030003d14965800c180040d112540c0180340c034020341007585c01e410042c1032044a1400741c200c4c0f030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 509917086 1250 509915836 509915839
    0x6040c0905010c02061305030a08030f0604020a0c0f1115090a090e1905030d0c1d1e060a0c06090c060824060c030d110406110109080d05100e0a0504020103140f06 71
    0x19603034041b452554a001c0324a0b0b0200c0d078036200d0000e456080060140145000c1c500c1d007203014001d9143c041c100401c1c0d01800607544005800d0b090050040340080703200000082c050210028091040382c00f045080f41030a007a92018140090008250f0a05c012420010400070004120b07400b0558071143e16814007101c241c031105291072035034003805014401c0f512401c3e156242008001c211600107004c1502d030401005201c00b04c550004194200544c3d091540042107c40f00c0390340c0480c204010b550b41066046604101c15440d01e400020240d00ca6a005e150250303c1c000205850042e004041f50001000442d07480d00091a401c0c244d00c0141006803146411200e55455804c902074061031400380602c05540c90b07080049010116551900520a58100b903881414480020042d01c0c240c503c03c420040a2400c104517400210201e0752140703800540f010108188141d86000b014507a500c1500d0100c02c2c650b440c020311086680610804040ca000320141e4423440c584240e0a0199890040185 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 509918336 1250 509917086 509917099
    0x3060613020307050408100603060e0a0308041209050d06090b0601050f0d0b0409080a0915090806190608161d07050d050c0c0a0305040f0608091207020d12030506040c0905010c02 78
    0x8003e9400f4000380c2e8007604800044074205640b13220100098010380c4400c0d5200703442c0114055581c1c9020896821140d05034841200588a41d540c0d004000e0030344240b103080080c041d001260a0390f0b00b00d5940001401140041038146070b5091620154801502060501600b0400300c080c6407019070503140321034061079002032488000400f007005849000c50003041c1140000e070000885400080e040252054441c0102c800c03140c580040d50103a5140c050780709694400000944000020403800754281c0b005080030480e07541c0c8510b800c0ca02003a116440c0690a0710311400c1c010010191242000001403203000001c50501c600c0241c00c902c20114298202070300c600c002050709200c04211001030340003008890107040941802001504140900d086070f034014880002c00714400c100c0c05011b0740c9150003034a0304000300c4103042640c0e441290101c0c0c10000030198040070411031820555900c005440124052a15600b08001c5603007520b044800e00003010700502403039900280c0031500c164141e800b03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 509919586 1250 509918336 509918341
    0x60a12060204030618050105070809031e13031203050603071a16020a09090201020615090106181d04050d02010903140c1615020d020604050c01120e0109140705030606130203 76
    0x10a010b4031a50f040070b0480f90410903400d602c1070543c00107151541c050402004113442d10b00f000c8851030b400781e82e40c0000d80e1080c00320601c00c0d146a2140303040d100c3c94040b0719180c1103170703502c110399048081e50080e90030005100d80c20000301d405028941c0d108070110054482c0d5400c150310402d8501440d0402403522201003101000b440400300ca070b10f10180c00030051019a60b441486502402c40d1440c01c0b4010700800001c602e5070b680d81c2070b0050310440000c003034403056800c00c14100e0324822001c00462210b160254009200c440a40c040112410107a962804c00d1500f800c2c040d203030810441c400011a813500c00d081c00800d0703120780d05904000380d0000c166581c2031101000752900c8030b20f5281e14a40c90404070000344001e13940d160401107540503002d50300031018044c0160384403202110068007036003065400b29031039803041305200603080c41c4800c00035840c3c11188404d4211503844000b110503030601003800041200410640d0000c101c100c00410316842d140000c1000000210003510300380307030003002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 509920836 1250 509919586 509919593
    0x80d03020c0c0a270506060a11191b12171305030105010b030601090e041502030c07060519060b09030309060901020109050a20011707121b091508060a12 67
    0x12120b58000003881881d015464403d6003000d1284521a003c042d12050282c446000e514040d00d446520010801810300703510341c0080d14015070400c0c1c0724070340e401110188640c5074084001c0d01e20441c0a04640c40c06c004070160b504541050942051064180c21010500007600c50f0410741010b10b02501502d448040c43d455001e850b00b0183c1020364103508100002c280d16035240b01543c8245400d0340c580407100c0d0740b0031082d041c075034090350080c0c0000c03008100c8440801030b603001507410200c0289100d2a20025407180c004550b0203072001ca003040c2e191149820301c0d16682c064180a08030205100b80340000b03d00c0080e5403441103076101c0d801043c010504544ca60b002b0351000003040d410009840d04c3c1c00242c90403442800c2540803243d1b07072124002001a041d4031810030813081c2ca00d032500b01401d50b2a456030a07204920b02d11604600b01c0d440d03081c00703d005c104500c2c004005007029150652241d080981ca01c202ea400303050076a0402c0928000c12005582d07180543c42180c02420049032035010509 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 509922086 1250 509920836 509920843
    0xf0303030b1816050f070605100f0f030f0305070606080d11190b040203101e15030b0403050309120f070b01090902030604080f0d020f18010e01090512010902210607050301080d03020c 80
    0x9517415503058010580b01e05025454005030b12030b121400034040c84544820084040c0745160040c3c0c00c5460340c000301030000031b40401e44c0c1a440c0e0b009040c164200b800030b5940e2400c2e501c850700701c07100940146401c0450706d90000d01c0c0c10f001c041c02001500c011410341040700100c0c18114405416045000041015501d041c810700302140f25583e0103106050307a01c030256184c61f11023071005000d14505220008080341c8c0300c50901c1031f02d90202e01c05800c0e480d05d4030115010f800250140000e40501002d5803440e05110008100c1c0003415250303503403141072a040007480080d0591203904190b081000e030800580e40851410740c081e910884c5142c507001400c80560b068054214804030407440007868aa0032169403020307200810700f50840c0f5500d13031031500044a90305000c0751070b50301007190f101003800903107061000c032a422103d24000051000040e00001c941c2451401e113902008003010040909100620241c0c3d031004031400c1c8140f0399450040c102e0750307900e0071800342d8040550100c0c1d14400c120050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 509923336 1250 509922086 509922097
    0x30c0309050709050f01080f060604050703180b1012051203250e0a060e13020a0212030f15030f06060907030b1021060807030224040f0303030b181605 66
    0x700072284066120990703180103100555002d0341030080540005000c940000700c00381521580c8010704650384a03042031102500010340083c05068541c1441030124502001d840104ca00a000d040c42a05010550b0701a0200c0c60300001d40364450a204600890341c0042d141100b1964000e040742e403640c2d01c0c002c105101806110520559101c40200c0104550280340120101003c841c440701003136031038a050362040b514290a82c0c0000443d82c0a015000ba258050041500d0f140107841c4a10a00e0792041030a40c8101ea094841e0442c440030b01003007404031542480c001806a000b8000864003016866444c01d0040816118045200004060901c203804c80c01e801c0c480540a600c206401c100c01800c40003200c0850001101580c0d0f10031180348444c054032048900d600c015024190940d0240074101308071301104250b02991580704844024220000d100500300e07024030000d2241145001016102c0f800407651045e024059010f1451011100d0b154200a4980c2c0c0c0c0801c03044800e0080d078550041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 509924586 1250 509923336 509923343
    0x70b1608011721040e070c06111821030c0303090d020a03140304020a0504050112020108091f1d0a03020f070602060408030a0e011103100815280e10020d0b0111030a030c0309 76
    0x40d17806204c86240c20201c0d22181d41c0c070440303041c04009104001c1242a009450010640003274280480341c29081c03c4c1b0414100c03403030342c3d448210502e000341c1c48203296038840003041c082580000b04004101c803003806030101d0391915201500314804180c40007803100c0c551201d8000000000408035046641c1c1441c1e80009040141050005607902c0d01c10603591418020180d000c030350203a0010b6510000070555044000d401064030100d41180400007008000c0c202050750001890206d40106020800c6000c01e018480e5005020500603585541c0c00c20003664403e00940d0300c14001d210000d84100c0036a07a000556882c00a08402040ba42030f0141240101e0684655030000a00100b00110402401550400002c0344d031010b80081c0902903540301140c0c1c20f0b1406000030080070040445026500141055100201d41c1d418143c05240c101844480301850184c1c0c00120001000070500a03941c0311f0400b420015580c4407581c0c0e09684034130501d0038800030540e68541a0030b0ba80d0090703201140b070303d42 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 509925836 1250 509924586 509924609
    0x415111c1202120103150b0f1509040e0a12021002040b040314030d110c0708061e041416090e0604021e18040803012409060e06070b160801172104 64
    0x82d80c0c1010030301e2026105640034121f04010f00c089540c102a20310005060000e40411411190521460525000810003ea03c0790701d0703811502042d00300f0810440f606000fa0607440301900424000380c5020004484151028014841000901001c000381c45c200ea8200050b00d2020b0900d003600c904600c40c0c1114891081d1804034007d46209100c005000703105c0400c011141e0b0103440d41045691007030100ca41090b41c424001120303c0000807440c00702e40103880f503503004203000e200d0301000c2d04210169501c83d00b15000c040c010404c40740103020b013000c84d0120f6006031800b4200354003c680c0c01c1480076040114444808c0303150000d6180e00200503070402405001c0c05aa080c1494510400e5000307100d02903c1a042d40c0c2d900003100d000740404028581c5503220031803010718007101507640081c144603442d4449014020320010810310400688a480e503c007005102c0084c2c20070240c060181038006000c61040d04410400303501c400181c3c030420341c9500c4a28091615241c02c182c0b264403945c1c021401046 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 509927086 1250 509925836 509925839
    0x20d05031305060f01320d0602071401020304060b0f06090d1e030e0a0603050f010e0405030712030f0e0f071a09030d080f13080403021e060415111c12021201 69
    0x4182a0070f00b8140c0b0351691b088010341540c6240b511022104007406440b100213040710390103e141056160050a2085a02504140254843e00368402000a07070340c80c1c1341d4000040004000c03c520600c10220400c440d9114407408070303c08210540140c3c0c2806004217880c1c01340000384042d00810307074000c50000c00018a40600c43c6030003842c0b081350141c004d02a0340308100100f00103000f402040d11030640c0210941881e807a015210b504800e0140081d11300c0d00081200c500800c824514a50f00050551408260040301d20101c1c0e04642c210b00300610241c2010315043d09684021800c0c00c00c035425800d9200d07208002442450140c4500b44419030b16210b004034041902d5040a02c0178401e0100f145102490340c0c5011461140e500502e0000b802444104004d00051800d0354004240000d003070a03e211841c00e1102240d01640150803043c1c1488604020300381840d403000c2c09100d807000910140c40150020b01c4000d00c1000e04200c00014041c44840740a0b442c040d550680d030140c060290340640c13a5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 509928336 1250 509927086 509927101
    0xf0a06090e07030507091107030f050d05040c03200105030703231f1a07080313060e0f0c0103020c06040f1407031506050301020c0726030415030c020607020d0503130506 74
    0x42c2814441240c030b902540e003001541c042c140c0f00f02403181e20301064140c9008403983d022140e0202d042402c0e014001d06000c024116050380c812075104ea4807a8520304125411828222414907441c40c1401003070620519240b0f5690740300060301d030000114103000c5285a82c00c082e01300341151000c1503600c0d01c0c018404000301085420032420059480000743e1943c19202c0e036821740c00640ca90b09484010104000b140f0014011f4001580d00404034031080e203030302800740d64107820b4800c402795607403050384100d010100880c0140201c000000090070210710740300010000b01c0c0c6410000f00040c1c07542440c419660300781322207a03c03400004200242941c203159100c0ca002070514060302802e000c4540341050114850805200b103a4048940200400800b07161036150081951400e00d00c0364020309035454140240010800340000c0c10b40c50180f507200c000d05940003800c4903c0300c2c1900b800c550261050004c0306401241a060705845480d02c036599644018a40b150f90b80d560600034a10b200300b90410250303 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 509929586 1250 509928336 509928343
    0x150402031f0e0108070e071709070504050115140a0507020d03021605060405090a05061507110f0613120812041101140301231801060f110a03080f0a06090e 68
    0xc0703035601c0203403000c82501c9680c00403000d0024000c441c9280d00081040c8000340758982a01e51048961410300311000a901d0b0b0284c090311b069a15003055031042c00144000e107840c5c00741902601a90002d240401a01c0100410410ae43c000d81c050581d070000e400d5083c184101308a0f40401e402410040981c1d48034030b0020f683e03141800c884102070f15005000b080c2454076408960899a005285d50080e40b500c07841c0e10700500b00a04240da00024160751002d150818401515407503010390010540807200380f0074442243c04120040340b256904010182c580c0544201ea40c0a460700f056245080000302c6c5010034952103888000326080d0885010481000b2100c0d515501c05030007070382d9013040b40c41c08008402c4140002e000b8880d10b040220141d2001129500e842000c04600074052070100728103120624855000380c20640c001945544004110354004060007040a0390a000309040300c02c81d10001c0c0740d040040d1501603001c6401000c281441d8141e00018050120030104105096240b08450f94 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 509930836 1250 509929586 509929621
    0xc070b0415020106030206030a020d0b1314010506030c0421060f050103120e060405010f09050910080d020a0210030902011e110f0708061b041707060e0907120515040203 74
    0xc10000114030510709500c180503100c2102d5000d412581561103118000b000b03504005141c90002e982c40d01d19105a685003052030040301e40000001400c8412580724920581050300001e008403010000d00206601900442e408c0380c140507148501200402805e0a41c400e00d440041c2655043c1312500803140c80d6980218100c038030401415500c00000f200c140d6450841d80d00b4903178820401d00c000c120315400743c0c07060122640b00b4982403d9064540f800a103400400fa91158241d00d1048018000d00c50308001035104c8500c1400100700912035503001a41d1140c070103580004150315502d0620869008400c0b10403010f0400c5416000c50b01c0e103a00041c00e0b40182c0c40380c0ca00d640f1445d910342c6150240850751600340e6a10f000540310755600d00000180c50072544030f000006002c20000055000c0c400ea8003c108105008080c1500c60702d032101c0100a8038110400b40d114103180014481c9071a04034007548010034000c1d20100c1c41d5581c00040030746045130020070302d412a000104101e01d00503512003025 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 509932086 1250 509930836 509930849
    0x1a09010801050117061002101103041b030c0b09010e04330b040b030603190c060f0f050a200109030804021203040605030a0f02071e0c08031804020f0c070b04 69
    0x400c5a80c2e510011100c0001a81c046280d0070071a1000c1451303414280280c01d00030b507184c0129001480d208099900716461404089240b03203002c0180000c03c6200c1c80e4041d28002d4841140b100035095484400040241e4492242501000542c200c002e9000f1340660305035074001482049203103e01801110401401003502800141d1445101003642601c2c03804820740b10042d88960500d4180310340341c0415800900380b00da0600c180c0314000001c040e070030003490007644070380c60440003070b0b162900c094003e603004a0b41038203011011300303a00c8481e44d103c03003600c200d143c0500c1c141c1c3c0c0301b442c48010b100c3c248009001500095082c42c1020080c1074010300150f00461007541c10401c072458021255071a4080da004104c0050780c00c002041b000d02403504582940ca80c07000d0010314105c59980c2e40c1c80350062600c1107014001d40e401861041c010307014000002400c8030000f542c60308091603010000c40e180400034a00c95a400704200000748a24000d0b0396a9265443c100d6890948440549a05405c20310482 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 509933336 1250 509932086 509932097
    0x304050a080720150d0209030c0409150506010302070f0204051005060406030c020f0c0117071e08060f0409020a05060705011d070f0b0715020f0903120307030c0c02090714041a0901 79
    0x3c001909040c19014900041405510b0910800301c940d071020394080303408942e05219009031010260703aa8400c4425030791050f082450103503e4560007105550006112606140c1305100342c4002c50404481e00d0300706035041303a00144981d2442c00740d5901c640d650b0449a000b89000c180440e0058142d440714146c89055002c0399405580c00e40ca2a550b400d9070720100f8005840c50b0101145078148143c000d8021401c2d04007180035805c039100e00650940409078100001d00c60800384495810700e07800308090901f05403418411800160040f51030701020340f04a034028880014100b041c80b10030743c0044046000d030b11002c00a205410076070703a40c4031000c0c05a42004025510300048915800c0119040a80d002d810b04141c0401c0e00c3c0044000d400040c000c0d200c2210030070140155540a000310528207401d05c0d8a19100e00300703c040102180c4518070448184041154a04013680d11241034a0307000585280c600c51001e00d0625074a494000da62240d507601044600c0c00000c0030820000d0414401e0a80c1d48 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 509934586 1250 509933336 509933393
    0x11422120e030717070e25080a052a0f070f0b040b070215160c0203061303090f050303070b06031509030403021005030112061d16050405010e0c0f0304050a0807 70
    0xc041250403801c0c041000e0b548019010046d012100040c80d50180d6241e40c1100b10f010441c0c41c00542e40300100a600000301000b0410002d00114800c2541004c0404041c0c0c920a0709600d58403014005825003403000070010400a2085a2600403103c006a2040303035030343c04100030f1400e11030200060307034202c40c0c103001c03040010700d114030005005400741c180d0080c0021603260503d820b2125041e240450080001c1902c003000581c9041180c9809044868403014004070350342001014003020340c0118020001c80d66042008e540c1c000155140c0c5900000075100ba0788a440000c0d00e0a0342c56030141e82c00005035000c00445e240b022002c0e00450340255000040c0b05105602140c240c4001d000351145058103040e10ac0224050b075100303090000c0740754100144c04072400b84191030440d0025940f907107442c3d1002c081c8468146401803600403c406080055982451850410240120740140c080050040000380034000104035000896400c040b07000c1d5103440c9410681c0d0750a030710060580c0b031249075035036 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 509935836 1250 509934586 509934599
    0x19240302030c0720060f190504050a03300f020d08041208061305090307020f040c02030a080406090c141915120609020c0a1202011422120e0307 63
    0x3124802c0e1a41400c075072038200203903a0410b001c042c81521081080e103410900405072034800082c5612245551102d49411113290034681508034828100b04110043c007007080291140107110b4103803948500414452001004142c01203aa550700840c961030340a00b400110300e070444103e465442c511b9003910f010101850741070310321030320668000301203924917015451841d00c0340340c8581e08500014524035440031100d000c0b03420307103c040d40d1605a030341000603070200f146407407a020440714005039000d0020416580000c0d44030300a420000c0d05010161001030204070a0340c1c82000550b6011500d002c800342c0301e859404d88080c1c0488490300038103100800e14100e812813035440088840c00c044294840780312003802c036030702d200950318241100d480e101c010400650344d0002d064030800c031078010440070b40d6a08003606164401d03001c5e070046d039140800070a0110100c2401c29031080005d40040039030041850ba1101040c603040024001a20780030540c034040340d01c07034080c02d0021421012200c601d515403d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 509937086 1250 509935836 509935841
    0x6030203190203070203130f0609091b0305060109080a030302030105120102281b0b06010801061106010504021806070f0501051006050d1503081201080717030d0902192403 75
    0x1c40503088850442903000204030306030019580b0003a1403054a007071250b901d40948460341150010200341700312080c20b20010780d001c1c1c0c090f8010181c450040c00355120302c215071030003440d140002408250f1240300107101a4054100070004102581c11280f860341c080c140203009400a00450707100d201082e40c1c1c564040c405009680600c0d145440c55003084400700da4072008030500642e004c06020341604102c4068280810300034015000701450002450300400051018030160050014010104000211110002400c605513031058500607650b603140c400440031921100d80301076001c80c001903034800704a80b210940c0f002612440090086071a081000480a0a10f00400c8001a41880007408104954008240c00000303d03840c08a055241e403604201c6038086030b100241c403025240100032451081020030014a0030307a43c032828584503444041d880e88107100040098549030f00280003599201c4503452604145190001541507544446040032480e441501d40c81d0186000620190360290 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 509938336 1250 509937086 509937091
    0x5100509100e1f12060608090c09040b2806240503060616060209030a0f110f010509010f09170a03020c0d0209190f0216060c020c0604090b0102100f06060906030203 72
    0x4029004000c030030410b10312032945101e0f000342045154a1440001344c01446641c001c0c00103565261828900303541071300d1500c9485000d003130041030600204000700701d0003511142c200540c0f810b0103201e64550501452801030a502503500c007460724100090200e240035021400d141841600d0343c03203064420381912280811508550013140c00c00813149145045414220950b200b02e0006080c1007072200480c0c503010340c41908460400a42c20030b5400d00c0a2140f0700c4c10540811240c2201140380800000d025002c0d0341603180c140110321400d803d41d58060241000544041401c00c0140448070080c1c90752040360b07010940250052045500f9070703003001410311138000d40281c90901c1c640c40c0c0a1080a480c1c41c004142c01ca07983d41e5050020064841c0c0c0024a071544c1640c412828441c01800d00500320343e10707046907400b59404040d900120761074003000d94003241c3c426800001c1d00000c0c400180d080030601b5582d1201c10707145c0004580301911b01d07440003003513444942c6c5031000d607500c540040d4101e2009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 509939586 1250 509938336 509938339
    0xf08060a06030b280603030e12031303020103090f0f081c0e030406050c0a0f0602030115110d050d1508010207110a060219060204170705100215060f030705100509100e 73
    0x7028001201000403440c28075084d060642a800040c4101903250111101e070f820840000d26900100c0319541380c191b085024000b4480061440c080110601018402143c80000e05041e01c07420002c0601103861000c0c4410381d0016124600c1c2611440c01c0345543c1d1040105c0f10b03954640e03000100024505105070181ea03103910008500d4a0306000b41540d00e50040c18118000c1e1040190704c0703000030006016002c1e424030508001da1030354100071802c020741c070112029000704480c0074800c0c22404000211020181d250341410765503018500ca00303d020b861124140488101c0311755000442d05815401040c415025070480f006d11001d038010003500d04c54a02c07403240180d00581c0a00040c034940d022401d082403041c00018582903540d5030500c2d6800307007403080441542020400b04140c1c01c002c00003520426561002c0c0c55024088244000241000382205003e1801818220b205441c204a00d03405014010a42c015658458100800b42da00010106018124207050b203859540111031b0071b00700880 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 509940836 1250 509939586 509939603
    0xa0c1704080a11060408190203010609050906130501021b0604060605041b2a080d0c080601051e21100f06170a0b1c0c1a0405010c08130f08060a0603 65
    0x15074403046004540d0f00c480c1c5a100404100002d02e000003001010b2982d12100800d00085410f801003508440680d84580301442c184002c210b881140868019030100300103506c030742000c41d01d091180c02400340c070103d00005e04001d03201303d00104002803010301c20340c42403c090200548481c00d10056644180c002c04c3c282030300c2c44d486000e090050072401c0c00c10b003c945212010900c103004100c0e01200d5900c0541710710724001203040322880a4020100710303203060709000f0301604150700001c203a8801c01106504100b41080610400b0021004480d440200c08088109103079643d8607581c810074084d01c04204041d50301d80c00181c0700d64422204412518a40c46034940c012242c00105580c4100030000340e040c640d40c07800c00d4216500c0503020145100d110100940074000e5242010181d1046c1d0012450b140d805010f01c4501100c0034115005d070381e400c0ca0044403804c014a01034045004210041c07107005d00d003680105091460032103200444a4802c00c5490350703100e9640d82c800301d40140c04041c03d50350 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 509942086 1250 509940836 509940853
    0xc0c07050111244002040b09180706030501060e090a1b3c03090c12080a081f14060708040f08160e0a0c0c05030a0c170408 54
    0x1801a04480075110061003034451581d40020000e0f071041030303807040d09803450b034100038803c4800742030320241c0d00f0106440c00000644680243c1061400c04404400e0003003010160b58011501c580c0c00680c44407902800907466800c00240c00034004c0e00c543c0100049104105000501d036110340200c50480f41c99803201800024140c041c0003224000804450070640c40c0d00c0c0382c20a01c04007400345840000c0643c1c46620312080300040012819071040041c2040b803005120641d0302c0380e503280751005a01d450030002480c02140c07405000705603443d8130400d26180312003240c1d02442201402020020130907503e102243d507644495101c26029a186550000c3c10010300344608283c6500e10001244e00400e094102112075941c0e05003548540c00a035407000d8294810080c044040290138000c00c1100c00e5050f0301070034100c45c210460303c001c0030340c04031035240d1011720201d40c05094074900c19500601a26a03510155001078200040c00d8000c89400c0504107428007000d80800590f02075914180c09040300742c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 509943336 1250 509942086 509942089
    0x11106100e060f030d030504140a031202031005190326070b060a15030204140d05100f0f02040e040203060709080d120e0604050f0d050703120c03091b05090c0c0705 72
    0x42400400443e0401c8030105140741c1c130b5508024000410020b59004502d615061810300c550b0b8540001003403c0341d1040044000007034120080e511031440700300d80143c40b55a04a4940c0038000640e1103550070604041d0780722428640b50345144240c034090b4a0400d58030384100c603540d080e00c549034031181c00c440c070a0007400006506401134540116008144000e41510380b4501174008220355481d40c0442d0f4001810000000c1051a80301400011541d44a40000319100c06440b045000d0390709050569841c1443e22140e541d80c006140b81000840454907503484103080b245400d0b05450581c0b1038880d4800007040d8610030900a820b503140c09001d003103601008842a00d81e045c0c40b4140c040e4076070f01da1050200a003005c2001d180700340d00410050900d10001c950366400d02140c4900001003140800c24040802d4000e20ba050701e404000400041038021100300314010130021000070314240c2c2b240024600904c8a804000549800b29080d0320507481e0904102418818800c4062883e04901c80070081d0707 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 509944586 1250 509943336 509943359
    0x3060d030210050711010e060c09060a0908070902120f160507020607020d0f021c2102100f020a030605030705150906160303060e0c090f0616060204090b01110610 71
    0x10180309004403402c0c0078422003444240ca004445a40000e0b2a0644890054109008611101c3c1d0110060000340c2411040301040b0b118001d142e80c01044006a05441c2510a51051000742002820384190319201d10485005e58001c0c509444400c0710039010440c010820f03149203000c5c1482400400403825404800d603003907004440140d92240c0280311200250b121642282c400740e200d8401a4081ca00510400940c03c199056880d40b601c4140545800110500b85000301710039040c9044042c228032141c224900030042c070144a000307040155079070060807a038000d002c00c141c00d5141813250340e84a03030506070317540c1c0a40b10706a40b19040791290014542c1c400018104484080c0c1440d20b0700c2001d911a00c1c19030480141100000e503104002c204640f40c0890030380d003040030032201c20328141c1c42c1070000c0e00320650700d032182e031107080f000600d1710240d83c05035038025605500c8401951030f144c0e641100401443c003228114082003079080003022511001c034209110700300e04a01c0107941404c194200c2034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 509945836 1250 509944586 509944609
    0x10207111c060510050d0606061112030f040609140c0307150801032d110102010c030203011409180a0308010509070f02120c12030408070201170610181a04030605010e0c0306 76
    0x30b10401048000c50b481d101c6d48040307034050380111800f0034400d140103070051400d40140602d4001b9040400120303001140441283c4d0081041ca080751001c4c0c40c0c5052040042500c910300a00030328425040745101d860200d2059041101101074030801d40d41c039039540c48c0510820f03600400241075400140002200880d80b000c03455a035003443c982c04e5529624020300e000035805c0c1034036801a09050000c4560f82409100340020a5150550641d49040c00da1540ba5144d0003103284203030003040c001110305482148140807002e107201220710318a001d04025003021001c5c011940114014000034040c40d008001ca000c914155034000e20901540d5404802d440d048130900a0302406040b94550034007841c4d00186005601540c0c1c1c440d0b50307030140e2002406901004e405c3c0d00c05500d41030b040020030303910345030306103031810141c00d04400e040764a2230143c480084076049800712103540000c81000100880140c070940780300b124100126602c4224408030314800301c81c1c030504100204001855800c000f4623821 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 509947086 1250 509945836 509945851
    0xc02032a0a0209040807110a1a0a0c1b090b123403060608100e071802120106020a02190f030221100c1b0206030103020d0203070801020408010207111c0605 68
    0x9101150a50003d080d41e14242d50686414a006c00e03ea010700183c4140c0c074208035021200c0061031407030700c4148011480300341401d884600f00420f80c402c01d14080d08080341850307440344032020f400386060110f00c01048240643e88125140c1040000796040c0b0351900446602d10300020301050f030b01d0750f540c5511090803031518403140303502a180040601c524404c0c60f003e140315540200350709080550491619241d07030f540701801e60038007030901441d81c004030f041320940303403462100c840251a01c806280a0300c102c0000d4070f04400e9003000024460741c049020064079100b101e1558070b03413030100a550300109450043c46c16035101010104014070702440c400300310b400e102ca181400c01030407003401824815581500e4810b01e8548819000d5164407510b001c1604044110102031240140c000c9442c601050100030700954841c49200255035042006000601411009550340c0e5180d1101c54040d4004450888480301e06c580b0320301440c5010140780409a8a120282c10504d4250300c800c0e019010103840e11 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 509948336 1250 509947086 509947093
    0x20a030803070801031e0317070309200f0d0503090918010504030309050708030f1803031b2b020c01080415060611060903130303030c03021204030806040c02032a 71
    0x40e0000024510940e51510303458520340c51400c3c00c1c5040262200f02e02c0d1345065004100d0002a08401000d450750110254042e4564a4003000d80c000c0080c65809411490b5000050003100001d00c5940192a815100142900d20503001d12491011000f40200f6541003441100130500b020000745070b00c000050307400540b01d00c07550b09403421078409a4050b40025103844621003448030801030782d801007605800a52515110185200d5540149003003807000134424a043c2072b40b075404005031030400e40480c100100321507042d100103175191490200754095081155030f455200c50320341f480d6400e004941d0090403c10400c60011500f01b400140100c80e1000c14401302103440d81e0511400c03000d010591165156800038601640c80c1a00003010b106103070b0f10800c4003100304081c001001003100d9060030040384d00744d286507094002c0d000d1103815281c01504042008141079000d0030150241c80d050b00c007000055100360701283c40e031184902e0581c4900da811105003580040401004040305a407096 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 509949586 1250 509948336 509948339
    0xa050307170c03040b01061b1412031006020f0705010e06130b040914150d0b0a0609020a0309030f18060c14150712050105151c050a061712030a09020a 66
    0x100c41072541c1901c1c954032014000c01000704110252210741c3c09000700d400c06040100310f600801c9a040c0b10380c0701c001c0942036042003500b6140d008101180e951009604842e449240c59071540140b000e840c8282e500520a13100c5400fa5000c0100707406040e81d1041e503c00703078400707210400c0c0030141e4003007a80b1740c0300b4000a5000044003c40d1001510142010b50307404a90440c204207030300610314001c0c003041e0f005202030402916594541002d15a520b600540307201280c0e4071488032200421259015078100c1c2d00014a000f06280e02d03900900b00540b01e9281c44400c80c0c0b40f40c41c11951048000004207458141d040c0074001303203001d24841c1d0140d0b441410301d0b110407201c0c0300300c5505103003002c1028403100400005208940f47c00005502c203140c0c8801d0304001c1589842d0000d200b10511000b083c411410004441c1e0300140031000b42d0040d40340c040c43c14400da0406080590080c40c9500c14202004da004058050b4000003082c0c07103000381c1f1408945400c41e110b55507444014903014100b00c1e03101403031000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 509950836 1250 509949586 509949617
    0x10081005090f010c03050a0c0e130504020303121e010e0f0106050c03040902180a0e16050901110f061b040612150f0306050114010c0209150411070b04050705030f030a050307 76
    0x1401080c1399090b035010a40b42004a00401a078012a42002c00e00600c0c80e010340491b100c03500c6004480302c10f00008a0107480d030380007085c1184617408100d10f920b41400b0030481c6801590061494a0705110304503000c5a076992200d009054040d1003e0028101800c010000d10f03200f8800b6081c400300c070700140c92a040e0391b464184120781c45000744803010286004840c2541c030703220302c10a0041811301e82031006494005103001183c0643e1851200f40301c030115100426134441c0200d10768002010f0202c80c2c1000d5603400c01c42e0740307503000c895200a540030040310409505185091780d0440d68140c07981100d0541380184c51000d491249204215490404800a906112120714500441c0203560024055050050400f15084a280c13040d040c060b555429100513162806801d81c89104501c02d4505c00c0300c1c410001c0c0180811821a40c401b032030106002c4140104007030b100d070241d03104a0843d2040795545042c0750f141c004148030b408568000380400d5078010700510085038070210500e05111090301600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 509952086 1250 509950836 509950841
    0x5100803041e0f0b03070315050a12060f0b01170603030706020a1d010302190c0f0804080f010e06060109060c031403240910091a15090910081005090f01 67
    0x40c41141d0420311041c41401400c40400d00e40d0241c4040c03843c0c21a00c03400d0808080041c0700c050b046004040c1d44a0514004010340c1011001030000244940c0c00203940c1c803142361045c0d04034442580c103985004001013021a581c491850900410b845d0614084800d8451121400006158580500080150380d000036103c0c4001c081d40402030b01ea1a005030454600c6210343c000c07103401e40341414030400c40000c00b440508200e20703101c591898280711410240c0703801080394003121001454001c1c041004520f503c00402e0f5000c0c5042010001c20401e0f81d14091141d6961040d58600d01141c0100410b00ca0305203d0300425403040d0007800c003402020241d030074240c01640200c40040c0100b4201c20f0380f40605002c40a00214054101c0d40342c03419060031451200802068480d5101081d0380f21340b880340d9006560103500c0050002015030a5010a219081100782d103c0828180305500c0440003c40703401d488900103064800480003040c3d80d1041c0d0b40600c0c01031501038550a003500c900c61121a80308003d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 509953336 1250 509952086 509952089
    0x7050c0409150f091a181b060d1b05031b0301030c05090718030b060406090c1409010215130501060e04050c0625050a060b0d022805060c0610060318060510080304 71
    0x1400310143c510706102010500010006d259103681c00200703984005050350000054000300440780d40380e40d0310040c0d0070040180398030119480f281a010581107081da0b00007028601c511241c00c0c0400c140d0301d11509030503042c4000d00008000305014a414040d608140368015405802c0f400c0003207140015280780b4041401c00ea00031078803070707608104011440c2013600800e00117180d550002c2c030000400b00006026104a4480860080004142120160705c00c00a81c00107102004040d03242d420001030000044021520a072080d60900d030001440002004403144110342010107406140c1064013040349a500034282011501e80312101c80e01d4140e03502c40c0181c0400d200da030080084083d146480070684d202c07900814451080e035613074200941c4400000c04600e0b07051880ca07ca0000d44148800d000401580010381c03c40c00105883c0492040001d03058000c180420800260995422046054031102c000d05281d420003000301000148694000d15040490054861042038031214900c1c99034215 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 509954586 1250 509953336 509953373
    0x6140a0501091104030f020d150e0102071e050a06020c010207060c030504050f0105010b121b07030512090304060e0d0c05040e0703110306010501020a0b100902070807050c0409150f09 80
    0x940c0010000040140300c1d200300407201d07600182c02d052458844d5000d6000c100030290140890311058800c00000d118811a10f51490500304075034000c0f205d41500070740266008a40c0088200100320040640c540c032025041c1d0b02900902b003c400f141c2d44c00002e50000c20004180d0764090180750001895401203a1588140365400030300c0303203400e007400d9150030550308440c0d00d5640340c000140030551504e411100f10b18210510308071552500185140c6054110301d20881c00403001ca10304081590140003060342c65030f401c40244550f01e845030034030b4a911a0384909004520003120000303c0e4205030389106486801028100e102a641c0d0012405503110072a00e1800750308000403d000f00034040c814028001c8003540240455814000040d6980f41c484030081c018941c0040016429507000c42c08078080c11004c1360554850801b0b02c0c00c116640c010942c00c441074003840c05232010600302841083e40403600014a5003200120400c160000d101d082001c01e280e075201c040d00b00200e6105840c0412581e074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 509955836 1250 509954586 509954591
    0xd0b09040812060d0b060d0305040e090d0f0f0f0c1a0a15060302180123070c0303090611150c090603090d02060108030f07033b0102010f090215030406140a 68
    0x4144440c02c00010040815100b0340300d10041c000132840500034160b100006841066280305035050658250045920440c9020b149000300101e1035001304184480021035182d01d00034400604d0261a81e05403050f1100014070810707880b54105109218640d84640100c1600c2492000d001d544640c000e41103544501c4e19444026050701504071031034581c018600ea250031800c01011038101d00b01c040c0d40c21405410094010380c1d41c0031309850540b15150a5003000e00d40c540c3d40c4a10700d001c1c0d55040d411721050b000300e000c0010000d24180980c1d00145284119000b92070700c00704070300e820b0300c41d000090001c0010890900c1051000e44681c1300950090b500700004110213160400020b240400581040c041d0f504240140c0101e401c120065400301585410304151100041a5102082c510a0510003409484d140e130700c03031840d0785008501c0482d4000c0c2d00901c840d0701d480c01040c1c20b44028a0300207401940c044600480c1e11a00002385400510509011580000c440d561982d901d20a5803081075403a07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 509957086 1250 509955836 509955847
    0xf0d14010515030d0207090b120303010e070e040b090a360c1a04030609080f07080c060916230a03030807020d091409060f061b10021305060d0b090408 66
    0x880c025404803220021801450f0502c0c406030b000303480d18220301c500040079840b408d6410303560b510403511000708010361046a03125070755141018607180d01511250082104507483c82114105405892103050002d0090f40040e01c035204020001e02d000545907030b41d556102d120a20300d080c0090803030441000303480716011400c110f0526003142070071540300405000e2032104003d03898088805550459820101c00a240352240c24018068403e9510303041e0350340000078200c420840c1000103808914285022510503513180e60905651b41c030002062880081c1c03030803003001a035031052040116620700d110349207142c8541502103104c100c3e07075410850210300d03907008021600d641000b0b00901180e076490140c180342c0c505003909503c8061414600d000c0d07001107000400c607845110f080e50071000f0284c034595450164015003c902e5200e2220705e00365000b018442450310425000303803100d60b41a0404000300c42e20b80380410403694070042034143c0c0252101200c4503240c2d20340200a03c620701030241e2036aa00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 509958336 1250 509957086 509957101
    0x18040f030306260f03160210020a0c121b050319021c12080708010302010e090901020715061406090a060c26030f0610021b010c050f0312070c050c0f0d140105 69
    0x201551100e207056500610210003c08521b01c3c40702074541e01560078081ea014008001c90901c00c2039540079242d40e062910019540d000040b45582c92809003400e0383d0b058001e1a0311041c145414880e0300c1e03250348a2f0340d2100d070043c107280103501410710040c0134480c04100083d040346070200c01c000c181c4000303401014040c4140d0f00155025840000c0c2d1400c40b18541c10756002070b00c1101599800b90040503000c00181c07000c0c20950403146516007060f00100143c5a5144c114007078401c60044100d05050320b16001c2041c18440281d03030040c0c82c000c1c000d5112070f0410b5030499000440d40c406503241c0580b012003000c0e800990342d000c04c200406104550752803034003c2d2900c2c00410003418040c05030782c2c020303001035229034046544a034100c05003840c0000f40d10403500480d0484400385000d00710380075403618008280d100000810350301d100041e0100d907079541c2d588151070112824501801c0c0b5009802c80c000d06141071405204c00e4500244003403c400c20a840711089020100402d080350780d914424000e00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 509959586 1250 509958336 509958343
    0xb010b090117070212030c0405090405160803040b07060b01020a080705011b050901050a030c020c19090b04050402031b13050f0f091f1107020d0c09050618040f03030626 74
    0x620300d0350b05091450600a42c000e40d100c0003000c1303500f68041c010020030610740b210b604987c000d240003004000745090500380309841e038a00814907844a40c10300c200042d006400b00654084409541c1d82c2ea09000a40c4c944001038035604414030f0450107449440701c005407004c4080c2200302c3c01000005071202c1c0c096141a49800c104681c0800c2c004103214281c1940c4e4400c003168036401e000c0c42c2c041200088031a069103002420040194404041d05200d12001d41314203003401100c0c54140c041c003588000c4400c0c84100c82050b030700a50180c12421802d610540f150b10952a52000034005031407841210b82044100e480a9503106003518100301442808000810b004c0c2e089144030700504180e581d04400c52000b00c0200c5c1d10240312503124001030400d42c0035003043e10045a0050f02d003140507003d500e01211096640c4c0104400a8a0f00c0003040d041e04020b1113300401203408020b00c190745690716202200c100d001c904030105622044086006501d10b904d00c0808440000082007903181d40000b03501703 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 509960836 1250 509959586 509959607
    0x90b0a051005070b0a02120a0b0a03080a0c03020705060a0c03050f1c0615080c040603111e03060a060302040b0703120e0f0c01020d0c20012c10020303060901031e0b010b0901 76
    0x74418018042022130644e1400787c150454808078002802c45840c901240b14100603900180002d07001107481c103505c90304602c1440d00c2d684a039003a505c04d251668200249402015484000100225036950000e03008000030b045c110004503038a41003501504948104010b59450181c80d13503214282000700d07120020300800070201c0c50410301014600002da070012801540300f124101502c0c0e5480c800da104030407049841c0b0845c150041d20642425014a0066600958445018a811400006950384241300751001d48040803480340c81e140300d5032002c54903080e0395012400c6136a40ca0800046810301000303151405e07800d80001c0c0010342c00d110000b9003041000ca444c0010b1000303003818900040d0b5050255004089449201c0f05520148070049421004181c08134080c0416444001c0c01d0030101100000d600104441c00710348000c2203c01240c80e03020642c1c010f90401c071030800600010700d81e440b91042c1a00300316104030503c881030311403001040d030a0740072501c001000a061703015564000c02e100e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 509962086 1250 509960836 509960851
    0xc010614040c1e09050d050a05210d0f0609090c090c0504140409051f0905060c1801030e10020f270105031602010612050c03070801060f090b0a051005070b 68
    0x105640c41584043c10100044401d00b00705048080000c8080b40503154000c0a810060040c1c01c140a1614025980700c40c0800107481c0d41c0308071441c0518441a40f10b410140d2000030b50b03140e041c02441080304018044030880e02090503102d010200300000184030b4460b40e14050001c070481240b82c4408982141c001c04481e4041080400080c000b410040819210b03c241c142c0300007a0004443c01c04c0c5090103c0060030843c501403440141c1405410794001e0b01c2554010310942d105621103443c0c1000511800c0d130020502c4980b004a240e1560090b0300c482c0c6041c43c80c0c015a061240005000000c81c2d0105103401c1440d9404503114901000802c0247c03512003186050650250651002a125000023801c5003804c031340d60400302044610030340010f001440d2210f200c1007800200c1c41c0c05612060025100c5000b8030903203000085040050148404880d01c11400700e0103503041003410fa0140004002c1c2c503030072210110001800391035089042411403480da4800340c88070520b140c801e007511005001e18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 509963336 1250 509962086 509962091
    0x32d02010c0f02122706070c180504030906030e120406170105370803040e01050f0904020108070f03150603151d0f19050702030904060e130201110709020c01061404 72
    0x1d000d013000c05000c50344070300d160320940d41150030040300200200e0440f00e2815048038010a80404000a8039054401d5851000203412a442100b6926085800459000e400100400380800140340240e110b414104402c01c207880c00001402c920381c030035034401e40c40100001c22820840200c441003902a0b8050038088802800e01c022943c101c4800740034070030282080d48140c0341810100d08021420000401215059030f44942e9520728a40f6110002d110380c5015180148001c051444c001d80100c1c03050b54140c460100d030740c82d144001c0b5a1000001e50000034581d407510686019520519128020649a9008201008040b100c0190a1045d90007421000d0414646007414288109003e0703011303161090b114520341e50789010402484203070021080d054504011700a07401d901000400c14075405590510800d50f4070304013200790000488042c000c1406c07522403e0010341c400c1000e802c80c00040011280e04c5603c401c00c400c101ea005c0c9900e03a00907950340340d04001b0110308411a40c80c1e44000ca404 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 509964586 1250 509963336 509963353
    0x111008010609080f120f04080a0f02040506040213090209040f09050a051608030301060513031a010314072108040e0708040209070f0509010f020f030703080f0a020301030807032d02010c0f02 83
    0x516a80301010f003042c10348090082400c10700311b00305505560051800c401250784a0318107080036002401c9c5a0002e83c01541050009640750070240200d8a60100c0040070702c8500d0302d40000c14009411420000350b005841c0c0c3c071041d9461000c6d0045400581c0103101030800c04c0c2040c40c0144c90f10795180404603049600c010704100026000c001d0324115203003414030702e560740260413014010070119080244400c2074981c6040c900b41646001e141620b2161880c080308100385030800b0f5450f41d1500c43c5031100742903002000001e001c0c0300e600d0307020103220740306450900c0c0e03c40c0c0c0c4002109004aa1800c0000c40749000c0005515068155030b4102d0003506001000608511000b0101c0c800e50041c18140223242079094001c41c400c001305c3c416907900005036902c4801c0c40c58001c108080a80d40782c0c054090f03000108003203880c0d51003107078100da90066850380f91105503034007900c030030000704101040c1ca2071180307050050007200741c0c040d1b0001e480d030b80c00052081030f0701002400d13000130124440215840710b0035 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 509965836 1250 509964586 509964613
    0x9080d051f090b0f0402041403280816240c0503040c061b08030c09011106090703021e0307090506010f0801030209010b0c0309130905060129030411100801060908 71
    0x1c40c0c03042d100040e4000c00c5074105000819082e54074100102c1d0402c0c800a40001ea80340c01c1d402030114a40c00b01c0c00d40c0d00e02420343c1c41c0405555114501003402c1040d0802141c000b0725080028140040040001040c80406445c1c0c8040600c0c1c401004d1101d11040d100300000400c244641031b0110b03028144035055081c130361034018000349140596424030288124140200584c03d442003400c550100c0d40c01d580386070900c210300c0b4a07001045460f0100b1038400a10310000307004580c80780b141480f100108005855a0208601040c094500d120b03500c1c803a070307041d100340c0e102409201c01410346140f01244a0400e00c000400206d0811170580c10402c8210041c401a070b10225905c0c1152071b4900c1c09601c8034842c002d403e00310b200700107440da84180307003030a050f5041a4030340190042901034410f030b4003580e980b0103101f45541862111000d080d111283c0206116241c0009903401c07a0144900d0801d031030b81000882ca443e004032003603201185450004000ba10780c8100ca03400508595005414426212030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 509967086 1250 509965836 509965891
    0x726070602031e040b030c0c19240203011d04140303010806060a1203020d080a0605090103050a0b0106021c0f050c1603020f010c030e0f0f100c0317070c06090204060909080d05 77
    0x9155007201f840c00911009402010041d0000d80c0c40c50401c0c405d40c060b0b09241c08415140800703183d40480d1007881019000581030702c00c0ea03048030000751a4091420701c0108040072400c0c004c00032204c1c0b403914807940c40010340030006980030b000e0a00040c40d041c1000c0007040015012070b8012441109020010000254081101900070415061201079511264006400340946800250700003403410000410b00000040ea0110785005441a40075a40c03a100202d0322000095449030006c8000c02d40c00443c184101c0c258a464941841e040d402c3c01c01c4410f4850806003000d100569a060070346090055140c1002100505602400c01c81c060701c4099030b01a040755220682107108ac0090319640c451525a40d440d207207201c070000d10080344140300032409408284100c5040c2d0028031030000340c2c0c8540030041c2d600c03401400591207401005044e96600000b0b090021000c98000347c564000040c020030074090a0000e602c140c80307003501d54401100b20400c07590001c018260319009080c80c407003068a0903 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 509968336 1250 509967086 509967091
    0x103050a0c0f030c050c03070b0f09011503082b09020f01030e0c04050402030a120f03180330050106020a0510061d13021c0506070804050726070602031e040b03 70
    0x28100412000d114070400c0c0c171180509880d224072400b0011340c200c01c10500faa0761500c11f210040310072481d03865001c00c217400c0f55501d81d000d010079000c08000b440031980903000b412500000e58141c0701071400c06038183e00701d1306071034440f030386115118406a8214a404059000c15017000c1ca401c1008800a03000b49a0300d49808041a01455841c00400c1c00d640f000c2c03190300c8010b43c10801340f07580801010300007031400b083c403e0702c2e0002902c0c001001d217802d01900c030b4002055405030346500440d121044000106101010756034034240f15102d408050080301c2c0500c500800305500038003803120007414901d00707040d41c20400590343d515003a014040700e402c40c26a20f82088145440c2c240c240e4030304d6401c5015111400b0040e5114007860880b44c001000269858906885842a540c850b10744e90402e580c0301200b07907001402d80c0c00440003400b21400404050001c901c42c28180520f1030031303e0f440341e8106511034020b440180c000040d80c5480207000701c889203120605441d25031801e4542003480d00c1a0002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 509969586 1250 509968336 509968367
    0x20f011104150207030503191803080301090509010e07030305040501120501052b081216050c101a13050103060506061603051e030f0601021b0906042c0c0103050a0c 72
    0x20042d400603841d200f002440e0242d58003500301e995810440301c82c0c50720040c4c5880c0040010300e0b00d03d4084141480361003484100c0350b01060050850f401d000c11107001e0500201600d80a66a8114502c010b54080029130000c5002c0c0d1076241c1e60324201030004046581c031600030315040c4d0400300104401d8544c05d01c050718160072181c0d2029680c00c07040a1005800040b000500b041101180c1021212581d1524501595141c0c0102c40c613428030034829174036805442e6005400c0e400c44d4000404000480c1c10205104046071894401804a4000200140220144400c000e42e0b50401441000703840c1c4605504030030106d82e99800c0021241e2580255250071a00408010f4041141800000d070290121103800c180280705d620380c94440d003015540751040b60210700502c15242c14035401120503031a07058602c2c010701040050381d40c001c107100151042070280c244071601c244c01800580c50400c80e400602402c070014103542904000010281d8501404040038a4a0f08032850380554114205645081c0c9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 509970836 1250 509969586 509969609
    0x3081902040f052112130e0f04110f0d0b0a0b0a0b0f0d020909042402031905090a020d1202060708070c110109090f0f060e09030403080c010902030706030c020f011104 73
    0x8a04e020913100c003070740904d103a140c4190340e0301c00004040301004e44250524a017032800c00e6995440743d080f8480c030a50b0145180b540708400b140104040c80342130751448a0181c4100b81005402d008140001030b50303d415921f40e0404401d102e410307a041e006908140c0d5084070a000030301c0c14054041c0d0300d4401d6003600c0031501c000040881c0036408a070152000b07080020500d502600c0c00b0309040810002003200507484541c550807075803c1e10028801c1d83c0c010303840b40c010503401c0f04038450400d0046c032010300605424802c401c50b11005076512101404814800d07151010b5070800c03203130b020745060009492207050120000403c030803180d000e5140e03100c00d0740060740003942c41c208100598000308d80703401c001e461908016002907503502a030001d100e82380c1c48070401c000c159030310200c480c2d840700160340301806600100420008601000c01a001e8140b02100001d0540c0407a40082d00d00f08076a4021008240c550b01d00100254043c081c1c0120130403c2c100034445072407952450a0188542e000b2000d141c076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 509972086 1250 509970836 509970859
    0x103110607060b0316170d08010504020904060801061412070b0a2601030b191503080c1e10270b1b0301090501050a1502030901080c1603081902040f05 66
    0x31083c3c10200c24450068142c84800126070413410800400b40204080c511062601e020720810010b1400b240c00e0b000d5440c90324590034801000081c0d4000d0340030503449034032808040381011080c031480d0001c00140402d013440110038028060300e2041e00314442243d4104140070803400500f841100c7c0300e0b010314074000000c0c82001c01900c502454400224040f050040300200801a2441c54507000c0c0d070000c8901414800580401d0054940c3e40c503c256110119150800000e01904003901e6110003000941c1c03100c42d0f1580e078210010000030030654082d446150b05c1300300c02c0c60902c1290101291511308200c11810000b070b4409111a8040090002302020000f40908030000d22404c3c190004000541c1d42e541d480800c000038210030700400b442200715460005122107003060200e90700c25a038000d18200001503006580e07842c001051034403c00c10401c5501c0b040c0e070440056859491003601e51603250700b0040002040904d401031a408030510420061121200510402080303c408450501070385 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 509973336 1250 509972086 509972093
    0xb07030e06120702060f0a0c02070302040507050408030c010f06050402091c0201020c040c0909110a081602030906160c271e0507080403080a09030e09062b03090e0103110607 76
    0x103100b14440d12803003040803000d001c006640856075500030004400c088070f00f80c440c42210401c640952540c0c0000d80c2c400b100c01c00040c02c0c035412031a40500f81d410980e003015502d0322901d0943e40071140000036030f5903c0505d140c006845100d000d01402c001d603011800c11443c00c020a0030f482a0302ca1041081201004003401c580c801c010722014104050300c140300c00d80e40158098040c2c070085c06440348640c1408120440728403483c0545e40e8440c996a140741150315040c9401e0480a500c0071817104501040004540903112800141841714510340e101d0406451801c0c507000304541074201c03410920030034444100b4210300c0c10808156190440000400d19803100c4040b41d0400040785601e81c083c101020090501c2c3c002610500c1035000e81ca8030031035507654109102c11500d014000401040080030500480d052542ca0030340c0c8104042e106002d1240d840809603115100c031001204c401c911080c0341c01c00c1503402600100103016945201c140341d411a031740d000c0007903100c40f4814002d500215550091 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 509974586 1250 509973336 509973349
    0xc0303020c010f020a0908060609151c051f050a06060f0f0c0b010801090b0c0f030f041b0807080f1605010c0c0914011a03060f010f0c14030904150b07030e 68
    0x451003e000119956210840c0c054648103051191005900404c070000e42c05003400e40400380301c1d81c64550600c0c6d00848103001c01040848403210701c2e524140027404503002460812500d05101400d00b81b0400701e2204e40510001d50300c000346041e2449082c160700700a860b42000c5680074125190601d9088100240000c0f1001104120064500058100005122041944000d030300b140200700318038056503040d81d0121244622010000352040030000a07668841014041d604148684000c142041031500303078000c5009039800140c0d10380c011a50400c6240402c100c0f01400940240184c003050f4024020242c400065106403410702184454000070080d103100600080c1514074002c00c4041c8803032203051030301013090261401c49007c0080d42c0103a050f0040c1036030f1040b18010050000398420000440d01c900307400718004140460301c994840003801d00701600020703c1d0044011500d0700307042c031304000a56952003448c81420043c2c80d000e1080306203040440c4c00300d035011708080500c10f140c0c1011900 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 509975836 1250 509974586 509974601
    0xa150302090a121b141509060a0801050a1a0304081812031e040e31030e24040605031e0108010504060e0f070515040905070f0914010c0303020c01 64
    0x1405101ca60700031609099050110f000e040c06001c40b80295145460b15400c04025401881044200c2d183e40c540c003403403d0103040004810f56518603082c0170404011400e40c3e04101e0407480070518950051000c3d09111050704000c000c02d40743e001410b854401404030038407028101425200c400200c07414254480c248100b048240907088446504050403203540740d40042e107550400344150351810002c0d01d190815103050b525280190f100b0b0391108065070250845018001040300701c2c2189041242d0070310184150000e000341c403001c01c518024400c00c9000d01d45118402d020040c0142c900e9900118002038500360b0705a410516506e440303000e04490010460420741424186070300022038201019040240540c3c0f044005010052020040644030962400c80d5085ca610400d410007035454402800076140c0d002c01522840c058988d188038003a02d400700c801401003504050002005540f0002190051100705280c1e0299006040020019001e24002600b01500455800f503030001c20f621a50 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 509977086 1250 509975836 509975839
    0x210203010b090f19030804170303190e01090c090c17070203041214100209010815031b060910170f07021518060f01060f1706040519230603010b0a15030209 68
    0x4c441556031602c51420f80c40f5001e0040380d020007031103083e8807503400010f0301d024690201a4001e402955081701004000c1190350170380d19074803005040b0100b081d54240d4405021a0b00c008101004111009090f4100355021000190444c004105401da4080155000c0d11011020a0f40d49941030600d0034a2000342c81900c1c0840c012380301c00c1401070718242c0c01003610400070303201c00d800b0703680e81100000c290101005498264100615100000011044083c20b20000030725881c01c00348040003281115020809401c007040d180ac00340c00d4026124420306512420303411140d4241d14107200000e455801e280da0450512088802040c292102450700a902103c0c00048520502d804c0c1e00d00703a0201e80138452040854450844031102c18841c0141040c110380103180303200c094a801c0c06000061100511203400c1600d42e0030140d0b0700e500240900026001a040c22148030108646040c04140c3c01030156846689042e005100390345541c4007440446132580007551561003049826006446540d01d40c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 509978336 1250 509977086 509977129
    0x1608030624040e0708270304080f0a052107020103110c0f01150803040f120309080307060f06140f0d0c1a030910020a120e010912210203010b090f 64
    0x900031198400b800445045000d4031440343c5810806640311207060756400501d400c145003000500d090100844921141d800450307280942d1000030f5400c050f2100c3d61300143e074210402803414000e04002da20440c2e030f03034414580e1784102501000304d00c41c03003081d50081c14941c948c07103116010704848003030f00c0e001c043d8001500d042140704190310b4000d0100d004a802c40d15243d400c0402c1c640d40010680701a101e4034a80310040c1414a100000405071501c81101040449007012420020900c00740440511a00c0042280014146803000f40c81c0c41e6084145904843d06200255641d80c000003000100d054030386d0710000300c0c0c504111860300c00640240d03809211003800403040b001100021881a000031098a071070f01c1002203400281d02c100c2c005100041c200e0610401440001c0c0d1103211030030a83c00000a40c0011540d40300c480462090508010a01040c1c11541700300c0d12440542d41e000d8403800031441d43d810020850110700415010074000d07d00c4000361622911602011791004000c1e1189 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 509979586 1250 509978336 509978389
    0xa0906030809150c0d111905030d05011d06010e0d0c0b0d180b04080a0c17070201030c11030f0f090a080604120207033917010b0616080306 61
    0x664190b030720880c4400e004007440c4104001c510b500509841a00a02c0c00c050240e01d120260110340b4104d1310178203910300d80100c3c20341c1106400d1101c0820f0000748904065a00d42031608100b600b200d0059001c0c60310342031200d40c0100400444c8031101d0340a802400d0004550707503080041811900881c20061160b100150003280c040c040b4400342a00103103100e002d10080d40c40e18103107003001201d080000c1101c5d02d0400884d0003d180e600c0a0705100030b45103014145c000854071354504009a070580c1000b0f8080c00034900e020f40d64140030b01400c0c000079061442501c0c1180346180d690384514402040d104078045070710303920143c442e4112100034000a006644480c1c942c0c40c2542c0f10003040c0d6080303a80c0c04a1100c0b00070580d00205090003220740082c0182c0d00c00b00b15200700084084034203118400910a40c0c0d182ca084002815003074040c0450301a10141ca8104a10b9182110640e84480b8031507941404601000340b80c4580b1a20300e941d1000d200b588940701c4001107091640d40281420134090204007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 509980836 1250 509979586 509979593
    0xc06010b0d02072406090e0613140601030c050f060307020705150d021909050d03020303070e0604030b040f0c061b080703090e04140709020f310e1501020606010c0f020a090603 77
    0x34020700e2103003030b0604210650b603030000b050840301400d08807d2160170210000d412040a521441ca807a40202d2071210400c0070400e41d0f9081c42c5003604100c8000744000800d0180303041030340380420082d1098030a10f207542800343c1c020355108420300c9014410801c0d25a82d2500e5050381c001d4812000340a202551262301c4002d07200040300c9000240b8000030960040001e60f8582031050300c64540d01034000c0c40c039507201d03588102d5810114103081c94006104000000004088800f11481a4001c8410456800da03500d4200c1030f0050990040081045044260a401118454210a1650142806980d1400d52034292020503240d80061350060714a4200070603c00594600c0000440701e1080d0b6104549640c40807049009840707041d0300e40b04091180d203c40014501180f84c42089054400440a07900c41c01d550341503400b50024580d10048005000c4031071000c10120b00400c1c0d00340040d20b098681080003c0141e004030300050822200d02140109640b00c44803000040c0180380c00a211040e144d04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 509982086 1250 509980836 509980883
    0x10b0603040812063606011b06050a06030b010902070b060f01020717070b04230a1d060d080c0309010314070c03200a110102100902010e0d06021c0b030706050c06010b0d0207 76
    0x324800441400240024599072041c001a0748d0b111150b20000500c40c3c85845800040030000d200703510550380d4020110110300151030480c001c0c1200400940d458000c0d00d0100e4503001c0c0a80b01c0d5014441000040b41c407683c020400314155076070801c02043d9402d640d641c41e45004119803161038141c0c0006004180410301d40029031001041d0403020281011050a2151642552081040362200380860002940c1640c1034940c20502c003d10310950300515484003001e0703038044145034005900000340d000741940c150003800c0780d80741218880c80780e611784698080c100c011801802420440402005925444020520b56841c5080310440d643e1002034030300031940c07240b21801203000d446001c404480d030328414040c00d000c15034181e50b440700e011440b40500000c60310189086490076028042c103007044901440300e00ba0003c12450205051401c1d0003032509000b001d0304142d08000c0c0401c0300c18440303200003070f14034119480c91103069511300e442d488450003801402030040420721070a6200c0201da5a50 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 509983336 1250 509982086 509982169
    0x1180b0f0d11120d0905090702010213090b01030608010b0a030602300402090f060a09020f071e0b010f03120804031b030f0e01020a0c0506210406060305010b060304081206 75
    0x70380f003960516010f80f000d25901c1d003000746081c002501d403030782c144105c0c24142801d030340145040c0005030800240c0b2900308440352154224083e2035584d004809029a030601070309005100c041c0003080080100c00200f034010300740d400040c217200c7e0001002c9144000c506a1181c6540c043c90036900d16100000310f42904100698059118103440380102e410300400f04100d90249000400201c58207181890040c080c2d048490580058102840310314046900b0b8860030303118100c1502c502481702c00e14640300b21750319411b800005000c244c1c501c0900029040c1e401c15020750056041c4800595140d25044440404c560140e188032a001e8101108040e0005001449910f190711000140c0b0601d200480c2c3d114484400500080f03a030070f0041020b42010401860031900700c110701c1061f001e0b042c5d203903602c80105842c100c503e180c3c0c0c0c807802c1042c880c3c22710074003000c007504444061660410b5111182907000d800d8114003404406c0c000b1035640e0b40c4081e1408003201c04170720f0000003500b1807413220f45c0c03045c1034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 509984586 1250 509983336 509983339
    0x1b050915040b060a2001111c0e030a0206040f0204090204060801050f011a070f060f05190501080c091503100f0e010e0303040b040305030c040801090c05010f0801180b0f0d11 76
    0x4080000b100341c5481030589040d099980d98003d1010342c04441488841c1012480e04d030255a03880041c2110b0301c1039401050380d0078000b0804250342040301c805004460380c61910008680050103440c25a40e40071580307541083e0007034240c0160001d0740c00010018415008001d501a242c11070000c0c0708007040d045240700b104407000e20b210726a43e030a110080e60311880900b4804181c20480d0b680068100c1c00c4041c0300707038012032000a00c03070460200d0380308882c0c0c1a103101098621814010f02ca42d00c050180b503005d403a146000e49242d60740d000c041001400003500703036202e1441c10402080b040e1801c0011200030100010244500905541400b006041c0c904e030200e02542006030201c0305140004c104e9025590140071408595600d8034101d032281c202400c0d08820705c1c1e0404c000100c1d080f0034090b0f55000741c000c00040303030103920b00400034011203840c14410b41800344110041140c04201100510460200e12011400d480500c4c006603490400c64000c541c060f10311030300b00c0c0a20a10031071050b000e410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 509985836 1250 509984586 509984591
    0xe15090a05040b09070506041809061503020a060e06030130200d02090a0507020a0c060216050103200a0c14070e0f0f060d0201090b0a030b030c0a03030207031b05091504 74
    0x44040441e17455488502941d50800010441005451580f2244005800350840c001030b080c01141e48080c241c4a2087c03655140348510601802545000e00c01400240304900307112012350f191101040503800144100074404540304c0e0341c20146060341000c0816403100100c641d9449070203140034040d141031074407114464070851007914185e0a0400001010580041540340d00c2d50310301c0c5c001c00c040c00300148460118080c20207a14002942000e0210190155030040d0800550031403407155096403a503c9541094100007104002d814000d001600c81c0c868449400d031b0300c1c21110010b89a0100d10000240011903103501103203d504003250180c181e5500780c40d1204140c40b140c8568001c48016180d0b02a07201d80e42d40414414505040c005461a03c10304001136004d0340ca1032500c1d03680d0030621014010036105c080e000c3d11460148041c01c0801400c4460452650440c1c4000f5607405650200a200c0c1c80c40c80220040c9480325000a80148002000d1034550319042c00042c8400965208040c000c50 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 509987086 1250 509985836 509985841
    0x20d0c030c0f09030f061116120c02130c0207050316050f012115150519020d02070308030a021605030705071202181513140c03010b040e15090a05040b 66
    0x9104140c0d42c0c04a1502d6a501d4104a045440380b045845000c44100c52065030b42d45040c8002214401810341554a10112801c402d1907041c1181c1104108040000f00a060103e0b000107a55216900e04611281c1c1e000052100161030140e15140703060700080d506102d50b900d40d25030100b60076114419500241d603400710355200304005555600c051401349d0b0f9100c02005030600055555844000c2d19214100e0303840f401c0c0e0361003540d1640c00340d00702c19050004c0c80001d26000d400e0403801d0a0349615007140300421b8404e44400b80252101801d0100514144d8000b01107903400b4074540642d44850244030405891202c2441c180d03a403a840380078115258085e02e50000385c0147e8690810b24440d0b005032683c100c1c0c0f031060302c400703410100051002a100c03101049644058a85190b21000046c0f02440058170141140491b20300c00d8008000a80486040006103c0446032000b45c400301d60b1344640c1c00c3c01310f80b04e420940302ca0065411040d60494076490800170702c01c2d080e030000340c0194000c1180d45842e8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 509988336 1250 509987086 509987111
    0xf030307050f0f0403060603230f060a0c0908030f07030807030902150f0d1a0a14130b0109080d0f0908030703020a03080c04080318090c2803020d020d0c03 68
    0x2804115102000714409200c0d084100e41020001d0100024655442d850603444c0c1d5504003c942d110780080e621070114280c010341c04400100c0b02d540140d8440000e103024218102c0301c0d40c2d280001000c010071780b9202d5603003081a40c01a8111070141c108101540c0e01d0741c049541d0070b07103150000b20080d00051098008a1103040c000e108043d582c84d009000000c01686a000c00952540300b0000400d040705c003001400100002c3d480f03200c88c0d090780c018a02c843c607001e05080042d10f40d43c0e81c228040c000034070304c40322607580c0d6001c0103964009058403010481e00700c0c0000603681c54103154000441401108420219035900c030b0000b01e1915003903100c688060b034498147d036507a8000c06c9801800750b030002c14400302280c050b4200395404618600014609074070703021068215049440d800311920281c4c001030350355180051941d58804480411b503400e0049124075030051a001c9144542c0c0d4201d00e60026a000e40f10b43c04503000c0290206040d9601c450000a620050008400d50f03400a1700d00300c41c21954 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 509989586 1250 509988336 509988343
    0x20030601021c02030304060504330b060906220e040c06030c1b230f0c10030e060703090302010906020304030c05120418020c10090503040f0b030c03070c020a08060c09030f 75
    0x381000b07a8020f40c119602e56440b0301c020640070303009036440103115084072060886880302d42801140c000e066480f0a0000a46100b502d2200549070300ca25000d020f00e840f103498030801e44030042e0001c480c52030012024808030703540c294550821540307861800c08000522800b42042000c1303494540c1c04000c0c0c260880310032210180f0030b01c5d409411850015481d800318100720000c2958001c199220000022110500c03450701e00c0c04003011245402c560004006440c00c030b5010020b11201e42001d214160403a24025220640100844181551080c1d0001414800d40c46100380c2c1740d20410440d505e0400c0d0501070209542404202c8891203041548240724008800b03641c121011010220f80f000f42e25a100340294200716171641ca144150594150f060404e0300030004a14025000ba554840c1010520a0342e1003403034000341d002c5c00d0200240304440e0041000c0300d074003103042e140c50510603c262001852660041e40701c8070003407041000303100c01611888000c000480d02102207640350303813000210984 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 509990836 1250 509989586 509989633
    0xc040f06050d0b010e09061b1b100c080105030706020a0b280e0607030c020d1409040c051909050f01030c0509030607081e040c03080a120501060207090e0c0a17012003060102 76
    0xc0c004100c600c1400520501800b6083c82e409c1e0160301c2c400703030050100d140d140c010902200c12007161140c040e495110f820520303040c00b42c80190040d010860600d50302a6403040171f098000c144001c1400002c1e54400054005140c1049507030403d0004c0e0207038086480a8907a50740780c1c0c2c0031360281c4408501020700034419290703028102c0d000b82014448000082d20020201081c2c2c1c4810141088820181c0c0e0301d6201d1580d0102c1c035074841940303c518100401800c6a400f02c5441c040c407040200500943d42c0c1c1042e100c10140d000d203400f10300258540c0c001c440c1d42c029004800d0701803103064203101d0b19907000b0b904039114080e110040c0d202d00c081c9403154107001c40161005443c1d0141c1d4681400030901040080c40b051010b401c00c40d6881c0207c101010407034030264000001030f08620014020403919000306c2d80d501801c24001c0c800c0300e0018000070002d03240d61081102101031035005580c404429003007200384540c05000400180e0201c50300e0010f03a130003201e01600502036105a40c0750500750f001e4080c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 509992086 1250 509990836 509990851
    0x20d090b09010905120a0501110a1107061205060604120605071202180603040302030f040e0105011206451406030307080319150b19020607020c040f06050d0b010e0906 73
    0x203291444d042c02d201100c1c40003100025140245003211010441c2401144070700b914110005990344182280145901d0001c0581c21090300009410040c043c2d0114502c0301140c81d1400c0018103850740d0002440030f00c01d0751702641903460340a00c3c0d4401d001450744000d1040e0304644614095031905503907003040340324242044030034088440110380c03981000c002940c0e01501c81c1c0116441c100055841c844207804c158440e201c180034680c014040e42d43e000780c0c0b00950402c4003000b803024a080070184500040b603001e40006141100d000e510f9404205204040c2544114480715001004600c04c2d001404105081900440300b0710042110f40c10000211544a030300b00f8070090460300d80082100e012040c2120091001b03440f44075081300c40e00400300060080c0220100c9981da06482d44040710500400410003083d50010801c001c401c0760085401010340c0001c80f0006141419401000014003503500800d4003c51070000702401c120140d21414182c90000c201040d1a0340d41d07078145d55441c0022031f084c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 509993336 1250 509992086 509992097
    0x60306010f03020c0709091202120a1b0f121d060a0806010c0f0206031005040b0a0e16020703080309010204081009240b0d051f0b0f060a050c03040303020d090b0901 72
    0x440c82440703980640f240c2c04c10b200c143c0300743c190385a068109940480005503420300360075444001c2a5010410b404003154209461410815095000341000d4107600011106546400c01c41041000f894580e405541d401005181c0800e00e10300010180d00c7c00022030a401c03100313201c807002e461a000045d9400f0000a42d81e4103001e588400045a0000b000c0300101c45401500a507031005030342d040c0240d48100050075170342440600d440e040000340c9220260072806841440c00620414844200d03551f80281c004851106000d81000200d00d402d1080d0f00281c10458080f0078801d40400640007002141c0011048514980030b0515034000c44910b807800800c40f046480c1c0f84081000601e50005014040d448009051514800462a004240700c0112240e4100e10403844a0002440c000c0005000b40b01003003280304020004a40014a0b18080502c103400105003039084038884e00845031803240c500141c948803984e0b403501a41e80c2d5034820b5000003240c0c0084d00810007000b030f0fa040d21040c02050351407 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 509994586 1250 509993336 509993357
    0xa140d17190c1202070b0f0703021201032405040c050a080f07060f051b0d03050a020c0c060d06150909050115200c03030a1206050a080d030e0a0b0405010207050c06030601 75
    0x1020002c0100e10382075800d01c0041414400640241d01c00340000d03c5c080c206440d034500e002c0b20100c1100c04020465018180b05000100e9252401680e241c15641d0040e20040c41c5000ca00c000351000e0003035294025981d040c00c082008000300d0910900454600b0350700100600e032500001501e070b000012103084194131940d010080e4a201c1d80201d12032241e1400d083e072801203091015a4030320180c4011404640c06043c20b0102e02c2d0b814490f46501c00006803045082c0070140d05004d41f90442e88142c140700c0c0c0e42c082800d488a03401603220358020001c40210908081c4441400b620740c0189120707859803a880d00000044100e04200d0220703443c0c1165542001e048410045405041c81000c01007040703128003020b4202c42d4500304010041848a600c4052950800c00740200a42d81c060700594014443c0403410840014000b070440b02d14105401c0108401c1800c0138400d11f03125070b900340640303001419401d20051000650007881494050307401d44141e80c04000034040720b8402900d00c5030000320074400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 509995836 1250 509994586 509994631
    0x20102100b0a18020c0f03090109030b0414010603030f020c030c0f090a1b1d0a05220b040203010b12060405090316170403050d08010812030115020a140d17 68
    0x1061540401007810350496243c040030701050303841c2d10011803000c1d40000e1000504004004001445040c10015441c148030140000c0c4001d2840c07100070b182c0304040c40841c0c02c11807005112821036582200070000c00380d03a801c00400200b9080c0b0040054011701b42c1440da50b04011603410240380c4043e101020228000d0140010080c0041000301010380e02c5140c2c0503011030300140c00c0310342c5403541e803040c0c14145280c0a01c0c2409500e0701e043d602c65270900e401000b0b15150080c400da07440c5d8080d03244011704a080400d1901428210040a6200d0300c0000045a9500d1500240c45d103031380c00038494417031940d07400c060000b252016a40303100250b200b032150441c40c00641742600c001c0c138480c0c0c40c00d5424649128881449808ca0342003100c10b504161101c0c4070b410780c000580e50050100a000301100c1c002020114903510041c0601c0508501c400d0040c0c250600802a00340c210b079005148160384070010403032070344510100b08020b0000d214070400c007070700450701000e95000d07041c045990381400d0990320 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 509997086 1250 509995836 509995841
    0xe0a030215090d0c0810200702010504030c061d040915180203240c0a05030a020906120a0b040506010309080904051806040f1506081504060209041508010506060702010210 75
    0x6803100c0d2a00100403a2596481d4402c0c070307a0443e40316595940d0f8090a11000703d081c1400d202c2c920390f01a1030400c41d512080e00c82d01500805502d080c410304e503a100c1a00040f21180709070382011f0920b81d0030350400034005038062510354003204540d070741d400d201c4048420032080d280300300f0001e4040c144d40070b00317002c0010590384445924018a2034844128040c1d502082c1801e0081540009000c4003c51003005c134075124800303640c0180b000e820f981c03a00d080e620700070b010707400040c0120400e03941c0440c04080648840044658040241c0010661894507400c06009444030448150050341410007282c1594042d0280c00c000715440031101e400d19050b4000e101c004d24009209091300b5044d8110402c5151091007500c2c011401112084482c255a00b402207c581c280c2e0910100a85080002c000800021070314051000480074850482d4441c6e042c89c1000c0d018124800780c1c854030740359480400e0f500901d91501215007040092016540395070404ca41d60141e400082c1c003582060a10151260069 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 509998336 1250 509997086 509997109
    0x8060411010306050a090501090f0204030c030b0c1b3711190b2101180509070b0301080705150a20070b070303050603061303120c090b0a18060e0a0302 66
    0x18580080c003d640e035400a02c103c1500e500106070141c0e500e0052252058a024007000c00041440552509141d551501040007007840064050900c030404103007141c00c03100440d0500c0d25454814540566a0f2555170f86071240900a800e80034082000f05070120070012200100c00144003110703a00e0a20358403908000300c0d0b546030341640420702c04604003000740056810000b500b000f100a5403aa0701500c0d2400381c03040c0403080d030303038000c0b169000400034074110345a214004040018086426182c500d03130589015240d80007900000c0c0044004243e06400055000454070b00f15071180b59180c800f0f41c0d62225201c1c84030000001028107000600030440440801605078003c42111000c550ba03081100303075030704290022000a9281ca090110a260421901d40c00040300105141142c50b9a0f401a040d52800030314940c9054690f845a454103001d010321074020044c042600341e603000490001841e09070108007910b003102c544000810304512402e1003007e0400040c002c000100d00b9074082040f11004c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 509999586 1250 509998336 509998339
    0x30503060112020705060a0b3102210103050c03010c030209030a031b05010c0c020a060203090d12030e060c071205041409131a0103050106080d020a0b090a0209010b121008060411 78
    0x1c110f1080005d20800c140e40c8904002c0d00c3c00580314108c40104514a401c01189200f03c40c410b140d03c4d203000e4644130624680b81000100169517841030010b54024008405001140076040000001445070215040040b000100e00810400300402c00071340484c02400b26007900743e40040003c030002070080800036a810010b03002d5a0300000d45642d030f20b00351400d404a80b0000307242038410a00318207003100007101400741c0b03001840c280b644134000b05446c1b02028402904d01d98168a0a070800d80c001da000c0702c00010180203851403880c04035400783d401d80c460350040321403002d12013280c222a031156081e242039805003220817040c02031000400c1000f000140980080c0f0b440512140c00091444a50203c01104c0c01289040303585542822800c64256500030030b80ca400c41680f484401da1301088400ca09540310340b0610740c584800a082e89172a0314440001d4000a0410010500700846000b411b142014016030403029502d541d407a081c13081e00e80c130850749250300020203c1c000034202018100d9000c0c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 510000836 1250 509999586 509999591
    0xd031e05120a09060c0504061b17070303020c070519031419061a010f09030f0f060e030c06100315020c010b192603092b0605060906030a030503060112 66
    0x103003080c04929035881034507040b50701d90760b03103140303004004107800b41803c3c2140d9800e0280c24603280ca00c0203040d456507903180c21054613140081800700300300d00000c001e480c1250380c1195100e04907450094000d601210700c3d80300c40d200716040060540303030103900811825122500114054034642d00c644210710941100c07aaa0300a40b001d903071614034802c1c00610164010741020030303030402c0c0300390203041c00501c0a50141000a400d55006100750088214811070b580002c822042c4074050900300c1400c4003522006204e60308158071000003100020282500c5100b48064400344e480320412181d107581702d40300c028040441164040203903446903000d4800b91034190f0000c03070440f0316000010440440d8203034441c2140c40c0410b00b8440080d07110b4105040450027a0004604c0741c05400d501da8a01135039094611480c004c00c1c4011200c05002043d0003844107001022845a10740c0c90450090a01281c1c00d03805050b90000250fa00c1c600019407602d49134241c0c440d01d1664031900e004443ca4521180c1c045240c2d078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 510002086 1250 510000836 510000847
    0x50f0c030408010912030c0914010c02030705060f191715041d0106060f0810031e0b130204050a021c0e03041706060907020f03030606181314060d031e05 67
    0x800078004d83ca25240f04040b1702c8074040c0108005001c80c0c0d41000304404100c5a28410700441b950350b4030b0860981c0b4242424103d1401134400203151480d50b4100c590000004100d9044442d81400582140203200046403040031200e2000c407110304c3c50200d000e940d15240000b0032640c1c0800212500d151402500100d0350110301c6080c811900f040030b41c0041c0a079036585082110a40c00542055407040600d400b4850742030034105414241010300000d400820000038000d854010300015140286c0d0104c0c1035042403900092010204e0207400307060b800365007020300096200540b44203c917200361404506d00c440e111200031040c01003601d0b00d900c1c84070b4882084003160b01d544520507480000700420080c000751038408140560a280600f5500c190b610415100e40b140c2004000c4d298000005d80e5501c0e00e44c03950454a6040e540a610f40d0f940207000000d0040c01c0c0766a50b08400c000e041743c49114040d60729000240310300902086c50150019840034070703c0c00e000d4264002d40b8010480b070702d000da0508 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 510003336 1250 510002086 510002099
    0x91d010207050a0519020604030221070306020706050c07030804120e2112040b0307120906060b120609010506120a0b09160e0604151b080a0c0c0902040501050f0c0304 73
    0x2a4000101510640d200410300c0d401c002003000080801d00c502aa0261481740c6580410903d000e00c0c00005e100f01804080a01034404000750000e8400302e400407a803265903641403840081d40b100c801070b5540c03424030002a00c8050003908554580d507041d6210349259449440e519565a410303e10341081001d0400c40100b10b0f982e01c501604c1c3d20b00c021801c5486204903050403443c0400c00000c008a284040c803081003a600f081c000e407580440182080a081d843d1240e841b4000c200070140102041c1c544400815100085400350014074400901000240c0f21142042600c103000d102d0300e6801001001400103a10703401c0410344d044407060f02c020580c3c020701d0000510380d103000c81c0c200d48102b141c40880d10145a200b190450f07502400d0321000c0c0741504082d03480c03003c4a003810649040c000c100c40903002074001da0000c8000e05400c814501d440d0703407035404020705000c1c403024142d030301d03e960300c501040d00200382c03007198200c2c1d03016121580340000c8c502d4242030a8000c842070500601050100082d81c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 510004586 1250 510003336 510003341
    0x22090204060e13090206160302070b2701110705040c030f0e010b0a12020f0907050702120105093318011107060e0a0b0f09070317030402010f110304091d01 68
    0x10307000a49510002a061009021240a950303480c0700440782040d0b80b0a0141c1c807480111490864052000104621242816403802c0040c1d44103e4110030001104071020b0043c11041c4083c091400384202c243e0080401181d0700c0c42000b007100890f0f0081c2e40204403901d03140d400700f501850f203810085008504042407208540d29850542d007581d440380b0000242c0d2070172201e490090090840707074000454060b00899114401a01103500611101c80440e1100f03004009903000294000d0003004a28400e2680501070081a40e8807017840c030800d4041c3d1312603840180c2c0c0b64108100c0e0b100711656000781800505549030058100d00c942164030710f103c045080207006038205000f04414944d40e07a03116203407550441e019010702c42d0251f040f601c48480006c030419041e07034221a4101d40300115413074401085080641d150301c01400040c80149002c039028119011f18400c2e8002d0b00c51504403144643d081e101c40900a00d511700c3c1e1780080006020b0300744640c1c0491038000c4102d03000b4500c1c800c1c04800a08 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 510005836 1250 510004586 510004589
    0xc02060c0315150a1106070c150f05090106032001050d020a031b0f0210021207030b040f0218100c05060109050a0f0c1d040e070e090307020306100905010b0f22090204 73
    0x100d00b20f0024018401507040201d03a51710790f004070000c02941c80d0600340100b80c581102d00082500248140380d16044890b03400a06581e0700e00c580070060342c201040c02d24007e00151004903200b000426001d1104020740d0038100d40c41006031542490034076400780a070020350110b50b0a9081c1031380e480307200d840c1e00450109411400f00360345039504000c0107203501910384182030341c0b00020640104008901d00003d06a0150403904504011480d451248002000742c0707101219100114070100b003062a0318850401110b201d0700030703100010541d815900c03c80d0380a900e030710060302940c800b400411a41005910250744135030030550018080d03c1100a80741500c003144203031000078130010815800400b0212000c41500030851f010048840e43c4405181c40350900e00ca4402140030000c000740c03807244144101c9444650003001d40d00c06142c101d14030f00340781c1e0031802440751032403a10001003082921841100e01c0ca20614030360394107043c3c174031031855508450400a24080b01414a001440c081030303001520 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 510007086 1250 510005836 510005869
    0x1d0d020c010822051b06040b04091503080c0309130e06040b070905090708091605090a0f110c0132060d03110f0c040c140d020f070b090a1101030c02060c0315 69
    0x8000380d401d04003030001c5000c84041c0b8846e940410040000d06c0d09a82260300b101c4a6903004522480c1141c5401c609014603030001d440344d4400603a60341c000c5004001082c142c0310840380115001001e413980d10442d40e16005c46481c0b580324002140224080d001d100e40d200d4041c0c40c18401c1e95458030046291540143c80c6480440c1240080c446050030500560074403c401c01c2181e0030307452401c400100b40b58006404800419980c004103801e001c0d640c1c0080c1100e5030b13030a00095503002c01e843c2c1c050003400750901030780c030803000080802d80341c41e50b0f60b40840b441900b1003403404488d103500c0200b01c03019550403421410300c035416031100c44492043c00849a0301d002078000d0140070380c1040512095a07005a008170400030807403480c0150492590070395601200b0b2501c01619903c0311080b400341031165100142030750020320100486010001010705075030b403013066810160301d5184015010f68441c2c00110000da0803410000e1035600048000e591700001825640400c0c0035502c001c10203156500c1141c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 510008336 1250 510007086 510007093
    0x5060a26100609060e0402030a03030209010306030609080c06011a04030305030c1605010506120f070b0c1612150b1c0302160602031207020f190f151d0d020c01082205 73
    0x4200e03003040c0741300340c6005010040d0811150700c1c03c1d6000a8480c071060100409050f400700e42038404ea4400e501c021702451340102c0400103040641070116058002e01505221882001d0010506401d02d40e141c3c0d50080c0054001e03030070319085a030151941d4100504000701c00800b8000060a24a00b14200043e6030164000196034280001401003980c0c10008a01c0305601c03100002901040000f03130041220203000381d03251078070303070040034a402c1c10400884c1c11001ca04132303100407460040a0503102c010500c258212403990217025012001c0d12454100ca41d440106244c0c0c180400700240f0140140c2031292040c0d413071696480182ea1425421608076a00580c0040358042c1c803101d04c803407841c0c1c1005c9180000e000190000b01296512901c442e021500001003060704000c000a00c00e18000c0390390700801d440e000c103110001400040096120301c442200703000079850142c503070201e4001e50060382c1c2da02038a0440030000c01510312003809020711980c07100542100d0910717030300101482101072069024 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 510009586 1250 510008336 510008339
    0x80a1b320618011d1008040c05040e1612120302031008030c0c0f0406030b13060204330f0f0c020f0904140f06010b040905041104060305010f0e0105060a261006 70
    0x1001d070100c00c011004c0030429100707442c1071540e400d1442170418900389411359540d40c562401c6001c2c00c1a55000617002400d155100340120400304000c464030400401c07108c1c50719902e4803001d210f06040c0074017511001800a190600511a800850340b00c504041e21100d140d0382c840740340349540d2040700c000007142c201401112a520b402c8000c044101e03c1210248103550442c0c031030200da0200946201e02d0840d400504008006964064500510305600700b04442400405610300441746c0c00c5c036418401e041402c4070201e40f80102c44480c0c4144850341c9503603030070100100940341d0307031025081a07038848070001150232179135142200a84224414850b40c46c0714404488000d242c24031021030880e42e07401000c014460a0480703429a0100c500c02140880e0399110b908001081c052186000d0740c10900700354000c0184041500079131081c034992441000203902100d01d150032140309640256018400050401200210407203c00c01d624041034140c100c19034a54240d032501640350716500203180c48100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 510010836 1250 510009586 510009589
    0x3020307021f270c09182001080a140a050a02070c03050a02180f040f02060c011d0d030204050607060e0102041805090d050c0607200304080a1b320618 66
    0x1140000c00f2500f540f45003910b00d15514002841820300030100035907515940c2000d60701c0d101e1050a8091307009050505100e282d003220940c10548402c4090204901074081403403980b41d48030b580160304000ca500211500c0380074101000d000c01800c41ea080179000d2200c0c030086143c070b0340003000a40c443e40040150100724414032540d102c500541c130849a17030354070070405003211140529a02550048421000e6001840001c080340903102d810505da41c6421844403c0704143c10800500c3c150040841c2c41351030025104805a11036405402e401207404e01004002036142e41100c40101001d000240c06e180e10307200003806200101c084141125111018001c0082041c030614a81c4000e91510368549162200b400765144000785c030380340170001070341c0d440c4040d05a81a6214114030464040c1c0b50b07200d5a45c0400da0fa00c10034140d042d02c3c05203100d43d070840303d010710040d404100c4020810490104140180000800245c40c11460203540001c41d400d20a6403818020259512040e130f040404008420 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 510012086 1250 510010836 510010871
    0x6040b130602070609061407080301180b040c1d0301060e070804120306060e090a0e060a0c08160f05071a0106030603050c03060f18010b1c0b0705160303020307021f 72
    0x610072400e40d000701d0800d21038541e00c000380105413030341e5060100240c3c1124603c1c94481c4240e030f0015001540200010404e0001c2ca022007000b40d0200e5000d00000d82002c00f0071040700c00042c1118045a001000f200c00c80c0c5d540041030029003002000002c0a0b9034030f0058900c0c10f0b00032118840065080e10802c410001400d42d0f1001000039480e0820660707091010190401c0c520b925987d200705400c40000d601082283c100d0707103250340c5c1c01c400d86d4001c3c241705899001030000070155601060380500081c903030000c1c0b40102c040307162483c0da52040c440c3e40d602c01039035107a210b04803e640c078040b0380c9400c5000310506106d0340d0085c500ea58000400c1803540c142a400c0c034101d017840e03500c26001f410520400c50311001d202c0c3c5e00813610060840b050b070b003800061801045200b2038250403140c01a0b00030316011310300889845907401800c120790259100f980440e2584280c102d41c4001043e0b4144841c0401c0c40303039002d0b581c81801030044a501d81d180101d0103800c60060a0701444c00c2d5110b18448240c4d0780700c030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 510013336 1250 510012086 510012089
    0x10206010b03071d040213031b08150a18140c0406060509030a02040b010c0506010b030103020a0f0e13230a11040605010e0f0a0b0708030601030c08090d03090c0506040b13 75
    0x1a041d40c15814008001446503082c40340400d40d41030030408402056403158122003940c4e41c4c440d48039400c0d6031342e0701e0103040c0032a22240d16031602594840004841c000410b0398018243d554030030700b070584d81b071070b40c264010461300d0791502522040090303000001d02d01c0c40c10800c929492000418802d501d40e01000161501c9070042020088148691243d03614001510762009078102c1e8040741800741c02d03004075403810f407000d03028009100350703000010011207500003507050b2402515682d540948500b511004640584920049007030401c0c001000c090300c5041d0355903600e124105e03403450114101c0982060031001c2c3ca00050a03044a420741e000c014088500d0265004152818400180307400c1c000b804410700503ea040c041c1c0d803504680603183d524110b041e4090104030a815848840f94104a60b503a00103c0c1d4440c042440c1c401c0000b1000d014110561058000c003001740401d2080002c12406001031900c21515618a010301250b5070b03480e0030203800038240481c06a0340b15140041e24030340b00c1826 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 510014586 1250 510013336 510013349
    0xc23090a060e0f071206060806030f03041a07080405040908030910110d05090f06090d020f060f010306020d142a0901140c0c040906020901030c1d120a060c020a0201020601 75
    0x14140104002e048a009490b4025142c0d14107840340d541d040001c2d1442c1d809000c0f003440c0305152a1020403459001414280900f00503000c48840013080d040e0140e40c1c1c461802100c981a03004540c602503031070490010034541344941e147c2e0381003d0341c50001c1000d407001c2500840301c15402001300045518200310f10400c5608141d41404010400c601d4090b40c4e21402c030000e24499150f00000b00200303c10842261403030600c1e011100715180000425484d002c1c184010001030241082003400071500080700d41c014000903040510503480c0d41c1d2090000d522180c0104040303915007020202c01e54800c110b842c03241032a00368021170340c445a2440c640c1e0000c55941000100c000f881450604e0f640007020081420b16090a00d0b030382c00620302e08515110000400d95409401d09461404010090300502002c1e0303403e880512410b00080e00a50355429044c87c40390408a10b078080100d1440e05000003503982c040d04060301c0000360326885840907a2404c00c079403009a400b1004003021542d04201041c0100304 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 510015836 1250 510014586 510014591
    0x1207030b0105060c070512030715140c0703020a0c0e180f060a020912070618120f02010e011809091101020f1504032001061809020f06070c23090a 64
    0x11039490030681003041c011140100004104840e10000400098000d46402000070309185030741c00c0c2e42c2d50b0f079910991003201c540140708000c40200c1c42c0b601074100310700015088201961307210101c2c0801600052030641c111300c15254848003140d41e010904001e402003880502052510540e05c1840050380f14484503980c1c8004030400802c403002c070700c1d1900201c2419000d691594040c0008001481840084909010380c00e4002001a00b201d00008081c04110a0102e4180d84020368044800100405001c681c001419000150b2003801720251890050500140c00c4220301e03c9101802485d030403070344030243c2d98500201400300340c400c10180280240f0003412070000c2030704101e480d1201031101e12410742125022504040c058241c2d0b50018844400b002c0010544540c100e000c1d0400d0300c40d952000070810321a410005142c0680c5402a4000e0321841103203980304113103e40c030791003858180c40004080d0742c04540558080c042403403901711a203600303030b0803c1c0850402070401000340c0708040c500d2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 510017086 1250 510015836 510015839
    0x1b07060504050105030609060433060c021f050d15080c04092d020402070b10050a05030d1101150b030106080105010302070b060409170318060f071b0302010605030a0b061207 76
    0x713a1100c22684d10500542c2d0074560741e00c48501040c06040642006a0364011813000740c00816405007402d40301c802c02039581c0122584c0c640b42030b5403441003001c0194000c40b0824240b106400d05c040315403110345c030b2881e003d0f1810b50108079140488641507540c015661441c0c40c00c0020440400000000040c2101c080003111107075541c24060383d001503100069240d41c002100a0060241c1c50800c0454018205542c0c610207450400141001150390209980c0300c42c8000c151400c2c40000d24099075000b4004103001806e52a050313440c501c0030400075195640742ca149808440c0601d1498004080003905941c5a5040090107442c001d0b050700611b0405105020382c80c04240c2808286400131015100002c20300d82504100d0030705c1013429440100b2034000000d120b0180316a07100e01d0280c0300b00005407142a1141010900001c1c400d544001c001008900d40340000c00301c08071503461252090000181140d91600842d081103070440f801c1d24004a00c508120245c02c080321003a14020320f80b0080d01449 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 510018336 1250 510017086 510017089
    0x60203070203010e031813060302180a050a20090a080a0b070f0507050c120a14060702240105040b120a05030a120c2109051006140a2403060b1b0706050405 68
    0x800f4403151941c0f0403141d05048142d907c502ea840b81019580207054400c401e101216030900c0844199410400103240c400002c020b2103403417003821030300c201420115a1480008802c2440c5801580c120b5521004526001416010402400d004c8521407100695546482c80b4041c3c8000300c11015641445070401078a0700145000c06c4500d5205811510455803a402100c214502040c42c0c4000b410101100c103180000240059400d1040ba103540c21210000101c10b122221300f01d5030344166180011000041c40546850f0700f101e1400c00010b09018201c26428540340e25089032041c068504d80c1000032806c007140d03804155042d4000c240c6e102400032651450009000d05010340c201705001d800480859050911600b15401d0660030400311601d403c2c00003098401022103108511110003240302c0140d841c1003070f550150460306891040700c81e84460640703800840620b44a204101507480901043d001403240141c1103143d42cbc0034240940da00320101403807502074580c001c602882024841081103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 510019586 1250 510018336 510018367
    0xc080106021506010c1e061401050411030103020603091c05090f121c02031606140f0f0f0408070804060f02160b0417160605130f050d02060a1206060203070203010e03 73
    0x4083c00b0300c1c20207400419810504880c00290750640000f40b0801441c0e01881941e07000b6025100c40c6a8070401266620010072045030751070101d07910340c080188010000b6140042c00b45900240c0d103003c4c0e0310752405150f801c010361000c0340c0344907000c140d010421184600300383c007030702d03a0072081035030f030340c1c01c880340140c006503607000c103207400100e12045080980c0b5000d00c01d005454001081490410100000345001000361507090341543c0304880c45400540484100710f0b030039001c0c580114a8134501d40380c5160200740c85200500507a001c0d5001c004d000000303210040100f00404103541c070070141d03064083c8000e0426503451454803104230a81070601482a12808a03001c6a02800d001c0c0e10124000c42018140b04c9081c201a01c011409000002c009800c84000e05405030750480035000302d13844401800c0506441e004498200341030a400764010f04142c00108907000141c284034a41400b0300702d003074007980e910350031180061f00301140400441c102405103441c0c1e4178070030003d14245006000e29242 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 510020836 1250 510019586 510019591
    0x11a070f0f2d150203060a030210051e09010527090f0402040b0328031b0b06031207030e0405070e0d120f091a070c030501020c0604110f0109140a0906090c0801060215 73
    0xf0706500101007140c0390f440d10480c0c130003954003501081030003546040280683c2c00500702940040d07240f020b1600007084180869200400586445e0b040001103080d0701c0906410028503044100000e02082c0244d890160442c070a1441c010041030629240c41488203640b842c41005020354800b2031840c40540341501484c0d048000c0051200d10100c66003801c5a00041c8400c595054070705c1481c074a8203100f0301e440201e114810030740481d52a5100174807a00c16a21901c00040c0025120309104081494103130071603a0400702518003403030010740c00000605042c0d50b404044458480002c0e0955406801a4001219007014200480c41c5841d02c2c402840c0e1800b4011200226180010445d08102802540304080d40c0c22000841d11208240c2000b6074070740041c1c4003514107a140d1351700c04a0501e443d4600200070001039685110640c5040511483c42d02000060741d440a804040459600418480d83c0006c0040c24008034255110f8000602800c606030001d0086400820003126402d1800e8001c64 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 510022086 1250 510020836 510020873
    0x50402030601030f0e060702011b0903060513050d090f1a09090601020a0f0b06031507020c010809070b0f030124170702031911070905011a070f0f2d 65
    0x590340c1d641e6000480040c81000400710810f480c107010140e03901000074120b881206680c000f000381001d240c0800d0390550400411700b0010700400820f10008116400141c0c100c0800034030000080c015903a1241041c0d2415411400100c1340c12040040400c041200b9000b011024a408215075050b05094200d1103003401581c003403d90b0b0340106449901c20020000303810b8221250441d0311040d454022a03804c0c0a039959440b078071401c8002e480c81c1d000d4150160180d45107400400f007116019006481d6041e005140c4810790144010001d500c0d1851001091080050741c007441c0d0780d60416401400ca5180c4540c50943c401c848622624200c2c3c1042e00a04c030a44d48490303421383c96540101c00c0b861842840010140c00400605407014030f60041d443c0c0c0c0b03500c085002510f11881e1036020a00071103000b40f140d17503140c008081680011000f5100103102c2c03030303000721110407001c0d20a4071205260703001c0000844041541940061200c0c403203241c44c444500c409031526880d20200d840c2c480141846000b41c5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 510023336 1250 510022086 510022091
    0x70b0c19031808040f030b06060f04030f020315070504063203100503030703030903030b030609120a051920060603030304030e040f1a010e0405011212090e01080c1e0a0504 75
    0x201c074a03454001031002982d80f200e58990382c2c3e500d072640c075883d030fa0051000f12010455000810b5540ca0000c00b0303200100c40e0203403490300b41880e40d290800c20680980060313816010700303008119951a007400e004c0c8511403075223910342d03a00e1421070f00030700125061a0260422030307540218041e0341400c1c403403044d112810342c003619140e845403043c0410f040d8a55009a51611001901804040c0c064100c3c01c1090700940b010400c4487d00d05c2070607111901101c0b400c1c1c6580009869041c0c0401c1c07000507102c91101c07458a0740c241030442e91000c480c201c2150304000413500c8604501806c2041c4c40d0503000129500c07000d0801c50a1120210350b4a01002d0401400d001205288042e180ca4a60140100010b02c0750103001d0080c14000b2149a0050b580d5424005000003a40030410704050040c03504a400f8501d03003000b100c0d010340b1110510020001c4100420656020000d84140c0d1250150b0184c401c000151034a04907420030040d851084403c80b0188000303030ba034607421941d207990f540e46c100c50041c0c0b0701 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 510024586 1250 510023336 510023351
    0x21b060118021c09050604060513050a02060c01020906030907080624012d080f0a020909040809041401080c0415081c11070311030d030207080307050d0b0d08070b0c1903 74
    0x600c0c1c010440d1070f4802c654500c2d2441c01c03018450000350b41030241d0b025107810021600c03a0541c8500b407110020001d01300364450f6402ea00141440401000882c3d00e0400050506041c14000307100d5a0094504036142c0d0300001050182a40606c5141d80054800d0940340a460920102d09800110150814144031404071a18805000607441100e041d034050042034820040030805000454181c94002803c0e0f500800100700300c0c2a0320031141150350082010520390380380c0da100800c90b4843c0340c1f426000f507260021181721080144590b40a422420b000c1d1441e0181c0b0410b1004444600711000648109584100482880407640620400880d01c075440e00304090fa00a940703000b800e48130780201f440341d014004280051089003102e00f88088003580c2100da080e0318110280c0c010301601502e510741c01c0010480041c01003000f0f240f000c3c04018041040200f040c0003070045115104140c60190b000030b0000100106a001d4503409000b42824600f0040402e20326035005094070b181e0018943d5580340e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 510025836 1250 510024586 510024607
    0x207111827070b04080105070801051207030b0a020f03270106061b2f1f02030306120f070e060f0102071809051c030c081302130506010c0b0406021b06011802 69
    0x11010300900a0041c0e61340c1d07602c80d51a4000c1074104c40680018600c07000101d550315000c80c152400d4000c1800809089040d40c4a40038040c41c080c108006003035080103024100e000070b5019620910401c8403056184e1840d9a944261000f03515405c0d90a17494180e00307100c441d40150208070401805000c4e07508002c035070300d45200c040d18015401840c0c40851100d60024035144541c10741c6000c8207036140b000d0f110b01120a2845030140306001c9001d03070400d000250b400e007000c28034803042200400c00c4641d006442e400203410806e694220b40074002c178120400c0341038100b10900c0d190404013803009264003440e00d00085404c599142c080c10b0825103c03e07031501400400c00c040211100e003e81e80b5102800401d030013900400101401c90003240c0b004000526503600d85042c08501600606030030008940c0551200041c103000b00320b0b80c1807110b1000400003080d500840544620301c20200145d485000e0201c16142a8019460311920747c0000018800315512400c071404ca8003881c4070140c1c4030b01c110308 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 510027086 1250 510025836 510025843
    0x10020304080703030c12050103050c0f01174011030a020906041e15030b10080a03180b030414010506040c1d180406050a1d0d0e010306090207111827 65
    0x45100a440c07c1000101c00e200001c103414603000d0701280d940d84c0903041c540c010b4800c25420703000041001809000135948401030941c0a0644410401090765080014103480300b2045210304074540d401d24030402420400d05160640389901c0071401841103003410381c00038044010003004180510b45600e030780404003105407aa046441c10040040c00401380c0d40a400c0c5c0c642c5601d1200781c981b14114004603020314410a0312000703848400000d00b001d0291074078103480004011000c031511510756100014848054005180101d10a207060003c81c0703148401d140c01d4072400341055126a151040c0d821809400005503c100c607906c010107001201e00400150740080d003520081c0039110079004010400c411507201d1486410610000c01c040c1c54440c0055006010440020707406601224805031401d010b1104c6d9004008149000f080391a2514800d0b0300744d03006a030007100d4400130013141c4070103481d14a0900b10300b2101681240c1c154a0111143d0b540d007000c0c05001c0d800300c503440c10b0407034060341c091 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 510028336 1250 510027086 510027107
    0x190b1804020c032b090309030f0c15020604061b090905040804090e0d09060311090105180307170106050f0a0b03100b0a0503010314150109020f1b03070510020304080703030c 76
    0x801601d40701c0c851207248418841d01c28040c00d52a01301000e03401d41d00360b040c3c40b6420815030590b580f0705109080d640e99104c8184c24031015501501c034a079002030034800248400d5100403042e409442c95081524010040c0d81010700c2c41c0c04003802c4d41181c0c0070460347c4038038441c0484a6006c0d0108251701c41d030130000282d1283c1e4001c104140e0505030900003c0000140000c4543c0c01680c81401c0c0d03130381c2c941007241220711b150140c5d510340c0001c1080303c545612400241042100c64403510b10558420740010b894807601ba0b20083c86402c071010b0f40d882020013031045000030081542c0441110301c2c60000a8210a614040d415200c0c4022011a00340c1c1800c40c07100001c2c0401c0c0c0345083c0d84000c00b100280541e082480102c641c61503440302c0c40c58452000c1a203800d00104021140c40c141d081c104070501079000305030704081242083c40300320742c00d4203183d41c46101c4800c1a0003840c2c0c1c2d420306042c11424041c0152201c9010742c0100188000203280c142140c0d120360301490f00003140442103c2c11114022403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 510029586 1250 510028336 510028357
    0x9050105040c0303090f14010509010e0909070f0b04080601120305070602030103030801230d060506031f050108010c210b0d0605160305070215130f0b070201020306190b180402 77
    0x203200c00c00080046040014007568081d03205d1032179003039035000000c040c90041d000f82e40440715400038640f515409000603000d00b0405042001c400700d00180070400008040b100d240180c1d0003c8403c1100c401c0700c0107a03201070250b0b140050326084c14000380541e10360040c403540060b44041c4042c20241f600c1081030f03a2005621100075552944c0d039040060400c44d0038081d861002d00e140b03030f03e00b444881c0c0d62111220300340068210014010b2503220385000309001041c00340c15002c1c1418101c4009030701040f44441039040b0a0006035541000c00035400c40d81000594818813001d410303c2c0d288092140001500032800640120b05201c18401050048954080c000c3c882804e20f828805201c104114084040c102d641c4c040041e96134105080340c0e0355062182c813611515020003c201020b02241c152034101703003d40c4a10440c030000790744000902001315070040041c1d50201c18086189072900d4040e04e00c1c551101c050350000d0801d51256010f100302c003e0050412007940b119131590710b81d030b0107a5052628 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 510030836 1250 510029586 510029591
    0x60c01090b010609030312020910110c030f1f06080a060903020114250f170408071407140d0215031305100f11040e0112080c19120c0803060d0204090501 67
    0xf5195409040b5443c0760104a003c9440540c22040382100c9100b45d80455000400078081d4411010342507400b1940604901070074058000d006a403074604120b1301019900b00d00c0101300c084100110800d2020141d0070504115040c418200700321200002d1030a00e0340d401400000310305015140a0f130040000d1384800f8101d02ca0380b0100f0143c2420341c6001c1d42c412402861684078080080e004030f0310224958905004a4042010041d0f220411411140d1013841110340d07501e011440e855081a100810301100312942c400081030000c171408050404040c4c03420380e0418405425a170008052840304c40040d00c0b40b080c003100042c004034681105180c050382180650308040e075400d8007000501011009a00b1450800c2d1040d411011400100e404850386404403640603401c01d002d000c000101c1400507a10500f0601440003000014041c003c42c1850070986c2070341091031458821442e0b0031000543c81800716608008021800b40e404680d80310404076400400d03850180300040c010f1440d28030280c019031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 510032086 1250 510030836 510030839
    0x6060906191d0612010630080304080c07140907030f090f14210a0305040f0c080303071d010818150a021b0d020319111902010e0d0b06060c01090b01 65
    0xa0303110340c25500070001070f2080c51801400c5070304e407401c0c0d0b80c00d4881c0ca110714500b141015114001200c40d158003621651091a02450a4a8041d03403a081920281e828005c001010707140e16204200007801054401078001c1482c00d418002440144001d020700285a2103075144081114142c2c0700c65451603008543c001074880030306081802c2e1203400d00100c1e00d840b070f4a02e40b890340302006120040510b220140149071861050044010b4480500100d484d01006456038001844c1e48121b6005800c16800450701d0345405d1a0003410800c201c5d079408981c007101503c82c1d50303a9a00150840d0700c03280c0e4a810b5248400c4001d059842c0c41c01d2422110a00306108052060007645500100f0b14140030701000070000100b48041520340c0000e00380c06001d13a20410000d080c40f200e2074076209d0750100d1400c0c041c03442c100ca105201d050406841c2070b601d00c285a01e001d40d00315a041001030706106070a4948881407a025540c2101b0f070180500340c0f5100340701c0461415468a4250001c00d000b5031b00808072213465 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 510033336 1250 510032086 510032129
    0x39022d1009050706030902060403081b0304150915171503120c0d0906090e15040906020c070b03060d0602030c0702030d0f08010504141305150c0901110606090619 71
    0xa05003601c048801e800348400c001082c40c400e018003001e180e002001e141c9803e15540c5c030908070764040c010416008049042c0d5600c01c40003840508010700c410a40301e0304141c41c2c1e4500a014030000d4129052001c001e940995449510050031081200e46920030101a101c24916594003a5400b50b1254180f292003036503481c1c603d0704006803038413215040884600b41040c040c02e6400000c14026000010500002000503640071604942c0040b0360400b000b00f03009412000c2815030b11000420b5403d03e40000f941d0240b90300c1080600c006013921141981541003050004031114000c040103080030703401102081243c0d09640448581c40e50007030890327020700b0000d034010b00310f015040f16500c0400c16900001030b46003401c2c065002e804031032812440f11540c40c517500c103000618508040d6401e2140305c140407003003024528058054800c407805552a130303000300001032a100512110403000c0d00101c1c181b00c5107440b503e00a941104c001c03203604014248002c060110001a540240300c021940034402001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 510034586 1250 510033336 510033341
    0x1b0b16081f05041a10200a02090c07031403040f120306140f15070b040b0703050601021c0507061d0f030903030d05040f0609030305040317060a060e0d0639022d10 71
    0x31074003907040310880380000b40700a91511103500c800794200800500090400c2070707a9008000740303444dd080c00c40340d82481c00983c40c155001210216000714010040c0000e101914250100d0000c1918050243e42e051003204a406408185058000c070341c0304001e03208513511600f85502c2192088140b54449405040040a6420580d404d80d1000c00400200f540d2a209018540c41000180c00600640090340b819910750300390f80c19900200714044c4036840000b106070107070281e111008881140d100000705180c0741015100204000141e108100f000c80b20786021069a00404004000040c20742d03a5052079548d645900c84010a89407604c0041300805400d5889180074074000d54403107070302d1506410a034503003040035100c2c0c990240c400901002075520a130f00344140c00c2000351841115900d15551403060303c0760844a114000d042d5001c0003100d404401d203402c1049500c608405003010400700280d00c0d040d40214580a4029000240c200075562003000500c3c0d01102080b41e04860328203901200 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 510035836 1250 510034586 510034607
    0x30207090c090801051312022a0a050d030804030201061e0312050c070b12150f09060301320a051e07170f0a0e07060f1b0b16081f05041a10 61
    0x108043c48140300303011b440c800901c0303440c04134048a24080c1c1040c1e803a640c0800c15000321100c0d500c0b0ae0b00c41d0b00411182c8585601010442c42512142005c0c02c2c20301c0c0c0a03080d5035294000490901c800e00000495220064408045a0300420809495181003104a50b00d00c258080d0143c58400e00d000002c0524000b00188143d10b41c0a0483c4041e40320090a10301d100c08071140e141c2d0200c52520340a01504d0592030941c2c01c4032000b0f000007520110540c41c030800c0314070584110704119030424074020581c4021042544a19900c41c00c000c1031600d0020071040a50703000041400049403400120800c1c041d550380485004511220303001803a009000c0220010708540402c00b860400c1160240b01d6000030311034007500c0407512444011341c0c0b60f903011201095221041401030440143e0080442d10700914a0301504000d030310070a24804d0305e94064000400a00b00554601c24000681c1542500e01885ca090b54000c07036021407648040c55428400e0701c00070640c07170b84c400c40c0c9042c603c2105401c04039254 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 510037086 1250 510035836 510035843
    0xa080a0c06020609070501050409050702070f0f08010e010b010f140c0307060509010f09080a030903050906040f0e1302010906050a021608010506012c01030b0d060c020109061404030207090c0908010513 88
    0xd0441c0d852010180c1c0310140e031b01c10140400c405010501200880d6000903501c0025881100c04503030b5150710415080a250f8403007428111001020300140310f0a004285146403c3c20081c00341e80b0100000804440c8255040800c005030340c4c0544441c03031034007011134004035103020489495100c5030600714002d01d02076400380b08540c40c0511381c030400302c90f5004109020750411005d80c01c0c03200d2407405402600e6010412070030820100b1042c80c0998801028202401d1b204c81038020301810010011000c08000d004024019004030518006130382c425006009c1e5039030b0f841d1180e190001c3c0e9000380c2c40c2c041e1545507074070a503941c01d81c085040001540445d2254809a83e0a66045141880d0500c0201700c0302d844c4076171f001d031040d10703e01c01e50081c0c000c1000c15102801186407040c481d105c032000c48150b83d0380440180d4540c001807060001c9801081081c110200300d4000f10700f0541c4c0c002e580d070440b5225001285860b01c4d120781116000300c03401d0f8010708501c0300031f101526104006140c031010010044 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 510038336 1250 510037086 510037093
    0xf090120160e1e1503030d06050f01051e0d090210020c2d04020f090303030901020717040b03040f02310f0b0102061f090903030902030d0813110a080a0c0602 69
    0x1115140300c81c1c640e00807071581c00e030a0101c0d050308400504184000f4070741002c070074045002104e01d413001c10080082c1050100002699030078402041a10001040c1e010304204080c009200345041140c0301e510312101544050341d40d03080c3d00280c040500380011010754015402010001e000d50003242510802508a81d0a01d00c1e0302056030700301c078807540c0d821002c2c094410038072808410b007860b80c0280108104203554909000d08040040e02d16401180c80c10350503500401c4642c204200240307001c803049516406241002c0c18591003181c10700000f80080c0c5a450246900d5007551103041401c00761520440602d519855a02004a54540707130480307442101d450001c0c4c1da580c3c20303e1485810b082c40416800f601e0076464000c40120380003000c01c0d402001c0c0c698030400203a500401c3c85401803841c400d46011034442c0c00b500416080c0601e0700807403800d02c448030017000040001411080350281d400319401c3c410041000104a003200c460f002610b00d4403a1034117080a00040e52100c4040320780b55402c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 510039586 1250 510038336 510038339
    0xe0f07081216020d0b09030c0c0f06070305030a0b120307030e0402070b0402090a14011410080906010605130315140a1401030b180105070908010c140f09012016 70
    0x1410354841480c003000c000c00a0510440500b00e00d2000e00d280420b0004040d0014000305032903204113160b041da000c004980c030000d10556000814400394111041c101c481c445c403449100301260084c400d0540003001c006001000401c4030000fa80a03815601c0045c2410170082005040d0359942c0e400500b0980c0070036100004000c0c14a003900031138000646c0700c0c0110441b038130b41d03038240405000d01a04650185842e084082c80a00580d1a518000c0c00003080100c14100f0590500c9104901c03c05603d003001090800c02c11052000901c050440c2c0c5507141c0b142c1e8903180c840c5640200b1003103030001800e107903082b4003640100200d0713040751700c0c00c01c0c3d040c0c0407050030746030707050301c642103070307220243c1200e48185200104003091445080740c0d4040c1803041c0c40900c0e01d4840a145003100c80451f0480040f4101c00814010107500344900c140b1601035040c0454414a110740d0240c2a0081380c04541d07175448001281c1c08280d00c110450100f544028000d0f50118100300000c1c0e031624031041198940c1d1100c40e60 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 510040836 1250 510039586 510039599
    0xb07020111030112031407060f0617031e0a050c1006030b0108030703020a0609020402300c0a120903230903011103040f03030903020f0f0303010f0b28030f0e0f07 71
    0x459048400120781301e00c3c0c181880c2e800707035051841800303101c0d02d031401841a500402d0544c00b8602c40101c480800142150070401a40a8003c5000d9a11000e03802448000301c421a00c11110042078000e5041c10348445011500700c0b8188103a40e40002d5502428032010100710b000d400020549201f4482c0d10042e83c0c940da8030680c4e0780604039018005a10000c40640403aa4941c800480c0c140003800140c6080c4400741c01501d510003806000c6222810424040c01c888400300705c1c1d80e004642503920394900581560000e21700d0341070350000c0030020f644101100030180250641254103180e032526403480c1d01c5108034501d80d50000c48146000e5400c11585400c0114260100c074840ca601800d4402481031586080300140f01d0320740c0403000d605c04d055409810007000c02c1914069440b40c001140d481d0304103185060381a11580c48a81d800702c0521280c100c48880f0a4503600c1e01000d00c42204035038080d044201e001c4e0040e40720400c880c928049490040040208241602c40904012518480e40d00c14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 510042086 1250 510040836 510040871
    0x9050106020a0c060806010309060e0615010e01020705150c01060e090c010507030917070e010b37050307091208040e0f061f0909020a020d08180a06270b070201 70
    0x340d00500031020f01001384000341c003c541854202c0e6041c50005401752481d5905812610181d190040300d074060010001315140f4801000140502840d00c0000d0304044800070b585c07003525005280c86603001000b820322102603001510761101c40103000780805540c4a1850400c8003003036840040901a800c0f4048007075011b00704466901d40e066035500c46013840c14080f021610b42d482c2c0d4540550040035030018141c0c110a02042c01b0b0040c403110240d85e2240e02c0070558618440307208480e05c21161108250545038000c00d1005050100d0a046035a9904d0314004c4610002c02d4128251400480700c08400b80100c882c05441030b260403940d000b2850301c518482400000b0304a928a40c440c94031248000132020607400b0081d260804d050008034282c945542130141d801403205c9130f00603401300e00401241c0340d0006035250071074035480d481c12442d401304d1020313601c8250704c12000d440380c4c3d00c403280c01c081141d1241d54546281e403101c80103c0145940e1802e17210b50b170400d0b91207000560a000e00b2880d041c9186 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 510043336 1250 510042086 510042103
    0x10210020319020c030903100204141203030406090302030c070602060f36070f12061d0307020402090d0803160e010207060e0d0206210406051308070b0606040801020f040905010602 79
    0xa601e5541c20600103003441c2d000e5405980308000c680001e01a01455803020030000403841340b25400582c0311824041100d0030301c1611881c0a208182000c240b0b0b010304008000c59421681014000c190000f240c2030903459445564180402d6115103803001030215404140705004100012a1901c00d44071088116030310810f0350005c544001d440300c04030202c01300e860035803030125582c02c0541d498607560750b00c0c407a100646a448600d1034902e024086042045d81d200760809079048000c01e80c401030103c2c0c0156541e00800c0d00080c0507503800074503d490f50b1358907101d108605610880741139403850003160b0008048140d80200c0c000c608019104182580003040000540311150780f84a440c08003801040300c0c0350100c00c000c3e60807010810032013200c2c541c0400d610341d20f2820002003065605141c508141201c1000744100c0343e030890b0396070003000500044211540541c01c4020200b4540302c4400290045c45264013109040d031001400101207040c000c05841114074101003040281c0c0e80303510998540c15030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 510044586 1250 510043336 510043351
    0xc08041502010c09261c030605030c040608030d020c031317061506070b0a0b1c0c080105060616060b0303030a0903140f0a080a06080114220b150f18060102100203 71
    0x142c20301e112024114844000010020fa421501c46c0440c0c0c9072000f00145905c0b210b44002504e9030380600c62401c08000030510a441960100042c038a07041c0201e03142d010341650b028106800042c2c1c0460005e0410540d0310300194a0b10698245646050b804420100c040300d440d0b00e401800c1c006010306405c8000c551358028060030061600141ea910901526401001c021040350746012401c12a285e400c803500d2050305101e000410780c071050602030381c81320655010100d2a810001040259241c09041d910b001c45010b5001c102c03c001850540c01501c491218160188000310410114495035001103400c607000b61039891041405030300d5101c3d20322500035411410602004044e020303912809000e50701040f200700002d0540d45807c0c040d400e42c0c1c02a200000e40018070000d02c5201e083c014801442c0001c003c6440e05504d8482e9140030a081008000e000c032011039581c0f120140c0c0720701000808140d8020f014009500e403903981e00d816aa403d6030118010700c40e110700d0302121000c600c21a070180c4407 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 510045836 1250 510044586 510044609
    0xf1b05030115090905091e030a0516060902100e0a0608060904081b0307060204090c08270102071703010305061b070b06060c011b030e0a0c1202010c08041502010c09 72
    0x800e00380003038030b800b9081040100b00411400099481c1103114503402007a240c00030308451000c010242a500350090b001001c01c3c3c00030881003140ca40c02c1012643d20005201c103400040c511418103000510907480040c0d000001d002030401c80c99480700482910060032282c0c0300e00c0c0c0d42c454008031251042100c516802100110116011071700c07140c007501e52100c1121201e4405500104200d0440c0c200400c100c0d41c00741c010070140038480142c01507500820309407074003134014680400d80002c489070200320300a00c1866a4140d419183d001c1d0101e42c40141c010344664a240010741040307405a100340320980e9940540d6000c9003880c1c1c542f000594088c0300c11601130f0b01b0501780d5118841c040001400e4070744c0c01b4030204688a0743c07d1003070052424070119103410001890341103001070152281125104820b0700442041c4c000500030444040545881c040c8040c0070000a100603200c610000d02c01800200700428005150b01550034111111045a402448a65103c8900340c55003002400b030443d8401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 510047086 1250 510045836 510045839
    0xf03110909130f0210020c0a050904020609040906061a090907090b0f09030c12060619060f050906040902072d08040312030f0608011a090709170c04020a030f1b050301 73
    0x90032240100342c01070150840c0c900c1070201d030340066070a20307a4609142c056080420151a00d03d4907010130300003007400380c42c80021450a40e00056291040b5600c052155580d2044581403140b69446800507145080b050344601e03491684a18080c0c01441405100b001c2440c0042c0c411440343c0310050444d03405019803400d02103070030784440d441d400907240c0a41510449541d4034495940b615850f800000c04409007105003025018040c0c2d20841102200b22a042e9100c1000b98540c0030905c80c01c0b2603450703c1c000d5180d0500d203002403501e1055911100046001244903001d1024409c041c000da140300c0300903106000d52815200700001110310001d44000f10900c0100f0110300355560b0744c1e01036803507898000b60200000c2c0c5804c003100c55a0f00000416076680342c8126940d03614a90000000c0720072100206140b40902004142004070f01481e42d030350145013081d00c00321004000e4241c60312401003040d91681046800107005000840e41e200229003004110b2400c2c0100c2d18000004d44c42d66983c00b860750b0b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 510048336 1250 510047086 510047101
    0x6080c0907050c011b0c061d19020d0203060c040608010905041707020607140304051002011415011106041a0a180803070e040609050103050c1c150e01020a0f03110909 73
    0x29000f504409030695200c030070f039840700642101400e02094442d113520322060003904050b0102e5000c1d40039860301c41c5941d002d031913522900241030051b8404032a90440603000b030b440031a04440740314a0094141c461082802300c024130600c003400c02e542050395103819030b03030303940060109541d0103490240c00d940940c400044c03c0e030480c000a000040c006009545412300c00d9456415290200b01d00720580d0700040740a0040d03140a40240d20086038520080c000052174400100741c80f5405400429211030030014518564010610b03045071050031019581d152405c1c1c04c0c0100c0065503441c108400e4410207000a0716100103100e60740302d1104507544e8900440250390382400d1580007522000511001e141c21940564490040b14090314004601050790b52541c9071031890003017440380f060300c02d1400c2410440c200080b43c80001c507042d00a0601c0c6040c0d0b42500f4034a00826205012030015400020038402c0550410170305a415000b079a001c000c0c94541004075141800b8107407080340e20004880215201 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 510049586 1250 510048336 510048347
    0xc060305070516111509011e0e031002030f1834060c02030c01080603030d02030703020d020406031b030e15040c0801020a0801060e03071503050423070906080c0907 72
    0x102030350411a03e080800c802c11000d03070041c0b680460b2403000d84e0b010b0b03c04a061007a00030750441c241c840701d03c0c100010000040e00a4030745407403030f0089000550700741800c40c0c41005c80918098016090b140c0c03001c040300040b0080e6200b03d5001d8500003040c0c011840303460140348840c40300b400040c0a415800544401340c10403400b800540c3c0721010b01540900c401c00070700e2900d60020441038590880445051040c9814500400065418402a6410024070791004003c80c1d1400e080f201d40140d136903035620070540c000d0054034900ca00c02ea01c041f030040398403901a4040e9507021703e07074030000c1c01c4072203200000c5042e102c8920000c0b10680028454500160030396011940051103801d128204d1070b22008840d003203030002d29240740068926001000f0064121940c003140c484103034040d2196038102040310791140c045241441c10503582e88000307002c3c0f00e0005880c0c000200c03508118500300000c0e0074a030340c0e0b41c0518003800c2d034611704d80b00e00016440340014036000701072005820030741140d5500c2402e465 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 510050836 1250 510049586 510049591
    0x80307030608030a02010f1a0d020d06091b090e120901030902010e270c0403030504030f0f201002160b0c070e0702071401020c030703242306030a0c060305 68
    0x145512441c010480507000d1000e48204040340e03000040c01110030342c511051ba24a1309032176081070308070194000c85448050510b50b2158040e566036800d10010300d821001051502409441e07000908200920311a6524500f411550401c0c0188190103000f03840640f5081501c01034040800c0c20098444103500a401002c406030050620349030078034192020914042e0f41d0b01420b403446032200b41c43c00002510850654006001c0c1e14882e087c2815039038054211311850102401e54074007082d40c0700400915035000128107074849a041e030300e2a580160b0100940e4116103da00c00d050404050450b180700240c003601d202c1c2d860107041d00283c80e0482d601c5a50b80016280080d900070300318041003a18540b40b16a000e41c0c07981e4018901c582c50a0031640306090359601a904540254030200360700c0c0e50025408040c3c0c1e40000745046220703800c0542540c072690356004001e82030704001c000703040412003185580102d0450000012240d640a041640701d88140c0d0005040141448050200c18881d610066 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 510052086 1250 510050836 510050851
    0x30415020d1d0a03050a210206071218080c01060807050411030f0a090b0f0402131b030b190b04140f1e18010314010e16060c060f0c090326070803 64
    0x181e0f035032a919006d051104039181a42c0340f81c1222541031a582808222008540991002e81141d0401080040072403c1081500036450348071404861140c580c00b881d448020341c403030891030b40d0362070132620540a07004510079285940903060001030b00d400c15001d51400d484c40300d000c071440d42c1c1c1e5001c1940189007000e05400c0e91141d403808200b00081705d040105018001101110010780b03403920400000c81d0306220381c51070003424841c1002000100300701c0c1f5a14900f8908002c280046994046451000a58400f200000042c100010018001c40c0140252951507100030100140030717060141c000f8a011195810803d40d0500601c03a280048640602c40310080c0112902007540768201003402d000c0e0820ba039802d0115024144118003481207103154480d40c0083d0140d21400541c0000f14003480c41104103128401c0001000c000c1c440c2d100b414150002d00d0100803604048000515841e4580002c4803d1404160f400c101c200820021042e228000003a81d8580000e540d10350815400140014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 510053336 1250 510052086 510052099
    0xf0402030a060e241e282702040b19030f1b080901090b1810020d09030f020313030f11131a04051b0c03160302030415020d1d 55
    0x825410018211036000d034030b0b2588490003480003400c41c00759071030130101094400c808071071500301d071841100034000b00108121070540760018100303003804c1030801c0040d840307030710740d00b07015000c039110305019207414030b000b00c1e032403004068006241e00408034811342c01085e078000420301182d90f0726582e0f0b00c0e80e480002d240345408103003481002c2155090710781000b005000140102c0705080c02ea5400078200d51f0280d001402849082c0d40b603100e40102d20303005080ca56100103e011035016980c010003070725034401100b0030115540c040441c0980700800300310728100d0000d580c0458a4070742910000070384403a190b00361402000039195650322601441c1203082200d50120a03000210241d54000c0d0b80880806400c00106d02e504007580440407a00c19002c3c00c0d03100f103203890188001081d009100d000c41400400c851a5210103040e036091540c000c10030040840c0d041241403004055010000d0022641d44146160000300c07840c400342e8652583c131158100081034110700c1c84418804a00c03500c103070302029100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 510054586 1250 510053336 510053339
    0xf1107030605102102010e011e0e030c0a030b040209010b18061b01020a0c15180210020f0a050a051e0a0611040819051b06032a0a0810050604050f0402030a06 69
    0x1944a13403e181c41e2408542c6100b00980c00940d40c120383d0407089020300b4a041030750104801100f8006440d000c8480c3c0c10000c0b03013855414651004c1002d1448600300418611802d9581e15140700325100c03c4030228041c4001c04000240e05004600307a0305d02d070781040f0f2031480d11130440c81403040d2a0001c1681a00350003c82c003640040c80000e00c0100101d1856943c0d507400c4071414100001c10360044005016180d20708605210700780c00419001d04c10030b80c12110030000d034014800c101e190000c601320b40d001c0c0f400b035010900c00300030000800395241445042500e200b0141520074141070411549004495089a840000050056480401040b060030051030501d52141030080c40c1803218144400ea0114070240841400400c10008098460481c552500c4031000f1011404500001d402c10b20104188072000702c16445080d0f00780070180c1442e000d40e4443d136820320b00800d00c020a458010100b201d648011030300b802c010080382c0503074030040e00c080300106290b42444025800107040420003a0341c0c503030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 510055836 1250 510054586 510054599
    0xd030c0e0a0e0a05010f0b0901080604090212030a080603010b0f0d170f13050405010803070f140d170f0f1305150a020a110d140d0b130c0f110703060510 67
    0x10480042c0c038442010200524010560b030040b1101a041802c50407003515003005000e10000440c0d403684801e203805c203074039198100032902402d08103c000354080002040c42d00d040d075000014210110703865035039408a48403481410708841641010540000084491a041e070510310074005040744100900104070281c81c009403040e802030070074031030401c500146064008440b1403400b006040c04440400080d454420003544c0d074803510400800341d4203203d0303002e800e02802c006040c0051340e02030282c442200c48000001d03c5e44000c81807540c5040408030108140305407801509120700c0f410720101c0b07000e80702c0c460018024005400212a00d10942e1090803c200b845440c140c0a40b02001000d625122424000b4255041283c0740400950000c0400c1201076408841d045184440d6850103a940700c0c000100005860440702a503042500c5000c10019160300b540521240c2c0060b607158800303c40154803c4030311848400c801c40381ca5102c104140042070392507010035041001554071213202c41c0da610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 510057086 1250 510055836 510055849
    0x120103050c150408031e070c03030e0a1202011710031703062403040609140d080f01091815060e010e040309050f0310111303060e070e0402030d030c0e 66
    0x2042260140c00003819440c26040490601801d180072001150400e420302003d00c0e564054000c00c40c20403c002e4460f00840002c0c04100da8030300b0b80120004a405442c1d05000d001c1c004110b90080c042c01940d00700207031400c1000e0410a0302d84d4143d45107188981c40c4001c041f2440005051003c0c100c142030000000200c0c0b02303191140d5298085141a00c83c60800100302e03000e0706002444d0020311500700e4800002164a049960061780310300700182e1814542048810f0110840d41143c2c1d038420f00c1c90a84489402c540c41034494107661100829603a2281c04983c1a203084001003800300d400200c2003000155154405c0c0d66618591000096195450b41c0000044900b80e210f041d1040e0301a00780800d044d800808280541015181c1c0c1d0f15098003030020035911550800400c0c10310756503180759050024607000f180c903030b11881d41041031402d803203081100c0108041101645140701d04640003500c00c19070120a44150340040c06042240080c04069000e40b140840590030407000b800c0f8402550360b0300303 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 510058336 1250 510057086 510057089
    0x30a030506011b0b0411180f10090f0902030706110a0305180604030b0f0f040b0106030c020c120304080c09010506040b030702030c030712270605090109120521030105090f0c1201 78
    0x129869440d41c1054100042584501b911490150501d909000f031098088902c098000c207010441c01e160340c0d904154000c50781032642124084504100600b104044560030001104d40203e055071500c0f07627134800541c0c0c200c0c64a240e17001c461b0456207025021a000d00e01401101190110810319125198002946680142c100300c2d100a5898144422540e0340850541d10440c000307101a41f42c1041d0315440350080052040c2010540c0ba048601280b030310074041c001c0e0501e4090590200c5c0d4090584107910b0390018002e00a55214022500c0f03058030704082014121040a0903081c034040c10050036980f1640010305400c25071008020b901e0104070104010702140780100040706000c601e40c0001410420803002d101c4002c00880f26420708440424046411a103050511a64420f1000010381c0d1015055105606100401d0342a909200e00460990a40e02d0440300603d0000c583c480e8a0001e03020a000b07168000c01e61030001070300d042680c804580c0200034042d03800e082401c0c4200f80c0c0e48080c1c09 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 510059586 1250 510058336 510058343
    0x915050a05040309090605211c020f0f01060e0a0e071a090f030a1101120b09011d010b0307050406081e04110420030a0908130b0a08070f02030a030506011b 68
    0x250340400007850f9204e0741900103002c40a0041c82013524080006692070006a070228140c03080f00b074555542c042c00c1240c54180503050320040007c008007140a52622100c0080380b485010708294454814010300c0ba04090b01c016420503d0182c0350f2034a800b004025005070300302544101c03003003c45c4038072800b0a003088800700412075a580d11608c0c418440010701c680c0d50700d4065440220094000b55001c000c40382404420700e0a094809140d0740220084c1410b560420b03003050b5054004240c0082c1c0c1040202c0c0d411550f0850b039102c5c0d0307070f40c111400369110443ea8000000c0c82404280426441040c105400c159440c0540c0c121010394862a405107070706a60441d0350b0190303500000b400b82003030f0180148458a044000b541d2034040810310078035100c001c2c000c00c81540c0d00c0c600340c0708020741e00c03003540c882c2001c200c0c440071901c0d12040e119059510400f0018080f550b240000791440d0710a001c40107030000c55601079070519014410650151a02520060520604c004030b2180881500d00e01c40c8174a00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 510060836 1250 510059586 510059591
    0x705150c220617040f03080907350c10050c1501060201020a110c060d02070836090705070305160501020f0a03050a0e070b1606060e1501030c02060a0915050a 69
    0x15042c00a884024800365070b51868801c1010440400c4840c1100e520b19a018244200ca81e40c44021850400e0000d0304040c072000302d081414030170210403101c0c0c0081d240103900305012a1843c1c6070419034609548110690000726034407200705803449500035005100d0428211020740f01081626001628241c2003840181e40c0031a2004040c3d6020303c025009080382c030080d05014a011004c64914407600c004941110b030001010300403c180603040341c0303d0701220300814401141c441122110f0752620344c00e07074009000800ba10b03582032405500c1c1038000d5201e03481d1946000030594051f165a00044020f007000c01d5200c010402007082070005040c5003610502c401c0ea105d031700c164082d0854001070200407100e803512070700e10000c2e18000b0b2407806a440c0c01030700507100c1a1282c4941072050540740e0041513181044000108134020448203401074980c03509030403000c81076034011809c584002d000080103900c104085481402903038488001d10b401880364801000200b40e0407010b41d44142d605010095 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 510062086 1250 510060836 510060839
    0x18060302030a081c060f1e03020a030b04050d1e03090f02030601031511040b040302061309060e0a1b08010e2a1810050712091e03170705150c22 63
    0x21070a800703d583c0440c0c030b18017007000500381022034004900340d0061001c88140458817580c440c00140c42032005541c02030139001640e0312450044045d09003034804460520503c4048549036000b0810421421890300c83c0043c042c04182049015110111050f10241e0b503280740b00c0056103007802224084c41c051813051040c04e00d400c3c01e6504590010180398a8a0400c0c0310922010034031000311011650112031542d2a1100445015400b1580b07601041c8407918220340041c09032103604260380f24500000c0d0810000050a54485003a0002401c020000311401c1c018040e03583d180000f90f4108812820010680b1012049840720010a080da0880d8040205410300c034201d1400b4034038105001561440b00c0c1e103100c0c2801420a0096503001030030040b01e50091181e151141e201e00004110b900751041d0551103006008041818900060718034403455040c0407002000181100c454680c450010003049401500014200c1006000c01e041ca000410140c00b8503500711031241800b80010240f514201d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 510063336 1250 510062086 510062107
    0x2040e010f24030c1e12111e092703070c051e010503041509080d0209131a0103320115092102030109021507021309050718060302030a08 60
    0x10b42d06070386241064400b45010710009541400402c1110a402c0ba0070081088900c200701820010750460205102c01c1c0c40c00c2800d014049506008900090320254103050030261081044901500c1140d04103002c04040380350a68040351030000792820a03a5007928508402a181c01c65001c844281d031010300f1403d00740294039001c3d1202d11101004610f00958940c0400068a0750000074409030802c000055484001c00305d54002001d0143e101c60456500c03050903520f80000e41101150070f000c0e8072003441c000c00c000d040344030710801400458000b944030b440000046014181e40308001014100d00002032a03406145004984903005d00f4561340e9040d81010010706001b0241050781301084820103007082180480c1c0034014404031070000c554030301c4000340042405030402a070000c0d040300c01902c1a070080154031024181c05803003114100f918a003111003110540341102809401c50b04404070800511201040038010718400910214909a0381c0c0c0020381000d011a0341601c2d840000514020718 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 510064586 1250 510063336 510063371
    0x12040611060604090f0305180a0b07031206064a010809120a03180f0c0f08010905070e060a08071d0a091703060303120c19080106080c0702040e010f 65
    0x102d20161401c1041d2401910707038455100700d034400a01840300001c3d90800d00709140252000b180c0c0e01400e103500d069a101c03905080383c1c1c003140090f000100e2203078048074050b03d00e001d0f0204407070315981d640346004401000c02c141654007050745c400d05940b044e503032105803054042c44009003030701c12040da011b289150005460040014a00d01c90741e009402043c000034490b6064648203200e9140019401392380d03901c0d17201b481007080320180115101e80755100c2080340351120601510341900c00d1115003540ca440c25800e80fa0101e40041c090f4008807403e02c8403120460040d54070001c001c04240d101c5039141e500504001c0103070000d844420b400c40141c00c0e0070326180c50194010340b9903503040010401c0b944600d29154002100e41401210000200d04159030400c142c512442c3c00066140c49410101c82e40b80d0503901c211040c41c0328042c0c10300c0100080b03010f0300f82e46040f2045511038000301c1da50f802010307080d070340818001c0b80c0c003039514058890198824802c080500c07519600c001040340703404603135541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 510065836 1250 510064586 510064591
    0x2040e0411181909020402040905131103030a081503070315060f0b18012d0c05060a06061b020604170307020f061809060d05011401091103070c11031204061106 70
    0x810307141d041c144106944000395081c1c980c40c203810f0008100c0304030300c0042c01034030441d13014445e400d04100501c00940c00501608500c184a8864240005005024948c40f4000d80070380c0b1002c1a26007000490f115044086084034141c02000d90303045580700c0e554000e0006040d00102c0701c5d9951140709115100e800b480e840060041d0040280c103010030009241c8041d80440c00c22810400e40071207c0e0001c111580c43d10064100f0740c21401c0944d05800710040c411280c00000f61054810ba4012606202d0140f14244c240c3e00207680d030b005101d00209203010340350580d00d4204c0e0000802c02c000240f021844641d01350442c422405559248841d00402036030407100c40d1454403401d4100003170308010200c03d06050901d00103403107414007907840c007000481c15501104068590750a01c0207086590030f40080c1141030311403140041010311158180305510340401c54070100030a1030b8401940124008131514401550000d0841d03058214144684620f50010360001d4040307040421070340f402c8042400351a0307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 510067086 1250 510065836 510065869
    0x2010603120c0204141f090e0a020d17040e15030c0a06030908040305011d100902090606090d14010209010e0402030c03041b0305010501080a1203090c0501030f02040e0411 75
    0x10595065807990124500d046004005202900500a00315281c640124500348109076075103225280c20384903e00d00b04c04403059200240001c3c0c03804101103442d0f02c03507400c0341c600680003440c0400341507003441403810b1200700540d469120200c41111035200c0c90700800c064544002c60300c04074108540c0c1d000c01401151060f92103600302511302d0400e038135800754001c2190310924000c6100d55460811140c1c0b07101ea83c03c007910650801a5204501d0081e408600d24504220211f0301a4a40c40d01800100c40c0d035060020b40c8541a0800710342245080c0c005812a404021b100d28034280b0295600440c16503d00401c03101a50003103280d50981d80c000c54080d41c10501a42c082d440d602d032010000c074840c4001807001380484c0e11030709843e29180d4141d44c1c14000d198040020400395840d091104d41c2c03900c40d070008962014030000c140115038031900900c003078203500801e0a04824100300054000d82004004508503035400c0c04001400c0d0060783d092401140621079141100b4465014016070b00a404140c2 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 510068336 1250 510067086 510067091
    0x602030c18030a02102102071101020c01050c0a030c022704120314010e0405010b0d050303060405010906060e09071115040b07020706050304062a08100e01120204091b0f0608070201 79
    0x940260300d441100210310400d92804807091000c0304803c9171800c41d520740c030040c01b03440450400c04103c50f44c2074039040400300742c0032205c20745030038801141c6c9031241c200c20040b20780140009600180c01f82e418041030504c0101941c2801c64035905030805c40c1c13a20b420710f402d00349003802400280682e0020318071b010000c030b107401d1012030164030195205081c10b2080b1008540300100103001c0c0142035101e640380c44c50040c407042c9502040e04005647e9002074814074800c0d491f1000018100c8124410704003152210b07291a40104a05810414440f50060440c418403c102426030405003051009544000414444440311b00b482e00305400076003c018118020755120301000e20825030807078181ca030b005900003404900307840c0301d01e0b620b404d8003a070442e180241010810024402270300440305511440c0708034004038520f5621151503500403400c0c480c034031030f0741220304414015044c5504402c2c0d0580c000c0f2036090fa00b203810019580c212425500407007544c4044070040c00350b9944828260f03044096440203 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 510069586 1250 510068336 510068353
    0x306070507031b020d0506010f1d04030315050301020f18060405030703080313050d0f030b0d0b131e060203070219051903110703111002071d0606070602030c1803 71
    0x5005407050361005010700c494840110003203501010104440e5901a02500544159291090750380300280035900c881c0701d04600114000001141c0c070700c040c00b070b0f030740302d00c840d58880f502e0540c0180901032842e02081d85140740806d42e034409000620425080ea40c0c1e05a03034a45240109100001d640780f098454a02044108803d80d00001c910302074036005000c40c3d03a41c1d1030300803c0c01c1c0b204800c2c1000070502d000d03004414015640240c1c0c181d24449517900c0500c4070b8518030b001c11510040c0e4500042003421904041600c0360000601c88164610520300710280d1001c01c100d200000800520407544583c0000400c9602c5605122001042c00c4444010541c800c00e90344107a1200d40b50100007140728071094155090611828a400b122001042680e10302d07503c1e401c041c0030f0301d581901e41a00a4843d1071020006a1000aa84003100d80c1440710542c203c00740180382410b114081c0c41594400414804072001c10600d100850041504814069440d210401c2001901e19503055251094020300003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 510070836 1250 510069586 510069601
    0xc070e0610050903060f0720161e140102100608030307180308030c1c050709060f140316020102190c12030204080d39060506030c0303040324020c010c0305060306 71
    0x2003846d00403000c40400001690384000407107000b0003196003010200d801c46440d1210000105181301e5500c0307884802d03407810341c55540030a900340203014460000002d19004003c62000030200541c0340c94148166040000c0c08a040b000b542c0c0c40b0740200d10503403c0003062040140e0010309460440500c103801102e0189561600149804001c3c01c00fa45800c002498500480380d2180441c414a0303049000c001500740941c00034405181c034055103002c541b035042c050111a000b4044000e4941d0b1000e000b52035541c40c0c81d241103603c000c1c29444410340d9000d0001d004001140c5841e1085610240da5800542a4a0a00d00080b291700201d06040c184108400e01003c5804541520219400c0c104980c8241c20050150304840031004500080c9c96600c1d01c1d08640d0320552039650a040c0146824400b58465200f0552240004080300d41d01d6481000108009000002c20a18244040514000c40c500c0b1500540990340145041e514070f955510480d082e06405218403a041907043e0000d02c220700c0e201a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 510071942 1106 510070836 510070843
    0x4050a022806080a0e0d0f031a120c1815121608030304031215062d02030702040506030d0e09040c050604030c05031605010e0f150703020703140604080315060c070e0610050903 77
    0x30018131205969000180038144059374002d11102e44070801003d0071b032030210b0400c140a41e508075601043c0c82a021402001180c001c0d5580c0d2401d4030300101242c1d1407407100700c0d604d03103041450150703845003507003403400d40b821810310350344100c54910404900c64410f1404103000802000910406d5404405024014402c0c1d40c2404561118001c07d0f4171091015050000502c000c2c68040961810100890304180500f40f5180aa41c40b000850241e5000d90070544d42c0510383da40412640c01c1c1040403104400301c2e0746821400e035080c00c00003411104c500b020396106400390025500b040d900d89501204030701c281851990344010510780603403900c19501c005d65061140031585a031301b00005c5a005d03c21a44101801c1c41c0d40e81703a40c540c0c0030000d6044032040d044203060151252440702003050344003518011180d030701c80c2d181c8117003000300c4908e01e4100300007000030a0154528645001 = true := by decide +kernel

theorem cover : BRFrame.Cov 509892086 510071942 := by
  have h0 := BRFrame.cov_init 509892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 509892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 509892086 ≤ n) (h2 : n < 510071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
