-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0183
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:18:44.124322+00:00
-- url     : https://prove2.me/submissions/ba639b0a-8e03-4aed-a51b-e7040b90e0e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 32733818 ≤ n < 32913674 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 32735068 1250 32733818 32733829
    0x3010b0d060f030303140a18030806041b030c03060602010b03030d02031e190b03150711030708070507050a080723041b02010606020115140d030207080d0507030216050f09060f 77
    0x10744c4207480c04a00c0c1c803500b074100b0307140c50401040c0800c1d4a01e8984205416030f08070300c415084503058101143c0780e0f160640890060010038440300e5090b034248410f411080d9050b84118040350843d601007040c0e0b521132000f04c6c00e07a61084034907a8542d0060000c0d040c3c01460380d000395040b004680c4010b18443c1007041c241c41881040782d00c2903030710000b20b20065000d101c6004030002010110003a01c26000859140441c100c0080c001404004291851810b134100400403650000c1d00005c105844004900d086640c8100d240a03d07030040e480c000b0300203540b980000e807060540380c002910004c01d400481c1c00620031016804066030054990b10300c024241c01c2e480c1548640c1c03400b6400411994280b00c4086c0c01c0d01c0109810380d40500c0588002c02084480074460303c41d4181c2101c01c44058401810204d15282007900000500d0007254088503003650004000c1031054844c0e0242c514014400b0740d00c07020705419201d40e83d001901c0e44085c100030f01c0c160700200d51101d0010f200c1e14152490501040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 32736318 1250 32735068 32735099
    0xc041502010b03070e06130c090b0c0f070503030f0d05060102070504060e100506040b040b09040902060c0703110102010207080a0806031c03140f010506070f0f0f030504170d0503010b0d06 82
    0x800340c1d54810304158503003000c0c00100c02070480000381004900300703000400c114005e860740301412559100d00d003041c0944158041e80040241501c03850b11141d060700c14a440b00c040c102c8403540da00c00d0303203000100e601f00070041d2081030485846e001c1c00c0613840c954540c06441c004141e9411805055800300301e136942ca205101c098003c5100c00005403030102d048141d40070b51034201718421103060004000c0383c0c0282046405480c8050300d03d03620b170400342001c10040e1402c008000e520203000308100640c01c1c80096480300322809004d0010b154008900164201c1c0301e0904060305035002007000c44040c502914285800a4020381110030000ea00e6114644078011541d01c5c0300000d807201c0f12150a004c41405581d0000c2c030b01c60341c1c101d49524090000342c1606c201c2200070728407003401d14000c003031064890760980956004451a040302200c0d01d402001c6038050f02500b403030307040700352180d0050210005110214000c5525900e01e564240306070500d881d01f1400a071504c260700c2e21800700d4010017081444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 32737568 1250 32736318 32736359
    0x201181802030f1023040f060b0a0807030c02060a0b0102030d09060606020d1803030c080c03131a0306010c08030c0408120307110a03020705061305030109110901080111070b0c04 78
    0x507140e08004100c50381200e000707031900c1140400303d001803161614900600152541881101c21796030b00240114024149900740b43c84024581400019031250aa0041c84036040e60358a108465444150503400c03501d0040074000140c0c0141d0015581c080d05500c407080700d0805004581c140a22281d05800303545031280205e54058840c07404021306501040841200c0045040c070a4119009040c140100d40c8184800b0701008030039030080c0c0500580b641115003080300c2005136580c5400c642e02540c0c1c0c200d840c0c40b8041d4010003462448041c070071000282da025050503582c5981310116615188080d80001e4590070030303440100000a480601000040c130000301d14080280c8a1506080150607807106100030304480d003182c110703180000da0216a0106032041110b8290b103c0798401c0a144080324240c00c0706030150300c6c180c01380b0184000307099082d401c0101240c42070042d030389462145090340e41030211207400c50000d000c00000113048c4601740303500811084541d4209a621022140040104c1d00720 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 32738818 1250 32737568 32737571
    0x7050303090d080601020c090a02030a020729010b03040b070c29150a06050406080a060e0106020604110609030c0d1e03050c06010f0f030201050711030318030717030702011818 77
    0x400842ca5081180c0940c40503090024140744101440441c4001400402840d8640c1d40003000230a1410309a0584480ca50001e1103c88003800f4a401004411154280c103a4544180c02c00040d203440b110045030310407a80080340a80300d0f20340700000d90318110304110403644240005150200094540703035164100825018084007414404540c4110903c040380079405014105018007003603410408850440740c00345029aa0f03a50707031880e040010142c035000411068850000090b08541c001441c1d406107000d4401d8140302085441000454880e41b4800f40d0560010304501c541840e240141071015400b80d8000d1800320030034400e0070110f901601c01100400c001040e02e8a125104111040c05030020703010100d00507003007107480316444025100080c100700000071180d04201008035440380c03c074405000c4a403110444500d282c0043c00340c0d12940e000e88241d03480040c940050242100040710340e035024518209031500111008891441c80080e107450b114000142c48a031003180100710b4041040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 32740068 1250 32738818 32738833
    0x80c03070212010b011704030c15020d0c03060311061612020a0312050403020606060705032814031021050708030a0905100e010810050312091005180d080705030309 72
    0x400540b40d04040c00304107540e24110481d05641d800042205111408080103002c96945140403241d005007214002c0506414420130fa051b4003d540151a84407c0c41c1014012020303051012804c9880d40e110182054003030449120072400d012005100c42103000d170240a00300060344030000e00b0b241080c0d1540059008071044014594040817000c3c241c1d8511606209500300f640b8000d41d500d4000c0c014a1051900007640f0040100401c22a9020340311401c0341c1c41c409103c06070b440c0c0d4180139400c0040100b418900c1c08203500c040a01203d01c03070440340580d100b015040000c00e84040042d03a031045501134000f114040464410092140240300b4174005660f1000c000c00c006101507242e07440980290074541c400300c5c4413a0000a11690414280703041c0007542e0380c02c1001d0314000c0940c4d024a81502998130200c49043c010b0000f05a980c0096469070b101500710300f82100c440c400c0c00894006000c0070b1450f00752034079002110712030050140e240103040801c66204e0a04682c01520742e010746910446 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 32741318 1250 32740068 32740073
    0xc020f0114011509030818010c140d02060c07032007050a0e0a0f090308150102100e07032003030304060902010302090405130b060411070b06041506020601061701150516080c0307 78
    0x85881140c02d0743e8035003414032070319580e9280032a015007151030100d04000800080a40d111340d00c046c09a6810404a076403407610214a40d45441071560150300500800c00002d400740104400c035910941e055880d1000386032200c0b81800d500f54252041c0141d402103c400140503555041888064141200850790b1401c1080305907045440d9119055101414041113202294029a006a000c00400d2502208800400040f820050000f105c3c64030030f40303040700d40c00241e00000b9494041e6403040320142c006440901c2640c102805c81130109a166004100050001e152504036000c01403040c103000d42402e615030001020303180200c400440c00001c55100606202c0816540c81e00054141c4007041052100300120380684680340d07001d0916900b00c00800d02e240c480354483d00b05203407a00303119480e2030703140e0b50001e4468a0a00c901c8001400a0310b0310b58003550b03000e40c1c0504840814448804c6c402001100356170703940041c42c0a800c14240c1d222841c010800c1d45c07000300340c0d020440000d10346c0e601551 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 32742568 1250 32741318 32741339
    0x40c0f0801060b030c030402040b1002030403060b03010b15130305030412030e0114030a09050a0501090303020c0d1d0909030d0f06050a060801120b090f1b0f0d020a03060c020f011401 80
    0x340d2140006a0420804205030540c140459030440002480c803a52540c40c2c0c00424003818880040700e0b0098010b00040c903420354088043c0c000d0b60703c600c80c10b0100c51007030810103080e109410034581d403141044449060000c42e1030000c100e40111650760001c00d641d03070303205d0700d040d03412580c00041da6035a000104001c0503409880a0700641c402d00f09001000b01c171118011440c0401030000c2a440d41e160b4401d0305100c001c0000e00200c5a01000902059019150080194000c190600081c1c890034407944415809290311052900890040460b03002842c4200980c1d20009020f40c2401e000c00c12030340641c0701240c01114100001c080010400c20301c0d00d402d20062101646c0042c04124103000140041e550b0f11028021003500719030f5a4074940c4400450070f0900c1002424414540700710340c4005a400481e03008500e03000d80880d110150344244c8418400208c1c601c41009510110740c480520004210b684000f4031041c203841110b4650380a8142c581c21254800038001e40441c00400400011094 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 32743818 1250 32742568 32742599
    0x7080606090106030c0f08061309051605090f04020405190c090303020f030c03030a0e01150f180603020609010305040302070503070e1906030c06030b06120f0403080f06030a020d05070b03040c 84
    0x941c6400c202171400840700404440c0e6201e03101c401c110401e404036226544a0440380601c404c1003204110392034807450019954204004070300a02c400c143c5002600e850070000941c810075141c10104c419070746075820440241401450900d1b030540d09c5c19621103035000ca1088107084031840d10b44034001403e6040c06854520110014150f40d441001080ca0741c54000c0b00740c0c0e8015400c41804990540350055150141a40142107a4140c04041c4000740000799500010201c6601c5882e06c1c44805903d0b00082c01d64000d03000181d0002010050074500b54032035444036038442d02a106651007241c0760b0740001c0c10f000c1a03900103c95101044280b0803008050740c0c140c42c050036503000401c0540d285980b0388a19000500c02c03031040c541e88201c07034440f9072503501c02c4942041906000e041c1ca490715500391005c81d40c040d101600000c06410015003140ea1103c3c40d1401508018010848906070b40d0802c2214131020078111228003500100043c9810600042c5000300d10405400ca1280d04124043d502d2410 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 32745068 1250 32743818 32743829
    0xc0102120603010b01090311040f1503140610030f14060112061409060403140d110414030a0c09020a050705010207050703030f0c0201050a030c020102090d050606030111181011070806060901 83
    0x5004082042071ba002585c2404507580b12500c4081076440c0320009000340301c400300f822841410036018500040320b0031903c44c1540e2085041c4c12422034071400301552020115902c1041d10300500b030500120342a141c50340b00da03510030040b4210580c1c1d00d054003407e0410030b84c80200b043c2d100c1001c0004224640c05141201c5c40d40300101e0f441c1e031514111890782c0360401380c400b070305018a03440c0252021540204460a5000803c81841296180d1113500c18550003031081241014a4603900320040c500803585050440d0440580c03041d50303040154040095100d04480b000f0f001c0304000c0c09000403002c1c00138100107405000541a030340d01d1400c01a103607254541005c420400600030b5480141e80000580d054503e5501d030000300012100750a82c0207101d541200c80d4002e1302c1c480e450301003200002e600f5201e0032082e0000d0261074032100f1400ba080c00b0b4801e180542c044c103c030300d00082e03003048280502a0304191a0100282502c00d040900740004e40d00000e0941e000074040200c5030400d08110344c010803 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 32746318 1250 32745068 32745071
    0x150a140c09030c10122406030c091203080609070e0307060509060d0906020c0106080708060708100b0c07080d1407120e06030c040503070b0906091908030c03190f08010b09010309080c010212060301 86
    0x40c01b4540b5100600c42070041c14189662202880070161240741c0c85400b41c207160a41c41040300c60f605000d001c120003102c41e184a03212410024407101c0c414400c2c94450310001e4002c00c141820144140d80d542c000d0151190022401c0c0301b000c0d42a50a4020a55001c1c0610401681c441c2042e96803402e481868115002d00e030701549040264500001300b00d80d020225103403450003038488020107503440750707503500c00a524500031034000c00b4201c000c2040c03000c54102c602180d0105042e00c4060b80c50714488131b0550007800c0300781321910100b82d034282c008090b22000d10f0586048504c03a0001001a001990030019000009c5000c0c081c50508004500140107030f500d08500382014a4000b600354070503110101d01030705213102045041400419240c001d04410070640761105102350445640f40c01c110304117502030305605a1413500038010b0f0280e45601647d996044100e81c20008500140d5101503030181c10103903501282c7c0c01144429015111828452001583e2041a1440c032a16020090f0074140b10341d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 32747568 1250 32746318 32746361
    0x3070501030b0603011403030403120f02070e06030a020918010c0f030e01050f0c0a030b0306090f011a031c0203040504020f030108011a03030a0c0201030f0608150a140c09030c1012 79
    0x160f4406064074112a0401d41a80e00c02c001c00e000f0038290700503039200400c0000036542010b0001d07044203a01b202c2c0707051942215030b1650b90b242a90803206007640c603560140c00443c51900036041401109600c0121400208980c95081034494215202003083d040002c03a01d0480d072240f242d041c0201420342032210020300c820304001c840f00005890282c100c1700501070014603004901d01070f41194001d450028155a690701d030030b903183c5495407070351450b44031035500c0d04810b01d070031600d0062001080c00b0b024008100102c0c6040c0941a910203200f840340a61000f4440011541d4842c001403842481003110316031294546040d890035180c0c1402010300e800da00403804050b948001040c0c072001c02c8907281507680c0c0c0000f400140d00510081080d2041c0b07070b05003400440e071700300c0005020004610610b0220942d544400c034060454914011011301081404017040d00301c0d00c880e020384101078008041d103070920f241e1400980180d400d008d03044c000c203401c8100320203c95420f11455404059a10001795103 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 32748818 1250 32747568 32747591
    0x312040501021902031501091e0203010b07140f0a0602040e06010807020d03230924040305030609100902030f090105010803041406030703060806090a1118040f05030c0102040b090307050103 83
    0x44034055031543d2850100d0580380030035550200001c0300310b10b036811414950355864202100103005108891010300358540450b00c10036440388203d904a40c6003298940c2046c0c00c50391118a64110b1004404052003203402040a4801c24001569021f22440c00183c1d10780c5003061103102c40314010310190601004004105906401062902c1c843d4210318000030610034045a10b41c0b110ba04030700b8500b43e01c00d5001003044180000440003010708031441c00c0c00078540103808441c2e1080c401c0b1030003000958148082140b6003081d51405800401003031200c2321032a298100c00b401c981044580741c0441b900d032418061006800e10556016008650180d0b00d85428444c00315086c0350707040a1a405440b00200103801c951095001d500506410410340c1c0c442d00308243c08540d500c00944058a80c0700060404d910b0514000d180c20900100c800c005001ca03a0350f9440d110b01407800780d20207950324081000380ca0007085081c401003028004240c0d0281e224210340c03090510f4000c0c1908560305140c03600080010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 32750068 1250 32748818 32748823
    0x903030b10020c0d0c080f071e06090905040305070f0303021908060303040303050c0703021c0b0703060e070302030a1b09030b060603091e0f01060306020a0825030c020102090306040803010302031204050102 90
    0x1150070f020ba8245064150310318106104076419408950240604525a1452400071906a01f210711642614502c051700300318080708001c840c820b410100d80002010002e1000ba80c0010354001d0090510a04080c16501c0300c50842c1d04004003140020390010308540a507200c0703c0c010480c041d0a01c0c0000c82450801c02080d9a88070b14040607041c00b03804208504548000c0000303d000c1c1d5409040901d0006203900e907407103407481c4004111072641e103034800607114a10910031541150800034000103c0d44071604203038001d600160001c49240d4440000c06500001303004030540007000c5035100b0000c5440c0d03042ca0000f2040c05020503100d45d0080040c0b220444000900c405200c2c4800382c80750552450410107480c25030103c00c0200c1319428a040003050217102e5000d040c008480b600d030100b80d0750310710010480c019040c6880340108071003c40f00d006103034170a40c070110b01d006060000500c2c211485000903e400701c1260110f8120800000502c01c5003804d00c110035a0071003515145040c5420000040d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 32751318 1250 32750068 32750083
    0xb0907060f030906090c120b070c02010207030308090c0a030b01050418020a3b060405090c0d1506050a080109230705090703020403060c081005010507080f0c01021c0903030b1002 78
    0x201500e80701100709000c2c096210306510307503000032400090340d51011081a11594100191a0108c944c40083c0c082d500416140c0492503050b03016000c2c0600795a42614002030180c0038401500c614034141034181c403071002c2140614040d800c40720556140070100416501440700f18080c009441c070010006840711b103d2070080e1290300183c1c2458201c4005000108004d0022004024006400d0254071490001c40d150142106a409004a40c0c2d0071605035554800b41c01c01c00e4110800d0b01140c00805c041c201218402c410000001c603407aa52040000c0385600b60360000307070a99658401c1001041a621125082d0071109a031504418141d480325988a6401c0e22606004400c4080004c2c2c14510030360440e005141d002004200400244000421100702125803c4d1002c020080124056014105441c011a80269007509c0c0007010007031050306400840d0182d900750740a200745000321314144601c1c1d40d03512100000107042c1805080003419122034880043c041d5045450a01d00c07260b0104102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 32752568 1250 32751318 32751347
    0x14060a0b06040b0c0c09070e040c0507050d12020904020c010509061003020604030f02060912010c111605010c050a06050103080d0b04110d18060c050a080c0f07021507050115030b090706 81
    0x41e9201e070341d48000c0700c3c2082d421517a0140e001515104105d550364004c050103e91180542d401c04c55072000003015180c0b84180c1901a2595200d450a0b8140a00c1000d101079020030b440e00c054101010800403c0603a0031141003031200d039441d2404c1240c011002c004c20742d80202c1d03540c1f070a017100b451600801e69510907400701030094a10901d5503415519420119444610080c03c0110441028100340b802040a4400403000507e840e03d000a516000155105003d615450050919162a0040d41d55100a5070200d50f03030b0040c80c85c107401080651092034020f40c001c92800790780d1030982240074120350034170544030b1050345000031400350308160506842100124050004019980c0f482c2140b42e5858540010f142505020309507154607801070113000340003029201d04030031b6241c1c41c0b01c0f403980d0b001e0b400c4256050401440600701529000440c0d841d40345000540f80d2420780f60741c035498203482600c03000e00c411880d04d84080040090804a070341d400038a40e40540303509818218000c00c00d11200325032 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 32753818 1250 32752568 32752589
    0x41517071e0314010f05211c11060c12010b04060912060e0604030207050102010b0307050904110604031502090a050301020a09060806030708060a0c1e0c030507080c030714060a0b0604 80
    0x204103a0303010754000400100d10703840740f850350f607911514105684050b01071076014101d5041c0340702440e9440c00e907181c020042d020282c2090490800c09001110036092820200f24001c2c3c0d800a000c1000d001a500038803c500c0384550703c070205180b2040981040e1305c05c00c00840308010401c1042e510981c04030540d5108030050340c0903940c90603c040901201e040f0b154503070007120184001c064000407000c0441d4001c0e0024401e143c0307200c00301340e1180b185110380b9400c054810300040001c2c0c400ea10501690780010701c2e150505407a600c03528818403c540c0c4506845a0002e08021300b49841207840000300804c4000394601800000024609034151050740103008004000c549265400e00005014116a1048510901c5c242c0c0007903001c0d00108803138801082d102c1001480150510810341401e014984810706008030540c1c085a0b240c0c4211001e6614800c01c0c03020426584040c4010700c0014040c5e43c04001c4107091403c0e00e8103101019101d50445485c00c0c5285e416038030341106540071181000302 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 32755068 1250 32753818 32753867
    0x305030a06031a0f10030c180e0d020109110a0312030504031407032d08010e07030b0a170f0c30010203070c120f14070f0804151707 58
    0x4000c409007515400050001c42e041503055290001421420301c28081d100e40c02c943c50f128186070110742911400090842d1101b0b45042c00884400d110030802110a103500007400040c000203181408105082440181d440b60b4002e401d0200e81140344059040459001440c24959505c2e52500c03610811200207141e1550001000e00d030040c4401c40e010b11000ca011541d41216180041880c441060b04009400b2a00210042156020070b40445001c42d0f48840103c1e908080754440c586100400c41d408040e2a10410905034036082200741c01065084100000d80042d07030f0b00c260501c035500e40b5406030b40d4800090046160f0b5100b2200001d011390945031081113003c07030800740d001500b14402c00182e40c0000140031801c0d510203034092105000d036029040c00b9104980c2103558500c1c0c081d6201c0010303030b00c440362076030142c0c030034010321080303201d0940c944129003641d0380c1c0100342c0c00591150340c080065a86040c1070a8000d4109401039003810070520310ba2612120144c1030f06408000125051030003503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 32756318 1250 32755068 32755081
    0x3031d01020a0302041e0501091217040b0904180b01060e01180b0a02070b041404050c0721020f070e070302030c0409060f090c0201090308180102070602130e01060516030503 76
    0x91010910000259900e210010026000c0c3d881407040740f50741041030200080d01340413550040e043c4c031816590399841e00c1c905003400d076a02204c01c0041d42c9000039240c224072a491400010310042c40540e2885484810311401c1108071800ac0da940034083c03410048c4000001d000b946000e054612908100250080f6400100c41680d005d1101da84a080030310400b03e12200c0c0c034009041089141da00325a802629440158201d004510504041e4121411407061928207500415403040c48402c100c0d08001042e140d01c445081e00e520340b6503a20446001a800c203e82c1407020400c0081c3e420000c10030245840706102c50300c84002c0a9504260b404400303d42018803210842c0e008000d408418420705031200703a018a040e1940c400d4407901c52421205510060040c0202d80d0700c55015101ca0841d5a12812a00f901e41c04c500b00c1d001c0310355820054500010480d201409900c1d11150092202e2420003036881400b52044e0804418460103000d00141444004038402c11954035103003440d107a0b180d80 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 32757568 1250 32756318 32756351
    0x1e030c040e0111030f04020307230d06090503070c140a0f0b0903010905070b03190c120b01020f030f120105040603120516080406020d020c0402030c0406140417070602012003040303 79
    0x150f129564220000144006110600e11050003640202c06a441d220f0361000c4411014140414120300d01a807070030300708458540000b00051445c012940420030528540d01d003070a5600964007114a155407a4050140070b00c02c0c0080300a5100c11345040242c1313814107112179030010755445210301039000020060f455031401e41110f924141d2001c00c980d204d645408030240260411605540c140c103882100041c0d180890151042c02103051300c0760785496900300000e10103450341c81500c2c1d041d4401d003107001c0340581041000b458280070016440b44c68441f0011721208113101a030000b0300c258140302c42800031514080f81044032401600b03042e40c0c0c0d00443d400c0d038a07000e26442c1020b0303c00e81c1c010400145060b00499142503048d115400d441202c2d2000c41088100d000a5030020f880030018081030150030300803404420380c0318044d5041c0c0d003856500c0b02c0c404003110b000102c1d410a908054410040260240220103e00042e0b201a941c1c141100001ca9203600004001130101038442c110424500b41c82c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 32758818 1250 32757568 32757581
    0x40203060a091407081303080402010503070c0c08010204080c0d1e0507150c0203060601030507120e010e01020304060b03060c0a1409040905011415010507080f13090c08061e030c040e01 81
    0x20502c050120f0300300020a9251a0b0044910001181c4c3c4840092003010103030740e4111030143d0588500e4004c5d2115001100e41340c000a200d0313028030803080c030a1404540881c031614000c1204000161b0380c3c608007580c050800490a00840c0100e07503c404034000546044404a0100c0c00351a00d00e1002e4400e0130080d16044d0f261f40300d0385020b000e8480703080721503900c07540000340c190090f804c030340040c2c50342d1004402b01c81048822000050704900c1010196441d60007c8000000d240004680c6020b0701581508a03842501c04443e460703036880001100b4241030244991110301d1100c601d061401031300c0040e00954403200000396102c0300090100a0703984540c1b1000030542c120000b0000741100c02640c3c000d910095603200b00b14601c241054100e03602c2502140c00d144c3c0c1c04040c40c2e00b004080d40085000c0e800071090071103801e500110218004041e81b2412040d80065079908580d4144103060000c02c108601300054502d4110ac5a6611510f002440c20ba45210543d0005503201101c0100c500400c407 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 32760068 1250 32758818 32758829
    0xf0d020309120310050901170601050609040923060108060c0403020d060f090c0e060609010e21060702011e110a110c0d0602040e0106020f100903021905030309010b041109040203060a 80
    0x841030004045091000344c042c0d03241034507000da542e602e402001042c0d1800450f0000c1c5c0d90f01a40043c40f02d420000050040240f000d40007280c8000309a0b07030442140c10449250410100b40c0c01c407602610801c1020070300400141e07020344440e081001030b440d464071540c080a40580c1c502d042d03500411400307a000070b0000c04c0003002008128900d00d0800740c00d600c80d11034500301e4074002c00030501c0343c0b500c41d0464242100c161a040104c04594090000b40354501422444100e043c0c40d03a080e182d0380a001007446004203600000301100e00c2d44d2090182003c20314610002442c004a2440c8851f002041391070081840c1070060300e4144004410349400345201072190420880b6183c0c1003000a645c0150042e9051804451856a21101c00f01d950303088846001c100c81d8011217602610310321035072109610390b00906c1a902c8011030310001d03800e0a00c620700107c489a00000411a20442c28814421114401c032018130a21a2056800240c1d01503082c42c10710843e40000402e01540d03404900c14002c02 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 32761318 1250 32760068 32760103
    0xe040206041508040309050105040f1208090307030b0a0f0606080406050a0f021603030605030109080f070302030d020a0c031704030815011b030215010e060306010902090103181b09020f0d020309 85
    0x2c0c20400c0081c080001601d08038003003410761502049543c041e00507101621802041c03004030781d25001350030800200718501918000401c10001e40e00303447c280001d00145010b4841490705007404129001211984a85c1d850001c0ca05038051110380d601c401c942c0c0d017040d0000d102041d1500c4442c1c8160040010707001c142106032001802000c02c0140340c0300d813201140241c5041104546e01c000781800d984107000c008200042c06c02050f41200402c07400382030600c1c0070344103c0b030610b5015401d000481c3d00284e00c11012030740121141c410182e00240c07501d00c1e1001c4030441c840e00e04180d41e0141000e18054079100c05241403e4024040d0b92051485000d01c2d1000c081b02400d44100f810041d40380c9245030b02600d418250315002007141ca105c040540d0103035902030300800c041c0c0c1c40c00103480000d4000e40312072410191182e500740c034040413681c510f2000070700880d809500b10600c40b03208116440c0940c404207031940148071844000d09042c00303071103408c1851b00025940703541d4031354481d007055030910940703a201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 32762568 1250 32761318 32761349
    0x14180901031101141201120c030803070306030c050d120e011404030f03200a1106040323010c1403150303070c03060203090d090b0901210c050904110301050306010e04020604 76
    0x10160000402d00ba1a00b038882501032050f0b540f00c00e00900c121100907031484c200500401c442e1410b0a8584440d600868402036604d407603698550581d0710075504080000d440341c8061043c00a815400c0380101000c42c0c40a516001c0c641c0d0314061050400031001c2400309441c05001d0a901031500d04404c031124401e01c664558070303441d09408a100c1c4100c1540001c3c525216052001c1c22081c80070a56941000140446030040c1d54611864205405094008000340000000134054400d15401310050703005d8900c000b01240e00003421500c040840354200690b1011800d0706e1401082203a802809440391040c1001c642000703c1d26621407a040101f84222011b00001400290f5001c0c50154a80e07405070349031500065006c5400c03400c0c03402010440c0d2020490380d441e0750b024041d00c900d250350041c10b0402600d014541c440884954041182c040340700000e41c0011840c0503c203500d003070428108000e0071541030001096407520140a8a100d010360b040105080d951224180c03401041d1601082442c1c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 32763818 1250 32762568 32762573
    0x1b030f01060b1305010e060403120212030702150708060f0d08040506030c120906040c0e0702010f020406090e01170607080408070804030303090b06151c1b0302031e04031418090103 79
    0x3158442080d0452400f04040302254035132181800141600300180410704141c250307100c03014090700c0f5554450540c070030f22202240c0011a80091071103080c0c036070090b100c039200d24821007225560040c2983c00f04920101080701790340c0d60005c04891080d040c0c44901401c039141c87c0480440c812078001684c410300202c204440d058444d402088030304140400003c19484048006580380016a0000d0101c00615814071110064141071a80300c4460b100106081343d5421242c42207921680040c80042d0083d0010b0190310110100680100307500c1660103c07400f0b950307a1642d20ad140180408042001000201701440f040b1000d442640d900302003010359071a80c07490050000c01c0c401da401c41d040000d82000030f189152080070007030700d200145801450309450030601c0c0c2140d079800c51070984c6195035503a41c0c00c401c00710950b03040d08060385480050b41c90804040d9a11040440008802c1d1400c1c1041007000081c1e1140b90000e60804003a0000c1d120a07504520405018403401440e41110720724000005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 32765068 1250 32763818 32763839
    0x1803071d06030712020306041101210606030606020c1c1a0f010905010902120426030a02090f03030f0a0e0103090b0702100c0201020c0a0f05010905060903030105030d0903051b030f0106 81
    0x211400c600315802280e859641181304400007a010b58182c000700000b070040365000030324401c500f00501d0580301c0480100300c01e4455200041c002206c40e6513071041400816014400c0d8005000207000070141c000e41400064042140414141280c441380c8000744200002001c0768200180c20b1803108503546000800794006a40c24424000e0082c100f0f000040c503014188202c801c1c0a040140402e0b02d59030b29181c4ea03500f0081d40f00c00b010601c2015840c84440d4030b200000d140140148400036a68100c01820044000451007406101b85c20801100c05d038152918100c3c0ca2008580c20010344101c5441c005034010401e801000c0c010031800c0041050072940030a1558034001e0240d0100001080040100d08030301860440c07118542c0012810070200d103032114100c1d1218400c000220301e0304020b03a1100e0406200350b0305e00005501c0400140807915050049071500c15507850000c00c02031440e210950303201c9515807a406400d0001c00091540e8030184091481001528024031880e90348454801 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 32766318 1250 32765068 32765071
    0x501020705010f090f060b01050417010b0f01020303060a0608060301090204060303050c010c0e0f0111030d0c180501021b060702040f0c0903060b09040b0c03090a06090308091b03031803071d 83
    0x856030b5180c52024980341949200d400c90443e00080244000145a55448000d10001c01d07468140002404001003403a21000e01d0388035a25400d002282d0020140c0900c0751100c00102d925042d074109200304a0140c0790038082800b01e8402e86011130140d250745010074018480000c0c0a5041400e024010040c1504000140740b440700b400004c202c500c0365940104c0301400742e5901c00741e00140900846038150702c10b100001180714080b0903289008036442c1c0d00c1c0c0c200c0e031440180402042c64010660f18842049544100605081c00030f0480005503440590085071280c2483c0d02c14100812800c003952030303e500c142d1071240424400c102104000302c01401d144081e200441d81d0034141210441c035802c050f01d40c1030103039500070600180e07a11401c4c003444050f000201104914807400c11440301262203030142c4980300b40a030700d0b1441581420407070b180c10301c01101c0e601c50703184800402800c0d583d10300100311a90120341e00251558139249400090819005500404010300c03000d0817040810712411501d03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 32767568 1250 32766318 32766323
    0x4150603021f0e010207080712060209060c010c020d03020a09062604050105011703130329040606060e011d0907090902040801020a020c0306070f0806130e0a0302070503070b03010510050f040305010207 88
    0x111000d03d03640b03004aa40f0101030040214640004004010401e000520342e85814400c200250410b01e50502084454100b008070080d513079141c4030807500d6541c0500040c1c501d282d1394034081d072808103c01e6001d440c3d0b25003840313280308018441044040c00101030002103082d401c44281050036060a00309a03000c0c26003809026182c1c410f030b8254101e0b030032000048401c000034411120f200c0a01e5500e41d070707100d0841403c08040c28403070076800320003107500040b02901c00d81c0304540024800e07050030002020b6016942c4154144901360704044a610f0314004e42d18000d003003c661407800e9542d11841221042240d5102808a600104001c0752054040d0040c06000ba2240d088545807900c0c1070415680d1002552000701141c00c00d1a26400d5a1180400c1540030101421036205224110318502c22203c1e00b090500d00350304100e244204141e0705000d820300524046008120351307820a03200700520700c0103124140c403a00480075906106402030007603540c40800000260f803281e85e28241345020b544285400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 32768818 1250 32767568 32767577
    0x220b010f090f0b0310080a05060f060414040f0204020c03070b06131b03050421050a080109050610110115030b071103040e150102010f050a0e01050a02040e04150603021f 74
    0x41004181c89848900708a41040801c6124546010052051540040d00c802c01d280e41c07820380401c1c010340c100080e6100300e100350028076961a01103007040c142c01001c0c11461040b802c0030528181d41d052201740c00e802941041ca6041f910a15100160091042d01005420390001203500d07000e000c08a00c0007441007401b998002c40d0240c07944050707400c03500c040301003400b8207c06a41c0059480d10076400180c0c090301c02c02c0412803103400030011f1440c013220280c642c0c000400c000350b4441c0580d0300c40c10300c50042110300401d000c0c5083c00070002e4594201503542000700910f9084041c0c41c07000c25040a20700c000d80c211b400c80401d8490505840442c403c488402c08036140c2c0110035201c84001046030110344084d140b58000b42c45048025501841c2d03c40080c0c111340d203038100d0040350300c1d59200e03103401498840e000050b645903101c07540d0f096501c020200b4000034814081040000c540491b580c0d405a80000521400c0314045885401000507420294000000c0d4600c0102c2c280100c51481e1005c0003a00c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 32770068 1250 32768818 32768837
    0x303050c0a050412050304050409080d1d0304050402091f080106020f0d02060105010c02130c0e03010b040209030c19030803070216050301090507030b220503130e100b09220b01 77
    0x1003540c80d00ca0041800002103040000300542207010083c0041c0c0391140e8141d915041e901e000040642d401d0000654003a030340001e20b8500240240704ea554918a0340f20303107060602c2c0f860501c0e03889000368419540a6500081c1034002c84e0b40c0c2410030b0414154250f034030300855038021402017000d10240103420161080c81041c45d89042c0014680004500ba41d005201076820580110b03600903c1610498014405414a5080c00d8850244c031146d50340c0b5581e0300300c05c3c010b140304150941c1d20010fa40c170700880c030420a003085500c0210b49419060001d549043c1035240140f401c90f07100030250710141180c2004818085902d9000c1039902e001c464807000d1145894542c01018201c9101e140c0082c1f161f4020103040000460f620041d43d03000c40700c9100ea80d100c403140c06041d0041c4031080000c86003600005026511609411014005407a10440c50013036440d200034060b05407002401460101000455460003aa03503045000681810380352041001c4240b81d040c50024202200a95020811080 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 32771318 1250 32770068 32770081
    0x40c06112b0f0c050601140117040f020a09140105040203040c0e0a1401050609060304110a150e09010602150403031a0a03140d080c07030c02180f040605010609031a09010f18030305 79
    0x6504143d100d4204003d80380503440c0400030b40c40d40d60100d9145040c407403a1101c000400d0600c0c060144264001c50300b19080160718410400310800c0340c6c100e507141030324000d4019100140c0b028210f0548800303540041c0d59032214101030b0308002e190340c414070207540c09404008281085800c8404c0120350300380b100e44c035030740c83e40200545401107509040c1c00c0401400041c0c085a44402c1e100c114100141c08500743c691200903030864040355626034000705440e006498910b00f4409007250041110f840071300740c03800c840890312558600150000c0c0c109900c404055015901c10203600b1a48040180558032040d600d21b45030542c8a41c681d03415010307005407445000c00501900186116404d10030001e80f8000e101e96042e02c0c441c15031182030783c200901c00041e003072000c00301841d540201580310455110380307000d140460545005801103000c120581030104002248051010322421200c00c6011090741e440d81260f0040100c50308800720507081011190b001007519103000a140d000c0e0340c0074070003540c891 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 32772568 1250 32771318 32771327
    0x140604030b040609020a0504111e0307080c071406070807110604050304091d06250306080d111504080d0c0804080702150f030f071106040c06112b0f 65
    0x10311026080c0703010140041c0000e0b00a5100074103ea00c01410091400d40703400108085071040e210075405e42c10001001004109841800c0d1404c0980302c4070ba0f40346142948008210034400742205040f0280420f80404010b01c82100004101020b81250440d01c3c082800810642007a142032010030380d15828201d100e000828aa803141d50040003c600e030a15000e448130003403400e80c02c80207600c074040002016846c0c0502003d40580940400840407001142d0302400e0802c40030404c00038945001d00070403408001140542520059040000300d8000f030101440c14070480d030400ca01102e00d0329042100b00040c14000d00302100810004115460603001c0c1074901da041964064009001440000c00503d01040c00000b0003a00c90802800c1071246110302d85690400e4500600c0024050100b0900e6a40007150015207440720340200380300c1c10281c551520503542c078001c0c241084410440f41208800030043d4080801003001604003e070104441c450742ca21103907961000040f40e2091b0f819517030780324 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 32773818 1250 32772568 32772577
    0xf01060609060f140307020f030d0f0e0d0f03050402120f0607080a0c0c020d0804030f0c080d0503011404050603011806020d05010f05010210020a0318060903080a050c070b15191406 79
    0xc0c0c507040d113000d01e40e1114585075040240200110320510640580d02e850034006041c04c0340c0313000e602107081014072040ea0140d0361000da0300c8081d54082100c143c08241d10550303810300c1c070b5120305000400f91564000315440c60280da000c010280314080342005130392000078040c3c1c42108540d54005980e00d4501c152420346104c00c41010000c0c070054092009464082c0b41c11248a00c618000751a0039500c0e640e480701075100440988112032403510400004400f40b0828181c0601841e10510f1b66062802d500c1103403181c1070307060f4000c0d85c1d2500012150785003580f041c0d0a540d500d00c2150f00814240c41c20710302075031007440701d1907000d414400001118115442000c055031816000f400450680c1e440040c02500f16020b0300041649030070020400407007654101c49850f001e200c0c0400c01c1c81447c140030f0150315014000b4a00f15240000700b00b8407440c98016107030300f03591090710140c4a4840141103204040740c481c405030301c108200d2007041d013905c4030300248c02168038410250701000c00110400525014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 32775068 1250 32773818 32773847
    0x102030a0903081b1c0f020106052206050303190905030a02091305030904050106090e07080f15031c0c1e03051b0316060e0c040605030304030210020f0f0106060906 72
    0x741c0c4041c00007800340c201600c5a0b8002040c90f0080c0385816000c1c0b4540100741c080480b074152401401284140e2010001ca44095140002c1c401c180c0b40802080d04d25800c0120b48080c40e04192841890744080e420070070041600904032a1584400a000841c00004500740b4010680303110000949060228401a280d900100f5202a03655402501a00c14001d000c04480c640000c0012105c40c0d656446400e0180c445035850303c80346414404440c402590151802060090301c1d000c01540b00b0342c1883d45544040000320604147d200c0001007894400c0c20700c00c03ca0120503100090a030103074030241d080c01c028091481d40340e500501d22050710a1465062010300015000c125445c84015644007070007a404406c0100e070310300803021018070705080c00d200b01200c90f16203c1d04101c803441010880f2000d0040101d030704201280c902800280c0c0c4e4480d520009004001400341c5800b21f50003400605d42c7e41a101055601c586080f00307455000780090f0040c900452a82c07803000c10010311030201c0b41011302 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 32776318 1250 32775068 32775077
    0x3131d06040b060c0a050a060f02030603070504020c100207061407050406020303130f0b0405060f0106030605010c120e0d0804030317090316051911100c030f03050a0207020603010308030402040b0102030a 89
    0x11166800d02000c2d240c6140b0940d000103081000360b14060f0100841076a480c011400385c6181032040c60418155401c01c04d600e4a000e0060007480107542c0c0c0801c039401100c20444006030703900c00749160507061000b1060700f0303208140f0202d036050900c05203130041a601c850b02100801c4035920100180d42c0390246005080c01680140002442d02402001c06603019000d12042002c2c0000d5564034800c1c502e040b102110590840c00522500d20fa004484130b0240526040502859082500003001242aa84050400a03810403030101c0d42e401ba150f003c140d400080c0102c10010a41d0419401c26401484100c00241c2c4c440c06400709180c9034081c2130302400124019524001c0c224200d820180701c4004103661707a000d000c004107441d10095110b00c030004e00c204902c0d20658142400c101d810384404442c5014400501d8840000a03807003a2a070302c00e00014100003880e41c8072940008028028194001d410020000010081c010b040c406148030b14400c440500c803030409030004a84a000d41c2c441100405c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 32777568 1250 32776318 32776321
    0x71a01081509100c1101050f010513020d020c01021303031209080d0504060b0303130806090303131403070c0303030209190f1a07060501030c0602100207050c1302130803131d 76
    0x5005031441c0c58020300c5040444442a050240752412074007001181c0c40440c1c070300c04410320078120a00a40754000c46020004440f9032500340031485007200b4614201c42e41c1c1c1c0c00034142e0040b55070780e0f040d983c002c0082c000071900d4400060391550f071810140030036000b103030320414041c603003112030b0140460f1b8a03880100c0b41e00f05130043c0c4003140a004040c20840e40192106104001510f0400c06000c01854010303401d00020f150034106410800c0103403060350306420800c20000104c901100160466034400038800081c004c80e02014118060024005c0c0925550300c0c0000500d64140c0244c160114200d880710646004000305080a04a0703214444000501070320030028143c07000c2815050f100d054a00324070f00340c050b40d15070741100c900760421078203d202c0003000e22885504010700103800c0700344002186040303c9a2501c540c1c1d8000320694505c28000c080320114415125010b42d610105490120422113484201043c1c490300540121503161144d580c00040c1c0088d14400c19001c215001564000c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 32778818 1250 32777568 32777593
    0x304050d060c03090203100204150c05060402100915020a0b0906100501080606070209090f0105010b181509040c0905040510060c0b06010c02100c030314061806011103040902071a0108 80
    0xa01003400140c003e141c2e0720407624000d0388013804901c2006014006c0143e40c1c605042505201d0f0583c0480708040004800341038000030400180a60020740446403440d802c0c043c0c000456680e082508031030f0b19003221a1500d00c1040d00050b13070741d2081d445800813150790f5031098201c95461104a0f000c03903403046840ca08114030750083c452035400c1480540f095280a20320780125001000c1503914500e980d0020342c0c82d80303036940284142c901400c1c1000a00b85003580d0f4000001c403071103400101c2d038030900c0e001c00e81100041c40e18045480481001c0c00038800000700c0840501085020700c50786000c2d505100014102c0a5494604000d0f642246c0b1501507a815907240c041c18918014940c40c140a02c0e1000039001d030b914a03036030003a05503075075440030890b215900d4010151451081480a988409010311060b41e96020340c454060f039111000c908141e0b90400101c41840040800130124040000c010580200176002003000601a10411003510107442d44440358a600b4420300c0d81d03540161000008 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 32780068 1250 32778818 32778821
    0xb0109110d0e030d02070c030507050d02180606040e04050a020f0a06050d1d010207050607020d03060b0313020d0b0a0e0f0303040309050d03030209060a20070308030619030c0605070b090304050d06 86
    0xb900c0100307070100ca003480c0503011103070f049134800413066600c2e088913041002040740030003a000240c401a10303da1201000e035400304115a8880006540680d5142d001030025120381003030710010480c51110b8100f508090410030749a466001040c1d00030300c8811100d00203400c1038012541290181d0f0755003850052203030030200c014500402055480c50401e0607020070600c003400680789040c00791000d0a11400e1109000e444d2245c0200a04185410702c80100400308812080d030b0350011904081204c0c2418074030008410307020001c0010019110742d420300815511581c0b090081d00e4216080740e01d0070000520b01c0b03950340011100100054141c6c0b00500260621034000180e041c880d0030054200840c443c00242150000d061190004089101c42480d98100c880c17405851840c0c20080e00c001821620787d80c1032807000420003802110b80c1e4000107100a04106410019500070000c500c0703060711400001c120398840340050340e10f4000c020104001e0040482140c3c115640140080c103103140c1540d4800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 32781318 1250 32780068 32780081
    0x70509010c0506070801060801092f090a0b03060f0d02030712020102030d06090506040501120b0703021309021c05180601060f05280f050f0301030f11060a08040b0109110d 75
    0x604100340c1c55101c800141d010000140540902c0c1c0300c0118944c1429401004070340142c2c8034140d210308140042010103460402524424601d48040208030001035018059100e511041130704410143c000040b8500050003443c0504030440c4d0340c0c00b01d2090441000100c0c6242c12010703506402a11082200d025540c003e00c41c0c580c03060040d00d080103074484034141100e0386603001843c10340c1c13207400300240b600d051710401d40074001400c00d04540c81425201c403018904c000300020240350740007804012455400c400d81d001805113050a564a070703072034034508607440055603078070700a2410040456001030365070910b0300540c40e56000030110b503803800c0c5086070703040b41c800042c0050142c10001c0f01c0000042d02c954420000c00100428001c0e9141e01000305050f041c50310781820003a0030710980d404a100ca40459044a0f0807030781102c80d40b0818140040761104601066030300080c00500000521b4010829511850082a00345c50b940c0e82d880c0b40c542610700d1010500c1c8041020040d0102c1c1e106140d0024 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 32782568 1250 32781318 32781337
    0x5040603020f091506070308060118030818040f0207111e0310110706021204051005090705040f18030207030c08030301050a03020d050a050601060903150b0109030807030c0210090503060610080705 86
    0x8013901d40e4940042403142e400702905a002400041c104905542c00c07050100305000c040e99107201d05031564582c5803142c0115407100302c00000ba03003082c0d0601d0307541d81c00000488071901001c541e54445403801451090401c4074180c0512148000e18481091000094400180c0a07001d84181d00441c0d41803c000c01c03129810200014091040a000c503441e44060030300f000034020490407a08207801d000c0c1ca440c1c2c4065030382c014142040100042580042011000ca910603680800d03249018490180500300b04e01c0300300300008015100b0003c0c1503000a202088030b000d403042c10f818548030400c450312440240240c98005c5803d81080005003000102480c0640c02101a00e2007503640b0340c0e1382401e10000f80d00680c001411140284180300d2514083c40f6480b40c0c514080002151020000e0010249440064003050002c1349040505010b4948252010b900034030429a0118440d03010340341c1c2c6a00c4c02013074001d124900010301a82481400c10500d0801911a04885c2d030b03d0b50b5048036150b1200440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 32783818 1250 32782568 32782591
    0xc04030321060e0411040e0109030914120a0b0105010f020f0309060f1209030408160e1b2809080307030801051c0206030f06010e0102061e0414100c02010605040603020f09 75
    0x3c03504255081680030fa44503078040c03d056081340e01080140d6400b003d901441d03914200003900001e410041c2801190344608034904d00100303250000c1c0d003030f5a600002c8034081c0a008842820044140042030581c1c0090b22500d00703010302c0410480c1d03141c203071024040c010b03801084920b49500d004000b078098040e800301040d181441c19148074030b124405440003580c0354008107003880078540c248007251842202e40010032642d843d0140c0c2540016001c0e2822203120101710386c0704580d0201da0100c601040d0b10b80d8582003d220450302014518540001100006095500205203081d000c0200e078503046e0180e44541c3d0603401c00007003250811a503860f0b00707a034082d41d030030320001601c80b80c000c0e6114a480008211282c6802c9002404581010a14a0454105038200700d1812010000d0715250346a003000905243c0e1203180c14207070440c0390780160560b44540d0b0566100da901c03640001814122542c02800060750707074014841074840720300009602c46520310030550141080d18401da8821040c13040c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 32785068 1250 32783818 32783831
    0x7090602030414060c0f0c0a0504140609040501090203030406090f0b0c03120919060501030b010e010807030609030e040e0a0309090b010c080d090206040308070b1003030804020103020306180c120c04030321 90
    0x201d192828010149501c01608001f29680d020304d01500300708000e240540d001e01455403511140c00c0441d20040c400c07441a80c00e80c0200341800001d6010100752640541100e6590b6115034020304181ca01e44603039100074040c01030110f80b00c203900c011b4410305503c000085040c21105c25850581035802090450707e48601a08400801d00400c2c00312a8a40111000a80c035415400c1403249250305811071300b00c51000a004008034080054080200c0b500701c48002200415440e080350311b215002c1a40e9030040c10300710324071394200000c81d0040e0100d01c41d0700c3d00003000b5522100d000070340d41c0e40b030005408200d80302c000c0004103110340001e0048072031820000641c0495580001c0c01030708180c00c00d4610701004160f0030104680001d082c0d80152142e804500d2541c5956402880814000c100904150700132001c10181d0301c4d12000c0301c0d16000c1e1000d0490b014504410354507a50b40010440003e8507901d000400c0c4095900f508660549401d503071000e2240074220310008107035000c001058074650390b4a8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 32786318 1250 32785068 32785087
    0x12111c05061008100209010203091003020d1407030e06090c0105070c09060806100b03010302060306040902040902103216030908060408040303080c161b0e1008060709060203041406 79
    0x441c0c948110280742da00822941406081da241545044110410510400c0000080c1c1c0c2c0003c29940103100488040318001001c62048001c0d020350b92088000d03c3c05e00185242503540d2103a507134402c0000da03500b00106c140301e0003001d58642e4182e420900a4028089020070740d40305070300a04015005449039841c559a8040c5542201c10b641d109182a402003028412500300b8044020018130411030003505650464002036910710004c0c04d0b40f4411075841c000107045460300c0d041400c0d1180c00406c500e0220760101405000e041d1004401c5605e030380000c0440c420700350389a4600740550a0480d10b0340c00c2c1401711001c3d58101d83c09050075410700147c03041c0043c29050070030200d88540d2146440a80301e500d9441e015180301c1002c0d0801c004108240848a41c2d60a25a0000d446580020f0030034004c0d02000000304ea030301d5075a004898804450000c01006840000b448400c8580c01c5080340c00d00d0380c0340d1500325072040f0a030003170a005030010030040021340c07481d22181c1c80e906001001306261240c2003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 32787568 1250 32786318 32786323
    0x60117010905090f2e09120e040e0d02070302040f090b010605091011030307030f0605030d05120703140406090c050907030c030e0601050d020603151203030405060112111c05 76
    0x1d074030000e8a50788420410590400c00e00034402070044a600030140083d040000030384005850888880f50141403035610300e4111690042d808880e0051803032607407488a40c070f000f00001004480a4021410126503261151000071003024484480c0e002c0d006090071603003000007810480c0380004103d078440c1241c5d0042031020045900a003041d0721010360362042c11007400382c044200c410181c14403032554122460040e021084a500226a01d0000f600c0040e171009080240300c41c0e000326400d440750310181c4500c540c010303008081d200141c0354807403c42d41e0b6240041301541d0b900c0d14522800205070020400044513608460710880c0306200184420b501d88010a820b03d400301c8006000a484860a020050701849249000b0018030f0140a4641c140700c0811414103071240c0081c00f1b08800800940714240e40c160388155032100602c0c0072820070000416681d660416102583c29020300310000420107401c3e90901d290b254018900c0d2100c0351401c0410143c0580804400c0f00c50b0078280a09000480a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 32788818 1250 32787568 32787571
    0xc040906060f0216060c080304410a0203030a050d020c10090201030e06040201090b1309020412030207080705130203041e14070f05180705190206040b070305190203060117 75
    0x60b0b52400706100395914024a44010040d1064400800c444140140d9501503503450046800842842c4d40e030f160f61411681e050a500004080c807611407034a0048801140080d281d010040b1a03030410070819550302540326010410002e41c1580100040c038069401132019260401501e5401400d00f20050201800d01e13007065690215030750b9402941045603054130480200f0b0f20f0080c0241490710302540042c04590b035902803035046220108400d0f45003950140d00c3c2003d0b00070b400e0195100c9549071a41d14442508a100301d0142c021440f0120742c1d028002681c3c41110f0004291180341041c0708051802544058829200d00701e40300540b54540322408002014244070b2441643c4014181002c242030864603040290b2140c0a12004c02503980c40a0400c1c510780c030500004038039a1503410341680c56102e8609014180f003c010301404440c1d0f000300303900380318a02800111400340e44500c1c2c201e0440b50204d413405454600312440741d02c40c0c3c150380c1c051540a4030604200b550740200441d40312542c41c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 32790068 1250 32788818 32788829
    0x1060201090b09010207020a030b06060705160305011b05030106120b0405070801090e01020f03060609041806091110020d0c0c09020412050f030708031303050405040c0503070806010914090c040906 86
    0x1103420031a010001d0742d541c1140d011000c00300850031b040d240d030b000a01002d09403001170103e900c0800401e085990b030800310f5000c0c80c1d1080849030040700b81020300c60040d0040c84143e60952070200e9812a110780042c01004105c802d5480718a507030700b4841c0548020032100740022481380d031001d0021031902e4501c07626000c0c00d42616019001d61410701201c0c1a00c44030041400c0690040c4100c1001001c02c50689800c643c00b02c03121502c610550000c03c0007030458620514601080000010902900d54003208072a070203032461800a145803010300c0340345903608801c6001640300600124110f40b040080c0207590384912180c5171208e58072040c560590f0040e4006c100540401d000403001c00c502040b01c02103003001c081c069400d10004d62225055400014070660320503102441500030940704a00f1207016100060003041207002881f001000d40e0412109440840c02a00c00300b10603600070715811049170209000540440d1070038080c000c1495004d007900103003183c1484007042c08a46402904050407 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 32791318 1250 32790068 32790071
    0x6060910030b0c070819020a02040c0f020a0f11100f030c020d0c0602130b03150307050d23070306050c070506060a0e071b1203020c070e010b03060d030509030714281401020a060501060201 82
    0xc0900401003141e44007400e40060cc00c0c3c0713017520001184c0115170014003c0d00605e80c0544900e06040c01c8007803414589241e948860300746503941a070741e0440d0035001d1071302039548d08005034030381c81c841640e44071141401790303000c140414500d000184507600200408501101d02000d46941c0705040b681a0b0070076281c0103804070740c02d0307440c008900303042110710010700d000c480000721a030507a00e41d00e0034480750661404029038003100200c552081080325100540d4030442c01c2004c1e01e070107050f04610740c0011390101c550f40101c0d0045920f0740340500c2c40405070380a2070b0007042c998031921415a401030404400c0f000a03440039800c1404507880c14030362021500c00d510b015036181c0ca000d140e181030106981091f25403291940052050120341001c0c0d0b54800030513201c103281d6007900d080c10384207800fa10040700e40c14851401c0101c0c0c1c40141c9102161540380139543c00c402941d0f0721100c20010f00000d24030300c0d403900b14603400308000c1c0b464400490f050308060059804050080d03c0300c0040d148240c004c900580e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 32792568 1250 32791318 32791333
    0xf050303070311090906010c02010212030a0609050105040e1b010306050909010504120c0f0f0c03020603100302030601080a260412050102030601080705040608040209070302090307030506060910030b0c07081902 92
    0x40742c150080407a03030080100d20610344100700000400031800a00114100182d15040d1011079008006001c409610026150348902d800364107440600558091654a1400d0000000340340c2410b028448007410b4481c05808002180c1d030723042c4842c64071483c1842c105034654500185648511708582c0c02900900004665854a81007202185040300d05c1241040040321400380861405145d420545a1080e0f40c50421006401c1402050440c0d07003001e54022170000c00d20041446030303e40300b41124402d40a4950580c0e803410b40d142c4450941e5800f52415104411204000300d08807080840c034500c6200e0385081c43e840340b1404140161410300bc031890380d4000203000440d038219502c5580f00f070307075403901f145002d06105000b07242a1015100a00408919002c02d00040c0640c050b5000c10b0806411145255500d040080d510082500c01c0c2d805849030b0004120842c100d00044820341e40c111550b110035460788182046c443e44070110903160300d1380500c0000d204072800002d6803880d00075580140540e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 32793818 1250 32792568 32792581
    0x7050a0902030f10060207030b150604060302130614070206030a06031208010f0b07020a0b0d0f020a02160906030b06060a020c0d0c0e06010f02060a0902010203090315071806080f06010c0f050303 85
    0x40c141c0c01390012401c43c00b400c004000d030b10750000740d49050700e50110305250561160596201d40100c00f90515600c010701060100d401507060b4068400c00c0045044125141c2d034583c000d8500c4d034002d11403981c00000810004001d4201000110303000202c00200066a80d56078581c00750044580d480c05000030f5483e401006807138000c0d145000030385061900a071503d4101d50000304040c0c0c0f903100b403a4450304081120750003540c0943c0110b000032142c003420342d9141009031000b51110088100001a800200008030707560720380303120f0034007601e50060800c241516604200200c85d00030b500d0100851150840e070301d00795212061011036141c0f040c0760098056007000b81c03109800c40020110350400c40d031100d82004403031340042c10513001220500002601211070004034110f125541c81c554140c420074031484503522456603020712940c641d984240c8140005034518860349a00d100d00c8000683c07040102c1d450a0b407111a180e080f0105041c8004070720490f0340c031101f034118440000d6a064001100300a917 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 32795068 1250 32793818 32793841
    0x120301030803011a09060d0f090c09020c0106080102030405070509270c1e090403030b0a0506070b070807050f12060604080a031707030605030a110607080d0b03010c080112060e07050a090203 83
    0x50340651425040c10402d480d400714010f4003c4084000085448d13152902e100b0240b41d1005030300c6074100820031680c1d9101e429a0f0069404034488080541c80c107000040d07501c3e010b1007070307900499108001d054150702d050104420359001038141d00003220a156110440b610a072951801c07040020040c040b4010b84038104200d001c0400384050055144040c12440c6a6400c001030ba48181d00d401e002409000c0e032000310f124030318103800103038010000040d50802d00c40d4030032074244212455070b107220b0f9603900c1201c22074160003601070900111805104403e40c044c1603010f00c0d40c0c00040508081e0078281d8030108186008006203080e0040350040c40c0c640b6051a400d1001c6da88402c10707040502c161440c14020903510341821402905080101c20344a0003030f07171000126081c403174012840d180c85450720301c201d400805030f08a44911039840c102c0d403c14801e000710034907412180d0440c48110241d8043c0c0700c002c0980990034011980703000b4800301040c1503031072841500191900082c01600e900d0074524200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 32796318 1250 32795068 32795099
    0x100908010507030b010e100908010905010203090105011403030421080d02090a05040e19050c0a0e0708070f050301090b010e040c200303010f061101021611010807080907120512030103080301 83
    0x20b00305428080100140c0c2d0b046a0342218925098407140c48103010004200e5108489130003180e0a035080841c0041413100540156005d03956141c000c0100d6607031001d080819486a02103e9010740091000b0000015048000400e5480800d00142d101d80f10340d648c04070700e920030325038550007a5000c9151181270a01a0030000a44002d030350401400da0101240c40d41e40304503000303207a00180010b0310042048000e110784500360b4409054071103100d032108c0900603d640101d55003400a011440003070941071007401c1c4800c030080a62034052459090200071005008100070b41811710048918903211600d45100740300c50107401d540d07040000011132001483d001114090721160368414001032091203244401710089400e5820400e0301680303680c0703825019002d500180c1d180402c0c80800b65082c0410010036640400b000da0340c916850b075400d8030a4030001000d0741c6c4405d4640c4200014007444074540346540c11a4081d50407100d5030b6060b11000e4580d03902c00d800844002c44c01000402c0399000d01d04a12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 32797568 1250 32796318 32796331
    0xc0308030405010f0b0604140301060e09012007120c03021c02100b0a0e0604091403070c090b01081006080711190210050304030512040f0605090d0e04060501020c040c05091009080105 80
    0x5e00c490742003180040e0346805079000301d040e12140710b4002502139400358421070041000c40d200c0b588929010107000c0c000e00019882c1402c0c3e8070818a440b00d04050f0b08102c3d60165400344403501d1180c0120402c58180300034000450941c8590080c120300c100c0d0440b289581200c99a0080107981e1688141c0400d441402501d00d000e804000c506010300e01c0c0e25040c19610510680b07000030020385905007011021800508001240000607441c8280501c600c9020306480e0a04014401ea070400801140c40b800101c9001c058644440014009688114403160f00083c01d481c0401044003d01000390405103041040c81d071348498441c6440c210f042243c00c3c0514244207090203820351800d910302500c00d1246100e950b850105600000d020040801d04641c146500000100180d103403032001c0c5a0303504884180301000c00d03480e6500c03041a01d810300440c0240c5206a024000300c031a00414400031300010781c840030500c00300380070004154582c2d49020f00002d210381d403801c042d40d04d400166421108080d00d072 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 32798818 1250 32797568 32797571
    0xa05030703050601150201020912030901020c0901180c0201110a080412050a02030a0516061406130605060703031104092f161b03060c0504030b060a05090c03040309030c0308030405010f 81
    0xc00120b20701240761411035101c0c800200700c2d1400401d00700e0081c840c0d04551a8001ea81100c404428070300040501071a000c01c1e0200c40e0451500310070882c03102424030900f50b84c1401c680007289118419005400016014000819175441404104c090307504201e000c000018500d108010030b0006111030940c1c03441c02c2d814014038001c9002c00c025202d10415a4074420b0240002d02401090048005641015000b050400c0848400540f01d418804203a692034859400010b503000d00d10300b40d1040c00e00f1148000d00442c40c1c400315a4060f0301070212548428042d420600c000142e4402a01520500a0ba2704490140807100003100290400d1048e00b5120405d9041c407900c1850841d48860025003604015800c5280e4202c2070141c02604107030b0001050f481c20000041010764215002d081a00e10420900c07076581d80f00400d2000c10762107841a994803022480105014008000c010768000d4064078002c400982c90b41c4035000e0200719540b0071107504000008000a0010a226001460020000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 32800068 1250 32798818 32798833
    0x3060204080307170310030210020309062106040e07060309140f01021c05011203050304081308011d0f0d051b0307210206040302060f07030e100b0103050730060506030f01050a0503 79
    0x52495015086e0b00009008980894812880314020010f99160440040429a96034105450000070400008074a810071b030101000c01c02900d4540103c100c1d240400000340081864000d04401400f9180400d42d024007203071501001c2000f080c04100901040e100015980b014000401d890802c0455002100d0301c2c94600140940e82c4c066910100080c0c1501c1c1c155201d46903400d0456040c865900c801b00551082c020010301c2d808190002d4100210803888130340c420078070220f03107610f604500e440000c89070052440d9200807030185015011420b001c600f403202e902c1d0072000d1507217580c2c071041055484128103003240b016207000e14508002c0384001c1c0302400b51824241d0300030b941c1c0d000c090000b010019915001402d028401e50044034480c0b4550115000007005c105503600400c080301070b450000f0704140004800328019603801c030210140184d00c074501d894a0740d0410040e00c81d103180c2203440c0d0719000300141541c1c44c4030146008420210344a025945000708000c01201a07a201d10700a800004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 32801318 1250 32800068 32800081
    0x70f090e06010f12140f0601030212010513020702030f0309041104080628140f01080309090a02070f1a0a0e0705210c09010e01030501050c090607120306030602040803071703 76
    0x140180c0000007070800303011007050201c0a4808103401d40c1090032030303850200c00d151012150301c4014000c0d4003100d06c1005a4403514011800da2182007006003424141c40010845410b00b14082d9414061811006040900d0b990001c0d00303100c0c444c0c11514091b44041820406413900d4803410b145210900881481c0c43d252a0003191140001091040885181c11311500400007046140c940002c241004022410409512510901e010390307000920703103508000402c0075000003040f903107a004001d10007c0315680e841c9900b4082e500020381100c803218901545000982070016000b03a50303c0f800c4110000307140c460000400c0707490040101300d06500000003040b094642210115002d1040c480b030100301e48801000c5407a04410540a94001102800020320500c0c40242c041c16a407042000f8080c0380c07585d400585103402400441c41c0e2044042002c2c100003039985440c02a181c215007008100d8507584d80f51201284c0199101c168640c100080b00c00070040c000310103210180b0320281c0d0909605002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 32802568 1250 32801318 32801339
    0x11701060518040201030f06060c110306090601150c150905010f0b100509060f040e061206010f091d010903020d020d08010b040504091509060603031e080a02030709030812070f09 78
    0xc180d0030024990b29004034080d64882d0b0001c288020b45008140401c558400e030040c00014154400d648414034031104142d10700c0e0201d4254081c812443c0100496400d0049212840c900c030000c42040c0309090000c0030004152410076032880300b28074000510200701f410500d080d56980340911003101d203868401b81590791580b280907031403a10f038644036031282a0b52001c40c1c3c1503c034001450740c29110105000600d00c00301016184a0141515800030003400f13208403d65848081c001c540d2809407000051280c40c071039611401e40814008013402d000e00c030082c1e4060850f52504019001600172018201c90709404010040b0b80102510b4444060741c509884000d0030701a0340206ca21540c0c540210906100c030180c0b000c0880803031800c08100e00c0ca220320345100249442d100072408112131080d1a10303441d1105500f084410740d56147e8104607901c07114400d0003035200074000410f005902c1d001201003500c140107803003000c00c19601c130002c41c10104005090b0034a500400c0c400c00640d0902480240040d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 32803818 1250 32802568 32802589
    0x90d0e180a0e010204050d0602070c08030307050703050a091706091b0109053709060603061202010c0501180c030b090606010c030c29040b0903130611031207080117010605 75
    0xe00c070001518581e40421034068070480c2e10565020800c07240c0c14080c8040c1d5802002910301c10142e801d01d01c0ea0782d03000b1540340d000442d1080c0c00709074140000000300380100000d1000b60075601c0c024500790b0301c90031694a92508210707800301a034020b038200088000100702d001301003d01e01107003440c80c190038070009044035600e000d101c3c091296103450984a6410074581410802d007048a1000d105104400c0c4039074404a20811031991b04103800007480d10302900c20030781904c0c44000301d005c038400300760010b6844040c1490200c0c3c50f90750b20f0819041c104208014040186c1c441c4451a049601c5d40c1070143d0542406821000c91b42c0100d0184250360380c11190001d40c40b941800c0004a100c86800c01d202040b6941c0d4001c4c80780c1004d40310209078118402a0b103842a8801c0c003065040f5120303c210700b83d0760b000e500540824524003070404c0c02101e028103014207160890340c0440b4074010003079079251324605041d01c2000100d002da10060151070510711512855402c0c01c03001700b181a285c040016100c018 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 32805068 1250 32803818 32803831
    0x1801030216080927070e04060501080601050702130513150b010203041712030109060611010501030305030c0d11070308070912030203190e040c020606010207090603050303060108091005090d0e18 85
    0x40000f02c928158071071103005089406600d0301c90344503015031501108000b5084030344d0300c009010880c404c0c0040c9030a00c40d502c03e4030b0b01a900d0040c00d0340c2c1c502c0151000d0b800000241c2c1c2c0070f09d20b1130540c10a003001b130050030b2041a034013014400c80211880c1100960f9102c52a01241c0760414045541e5070b64000262021585040303d228a40070983c45020f09103e101549000c52080000001c9070300001030700300c407085420a5842920f02010510894203d58003800024006803080020403200b078400000b0f011f0f070168085000403100d0180c0f03004a0540d000900440119542c4020400d000f43c002e030001e4014061a03140e4a000740c09580c0094480c803820021a41d04c0e103c2c04000344180e0300c14480645200405402005a5520400041c0d80c5010441d8140e00520800e06c02041e181100e000750021039900600460540e22102d0040d202c4c1071009020f0a07080c41340345156401c0d261700e4042d240c0104d102502030008401c1206008150762000001c0601490301c0583e0b00070644000700030242d0160 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 32806318 1250 32805068 32805083
    0x303160f08040e040305070210030203060f060a1701030c051008011202010c06110a020a110a03031b051906061a12040609021f170a09150908120108031801030216 71
    0x1285090001d9004a40055460040c401d041008241e0814018a1031600889a03021603c49584045060344011540076820051501c240034840c2086405421140101d040c5a18218203104540341c0d99482684243c40d044500c8030100080d0900042100c41428149803540701581440d40324070244c5500c2c4c6000341000200414401030001036800341c442103070f02072000c550718440306900070765500841c201610319800806020031140791030004103080f203a0503100c0b00e443c08020700862140c004440d006843e107000d41400580000f05440143c1101031240d0fa00050f40b50504000c1980d1030440c12408411040411a6141f03841c9404030b0240e01c10703070100d00420a80300b1480855694542e001302c03114080c5280c401c20417441e8001235000544040d0f01200040ea079100306a400c240c42410b240500059039044004082a545805c001d00c4107016219062428064004405d200341c0c00741d0008445070404075143c40140c2c6006030744503907201d00346815410032000a101c4602525400e20061032403 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 32807568 1250 32806318 32806343
    0x3050a11010603020901060e0f0306150112021201030507090b0901030221010b03030310031419030f02030c100203040b0a0b0306060f010c02030303070c020108090601153006050f030316 81
    0x30502508010060755000e06a246556035401002d8886000011598840d180c01c000f040700c181000944039100702401146074140505040054526a0042000104240e000c02c210070742d0b0500661000e000b58481c600418070149000c03e11800c680030001c01e5489692000c00410150352203864860342e500030303024440e0041800070020380c0144811801c05070180008002c01402c03810210800c0f00300c9000d14205489017882005241d1070301c0007000010f0f04817240720568004240f107400c01604010320382c01101c0c13800311580002d61410044503040d202040c0c00004000401508050841d0800d81690041c001162441c00198841c0c2d00181f180d801880c0406c0003445c16071182810181241e0003809591380e81c180140c00038407031600f90900760b010610100200f065400001034150407103810f41c40b00300f9030449020045848020200041441c42c1d1020183e4101c03c0d00d24101103e40381072480700182d07031480e050034000100c01e0740b50424400d4005000032558035040049038014183e002c040030860 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 32808818 1250 32807568 32807597
    0x70302040209031c18050402071505180a050304140f01090b0c010b040f050a060501050307020c090403051c050702160807030b130b0108060601080a0c170601050418021b03040303050a 80
    0xb014018619107a00c0703013406420052407608140609a0f120b01c0560341d018058403682440184c1c400c0c45001003070054100005c0e900702e000ca50102e500b00005001d210742c840c284000c000c0c549120201d090714030741c000160400c200307040394101090318441a107000c5220411800080c111006030b20904030400030001e1034007500c0700290301400001200500801001c90b041a0300e43c000c01e01211444201071528402280560140c010390b807107100641e0040685a4481052102d0741030007070411024040c0502c41c41c1e00c49103048503100c003071204c0c0030b200182e076145c1484000c0c5010380c86000c501c84400005002e1041c00400b003110410380c3d400400300405603d401c01c6020162801c00405006883c40c3c1001107501480442c240d03000d06401d913240440c179141c1008600c02c6803009070042001c1a039042c8100d849800758907003145e02002c141001070404d9941e4081450b010459000300307884950008004041da4101242c5441100e50b80009508150560790041c0851040305001030500c800b0808003004c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 32810068 1250 32808818 32808823
    0x4080c0606010f021f0e1902150f030408130506070b09060106050306130b0604120507061404050f0d02012a05061f18090503040605091f02030405061305040c050912030c07030204020903 81
    0x660700c080d0100e85503e1402c0503030302001c40b121f0b00103d214400c50095040c03021050816101c182103e015070a2445d1156580c1d070f40075601003000f80501c4000000001841d55440b030151280c94080c0506125624042c04c0f843e041c240140c11202c00e1040038824480c00340c85d52900340d0000303641c1c1c150005801d480c7c0e900180c0b070360041e42d02c00c0160341d14010310082007007404030b400001c0758055110519069110003c0082c0c0740954042c0980194915500341420300d480c0350022807150060404544001a0581140c100c2503810070b210815020740c0401c01c1007050800060364026110100c1c08007a0780c0303182d0001340410702d0b44a140c1c402068101c601303190607826400108510b5008007145d0395603540c1e103030141c40c07034020b8061148906410f280f02c0c84511440d882401004025901a610700341c10101000000e8100d0b01c3c3c4050b5000405402103000d4655114581440d001a00c03442c5d2104d01410400c402c040720200350040781d4005008000310356100042843c1940c0d4100c0d40542c0320300d0064046071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 32811318 1250 32810068 32810081
    0x602061f03050d03090510050403120f0f1104061106040f170c030304110901050609091605070203060117010b01020a050a11040906020a03060906090207110603040203030405030604080c0606010f021f 87
    0x2c0050245120040050b900b61388025a81842203066134182000705000c002146c5080390f0280205810503901c580039919688508010079aa100c0046c03210000c84007281102e00e195850003280b0000181484002e80100300103201141c0d000040041e49815602c3c1200300710b01036002030413010171090606074403250000365a052109c850459480b40327450304180c44410240c6120718080c0302c00c44004603603420094201c0c1e5964401800c000119191000907085e8036456502950801009104100059034103000c03445c002c06042442183c0790300f621004a0840748418030450542d03204c80e03207000010798082018060117404c5a803030442c0e9101c0a0115019280c0110f00400c1284002906a00990954041410b40d42c60b402c04105141c0c0f98a040380892007040406445044549580200c500d06031000b50361191000c0d050320300381369941010900d0504180c80c03c075a59940072078401941030080100981c000c0b000d180054202c0403400c8040e450300f1100310280380c3c45144c28402c1b182400c5d26007120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 32812568 1250 32811318 32811323
    0x70f0f050a03030203060f1002060414030f0d050a0605011110020904090807061b031104090515120307150902060904020705070509150117010509180a0804032103060602061f03 77
    0x4924025040c90b00034004c0d8012a0b03110f110782140b1001c0344007420055290b1601c6c6585c0d030000c00950b11162100302d001492480750608501c4100b04e0515169650030103818400e0040700d000c40c3e28103050a9510585a050b00724504120401c0066a6080d400152020000e0400f81005994a0031000880e000d000705400280002100082c14803c111556004000b0780102e0200c00d030100b024508110150352056034803401201c0280402c1c001600503501085d04850a40d600880c68000c503004500d100022a9a030700540d000821a001031001c1940da00e18641040c40c820803401c4420f5000440708d0040c050500d00840d40840c044040020400260024240041500605281c030040e486e4081d01e00402280c0021815a0030008004805a00340e060b604000c0034500030380e40c0c441d40d401d0380c15100f1804c10105c0c440c020f0b80c1004039540f0030060021318000c0303121030758015402d021983d03a4103907128080304261420f04100a4103034007098141c0c200d58040c1140b00c226800c144a05090305458001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 32813818 1250 32812568 32812573
    0xf04060809012d1d061b070f1103070602030a05030c0a0c0204050c0918090d0f02070b04060507020406050303090a09020904020c010f0b040501150801090207080408160e06060f070f0f05 81
    0x148580c142c800f0712104558602e00003d006107040b100c64041c04918403000b40700315034850804109420f1844082c20100e94000e00b22604214141e2100091304039500310076603c0c40a030216060540c01d05101d02409410a0300065180444a10005200d484020504c03050a000445d820800358841c018001700503400801c00e01c281e0030076001c00c80da15804400054855040912681c5141c0000c1d404540328400d01409020039810611042e200d103010000480214043c00f0804141e0061160242c8094000c5546003900c03845607206020440b9050b0304180e10940c400d20900e407030b940d1011800402d4a4082c0710158071145668049000ba00405041c0e1200d035003030040c000c036541a44d070300110780b0410881c3c0610869aa442413600c0c101c040b01240000903c00070010301c843e98140d001803040038802d0305070500c0c00c0d41c0c4000c524244800c100e07907250030110800040040802d50000705400600844511380f62900c016a02d640d14070552800070a0200880020410300c440c0c1d440d40032509801109 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 32815068 1250 32813818 32813861
    0xb0a0503040b0712090b06040c09080705060a03020f1306170108060a111b0c040f0606120e0c0909032101080703030c0606050306010b0d050108010605010c0308180f1f020f0406080901 80
    0x14001d4407000111407d0380601d00d00340846841078441d480c00422904514007900d051401c0001340512540030501c0b81003496020050105030350340c0c2c00000c1c22000280101200d80900b4440300420744071000700c40100300350304500140032501d004140c2d2500800d136100002017640b50751030b1a580304c0c020345210f64070301007000d0320800d154803000c15890300d80282107508202c244003141511045a8040c003690340020310090200b40c1042081e1b12440082c0ca80d14101c40c81815940006501e6006c2125a030140707030800b051001000003c0705000c1290a40714060102660420f40a90780d210707500e10000d010032500c150701100f48405503001a000d0304000d41611465071f102c1e560052240c0c0301d00c048092041c682000001c03d04c1040c030400c420350b641603441c81c1001040b52002c4400750700182c160640b0200840344120181402c00c000301118000381c020f490900c80000025854a03c12080f190b4061300400c0203c242c280c0d95407c8909584032410985000e489404186004000c4109040c240605088 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 32816318 1250 32815068 32815073
    0x30a090224040f050301090507050d030912080405030d0804020f0f0d06060b0a120605010e060c1501080105090d09030c0306020703020f030c0307020901050f0a0e06040b130b010206010b0a0503040b071209 89
    0xd00600a44003540b031100280f40d44c42040c5400c0758090100070340160090b9000303220760724004104e00c00c002c0c02890a0419562100f003c400144550341017241c1d01400010f08100c6030905000f66524122a03042c02691481e01c0d80101d01d41d110300950041c800c511001d003e00d456a030f800c0e183d1840036003260781000440c0d2160302c0319041358007507074603c000715000c011001c0000449000d407130251841a0356001c1d0071943c41d41401340e290002600b00c1a5401b13400c420140610380747d0b50442c001c0c01800b00205a901340091518208100c1b01170003010445108400d1010901e407000c00d4084075400000146e0716201414100d00f014041520300000340400141e418034400b0020141010900131501c19115903031310000c0003455102c551800d604034145440c200b00d0440d5001c410350740120040d0001c51224990710000d16102100200000784641c0c504440c06035507410810f07030703000d08a0842190300d00740700b88402a020707002c001d0005003002e04400001e40c0721031141040c044808150b0f4020f0000ea2031a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 32817568 1250 32816318 32816389
    0xf0c120a1b12120248030d020706060909050703060b1804080a050415090f06080f0402191a0c0c010c0302150402010e090a02030a110306010c060b0d170c0105010504050c030a0902 78
    0x1d00340403e03481c00100c0c2c1d5041d405d45d25403290001700c43c0340c00542c500341e810402c040c080c2d00170050036900e06554000c0064001c0e6280503401540d4400ca000e085040d00710718180080b500f124812500a444140c0f0004030b0080810325141c0094008203041c3d1102d10140342110b40b44540d4000f40340360340132616044001500404920142c4603201c1c00c03c1d0929480f8030f000c84810608940c00080c81c060400402c0c02b50070b1003960f103289244403150311101d081d110012004085807100004101e80d6000650210305542807001a90700c0c0024a0302040c840280d490007562520900055502048050081802c6a014006034944240050106402440d0002c1030710b000350811600302c3c4103d03007090000d11403150401c04a07407107540143c4480c010410603844400080110042c559000840d00c0104404515001500441c203001034031001c3d990340d0461212400e654041c4c0c4210b0081e0704020500980511000c280c1394800a1442c001510040500000b07000d0f031440881c140d502ca140da0645546120741 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 32818818 1250 32817568 32817637
    0x705030a0212091008060a0e0c0c010b0405070c080d060e010306050405150108061623041502010204030f080c0a0b0411010f0c08040306020f0c120a1b121202 69
    0x5a001d40341d90041040c0d11140b20300c64100c841d40e01000c0080a590401d000341c2071a900900050300114929885400790403080e08140e805814125002c107020107052024061a50300c00c43c180c80c28050750500d0003000d0000d001c0c10700010081035000c10030000100e07155021030300520310050410b46c156924201000100f03001d8070240d485002c2da00f41c040d52141c6000c00c8904071607006c0000d00c020351f240400041c0c02a11140300604000b80c0c95103194190103942101405180e80715402a40c40349007005111030b0402e00c80100c800d5900503c020004940d1005410024940011120759101c0d00040c2e41802e0180c22000103160f070030302c031050009002d0600380280001c1d2007030300d500e103042d0002c410695114488280040030107008100910000700aa005000a42c240000282c1003c2c1c80380304290030710724030940b8821032140c0415004442984020281920740991244031440b4480380c90350101200b50301309410078004400c403181c481c440030364112840b420700400c408100c0b1802a1041004091 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 32820068 1250 32818818 32818837
    0x60c0409050f061003020c010603020301090b0603011b0e060a0507050604031205070c020603060f0d02060309060f0a0e032b020c0f0705030c010c0b06010c02040603030509040501150c02091506070503 87
    0x50700d000508481d4180307000c0c6000d020018a00b40f0303c5028030904130080e6220003001d006035520f9400c00001a1802d0107102d035803500c2040751020901c0c015007030601712071041c0c011341c01c50101c2005540c1d1454102e5800c04060b141902c1c10795941480c401c5c150703031a2040c004014903511600042100740366029580521110206006000d10786030107000b00c66070042881c0c080d41c005010400324016142a198186d0825006000c0c10001003041e0000341c600e030070403034100425400c5003080041409210311207540c01910203000700b00a06410203c0e554a000b000c03150354402c40c10000c0400b800c0b86114000b905961040740c2590746014078401e03da00c56040b02207011441c8910000400e01c0e01c1d0101d2201440c000681d14030108c0d050a071546c900e540b0025004a05010002d007803500540c90300d0160401071070080e12025516103c040501c4100c85e0145d02041c04e0085683c0300701c03c2c0b16404540d00311038540480c3e003204d140c0c583c5120410480008040d1581c06080050f005040207004009890f4080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 32821318 1250 32820068 32820071
    0x307030b0f10060801060f0810030f080d0f110702040207110312090909031e0711090406090201022415010203040909030c0201090b25061401030318050d0b0f0403050c060c0409 77
    0x242c3d0340d02e0035110a0303000e010764404074034140510011988104034055203c04d0303151200f0304e041c0d0b598486000c0c0c048000301c1601d502c0000190310541040034007a000080e264a0020495070b00302c030301e01d505c8500600500034866a00000d190b010720a400108418941d4014240c4880d01c203c140c4241003540908500d07801021080c002030401040801541c200041e0340f0070103c47e502c003409015402d940212400c6561102c1119080680c0d29a83d040070300c1644103400000e0700c0356680c000680342842c41000c0c906420308204c205000365560104c1c50341c11217201c9040312240e403400c400503401d500a54001540307181c980400e610926501c90038030b04010b4001c0e00d50000c0151a810702d0080c3d0722901d81040302d40c4800f560545600b46090822070f004134002c00001a401c031402c00d1411200000b80c0c010342c0015044140030f0030f1041c0c0c424a50380208001c0b51040700b00300c5031381e8600e09500c0004204010300c04008000a041c0360003542250415a01401950350608c0c1000058280303812500500008a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 32822568 1250 32821318 32821351
    0xc120606050408072411121206040501091a0108060f030f1c0804031d06040306091101031107030905151201150806060405030c0f13020403050615101407020307030b0f 73
    0x22405c402c0042c07600d14032000c2500d001410781d141a04e480b04103a42180c0144502c0e10600c9a600340304024110000070110070503d54209201080301b55001a00028801c0f0700d054202d48410b0003200340440f5242d4207080041c001d941e0f02c00010403650390f961501d81c03d806400710700c604103440400c26030b5402d0002849504c21441400d41220814411100100070a800c0b03948542000e144002d82440c0b9400100322030b1506807030366540300554100350000c541900d416400d081807580c1600841001e0301440ca1024180b02094500410f201c902d442403e00503082840b05040a541640403120540360b085c41b404241c0d65108655100410311903c80300000b8404804248645408000c50f0100c3e20010300411707820b0301a41c2002001c1c0840079405600819843e9005400803181c0003030801180210003030b00c414600200c4c11700300f41003c0303500680300d1007800c01d80100b01600500c600800390040c0a080741c40d000c0c2c61012903c0c180c2e094002501940c0f0407000c0121866100503414441c280480400c2101e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 32823818 1250 32822568 32822579
    0x5060406060c170304150c0c050c040203070905060c0304030215070506070503040b070315093b0706082d16090b0d0c20030a08090a020307090c12060605040807 70
    0x1484100500285441c2000c01610f100b80380b0710004d550420f0052482c540b8030f1004044038004c0f1a19140030002255005115030148901401150070402c001c6d42c0540c61490904401414003040c2d0203014424400415030255a04041094901456001c0d20301501d00d107003022107025030f42051800310b40ca4415070000404040c4500c00b40d0f8003030307a402400b0748415125192b054010f040c5449040486007080000055141a0342c0181c00303020707010480100d803505200ca00714441c0303c004a0115500c04104a0800c0740c21000217280d402c6412a1a20583c2503c4d005d1012426403004403214581d041c104c8540000d0713005100f001030050080118000328299980001c0d59158403e01c144850300c1d50501100c044417071540c001c007019030b040e850034283c5000000890700300d20710003103a981c190394400304503140346c3d40d040000709401401d20f8006040c0c09074141d000075030b103607054041d41c80d0140d200c01c0c09900c47d0340210840422040d00d00d1041c440c1c142c403620020f0082e0441d2140a51501c1a403900158 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 32825068 1250 32823818 32823827
    0x306050f040c06030c120902040912050a120e07051909050406021306020604020904120c06020d0b210304030303020a03110c0c09070e0a032303040b04090609180204050a0608100506040606 82
    0x17440701c030700e4640e6511001802c0e6500001e000301c2c0c1e426a04546c0312405d000000e5003140a002c812600307074a566450f54100c4800030700c8801e99802030680e103450041004024100081c0e018101c503030403181048401c584d41d620b00040740305a801a400281044244400c0004580141040c042c0141c0c080d45002c1e80d03544100c0c1c0d5440c050b100650440b090002041c04a0f046801c207810000090800b80d040c224240d980c241268080311800f2013103592106206603520b0150200060b420145600110304601c4003800c1e5224445c910008040c10742c0004c1550205000703801c00c10124070422803c5403244880a01542c80e0900400031781e20852000d400604038500551003d0b440f18006819544454110b2b601c46c9048a443c0380351014003c0c00c207440510301002000148080c1c0b448503501611145820850029601683c1004000c9070810040f001c8904050780d03519800e40d0122008262a103d1050100040a490300110b910b13000b2f4140304180300300350f90130003401010f041c1d5040106540c0e4000468 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 32826318 1250 32825068 32825081
    0x8010204061b0f0b060609060a0201020909010b030105030304060e0a15032003100e182a0306150f0a090f23010b1204050c09040308010302041a0f04020703020102040306050f040c0603 80
    0x10700858075060200c0c0422413080c0059401400a0b0410703161120074000284c0d160803264600005030b40026503492a800e00314151801011000001d0341554100f100082d200d0207a8003400e0200b0105c08401102c0b541d48011080091920a5070040c01080141005000d85221481c4404000a005071500781c1c102540441c0c0c8100382030702c4d81c080c550b400c00d585801d00e2100509042800c90384c600405101500501c0320f089141c1c10135103501e104403030311130f00c104034020141c1100c1d1180e041503040042da060030340c1030907e243c2000c031011012030a50500184407910300f0f8000500309450310013810001e001030740c044100e0001c1d1904401021079102a041b80c611030134054801d81d09401d102000d0b0b4000154401074110f441403043d2440140c488001c035001c01d800711025030000e4114401001941841d10402c030b000c140031000c1d88821080080410051021041043c1c0200e0380043c911061610030340c150f0340910b92120050086040030010341d01007940c15201626000b04251000440030b000e44140d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 32827568 1250 32826318 32826323
    0x30605150d0c050d02150301080105040b1302030604060b0d0501060b0405131503121e0206160c05070b03090a140304061710050d02060702040c0c060501080f0309040507031508010204061b 82
    0x1c032100c0f424a0140b00780381c0038221040b80c01c0008081542e800b8079040c40694080c140f0b1000019891070301d8100101c210071702804004000156541c18805a10042a45a441500031201243e059150310100f96140b0124101070455440d00c0804502c265961008204941d02200d4501324849034960070404c641c00c50101c10040c820303190003003002031540051442840c0c001e00304000c5040c8828410b58940c602450311034016040601000104010102d4040c00608245488280254244d44165550031903000b00382c1150404030000b070207003000b006070b01c881c90b500040561280c401e640b0f9441e5281c00c00d0145102259107004c1030304010030046000c40c81000702c0360301901914580001e00c58070016034a4240d8004030108020030250f1124091030b400364016a444541c0c103106e90030401d0840300f044e00b01420075080a070213100c03c0f480010a95900103801c441c0012a91144a07069000300076164503d502c45140060000e1541c2041d40034204030307415621940c9140d10888000e250001c543c8000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 32828818 1250 32827568 32827583
    0x20c030f0a0b09010b15210103051902060c03130e090102131703040905040b0f060f0604050f04060302030f1e010203132306012601090308060603040606030c030605150d 74
    0x210210b00d80c000119044182c1000000c0c5c1500f044010550504502c0c0001004080024019900389540c2a020b62540e075504100c1c031181d4107568816441c1e9481e40304402c105070245a1403010341d80c0700400c450384540c2100450f50740f00100020f82c44201d10310310825084000003800160b41d01811700072074151400010f085098642440719101c0d10003104c0c0400c1070b040c40b00348000f2403188545e105042c0110f00451441120b032801145a2114000041143e4014071280c1958409900d0b45c1082e501a41c408070344131485811200007007801484198070281d031512174060115005c01c40890035810304070100e064402d032680410f2143d03003070340300541d00784e0111203900728a480070502600303000305505c1c000003c04c030703450403c0c5030f1180c9072040070b0300b2075000b2400340c0c4100d080303c0710401c13020072080000c0002800100c00b9600c0c05008484001e00d001c0c051400003000408001d495407081b00a5a88240085609512410680c0c004c0108503886840c80e03500391a17000303491600b1032542002c154030846 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 32830068 1250 32828818 32828833
    0x30c0d020a0e1b07031e020a050303010501030f020d050f011e0602060c07080c0d120f110304020d15020a0503070e0f130c0318050307020307050604031104021c0c0f020c030f 76
    0x8051118580244102c08180d0658415a4444001e8004268080c041c4d604d443c2e01035140e00c00d00151b54110303689402554007008003203001410120035641102d4003402c00041c2c1c0611091b0002c040c0c0708051001c0b00e007600d85010890f2021a00304024141d502040c01d42c009012914510b11010040d4003451025900c440d00180c40300c0c0201009002c868469061b0300c0c200000c41403214500b21a8031205404034080f003803039000c44021403180c140056038600c8240300c41c2e5030301e0310002458440500003a00407007481034000c0070b01100c903a030700303000300c3c140703c011075603515500001400c0d60804d94400d40019130440850115140c8501c0e144900d0030014840108070000540c41402030000b8100e00080c9512070940d081c110140014402d0058020710103107688402a01c109400c1850b40e4010500c0b8a9060100b48041425128042c43c0c4640542e001070fa40c00c0001d240c0d044040e0168181918141040a41140145e002e949003205410030b03000c441e412600e200801d03031036800344c5100c0d40c00c641c040c05 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 32831318 1250 32830068 32830079
    0x10507081b03011802090402070f03020c04020403080d0e0f060405030304020103150503060a1a15070204050a022701020304091a0a090c14131203050a0e04050408041202031218030c0d020a 82
    0x725510a031244c006001842d0209600108044c0c1c0c0040d40d054402c0c84004503510709154051041d0b40034817008580461030b107800c543e22944140034400f007444034503030b56840c070b5a001d00c81007204a102100f5007088a41070f141c0b51600680da43e00440d0704038000f9040034002140201041180002d4030b000a01904d880d9130703100703000710043c0021440701c07075100180300c0e8080c4903031900340074000180604000b0603607400050040c04203075100030304000b05851042003002844002f00002803c4442000746600300d5402d9680102d145000d035410000700685000340440401c601c1004200300c0322010b44107603184580d2107104800f102c1040c0f900501150165420402e4036100000078102c1c0441a140201c1003030b1240031201e452400d000c001c82c085000041c800c0d1149401c6610341200c0482103c0c180040d02d8140c0d1031007018050b034460280d805030120800c0c011036406009070361080c1e0340140d046440300c203d0002c080d50386402da20720328060300a40080807507074200124114a0540c0250000c03c5192502 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 32832568 1250 32831318 32831339
    0x20a0215031b03010b07030806030705031903050f030c090f0d0b0a0209130f09050f0a050d030507020309030a05010c03060603090b0f0403120f1b0206100605180a08010507081b0301 79
    0x10007510140141da0540038010070480b02075800317400c3c0d180030f858403403c403031901400c0414050030951282e40300d154100140c0e42c00045182003010f5280c00003007210341525040d521801000f50602c0e8801003c402c21007015a40c8001d04000401100c3d014051004203040c00020b619185000d882c04001c40f0000e0108100341d0014010001d000d485004281c0b00311117100111401c3c41c03c10030388280c40340c15034000d01c402002104130f50351440300941240501075882e00e603250b4220401c4001c0c15144d01c00500382900070300c10341c1c8500001034140c81e4421201e143c80c60003022a4200507020926040010407422310070311425920740d5000d00da51103540c41c0c8812800324844018000c03420080034000903a010340c03080c0240ca401454122020480440d00301c0c4440c880954015400c0440d0700c030000300040000824500001c48445e030600b0750b9940307101004040250820484070b50081108070000411220540c000c13482441c0c3d6035034440090700c61442030701001c008024207140d0103000b40018000000704 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 32833818 1250 32832568 32832571
    0x607260601030e16080102030403080903040b04030303050a0914060103050f07061209060905100203040b060108090d03050711070609081605030703080a02011d010209010905060901090905060609090f16020a021503 93
    0x9000c11104c02c0d421100000c1c03003c04080d0031190499401005000801d90801ca5071500501d8180145013028144040c2c2c0c0c1c0c07107008601c40a0200354840c000700e00a02050380c00040541c0c1c220035030040700da86100c4000c0c2c3d10034080c030080314644104036039115049408580881568020b656034110306050300000b6000d00030004083c1c813580e545540603c0080d0040040c020018410203015881c0c1c981400d260740c01030350003040281489110000c204a0f5400031030034202140d032034180080d076500c40c00400c60304d02500001111041c4194000400e0343c0360003034846021200d04904a03181511501e900c400103298912035250560700504048c400501050080c11000c9114400011103c4119544100a162007183e21005941c0055103041c1d0b541e0040c10782c0058001a20801c0c0380030f43e0000001d1180c00b20348100340b9091344d10404280e8543e2247d007103681403203000300580381034107102c440c0710b2506005541d00b0403640001030f40b40c42054008550943c044c1d80041034400341040342d020a048940c070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 32835068 1250 32833818 32833841
    0x21030b0a17010e0f16080604080304080d0b0901060c0203070906080a080f09060409020a0e0a030b060f0d02040c020321010f030b0c1605030c010606050304080a030209190602060726060103 82
    0x4840c0310200f00c42c01e080040000d00e1210354010700c4440f07030700300d0a600307030b540c0e1500a00c2183d04118100004145078070201da40244d8051541d66891160010b5440240390701041c50354070027440c000002e42140e100900040141c021002d4692090f5285a8541203445603c0f03a403910f500100285804142c60768050403083c0820340c0220310f0316540e1400031346540d206411034034120b903003c515902181ea0001c1600600c41050b141c0700b481c282540c607075640d03440d00204183d01c140c82104580d9403680314461082c1e00542c1c007400c184a0395250402c065140d41002e804400020200e5039410102e5588041146c100d85420942c02e05242c25500e54070032191000302000b000d003000b0801c00d00c402030301d4013442598500403800303551140204007080e400e41300d2590101c1c08001c010b03c180004502d50b041280d01a0b80705080069031601d418011030148800102014281c81007080002010781c0c02044240c0b10304104d54902d8501c1503c4c620041201410800000c0a041044000b4079a03500a5001700309504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 32836318 1250 32835068 32835071
    0xa0302060a1106070903030306080f0c24070c0314030f07020103020310030222060902091e190b0d050105010f0c060914030a0201060f06030902130b0f06040321030b0a1701 75
    0x901150389442c03c4001d446080003e101c0410800a0591600c241c4014050010140c12120b1741c2c10016691100c40040070ba2080b00740110800071050045d0031005103605080c0255101d502504013100008400d1000b640d02507030300715003000100303400300454143c080c4a101250900d6041c0d001100250402800c2d104614031001c000310260351080744620b015100f000c0e0f5004401c0c000740c0c071001941c2e1a9480f4803842030043c018000b4558451036050290300078560300c003600024170400242d07002804c1341d030350840742c1c0d003c1c01c04203070050008020b005000c1d082c0d8080c84240d0f0380e00d00454282e81c0b000038010000d079110803000002201030b00402e0f521ba01a0f05154a0840900070482c110f51228180c4d0000d40e41d0b610041202c2c144100c0e48100405031070501b045410504e40105040c20038130803801c000c0d00d90b40d201d059581e90300c400c0548a0700001800f0b0588a40e224581710041c001c14200000290040c49c5164414510901030307031000c00d0018140d81ca15501e00042a920903e25800819255 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 32837568 1250 32836318 32836337
    0x304140303092e060306020c0c0301200d0b0607050313060504030206090f01090b0309030a080603070b0f0c10060b030915010302031902010201020d090b0106080703050108070b0702010c02041a0418020a0302060a 92
    0x40c283c80c06004060b50098400690342e0401d03840c00c0d494000c4d018400760099061040c80070399404d11007542c00710303481121445c0d80d440203180741d140000d0000008281d4400710101d83c0c14280722000004e0208800c85200414015481700801d413840e010318400258414020040144113040141c4081c01045041c1004142c098070350203007043d16082103e0318000e47d80701240e58140c0d03540c0280f1082d0032040c03e03400b418400e81020401c0b03010344640c2e40340402c0484005407510002d00704021500041d80c40301c00c02c201a58484203500e81d42e0b030007a40d85911511551200c800b0100d030400001d41225030050040030340725150b4148032248071001c0c00076415558280100f440c1403001d80145044140306503400041581080c0000c0c04403080501044200352400f0010710403d0350000e048001d0303801c2d00da03480d500c40100e4030041b1034001003004000e4100d82002080000343d4030a00c0d0121040004440500c4800d544484c80d028001c00c400c000380d03112300c017010b0402c09402c110005144c40050b601d003580c150b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 32838818 1250 32837568 32837653
    0x20a0302070506010612060603061505210702100b09090d0305070509090c090a0605030412180506130911180f01030902030613031205010302010f08091c0203030414030309 75
    0x30030200b41d000c0e9001c500c00341c810600e00881b92007040302a100ca8141044401e0619400907240c0b80900c0d1000184500041c1c100c03a802107107022500e2100400014081502c0c6c02407009490f410182c851001590a10201c171043d0b140c10b24009108814070801050300a111140c110041d22000c0c12840c2844002c2000d0780980e207034558550712500703048034916a282d651800b072001a41140d805034040140c1801070000041c10300d0f03a040c0e0310b146103161200307602d450181801c04240441e0b02150380000001042c0794040001c034604c03003c40d80445020410020741c03084c210303110300c20380c11461402c0c0d4412664403160b260035045112442810b00d0300044540e1240c1c046460901d09460402c1c0d102c0c01030300b40070101a80500b215142d00c141842c00d10095256500290400c60745035842000d00c00c10b01c0004d107900d0001c100440000c0d003a1700612401c6000d10300c1c00380d00d135802a50b041e9107280082c24551b40d02c800c00402c60b401598010028950300704a000c13969004000310341c1e0000010540c500501c107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 32840068 1250 32838818 32838823
    0x201080a11210108010207020a0b090f060d0c110f0d180801090b04060506060f0703081305070909020f090108030319020c120a1d010504060e03010f0c020304030213020309030409020a03020705 84
    0x342c00d0505004220828200c044a0340e40001640300740301907801000100700580740e030320010085800200300301e034a803c01c2100080c7c500100780000382d000072000c5000200f1510300d4001c485200c025440359002c02c038414000c69161241880761818944c090070400324001e110302c01e000400d000782108045010340786c0d480982524101c040686e001c40c49001484140070484c8107060708084200d6640d0304c0c100100c003a0a015004615002c0c05020310361000035070300000c030380c07a1418681c2e100058800036620b56900e84010900c001c1c051b40141d8000d0a50944c41c240b0f03004060588046030015821a9600400000301e9821618072081d6507400b4041008201c4040080070580301007540319a851304e40c881c1c00181260b0120540b60401c903413410400c02241d13007090403a816a40b4514014244051410200e405803e603107550790807541c43c016010440e83d42c0440940181c0784201e8018003031034200000e810a1b80020750304400b941d0005c101c10051b4012a034018034410300303a414050f040041540781e039030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 32841318 1250 32840068 32840077
    0xe070c030905101106010909050c010c151e20030a0509070f03050102030105040e01090201080c0a031103010b07030806010c0b01060c020d050f0615180103060f0b091807060e010c0201080a11 83
    0x4020a43d01d02e54450544130900805015010f1881d0070441a442600c4840d501d0b40f200c981a414400303132408120520002069820030001d0300c23041804400300400d081c8480c07401c0c4c20b5000060b00c1c0380801c00916840710100c45462000c2c0d0340c10f01411030b01e407607400300c3c001c140c01b0300041c0c02c0d4071402000143c0784007041020001107000d4400140c607985090240410344003400600319042c0d2410038081d0050380c21003012504403246510380394440d04240310a50007490000412a03012101200004111320b4060080c1f40c0c4511907030720382d000ca07101c900055907480c1d5800710041881e4007100040c40614440c4030300c905840c0c0000c00c45805814281c03074450800410031202c1c01103800601c1000041c80101114204005d41540e03844001032681c044a060580103000040407507440740c42030141d2044a4002c606040b100608465070360034141a031514108220f03031003609a004a880004119006050001d814041a15160b211b410241d00441e240400204134480305903540841c1c201c07282540001d030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 32842568 1250 32841318 32841349
    0x60216152006060918150c25050705011407030c0501090b0f060a0506031501030b0301020708030f010611010507050a080601030f0c020a051c0905100e0306070819060e070c030905 78
    0x204200d00f0902c00740107a9003402008003111000c001d22000114500140580303422480c0b072001d01c1281c41c1d40849004d14455004d9004a01100b090055401c00f584640400614441c400301c2d202c0559038001034410005243c042c4074540341c103110350300109000d401c240034420700c29800011038070b030140e6a80e4030b04041070360895120a903200400c08203046c08007110000d0541121550305601e025404104544881d1889504050320b032020000c00362004d40648401d01d41c00304040344c032883c00e6440d10a6045e0244507080001d01c08641040344000180726060080c80783e40da8075403501d00200000e94080602030650380c1050354510b9000c584a41510618200400c02e6019001d05160340c02d1143c030b00340051a20300c3c000e240c1c2d203110740c100c0d94001d0313450001c42c1d0043c0c0e004004000303900415aa10501180d1164060103000100503141c1d900400307040c40303075652010b003640310304898645c0b908880090140d038800301a4000480d403500c3c01b0340581540705102e490480344054485002c68443c05d00c0c020b58 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 32843818 1250 32842568 32842573
    0x2070b070305090c0303091009090609020306100f09030206030618010b03071202040806071103070501020a0917031224040f0f0e0604050307060207080f130f0602161520 74
    0x14840e08035814041c8070b40141e0001d006000115600c400641c8a1140000c054815101d00c9a940403440c041d428480c028045414100074680d03540804601a600450343c140c460342c03500f260440440d0140e42602d0304080950b44054819081d41e09002d90366002800c002d5212641c29200420141425400d5020f0400045844c0e140d0900200151545e000f00b41424800c1b80140001d220312840065540c1d80320840c1c1c84c08010301d011a110050551090600240c503650001900c0806260840070840444000c0443c80e001d8980d00080340d512409a10480d02d210040640800d440c1249051100244007451290400c1480001d00113400c031002c64071600e040c240c0782d00280349102c01034414640c13001881405000360b89081d59a550f202d10400b10000d00d046d601080101c2031101c00400e50344036511080c4034035543c000c03d1514010307180040c42413841c0c20882d0600425294408070344005100c1c269010500001c0c24005490b5004011080790000c0020030404100c588840002d88078002405802 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 32845068 1250 32843818 32843821
    0x303020f0f0c0c04051012060c110708010b0a05040501060206070f09082e0501080a0b09070e0114031c02030a0e03030d020a051b011802060307110727090305040308070c0902070b 78
    0xd004c180d0b1002003030301e10300706108282041284802c0c159080c01a901100c0014100d006480c1078070300340d140f012412064401c010010802e004d0540c8201c0c030f42c04045500d000e10315525820001540e0b024001d210060708401c01050455000e01031402c1e070b01401c1c0c200090000e403190200d929082182c48140342a01c0c0e01c9134003080c0100181d550003120000d408040c42198181040d00e940c81c111600001c0c1180205c40c00150f10300420f0200030050a054804540c155039a143c66001d084400d40c1982d100c0c2c05107103a12005031030700d101c1c001b0a00401da00134606040d00307008141d030420441610a40c16010400510b0f40303500045c070007410050710359107910b521100d90b03011020003032240b0344255400c1e130316003108201300070024110419820750440d10107649a4582c07004a4014141c2a8030303181c0c0f0b01c40c50780e021954420009981001002101580782100840d42c940001e82d80c8141002d004164208010300c00304070380704000d04080c0d029083d00c020440d03407280c03010204d23486041d050b91035894180 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 32846318 1250 32845068 32845093
    0xa02060c012c150a020c100608060f0103020a0501121d011d030406050d0f0b0306010801050a0b09060604090c02070b16021003051015020f0102120105031501120303020f0f0c 76
    0x140040c81c0032102482c10300140e1401c0c00c8282d550364402c0480c81c442c50110000307124204190112441d0b80810402d451f903c0c0040744120700075000c1d901868800e401000c00113100040c400e1001030480317400a00040c0340300e141500549542982c1c030800711602d500c80d502c40456040e5800401212030005000058406000e40d900f40c114005820100c1950010002005001c3d4400280d4841050400700012070701910501702d4010402c22903400c0d014041d45000191204c2c041d403025102d9244a102400b01030602400c110003d6011140564054400d0005000b5a00590320209901d401401250750207900e40c510202e0507080307003034103c80490b03d201900045080130032410542c18400d0509000d281407003040e40500700f1303441c0106031107050741603003070340b04948208240030007030748240003c664415140c019200706c08400d002e01030091040314480e00e07070640840d2032681294a0700c0b803091242c903007e64085000e588000600c0700415020300034500358480c04801458140c541c0401040900f400341c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 32847568 1250 32846318 32846351
    0x2090d0f12050403260408010905060708010f03080f070507030b010305030d0606030c0206060f011b060203060a06020607081603090b01060f020c060f0d240b070c050d020f01110a02060c01 82
    0x541100704000c02440100002042005070000c0f181c1301500d090042c80c04805280f08070701032940b00410542c2421102c406020010968902034081d03540c940310641c0c2c0340d101c030b00030401c03080c0700080003820200805100312620341c01400e10b4034070a03070645410503520348070f80c01c1d9841c00380c10580302a00009040003002400d03200311802004c041c00d007840800d0a084020b07403101e00040013140140850b13124180709130700c00c404081c0b210030340c1000e0500d100d007a4280300c0f0003034004031005801900c42e11408602940002606072141041d655482115502d00c0c1c0f2000e0120100315402040c9070300c0342070020015030741c0a01e15001e00801d61311401400740380d460091034100e844400d01e004100420154a424528400302c07101981d42180125030380d1880f89080f04e48190741d8204040d1002d440d00040f681d0551039000b041658000c2c02003000280c1c0780e10421804d581220b60080d0b201c400d24400c0b1041d5409103040010408403407094844145031f64001c07646660100c0310040190759140c91484004203031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 32848818 1250 32847568 32847593
    0x180703081b06010f060806310f020304020d03140706181b0321020304080d02030702010809060c04030f02040b0904080405120c031203100f0f050108010501030b03100b0402090d0f 78
    0x2036a0040c802c9500d0502065000780b01da0240500b0840400700144860b101ca03810355034100c240e115101e11420182000c80c003c6200c0200300e02c0b1050420100c080500c649000752409550002d10b00035142180769810385410040c0410340c001c00130144181000300700d2178070403030b0703905561922141812199841d180d4080070b418548044281079010050021686007042040b100242207174902c460300c40400c06910314001c507400101d25105a03881c0301e40041c0e000c800707048218400e80725111181c90f126100d5466860840c0d1903114100b00780010004164510990080a070025200041c4442c40f1000714031182011a010348159000280400090811403d40303250862171710b0150a900016200184d1500103072040140007000c080b0106000000c155001d000a01524148400f0940d440300100440300380e0f88607403400320301c003900000b4035540640264450907200401604606009070182d0000340300113551280c20030390034064020070351101a0645880c0b800340307411b0700b0890410b1800d1104d1026 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 32850068 1250 32848818 32848867
    0x1030204051f03080d02090a0f151b021005071b0816120609050c090a0f060902090105071401060518040204050106030b010c03080910050403171005011718070308 71
    0x800218040360110004280b6080d00e40c0700e04001e9440d400040d14078068004d44034000d6128100d4280050b50040b05452501203c044003d142e41e0010020030550307405095504040081c0100ca2040c40189400c00c4051039101d01400c099080190688424051450f034020115002038960780500017100d040000910052280c0641300801d820104483c0b6810010b0b02c0c02407072251039000702c504005003480b05041d040f80c06040341800b4a002ca0608025190010074420490b14000020035120075a0003125805075040c0c483c5403905031a0396601c0116484500c015555551755480858503903210391592100324540c106528050800340100411107030181d00c40c5c001d144c0381c41c58805a50740c000e0401c2071000e4041c108043c1c1e5580c0d01c1c5100d810280400c10399600e0070325100822040580046001d101c81e18021a9201e40e95207a881d1118a100140611800f141e40d506202c40300441c0040a070f1343c4281c0d0420500c44541940c8021440c100458008803182a008600e20b8024180c84203403c0010303070f = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 32851318 1250 32850068 32850091
    0x1505040b0105090f0609040207030c1a06090610031401060f1103030105010801050904030318060504051902130f06030219060f0c1113140f06011407050303060607050f0102120103020405 81
    0x1900c10001804520404a443d80218102d10b2a01242c2d81c62400781da441d80c1d8040d10075035072940940340003007004404420480304052071407900498102102030b020301c02c5202410240301d80d1154001c1080c5030328001e450408054440d50b181c0b0703040c248101c2a034020840390b1190800e80d01c0a43c07001c1c088042000100340702d13600a000400c640d0380c1c403000d03140c11204140c48501c45a25507003412005000d0b00305944070b000051015104c01c000096120920481c020800e42d4400350f0300c94500e0060a440410195018801c001d6003031443c0b007150f210780c1d60042040c00010b81542c0e00d90105841008610810038a000c50300f008000840c0c00030300c0c0500110f118681095503030b02c02c2d59203c01c420050041d0074000c0c1c000401030007914542da44841180308813004c02d5081d41c0b030080a68000f00c5811a42140003600501c0c85003450042e030b0094450781507000740610304503030b101000d01005401c0213005542510503070903850025002880185040400b215070001e19604500500c019110058050b03001c21 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 32852568 1250 32851318 32851331
    0x20307061e020610030f0302030d0501030b061215060f0316090c0e030a0f110a0302040e060103050f01090302030313050a0b0405060105040b010e1c080912010902090717010b0a030f0203070201150504 87
    0x400d04c0503420040d40d41c001030340100c922039420700328134500030b24045d0440340d403801d0004018041d040c00310612074102100c1d0010004060b0b200a038990713204065401458072844049141c610740400780c4590000082d0440b42c04403a800401c030340340c2076a40c0c401d8102c1d540d43c007011001c55a100d81c01c50040034041d0024070600c506583c9a0700c3c40101401c1c054007001e10202070030116a40c031400c0400035a0000e0050003516a1141d60582710b40f402e11040f50184920b601d040040341d01030045000c0c06170142c001c1c5056984281001a00d0103209008a0380c0703000e103c24800c00250480c034024000c034001c1d4011306035507045c0b00c103000c22203000c8038071a07041c40311000050f24550348001c550302c2100854000c0040c003e4042c94212218010707409031300d41c02a151141600c0c0850154404e61200780202c1e81880c481e280c1c104155940b450b80d030000e0f03401104040040c09882d00f40360082400c1e101c146800941ca1903a441190100e030400d0f502000180d440302c003004900b4070001c61800c080c000450701040034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 32853818 1250 32852568 32852581
    0x6040b0102120d06090519060501020714120106030b0c0408010c05030f01060f020f010c0507030206060d020f06160507121a0106081801020408030a17010b0309060103021c020307061e0206 82
    0x1109080c10b00303201c50000024800f1610100c64000c40000d1010b15000e01582c1842c164001c03281207002042c501c61458550001450340c800140c1c94210b91074030907003400d2419502c00707010b0782440c0d0b00c650320030035925101c0c0080051311030343c410342c03003500e41110640d201d9090074000e07800e444400f6449800c2040520038041c01e08101c0c05020b0454080d8240005007100b1701d60281c0c20240680d5042039294a030003121403169820a004142e80c510035825a50165121380030403004402c580c1c0065004484c1c22a280e285041030760040802c2014081110b42d0719019a440321b242c0741d07464204800b47d80c1210289410032241c103207507a0200700c0d07013480a0309941c10010f001700890001804080004103101186003005400c0d8116030281c542c600a50b5a5a03107482030103008213568006424901c00007200011f174404480080d2801a00b48001800903646140c0800a43d580c0c5c40d5280c2c00484181c0100500503a020840303100141a5a103806407070400c0440303200107259a210030780c025500080200640f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 32855068 1250 32853818 32853823
    0x9030203090909160806070e01030e0c010318080304060906050a090f02090c0c030408161208070f02010e06070f0212030406080f0a0603081204050c060a020c01120f09110906040b0102 80
    0x401d4505468921050796459605403810b82c81d00340145180040840c0403c043c400414414071400298451410b24141c0c603004408030748540b500c44e2119000b180c1103c145620a40003540e403280e190b9102840c0703008945480401c0d03401a0750840d542990b0f400610200403070381c013413190300005040b001c11215425440d401e07069001288000d208603403071000101100e407041e05540400d0704200849842c0da0f200d6800558450b03181c1c004002d03d540002d400a802032a000010485d103a010b030300c040c2031001580d02d5496002e0020402c90500110020b0b41c00e890311444098209907006070401740c80501d55005103e5800c111200b0942a034104100900006070800519900078598010720601941c821481400610440c8c100614003c1e00054980d41d400d00c05601d140100d0149003500c0d5040e4049042103000d21400b0344c10b01c05a013010060045541c0526a01511000d0184000c544294092409801c86030000411201880d240b00586032509020119590081003620204901010b4800203903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 32856318 1250 32855068 32855077
    0xb04090f02130204180b04110c07030b22050c0a0e1005010c0f05010501080a1e0b010501030203061212070b130c050904080403060c090501020d140405010c0c030b0a020c0706020109030203 82
    0x80c05007940000c081100101e0ba41180c0041c045c01956902c4c0c60041d400c82d81c00350241000d21303413041b42003511114455a942c41102c142001000040c99106d2035036a0302010848000d00c0c0104604040340c505c5414641202d1f4071848900c20b070b0142c42b90041031010401a80410b0300032034000d0200c20104142002564007907800d440c82401c110020207124030340f9400065145100407c00c0d42484000039003484000750807600e4900c2a42d04102040400c00401d2100107090307000f03041d905041c0e00412455002c0d500447c0c00c280d0203810341222544160186142251500038500000d0b80060004140101850500d401c1006d5100c001c54101d22030310b07945c524124901071a8480c0e4078401c003180400000e54203c42c0190b500900074880070100100240010040d413240380d000d401010150054903200e4805c0000807241401d8650805013031400461f0900e11542c0101c4100090020200200e01d00c0541144101241007000da0b40f00b010703000d00c41c1090801d902041c1568100310012001036000b2040e00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 32857568 1250 32856318 32856323
    0x90501031208011401030f0609020c060709080c0105030a05041509050705011d060301090b120106060512060904031e0c08180102070503030309060406050a020f190e010f05030a0203090c1207090b04090f 88
    0x2161fa05281c0d0440d2000304a158000713402a071000940080b00500402c0d264820720f0075894007181a03540b100381c01d071510b64070256680004d80030400100d071050590b100c00d4006028455020f4001085110f4000b2107420441c240c4590340031000402296034000b60f0180da0312800981900400d001e100030172120300042c014003100644902990720340c1d84230780c81c407001c000184030300a00c142541c550000d000381c1c0c001c5440c010311480681c002505030604121240c0640d0785030b5510212454641013100d858010300c400c0c44208000740c04243e02052a4002408103c060320128a404040c0c000000e46010700075071006000e50005e004008100c4c00202d000395100d03422950104056691240c490020700c10700d45191500704010402c1c0c0b400c80d46489032424490400d454202c03035000058015580d40f18150340501c00514100001540d0140c983c000d1508008864200c45c0340c0c2c0b000708006030342400e09424000349640848800c1081c00c1030b45c01215140b0209440811a03032070350380c848812110304d61502 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 32858818 1250 32857568 32857571
    0x20102031b0109080a2304051f14180a0e160305060102190302030d062102150705010c0203031009051003030e01120f0905010b090105010512130c09050103120801140103 74
    0x240d6041e00020341210303240c00e500480c10b950728154000d002d494010703080030f0b690b400214000b60b12011041581101c094940080ca000046240c0e85200d00020002e018403c2c2048000d01d50210b084001c0c2c0c002d003540a8090120b040c5015500041c405820455440340c030400c0b2007503050103901c0034030b15001e626401151802080c950740b4840141e2504282d004503100301504c1c0e020304010f00d030f0302001034445034800140070701c40a0350343c1c20352120840f84440002d4010042c43c01020040c0f8200310340540b50012000c0f40c50904110317445e10713030840d03204400e20005a08004108101c150550b000301c000703070103403007001c1002e41040081a88200d407180401414011180c0502c58140e0045e40f00e00e4511083e44010300045d030458061350081c1c00e240004507a40e60030900c046c4040d1800c070305040e050f601c060707480ea400d02400c80201e00e5900c001034505008150104402408a1100c00055000d8080c0900c00b15403940345243c580301c21aa211030745001c00031420010b210302e05603602440850042482e0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 32860068 1250 32858818 32858857
    0xf040305040506040f0e1501020d0302070609060603060b01080901020a14030a290102010606080103021c0813060201150e1501120b0a09060501020d0504060806100e0315011401020a02010203 83
    0x2400d480c28880d581006522003004540011806942c15010307040c0c41603100456910703112005501e1103813070000c01990140c1c000d07020483d0210300ca9805030a82c5400f49501085000842d01e0381002c0740c0c03ca0300190359054a03541c040d803555800c6081560080c0d050f1008615007411600c0040604581c40c5500340303019000030215103c0c0c000398110307098400d00310188900b603104450020361a05420a03850380507500b4901c0c0001d08034001c0c004513040382d401402d0603000c0d40050908144035540e1400c100c44e00003050050075001440341100c8800f0385507a0300000752000384186141d0900d07070160321055101184900700500310b60303a408100c10084080c00d0075242039040d4032092014180c0007005130b4010304244000101c031101c9030014000c039032082c0c0a540c0121802e4030103c442d8800c602441001c107940c400440c106090121404407590403c3c40c0c817003800c41178079000904150400084401c98813480b401444411502d10820031022070074001441c202a986d40041e44a0240707500d40c01a000d034048 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 32861318 1250 32860068 32860073
    0x903170112120c08030703090302120705030306060a091a040501080a0b0f150903011a090a062103030603081c0b010e01020a06090218160305090a080d020d110d02040501020f060c030f04 81
    0x5030304101503502002030745c1c90f85070944005004080d5940103070014440c2242c0c080303030794002c6c030100c401258219015514591b00d041c03e0140642c400394020041111008000420100403603110704601403183c95944c0c1c0d036207844001010010043c10810480d8135040c1d840e042540e43c400303040002007043d03c019114031840e0740b1100042c040c4011064055082c99800314050540200740d410220044403084010f8442088400495055010f0300c000c96405e0111480313540802c103940c506a600c280380108020303440380c0d02c0d84c03c10780000400c03002081000e070410007040c005000d040010b81080c40c080018651180000396244000760003e0a038654401d40c2e1003c6d510b0340e0713081050a200200205129042040e1106c50001c41c10281d1000a0301c0c10303001c035450000125101e0555030704a40803a040a00c0d622440000750711100e448441e656603254000300f40184207011f0070382203801d550b0050f00c071403030100007908000300c0b1403e0100070b400410401c1041c402030000d4a4001e007901080042507a40d61 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 32862568 1250 32861318 32861327
    0xc18060b03061e10020706021005090c01081f0909020102101103060f03030706111b01060803040302010815040c020f0c3f0303040605070306060c03020703110f04060801090317011212 80
    0x43c000e99004490404c0b00f10031580c00060b02c0d0100c0b5844da0032602d0003c10042d5403411501c0036510b00e1a540c2202141100e2580f181a0b101c3c0c0026204942001c1040b400c900140c1245507544001c50298482100c00d06644e0103000501c074180002c131041c4100602e20038482e00d00d00c13000f40b00318880c0481c0070340d500281d2400c00903604100e40c4030340b04005001d4258041046908413100c000c04002d80840e0480b4440d006005001c1101c0314000110700f07290842d401514100320081c400c814031058904e03103590a40d154081e00c988180c19030090300100c0340421842d030400d20305004950261440c1c0d02050400440b560b0410b05130701e49030281c0c1e800d8200103c000401d164180c0c0074204079210101c248404d00076141e01041c0522400e8404120043d80d075a003d0350070701c0003400060701682000008001081c401c040c0280b411034010041d0307810070000c030009400c0390040c0d001603400b0fa40d00c0140c0400c042e00084000102203620429001e65032614407030b5843c42441c4d03c40181501d4001684400c00c0b03000c3c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 32863818 1250 32862568 32862619
    0x141306050c0703020901081b0303040f06030b010c05190201030608030a0c170705060403171b0913150303031b020f0703030c1106030103051605060a0c03081b04030c18060b0306 77
    0x300a0161941c0d070721f24403542d8400c80341200e6584176074501e81d64102d00c0c0000c11103003100d00042d00c2281c2c90345400c1050b0700400d10b0204503410303c40030708480d2000036030510001c60a8074520040d070520070481d0000508968954100440b07990042054803030b15500074941d10203d6511088030071509030250407032855030050100c020701d00c0c82030030184410190000f030100d00800b10711129034410741c0c8003035401c0c02c0c80c00b180c021902d402000304400d4402c3c0c10407000c2c02405a90350000480e0039038208039400c000040c00c4c5d10543c0001d55400b45840ba01039119080d450b1880e4a100602c0b100311005050f58460120348402024401c04850040401c0181da0b101d50001d0740041c0203540301d40e50b074200f0584035941c0b0300303500b40e004a212030045268030f0040c0603205402c2c0960b032101100c0c00150741c00e454100026000c0f5122022040400313186100b0100140055407060311070f100b1161800100c03220308401c403030210940070309082045c00314185002c00d1766440301003102d901c01c40444484031800c03032485 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 32865068 1250 32863818 32863823
    0x7020406030b16020118020117060a0f090218090601171b0304080d0e150a02090604080f0d110f03030c09130606031a01030b03190215030a0903141306050c0703 70
    0x42c10020442880100c3c10080d0202103d078009026491585882c0724200d5004103000380801c0d400020002d004207260402c5034016409044210070584520f410130009105911400c0307500c1c0c0014280c0d5803184a00d2100e03114600544803151103041440000c1c18200800c014001c0c50710304a4001560b0032242860300c10303c0c10551a0301a901d08060421000d01d50002d45040d401505218400a181400046181d692000510400c0300c3d51240d441140c06540700003545517001000380310100e4031840603c040c140048140c4020601c0d846103401c06040c0920418071001590480408011200c001008a950007401c80c0903943d620a1600000f6051810020b420141a89424808289140c16600c1801d0030100e24482c0c03200d070050100110117460710043c0c241d4140e001200305070088040c00b4403581300984010010340c0e540007801081c54158100712540204a41c5a031117900905410044405001e0415410f41d40b4240444a07040e55065580c81004100300b00000c4c2440c0e598806c0c00f441d0069035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 32866318 1250 32865068 32865083
    0xd0215070f0507030b011502120c0f01060e01080d11030f13030b0a0504140f0c09130803040803070e010f0c03080411030f01020d15051503060103230702060703050601020a080702040603 81
    0x9002d08000341e0f00d1a55010880d8440313085030020a00c1d41020900d0320700884070754010400510385210341c0c0041e41001c01c404900307115440310290f00301c40a0182d4400303019400c103800c0d081d6140c001014907180c03410000340140004003d440c0400b80c3e0100032160f400300e060400c0b40e0340349201c082e9440c4000d060ba00150a0701d1444080c80580c1c52680c100d10b010341e001e51100c140d007080d04c14002c0d440c2d0403011070104595106941802e41400c0c01070035694041001c0302c011000d6000380e00d07804020740c801c560071104518000f0400510380d030054104400c0314001e01e0301c000c0d0300000507000341091072403400103018030041800007000c2000303010390a0034500001e001d495111480c803810074041d4000d000d04002c1c61b42881310819488007100c100310125080144500d06100c4a0441c00901d43c0c00504424101504c0f442c140303500c0d81100703d0550001c50700ca4190542403402000090500e04080e00d480205401c1605020300c50f82d00141d50519075412607401d0350b40307185c03510003d4010406c5038002413884 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 32867568 1250 32866318 32866343
    0x4090302010b010e0301060f09050408040504050115020601090b01120b03010905030d0902040516052a0304060504050418020f010f05090306090705100809060f0903130b0a110109020d021507 83
    0x95410b400c00207418000381c84a10f80c2401000800d800d0765140d01500c510310038181000c00044905401041c1c209000b21042460251544003207030540e003023600314080031114107030b1021003035504010850042182c40f0b0100614000c200009088540c4454000381d002d0315450803014a95080d4856a0802d901404032607451601080041c09007060b600c00368421031030040000d01c42c2030440c101041300b00e619a80d0341d141400010300c40312010343d0006810202d031341004111116407030810040015180b180c0305c06885034623181c00c11058407034150206421800c2c8048110040c1c55040c1086400082404d1080c0c044006140458190150002d01580b521502c01401200c441c0440c205007075404c2512400c3c480c482c01503003a210703500166002d46481c0e20040000d01c00404400d61140c0200400f0300381c0b0f2410002000100062806401c861040f1030006040d07c910350300201d100580c0480d8a0003400104c096800080036818202c5010740a5007540704c0610030440a602100d045903802480c260300b0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 32868818 1250 32867568 32867573
    0x905030c0d09170601050f01050c120f0318010b03070e0c0d060f05010201060506030c0301060c110402180109050103230403030207080301080a03080a0e06040213022b1505010801170c0409 82
    0x4002e040c1c0f1640200c1c09140400344000000840e80f60706884028101168143d03a55004443c175900142840d0554095048800d4000c5914402400b04020341000c3c503880c1d0815060071340701e40c1e95000c00505507a1408a918896850100380c14044441c15948207081e0707510900ba001c1c0c507200704030302401607a1400b49c001c40c401e60006843c2054440a034000c000054580c400e1002a101c159070300f8034441300a00040104901c42d1a10707001061050140508014415020400fa60800100104449a888501e60080d6840078405c4003c0809203000d001c9586031100d00e41c4a0304d11000c074000c0c1040d507900018281070282d0111100c06c0d0340221256a41c1d07079a11156074a903689007004030001040640803405180381da0144240d0350401e10058035035501c3e542e0808c0340070b14209070340c00241c0342c0a01c0194004c500183c080321340010291241e0028440440201c0b04840002c80d00020108040d5030031301450340e1002400d070549406140406006005141c0b031490000003080302a80f00d4146000b4404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 32870068 1250 32868818 32868827
    0xb030d050705070e07090b090105070818040b0102031306030b0303040f0f03051603080313050a0b070e151201060f02070e0a0b090f060603130f0f03170a02030c0403060905030c0d 78
    0x10402d029000b610720403a02e0301c446500c500d405540b102e00107024640309000c1c074181100207141d8000705051182c40c01d50503564243d104c0c0c0268000603070141000440b05004d0615001e10400c41390244051450303d41003c401c4088415240102002c050b5142032540c1c584e1001c000300c0c0d02504003200341d09100c1380c1d5034003904030000c0c1e1400120f0b00c80c010700618096040f01458002e041e41d501c00d8001c0e040d0f81c0c480900100072014541d0030340b000d2044490442c003151342c8101e032a0280704c059031509002c032181310900508248648040c0128071082240d119003521341018607040d00c085281040e81046c00c0e000c100c0c40c101450300054245241c0c5400e000c05100c2c680d200c08012401a50503d030340356940b12071443e0300d40085818a80107101040043c5d0101410800d500102c3e101d20601c0d400741c00903440c2e0303500001c0c004908401250f1074400001141d071031449815800060204294910714010211811501442c170000709819180c01c40e07241080303020b01c1603850012074a01151460354038810b0090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 32871318 1250 32870068 32870077
    0x60601080a021602181b03160e0f0405040c0501170c0a030b030f0706020313080309220212040b0403140c0705010e01210c030b0a051c02030102040b040627150804060b030d05 76
    0x7030031250721019111040b40b000c6c042d2441001c0a440c80e8007024504042621013081c0f0300315440d0701000c410b070100d8095030386200389030140e0b003e400d140800c20304002c009049480907018600340291074208001254820700c0440789030f81040e190204001c103490010070318042110b000381041e80616607010500590010103464451400c0d000086017540e43c0c0003440e01c0344201503405030440c841c0710421a4120020070046090007224400502d0300c0e066801c5950140703003e44003182d406800e042400149540075040100e00c4030741d5030501e03242c4a0341081442c1c2d03a42c840d00c1020706001e10700600000b17580c0200c40305561400e41d004008443d40001d03480d03d0060141c0d04500000c203290440d000c2c0c0300d00f00703900d010b030680d400607004d00400050443d03030580500c10300408903410740d000c00c40404d998601402504c020550b585500720684286607061042190460020741c05440c10700c82008000c5680c0e103101c0100f040b604143c902500c4909103480a0241d0007c000c1e0144289070840303100c88c6c0d01ca0000c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 32872568 1250 32871318 32871331
    0xb030307080d0b18040201080a05060f0a0602070810020306060301330305040309080f120714010603032001020901080703090c030b0c0c011104050f01051602031002030a0509060601080a02160218 85
    0x1100b1310518508403000c210030b42e0040c0c0083e00c07000001d5008142540302c15003085000f04240b150181807000a040a0495003000c00180c0240d081006482810000c414281405250070b5055241c00c1d40440e003940014820080c030b4150b40e404110249000028880c004601e621400c8900030161030003074007401c415242100014000107001503801404913040202a6813440075100b1107142071030803501038001c000162801e00701951501b00080013480399400940c4203444001c08400c2d00208607030503a4042021980c1c2c3c2e40100800c0600707030390083c00c05174884601c0c10700095440c00c0d41070480841840750401406030341e40401b400201d15911005d000b408104c0b90003406611600c2c0901041c6008503c43c0c107030002c0c81c40d012042d956016002614014500101c0c0744004102600028500401c0c3c24890700b40c55400800c4c000c400010707000d01644241c0605c0240018100080001c0c2400f81c01044121002e82c00b1600c0c60103076040d107107101c1c4400d400804484940c04800c000803000201581d05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 32873818 1250 32872568 32872579
    0xa03050d0b090103060c0e030c030d030e0309040606030c0206090d080c0a1b03030608010b03070e060603090f01050a020306181e0c161103010c090807030b07030e0a060b1003140a0b030307080d0b 85
    0x3005910b0001030071124009c02501401d130001721190140e0140288401203010760106004840c00c1c0d840e5881014000e08c030315036000c00c0c2840002c10203414248080d05c0340c019034200002d40307074041d5081482d5907085050300c042e0355907a81c242c800031546280c0405130100035101c0c81801c2014164580c200805940e2074500801005034003e04041d51a1040e109106c08103030640002481c07450540080c5600040c401c0540b030400400c4502e16003160700464040c2800707507011042c803500c1e062800d9021109003030349080314400d01307120007a40c03000c1000700c00c0d0a441c8100c00c4002404020403401762009800156002020200c072854a082001403800585000e58a0810010b1213148101c195508880440700506002403d540348d0010035540200080107254866154188446042000c01e08050083e0000620343d06500100018003009101074000c16041c0800440e6000315030071b58540241c14014005407660b1503d000c40c2c20741c02081405065034101264078070001001d508000010a000c450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 32875068 1250 32873818 32873837
    0x60e010506040e0103113601060302030c030f07020304081504020f030105010b0414041d100f0605061b0a0b0f04050d052b06030804090906110a020a03050d0b090103060c 74
    0x901c40720340030790300c100e4030140039010040011650007030107040402e102511061890140f10701c0010080444813560390460014956801c1d0044183c000b1409460740f403800b54a542170451041c0118040a45070070a8000c44002040c01507001b00219001410401c3c10ba41641c01001030340007240808840581c024180a14041d01501e410b209070703070613103c0c101d03205401d040c20560f00c0c9030072210001d886500281c1e100300300c010b070682450585840361601002040707a000d8001d881c0c4155501c100c40b09840a043c80020700c61551903400b41c0700d0510071040850b43c0400381500c41450300800320350103040c0a0205062014081d00714203440d1242e40540d044420a61200030100c4091103050b4004c00380840e06000c0300c452000032601081204031181010135204c0d120307181c0503460391040c0e0041c6d00b403039511401442041401d002d5900e1491007002e0302c41c2010f0b10940c01030344892400034001c00b008800510801d00d004035621006e40c040c0c1c00340100b00f2542c0c403483d01e03200400c040510b20740840c1c071800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 32876318 1250 32875068 32875079
    0x305011b0e0406080601030f140105010e150108040c0b0d0f06080f0d050703020601030803060d06110c100603020303040527010602030a03140613050a091a04020a080a0f03120609090501060e01 84
    0x1030f401210007220003001c5680ca151034a08042c0c08890044444c1d40c0030440346501001c09000f980e0290044450031034407030030700011107000050f00e0f8441c0d5044c0001c0d60300300004942c0030a4207000b110010100c450f554204244098028120a180021024a054400700e40940e000400c440184000c5044401100420005035040d016511004005a001c2401840061310120245821a0b07000d090800c00c00c0d0036030360b03010541d0907039100c0001c1c03c000481d910001e03480412049071000c0924001f00821400c2d17401103601e81c0725901481d030040c0001084202000d105d00d4020740341c0c6043c6804501d807541c4a200c0251298006c2c1499800030742420f0108114a07a8000283c0c01100010014000c04507038140880140034001c2c408180903644409000110f810300d51080e503443e608001010035840e05204106046005800c1721050f94880c50b51030000484034240900000d0301802d10603003155812890340042c00480d00302c040c0300c3d070504591904001c0305401107003e44000c1c1040c00916a05c03603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 32877568 1250 32876318 32876321
    0x1090603030f020a11060d140405010b19060c0807020f180703050c0910120204080124080a080d0218150c100c0c03032f040608060f0a060e0102070305011b0e04 70
    0x24440900180c0d00003117450007034a4500000e110941805002203a01060280e030407820000803141601d00d65100e4620304203038a4118282102450701640d22803440d424080002c0079442d45410081890000040302019035940b68000e100100c00180464030317004035808012112170081e21202c000c00d0a00c4003141000103640151071850001415007100d0980c416001c0381c12007068072800703913a01d908000c0400e4041c004e0048840c40442e0451805003500501c01f4080b14001a6024200c11740011700c1c458009007584084800012040c400581c0701c040850500100480181030554449200300b90308090800780d4002d009a40c03102c1301510010f00b2717071005400540780c01540080000c6c007601e502c2c0f130000b80a80d10000343e1544203205210300400983d03100d83caa51b0400b181160350240841c08102140c0e002e461180c0c0f02030181d0301d441c1040740a070080783c10380b078044c080d9000380315822480204a0b40f08100d82d200840d049002848880254580f101c088032000c2400700c009800038612a4407401d05 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 32878818 1250 32877568 32877583
    0x5030712080a200703090803030a021b030301030b0402010c081207031e050f0a090303020405100c0c081203060d030302070213060807060207050d03050a050c1c0305060108040c0504020307051201090603030f02 91
    0x44000c01e00b035050380404803c1d50b403041e0000c50a000f580800480c0c00e840400181d441200c1c4a0b40050352a000007051444111001c2d1544400d58800c10042c00010368500050743c01c0740d821300704461003200a00d04410b00d07005641c0c0c003100d6010224200910107605030400c000c8400e290720104c01c10610301b012242a0f9404603040c04c0b1210074400441c02d230703030083d0344407690140c040e24005007040c0c1c5603030010b500c0c2d07a82244d0078400078011807894000d002e40780c0c8103600108440c00040603180d0240c41c04200c1d03800018201849201c0200644042c180240c046071030f00fa03801402284035001d0500d00f40000e000501401100c1d03c2404004510740740005901010389400504020205031704c0d680864880d80002e07090400c100c02808484242c6004000d80c46414030032240c4911004a1554000c041f594010842c6040040d6503040c0404240d404884000359403042d00c0c0969a40c0c0d64003410b0720719215804402071300c88000c9000240300003a5600920a403482035680039011803c0300c074101d944052 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 32880068 1250 32878818 32878841
    0x31b0307060522110103060806090607081f12140102030f01080601060504050f0906010c2301051522150905040203070504140a150504050108100b031605010c080705030712080a 77
    0x1000c110f10010070200030b0304441d180c2c01450040b425a0300e54025a00380501680e07100c0b501e501010601000c69000508640d02c51451520741041113107442c3e49010021082c400e14260f070310006a00824000366641840714078200070001d5540742844825002d0803c0309101d224906c0c0100c10010503890310403011142254401407100c030a00c43c6c11020003103a1140940103a05100761030503508c000401c448501d50350128840f203400d0302d001c241d92099096074002890521314002d00c0001c5140d5981e0820681290307044800e545010300b108450344001094428801000a19039200018240c06141c00051003540700f03400303681c80c00d5078610620045d16480f0408a40c070038404000608040d4059102180c100d20465090800e20340d00c0c0041000c84000382c115602d141c01908955803150414014508a040150003e124103c1000306140510785ca0b4083d041c100548000d4050034040401c041d1001c140d0001d043d00c1d40c0748824502224a0008550a2404580210002900030003288190b0030040c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 32881318 1250 32880068 32880121
    0x150103110a0c0209060a1d09010b04050c04030b07020111040b040501030b03030301030201210207060212220209150303040504060906030308010b070b070c02010c0b0703060501021911010c05031b03070605 89
    0x455503404c02c030504900801d8103412800e0b601c2c002994042d140084842d110a2448400d8182003c600c81c17404d5904049403680518104028042c1d0080303941c04503002c80e0f4114024554944034520224050701100c500200c0250f00810045800c1010f83c009104035071090301d080200c0c002c0700c014961030740003d00c0042e0200d51048030074100e5411705c082101000c0204039006281040a0f41c429003203800c846124010310020004101000000202020b0032264452014906880942c0080d50f4400c006140481e4074462503481d45154908109442c0a40f8008200f03100c070a40f11210b410041145100540020742003a0001918246410032940c2c2c03d03401c8950000150b403124015103580359400000c07810011050b202d100810484a0324500a40e040c2d50042019071410303000915004409004103c001e024014400c00a4000f46010070aa8800e0070301600e00325213130030402e00718043e0b060007001240424031940541a000b2000380300b01d0344590704c10052911042c0105003038050500c104030884 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 32882568 1250 32881318 32881337
    0x905010806060d0c0801020414211e07050d06050406060b0301030503090f1302030a060305010f0e0703060c050702100201050601020d0905090f0a0216030207150807021b040212150103110a 82
    0x1420040201d003c014025018900d40a550301e0302d4508980c07041c0d00201c3d40d807111440003c80c62600c0e50001c054444420f40f42011419803884ca142c0300c5001ca807603030f000e05c0100491181c0118043c13141400400005048004c6c0482c00d0520801510048030225811442d1010100b8400da103a8250f030706a941050043d818240710809100752280407242076030744640001400d01c10350400e0700046102d9111038401042261440c6006800d480d52100b00101642c00e00c00d03445c00b40742000031034500300c07900031310045248030108809881d203115854020b500305c020181c02c10707038a07501500624040c0400780e0880c1c01c0d191103145d0803180b1602d03d006e480c4d4041c1c078031000318005000d03000311940c009107050801854280d802c1042d41c8044070315034003100503030003610080214641e10100d6144400d81428480302629129000075200e00c45510000a00404010303003012945655060300d0040c2400100070070a42080154031007542c0080c45510300280c10414800301d20007040040d00c40e800c0050300c840045 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 32883818 1250 32882568 32882581
    0x121203050f04140705060408010c11120d020904020409050708071b02060d02030a06050a0602071a03010305060609040f150e10060b09010f0c061b090b03010501020604060903180602160905010806 85
    0x103c01161000194034843c40d50089819a1000001d02c02040700c20000500269884005403a6600c9008410341e41c0d00005001c8403502e458400301e84411035071417030041c0e4815080380043c00a00490300700c10f105500d4241008103c43d04021464041c19084e11044a85048240fa07202c1540400700001c0d0400c00600c45010f100da070540185030420070409010941d60303100c6010490030f5a40740e2100006900a040810414201401c5001c26500c030259203490f541c15034036400d5440d00003030000c0c0c0c014083c1000103824002800c6210f201a540f000400e00e080301c500b2540d41c090908080300743e180740030309568401b03000c003184990011500b6807106c19083c481200e0066035200403c030f01100c14040002c101c05d000503e0380c45002542e143c2c0d101c030280c80c80c0309104010300103215904105890791702040184410ba0b0002911580541e100b44041401a03480c03404035102140104044940140020081502500803c0013214401c0400c0d105005070b41d078440740005d071002807051010b96000207011030f08 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 32885068 1250 32883818 32883833
    0x30215030106050d0507020f0a03091401021b060304031b060c0806060304030905010e030f0303010902040602060c04030302100203130203060405010b040b060703090314120412030e01080411041a0a121203050f04 92
    0x9020b0047c2c01078845105258130124148840010128000f440b103030307401d01c50f2003010760002c41046400c0c4002c0804d1140071a960301c3d0a44500c0c2041d110b05004000181050b1040003032405410700910701c01003004441c0f800740007400081501d0790204001000080083c03c11800f0b40e440382d43c040c3c0da4a10041e15000054030f09130032407442e054044c0a0000010039600c07040004600078404802c00603519890140c0c001c0c00c0041c042d01d0b991140008110400200f40d000501c0d001780e215841380181d0303a031603001100e07800031081c100003509401401d00300030500006511502c1210320030b84040c024034585200b080703007600c10300d140200400d00c6c0c40803d00203c0c1441c2e1800c08a80020000c8600d5052840241a1a07420507800310043d00c0080000d00d040681c030000704400c3c04420700341003003e801c0079503610603d07100c0740003600d0140c0c1e9101940d852401c1c10101e10401c50030090681c600700350326040d40e40c0d20344510f91030588190312614800c1f010075202e40314941c0308490884d15950356803260341da42e55 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 32886318 1250 32885068 32885071
    0x1030b06090907091205030304060c090303050f0c010207120509101115060607050102120115020d09210606090f11180910030506070818010b0603060402090406150504030215030106050d05 82
    0xc204400c203440440c0c10305d86240001d030b8550046008607141c3c40c10380703481002e40b600c01114004100f03501c81c042001030780050685600c410005c1c4c4080c0c8583c9540006802400385800180c130150b401232842c071307d00b9001801042841010703104980214040c81c01a00c040007900304440c402c0d0b000300c0e00d40807407140354181c85400000081130320b4501a42034680500fa41c01c40c41e10145e01c034a03840c00412500b40ca200000800c40100d001800345809203540207846038441c0e200c0c11001d06091000708450303081075070910f0000c90f400a0708001450b2540701c40d90042070300c0744100041905c0c0c82d000f8204504150250781206c01c2d0829170b01c54912104e820300540801c05018880744042c0004003100140e01481214440d408a0351002000e10b4503540c108a4010034440c0310030164501030b190059600c8070000c50b54031034030076600503a075582c2540c00710300109041c1c1d022000c0c001100c610a60708907030107001041101d000b01d80317a81c0c091016040d9060b50b4402032203080d01041040101c034414a25070380005 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 32887568 1250 32886318 32886331
    0xb030a030e1203120906060319030507020919090605090f010b090c091201050103030e0108180c0f03030706020d09020a050118051509060703080601080711030702060706110a050a03050601030b060909 87
    0xd0703080c504d0420f42003100c840255585501034000c141042501d0404000fa0300d001360041d50404214006500c025001d445100030181c010385045001a00c603541d2411181d0480c40c07144010400d400540c20900002c0c00b0076643d0740c607580036550340c40d54160014094091402002441400742c0d1b21882314562243d40042165504403000c5040c0341c2c24000c0a02c6001d009600948400411f03c5049000500e00b007001400c002c9410400301d50052900d20000c1c40301c92010003540c0c07a0354900042d800080c40c500445030010820717400040d40b059261001e4104044c8e0b68400e4072040701c080c0c5c40f00010741d0012407042c041c0b900050304400030403480c0703442140d0809044490200340d18207004440810041d03403140800f030700801c1c840d4051103001c3d40d0103190b0a500401070f00c1c1c008509608100b40c40d4580c41426406072142d90045594400d0004a6100300701030b0a40d080b0300c2e0307603d21040f0f0019050307400408000010a18180010301d103075000703002d6800e441000a000d540303481c2220303041064040c0c02521a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 32888818 1250 32887568 32887573
    0xe0d08160c051c08030114150406020c100503130b0402030c0d1112030c0d08060109030204060e060a050603070509010c08040801050106080108060f071e0c05070f03021201091a1f180b030a030e12 85
    0x714003281d05080002d00c00340064bd03000e800d900385a0024001c000303c00c4100c03c010400c0400c10070010b020703080120f01006500190344109500c031400024984802c0c031114584c402004028801000b40d00440700608180642e48901e40f80d54659900c0c0d11b9001e10441d003591900304102c440c0d1007522801c1c20a9001c9014140032410320b80b250049001c40b540e0340c00c600d28400c1c2c50014481a86090082d0100415040700c4151851401c290014054040c0c1c0c4240d82c18031003d07103081c03020051640180c03409004114001c0042c1e40c0c1d6120010401d180c280f1400e840b50044c80302042c0740101c0b0707515403449020940c603036200f07032000114507201e2900e00911120801c10640030200010b141805031030020034076518400041c500310300420030950700700882e11000b07a00d0308440e070000408100c240858107a0007505144a940c950200d05503c1c94901c003070300d1440c091030401164020240d45101c030610703407040080107030f82040c0f014542d4803140224003602084421500030b5240c40d003100c00d40d0f0341d405103905 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 32890068 1250 32888818 32888839
    0xa0e0a0f030c060204061d04060302011d040603020402030a06180203040308011701090512040602150405120f070807050a200a180b03010509010905120403030e0d08160c051c08030114 80
    0x103c45040703800039040b000018600030b4140d640281c019800810340f08045134100403007450b503030001c0c0204c2c035002c2001d9841009501500c01c81d80da41e40c400300040d50050400c1d540e91034131840e12030080c1002d000c0c21012044032030102c4810406482600c2c49141c0c580c462007500e0f400d021540d000e03104907400d4010a59200c81074078001440074003d05010b01011240c0a813594104400a801d2246489010310660300b000d0420011580000b00c1c400b107102c002030055907420140704544406d100300a0302500e20711001039420200240050a400758030b0241a00c505030090081003049001d82c4c982800c0d901c070324004400e02c01111585c4180d01155000c0c0380015034a001e940101c0e0030b5400498844046941d6420311105001060140001842c0791418480c6010705541e400342c002d10300a014103000300b0329004260304003e03100c0200c0e8103111036103c6064400d145407178240011855402058014140b001f81d01e00c1c43c415154a6101c5241e11050041c190703800e141d541101c02d02091410b5611650605 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 32891318 1250 32890068 32890073
    0x7020607060c0e010e010203070507050603060604030209100315050106080a050a1803020604020909070e0417042102030705040501051008040606050909060103300315050603100801050a0e0a0f030c 86
    0x31458403001100c0c0c89120419903c18005000c0114032249079040d034008018481c0010800719009080e00c4c0d040340c03401d80f40d407a40004150a402903400080d000800c0c901400001124a240401124030482080700000b00c080e80020603524280719100100c0d510340c0c0032803a444043d070002da038081199030380042c81d600c4c1e0395002240e60314132100075000f50b08010140310a47c2003040120342c0c030a61003802444898501582e205c1c542400800180ca03d42c00501c21007514501d030b0044800070b100c400c40c00e8030f14a28200c4c40c11000c840d8072004034880d100b1070000145509180c001d040c100c0c1e00042a07404000c4000e4000e03100200300500c22130741140e5130300d0040340c5d61751200311040c01180031500804541d030540c6840444450740101c1c9903201450709014254600e6000c00e0041002100e01d000b00d00d90710b04440702500502c1c82c7d0003c990203c000b00c01c1140d104c070804080b008030342c1d404009200544a01300307103c0840e8005410103c1580000030f6110101c7d000c044001000b92180c94203064840c4140c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 32892568 1250 32891318 32891321
    0x6090403030b060d020405030f0106050a0b0325050c010b0a0803040605090f120d02060703090c050103020d020c011e060f03020f06030903040b1306090506130e090a140f06011d0c0702060706 83
    0x1300c02011516078040b60912079030030200007802c0c079414100d0003081502e090800080144d413462040c0e0003505400400108844060840d100718540c074a1640c5250241185024045800541c0800400e43c80d08041e801c50340307441c2120760304840301c450246140900741001201d07650f0100812542100303000305400c010303403200b088803507a440406002d010080642c1c40c0007801c1c200003034020030400d13007018601404034848080070811100e003400c005039581100031540e00a40030321095529a5482c00b0a14181d0a41094107400d842d2504842004110703164440161800060300020350002e80202c2e482c22241801c03030080d40c21001240850382010346d0344103401655401445501c420b07101409040080301d4000b4110005848116100303414201440d6003105020f103035204141505d09c0d420b007c101440018458103030543d82180840c80010346248641c1d644280c46d20341503800c1d101e500000a54284440711a42252904122001050703d90300810015038024081c2a13a202208000306800207200c2d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 32893818 1250 32892568 32892577
    0xc06030b01030915061d090c0f0d05010903080a0c020706020303150d0807030e03010b0604080d03050a1b05120a0c1b33061a040302120a020415080d051206090403030b06 74
    0x1800384c08140300f400c0c442d082c0382a1111100c2e03060541a1903043c8410880d0201c7c080d038100d802610740d0b500c085a420002940c00d1001c12020380b040d480c1035400028580d0014100381700b2200c5100602415201079022070790b668583c4281001038100340081131001d00380c0c0c885500008001841070040b0111515030304030a07030225800b20041011400480c0712420203001d150000101158110b084c28502442c46407176075400d54002003010b954200051108140f5408120304030061070000305100310600300640207a00c182c006d500e07800c450301300003031038003155010b480d81d058940d90b074421801d50b01f00321040214132000c01c1100c501681b4011a00c1141c05440b544641070441404d039116420410340b4803088480710303080058410f040460172468048007000300c82c200ca9041d603148000d41824028503040412161009522a050008807504890a100303a6070686126800361900031a000006172854810300b09214013540c9558002025842c0800e12a0b912600a05020445215030720001d0380700e900 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 32895068 1250 32893818 32893853
    0x30c0102040803070c15050702040506130f02070606081c0c03021903050702040506011404051e090c0901110a03020a030e0d0c06110c0405040807110303070b090a0b070c0c06030b010309 81
    0x881c1030401e02072018410710090149001ba81100e484007a0014401d10540310003034091522b0f04081029034403090081c00d0004509034003080080795030284403019500c109020b0300e4007810178030040f4a803607005c100c0071840c1c3c0e050403a1300c10943c418031040d24000403400c0705a00398007441d844c1f034140303032020505c800525110f960365640c0d80f2901d20420044a01c0909224104134104485016101b444003c94081d01e50444201e405d6901c0b075515044400d910300040307900702d00d40c0024400484807810203002e00700c0c000d88480110540040c1d80f180e85440c1e000006c6e0050b400401c00d000403c1c01041c542042640141228070340e041d0980358800090f0580d03001e0000544440c040743c49104003403001403541c04040b00c050149003030035121092107016140d406400810045141583e659003002202c044640c02520000913203052070060b9112410007800341d807005140c000240c81948241084200e4952044c580441d6078144217040700180300000ba42814580d9038039004c001301d1170400040040c0d09 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 32896318 1250 32895068 32895073
    0x3040914011706060a03060b130212040b06060304080901030c09030203030313030801060203040812030a02040f080604060c0c03051e0412110307050616030c061e090b0708070f050c030c01020408 85
    0x149041400701001503002c01c10302e0103400007014805650740e030003e84411643c10800210340e41d82420006503400350101c0b40c210f8403a1000034661b90f800c090710a01da2256000c0c001e60622685c0395420700620388802c4034000c20084042003140e405600903400303100702031014900803c003a51651b003c42d00d16402902c01104d10207000216004151780030306464058800351015500301450840010b60390740d80d45201c0c828002c0003000203803490340140d042e0340080c0042c03101c020219540701440c130317150082a10162441410006803000d814044c031100140b07150f055840e245001209640107840145414081d050b08104110002d6620140c03403161420a0040d4a4402081c03c1c2c10105031418400e90301c07141c05000c5c01c0c046103440440c640b184001a0740c040c140080c0c001c0c150318007580145511001a031303500460b81c944084058091f4801030100c1e22035002200b41c2d484900b0f0039190150212403050000d03a54400d031100b80d6109801900c0303481c50040480e42004210503100d402d9130001d07081050180d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 32897568 1250 32896318 32896321
    0x1020309070f0f260303040c15020321040309030203030a02030c0105060a03030203120705070503070818010e06270301020c0f060a02040e061c020307180b09130f020303040914 77
    0x340014070900004280c10381c1000701091034400b410381d48540e14441c0c40c240e2104002c1d1198072140c00000701920090f110190790307036031400d803500e00040240b0f40a250144c80343c132400390a4441c0000111001e40001c41c82e0810340c180c0c490213213000804000c10840c04c0080e0b1107800001618200040c0c40c11a02d690055070711030302c80106150840d00003c02d003d01ca0181c103801007010075000b00c220303a264061211400e001d03039950002507440d44150100280103100018088017030021131005402d007040c840c8551072407548688011500c2c00d942c1061603038080010041e05108140809090722a4a4092082e41c044000c1c400064220780000314490b0240e0400e06a02204a40038048113034448950101103040c98103003801186800001000140250309041d103555180301c1c0b48580070f4005074000d00f101c0038951a00d0424203030f884054112903859080010001c2c00c1c1c5000c0070070500c110009480540d50307100c90384032000324002c60030003a6058041000046003c400d18061042608049420b241c1d86 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 32898818 1250 32897568 32897581
    0x40501060e0f011d010503040f080705010f050112021005031005060c0f060106020604120c030c0b0414010b030706080613021c0204050f010e030a03111c0c1103010501060203030a0221010602010203 86
    0x1118141c501c01070400c000744104c50ba04d1456000074054240081c64165147ea8441c80c2410394030406a802800510000c41c0080c201b000c1500407480f100700030b071014442a6a1030708260000192040c00941c480c0141c1c2919031220b2040c00038580c020310070321500c11115500c0d0046901036200700b0001c02c1c1500201c031452901d007000c11440d03004000601c0280900c1c84c26441d0303043d0080d02c9aa2140030041d9010044040c144140c580403078141c5c01c800342c59000d0030035103441c14107840c2d06a45a0402d509008070b41800b0b1034081402c0c4200c86035078686040c6642c5800c00c0082441709030313901002050f42444124000b8034a002c040c0c9079084001c00052b0364500342010815010840348000b8100040500440c000392030115480210316454201003800b8820031072801e061800440c403051450010710420131805512842641006004013a81c2009869070800e0500780c982c00d00945016070b00402c003040c0140140d50090003060071401c650940c00c0001c050b100781d000400e0380000c0040c2c4d008410b1000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 32900068 1250 32898818 32898829
    0x80a0209060306060a0902070303020906030702010903080906060a0311040e0a0521040b0d0504030e040f140108070b031f0f0906050f030c011b0501060e0412090f05010c060903030b040501060e 84
    0x10440300031401820f00e8544000007420101142c054660f6a81d008118038007058001c0c0c040c0d03064558000c1c54140c403481c2020b4001e00906951406a00240a010110f540c4c0350021031018000c441c080e2034100800d0954645041441000305141d801c0769450820700b07154103050050b10034461260005d03201e01d07402511040400a501c005504001104020800a06107130104683c000041e00303102044503521401c00791808a04034111a03001070070700f80c0c41c0c80254403603405100c074060410002c406c2a62190765483e5500307070b41e0203282920041040440c041c5808a9014020021b41100300d00744640c0300c000c1f00c20400e031503138032450b00162a0f0105110a140c40c0c842501300350300a500604401d411180000c10703179a800300c89400301c2d084250468003807007004c2d00540d01400740d00da190000c03420f091a219003007240e07122030100000c2c03c102000c204000d004400c5000c8543c165104054a045511140000d0543c0d10048007859540c42c407480315615240601170080c0540e44074400c0401c40c1c4410b015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 32901318 1250 32900068 32900071
    0x3050103030f08011401110a060e0609010c0810050103050c1608090406121a060a05040603050d030e0a051b040e010c080414070e010e09030903061815010e1603060b04080a0209 77
    0x9003030104041c010b002d4440345c0300c4a5084040c0c24139104216501b047c51950801d2008000603220780e00b8142000804100020780c0c0e8041c1712a6002003200c038800140031103d01e0402c0d102c9800418840a08002e41c0d84039400c41900203000c2c03107401d8030f018071074032031070f03100d1649140216800d03140492000030341c1c03505110310002045500020aa407000541d50b103c0f0060349602c113900d40154a001103071558032070a80c98809041c2c0504200400760320307070801d25038403030310a840000060309004036a11800c2011520204542d4020b0040080800ba0705106445104210060fa0400d80c0d070800740128007424001e036101032850740c4030403c0904113401c1c182c11000284407070650a070b00c00380080200d90b4914049074116000120012115102c0c41b84503411841440180b961510070b90040c0b2081810011450064101440c125000308448d0010b00e20740c10000d106040b440c418940008880b400200744540e101e003841c4c600015001c1c0c41d0300848606400940102c00b41c0d070300150704030003142807401c03405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 32902568 1250 32901318 32901347
    0x301051305030703030e031c02030604180f0303051506071103300702150a02070e01050405010b04060e030f01060602070303031505030606010c060b090c0c0c150a032a0305010303 78
    0x60a64416600d40942d80d00c108140141056640c46600030111002e100b550f240d00b140c56214142100503910020107504152034803841240703007540b049842d03d2200e40012031103502030086100e140301a14154000c01005100c054007500d0300b50442c1d4aa9a40307002008154880e082d140506000b5505151030301428000010014015000810302900c601350724004403076882401c19030f181c0d16403000c16044a0800345050555101240c5507149a80208142c4196008001b0100841e07a80e40c4c1000300780e81081c491285414410001031200512801c56190707210405411114601c201d1403044d03084880c142d0050006030450b0405000b015818003441c9041e0b00c142c030310042014109000240c548901501c281d040c0701200107904204051074020105020f0001d00740e100600d0240911400d0f0b50180341c1c4001140184083d8114500d00045500e440000990b903850400c100d4917802d5000b030a546011403012400e400401c2105840d01003a406208961780d80800c4a500d90f00c1d02416000001200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 32903818 1250 32902568 32902591
    0x105070804110f010c06020d05180106050f0f010512091c020a1109060a03060c030515010323060d05030c0309090105030706120908120403020c010912030503270a11030105 75
    0x91002084000d242c40c6000c0c0d1080b100c161114000200513510000c1c8040e00600c0c541c0081007141031200650320140c4240100ca0303510100c0000080598200e071200e01440b079000c0da00c040d0314a502d00f000d41d83c3c0c10600300103050141c90000c1d10702c400050020200c40c0e42840e40d12440c000100502469190406e028041c0000c000001c200d5461030304a481992000d0300038040f15000400700e40c0e500401d04011a000f450030003a8034030000c4001d018200445480001c48003440c0d5a148a52003449404000000701414801c40c4012154100b0030b1040a04040c6d4015188000203002c0741f0300340001e00046100000440d40d5041f240148004800141c0c02140f0a41080808220329500145810f030040c2080b0030025183c0150f10304034245d4092010600d00c0c0075a60b00800c0101758000420f2641c24000762614101c4980d100d500d07414142420388018000307213062010644c21001000d0074400941c0c00034100300307803c60400c0c4d082e1030311b403d001069802c0c02e81803d803c7c0e0642420300c1100c3d0003074282c02c81e = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 32905068 1250 32903818 32903821
    0xa0309120507090b01020a0f050601030c0e012702130b030f0c0306030a06020a17010b1b010b0d03050c120f030a06080307020d02100e100f1209020312070f06020301150201050708 78
    0x160103454600350b110f088622520391100321001c0c0c0c403d0280901e101d0380900c1031800014503003042c507a500301c00d01044584060001005c14020706200c40107048401180c1c517940040c045c003242d455210400c19000d207403550240204c40d20684001e640a000e4101c0c40d0101c1e07182e25211642c42200480506a1310031101c0805c280052901d010800341c4509030010300c056503c200b100310440300031102403e00d04000040000204d84800c102005007100b6021011000f403481031280150308a5014241300c591060200000304006405140500911288a02598400c0d601d9803118813040c0d011484561800600008000d0300310802e01c25180507100c41c0001758188a40c179404114801c41c40c81001e480391202c081c25032030740c0d481050100d40441c400380c0210049241c10f07001400304d420f008409004184445054044100383e846415000ca400400402040d005c6c00040140c40e8071070b80c0256030001a40340d500010400e2070004600030300708292140a400c0d03106100030f084580261070401002900300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 32906318 1250 32905068 32905073
    0x50d050303040b10051005030106020616090501140f0a1e020309010c0303020d2c010e01050f0105010f1e050d060b16060506030a050a0602090330031005060c0a030912 73
    0x150703544079a1000d0003044580300c071803030204c10710403d40c00182d01c82042c825414a00d1b610801450498410307408981d1030fa110078918548000c2c1c0d494005000a0308030350f00700b00303640c480c00c00308004011403030b480e91510031058441c4403254003500b1000003089481052003132105c410400100382100d9480036500300400500001c0003c80800c401400300764000c41c00740740b09801a407010401900c20801c440c02d04180000207502201c0c1401c0307101140d4a8145600380f80d0780306000c1c407803081c244000740e000c1030381c24a001900c060002e0384c1c030101044101d060400444008403a0140c040040e81ca4103a1142407600312402950100c0d00121984c100c14801d00004100aa80000045610000204841c3d56100209103003220a00014219101d001200418000c4175801880c1e04041542a10314a85541e901d4620700d02405000c1044a180100b81140304000311001d9038001034030080c448015a90f0750002012034110040e440000c0c2c006044480405802514240051003044845a0710b00c0707864 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 32907568 1250 32906318 32906323
    0x2030a020601060c030e0405090a020a050402040608041b0806090304030b07050a020a03030e160603020415030509100b030a02060c03130609180f06030819031112150f060a02010e0601050d05 83
    0x43c46901e0034418000c801340b04250040458201c51a4003900c208110315110880c2591000b0000c0103134003968020030701082d1418280226020748007941c842c0c031540d443c3d59076030200341215213540101990441c440425882400d2201c0e5001c0c120303410045031200c0c00d5050550103004080e00d100113001003009504406500030428105c0c1c25010b00b000030702d0a92580741e807805d01500c4102408818803503030010a20b43c0d016400b40c0b09481e90564090131512181c0030aa00f12441034401e0502a801030120078282c120030741010300031310303000760513240c18000c260301050540d0056442c078000e940001c56560800d4801c024007500400c02403514491b0246400060501e113131210503240b9006455949180044010350408001541d00108940e0703541d00808110041d085c004c584000000c0c1080e8001c2400311100050f10412548000b42800300e80340cac41c005014211050307078001c0d004140318a21825558985c000b03441e01c20029000851f0103c046d04110381041c0c016002140704006100c405400314100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 32908818 1250 32907568 32907571
    0x5060f010e060310090204080706020c060703140c0a060203010e04150c081b0405090405240103031b0201030b040905010f060e0408040e061c240b031005190203151002030a0206 77
    0x2c0d10310395981e4858184014400541740c000030b8001d0300010303001914020001d0b14500b102c40d99804e032030004e0348800801c907061090300000703030006040014110803110310f44020100f019200d811113400710380300d5860340240c0c1c00c04d134401c4174680700c1d2504110501c9000324146e842d0302032542040182c65000040900984000340001c070000503034041004800541508a0b4042c0600030804134040c80c0600d805555809101881d08880b44140400c8100040200c50f55050300d600d40c59035008007a015a001551004000b0183c1c105500c0308134a12052701c603845800c51880c0510004100703401c0011480080d541654003d1030fa40ca1420304000214200109075016580c0120b502d04181e00e0b00000212424800c1086541c0c000341000c96204100f04c40f04105124501c00ca40d00d03040148e0101c1750811118080107250300758102c2e05a04001d081c050703015036403041c048603d1003840000710101200701d07041100c1020305000c6a6440c041c0c9860b20000c0e80190043e02d10082d03240c0030311070720000d468410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 32910068 1250 32908818 32908847
    0x20a0e07090b0f040509040b06030715120f090b07030e0607021f0b010e0a080307050c0a0303021b1302040905040507090b0a140f060c0d0e04020c0c06070c030f0b0a05060f01 76
    0x10802a082d4200f050842d0001c290041c004c4405041c01c0c24880c000e40d80a0312080e03c2407040b183c000a515454045080384008581c4401c0c5140058001c14006881d6140d500003c07207030303100c07451000204090901405810941d40000f5030000004d19180703000c101406490540d8000c42030714111b02c0094041c3e9402c0c100200d0041003181303000f00107823200e03140039440a5008100902c0460005000400740075203d005008681003020b02e2000e210889246002c0078005070081c0a007403854030003030300f100022050301170106a903540c200c0301d001040383c009420000c203068440090006100d07080202c034018001e643c0041028000540004040e081d4070700c103445409201d00088191980c9000140200b46000340000395220807080120340c03120f404c185144049012440b0709520b40c1014800d861000b40711b10018036601290000300125038100410458039841e840c040440000da00140c850f038100d10460740310707055080610002c005c1e01e00081040b0b004900400401403d03a911047e034001021 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 32911318 1250 32910068 32910089
    0x1204140d0204060302060708031005091504020304140d0c030801050a0b0304120201020904180218040521130f0608010608041e0203010e010c0e0a080a0803060103150f0303020307020a0e0709 83
    0x1003051000c5409410243d00182d440f00012485c0e0041c446c060004505c203405454200c0c842c00d407150100026110162602540b03400410806040c80c102640250740040c0143c52400342411030482262070107a40c06d2500c80001e076042040001c05401440c014090001200c8294403941482c00380349207400001c00103010302952210710b00c2e0040c006e604440d40c141d0090018005000318038441d0501c6001e03180200e000300c81c8172f07910030620707040192544d01665116001d40704e0160441102100780b80401605010041b04005090340700865055240003805528000c5003011b181090281554034146e20031014000a4010030000546000c04101d070744950240c3e81031060101c0c000319004001c080e0560307140d50302c0c01ca0f111058941081c07201c41d0342142102d16040d4151510700c00e50302c840801e800200b44c3c40c0140081000d544c02030f000417041007580390079442c0c1c840e40e5461103220088140d00640c0503800005401055042202c007940250184170800d110600701404014446a03041c40364001c901c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 32912568 1250 32911318 32911339
    0x170f0c01031d0105010311100c0f0305031b0c010906060b070c05060d110d09120e01170408070f11030106140607060b06040504020408030c060a0b10080a0f0507030509120414 76
    0x82c01804986000180840000c219660712031400482607003ca004040c89109401007c100c014403a54191507000e0b0700450344071f140207683d41c090340d294102621211290215003000884042920064400310758000008035011a2504194007160082c0d080b0704621041003043c81c1c0855032400503103044600c242c424a980f2807135956000020058445480c0890a000445802e244015009035111314001c14904511181408040e40e00807134044266000c110500801c842200c1c004075603c1c0c3c0b0034040d440042c60426269a540030042401c0000c980208040c20034030010f003400d1090744003030b240d003049640311514070340d0000d40725025006e4028041511004050072548820090f20005d11016200b551038035150b4401d20344a80156400003045c0c0301d16070004440640ca40103051404070f010b0303c0c40d440a44907010803104044001c0400b00c103180c840e1105090b0079281d205242c441d07401c507a8001403500f000074045080032880d11321961002405d21050000c41c80d06140c107400214201e45c81e0340c88 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 32913674 1106 32912568 32912591
    0x70c0204050903131a09100908060606030613050603071a040614030114091e0f06010e09090622050f0c0114030f0a0903020109060c0207170f0c0103 65
    0xc041301c44204000d000040b524014010110141450250540701007400c1e042d254030f00800007448814200b044c004140002500501d007211030901c1d6040510000c2c01e00a400c1000d4602070390703580c01060035580d003005280e00410461900c0080da803030303140700d8685a0b0030070710641c7c0209804100c8109120704600403203069901c1511600540302c0e458041c0000554000c0c0400d1404080503410800403548202c1d280c0f2450418030100311901d8110001030886001d131481da8000c69500b010b100381d501c1c01055099010200248021071421000c1000b0121641c03108003400c076005a81c4440c842100104154044002c2a22410f10425a1a040261900c400ca03204071804403c90080707804402c80b41c00c991481c6001e840041905801502e400341200d00149251026901100041041d881054004100d0105410281603506403248480c0c2c0c4940d59008468101607843d04482d1742c = true := by decide +kernel

theorem cover : BRFrame.Cov 32733818 32913674 := by
  have h0 := BRFrame.cov_init 32733818
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 32733818 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 32733818 ≤ n) (h2 : n < 32913674) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
