-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0138
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:03:29.65864+00:00
-- url     : https://prove2.me/submissions/959b5213-d4c9-4797-89fc-77e0b8a2ebd6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 24640293 ≤ n < 24820149 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 24641543 1250 24640293 24640309
    0x105060307050403200a030305030907050f0a03140c0306100e06060316110f19031701150302070c0f030b010e07110303040201052809050301060801020903060708090a050303090312060d02 82
    0x181c1d015001844400045c81014100380102e43c403941c0200d0404408000d0540090145210382071410480d44420307150403e126545590740c0e0101d82201c89440180002813100b40a0b40c0014040320445030b00c0d603152400a07203000b2041d50605094130038450305003c400f0001c400b841d0f10540550b60340d8a1428103c0c0c1e05201054204056030070803840004146c034565052003100c02e02c9a142c02240ca03131083d110380310900103a00d86400c4002c1070001704c1c10340000000890143c100d035280344900941c60300c04107083e4041e500999084402080405c40420003032040c0c002400a103000301050b00c0d0780d605100d1171088894000d41600240040300303044000000c40001200d07801603081c81c1041d2154030340b00c0c0481c20031204c3c61292406172503002207280071550018110044800450003400459607403911b0320b080b80b06e0300d507865406802c40c000050005000302486034200151004459800e0f0140c0c40e01815174100741c0b180030700303030300000742c2150300e845141d800750b030401c10440303403901c152603180d000031034038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 24642793 1250 24641543 24641549
    0x106120812040206040305011103010905060301090f1209050405251e0e01030603080d09060b0a030b0406050c070804080c03101e0c020f0d090518130b0604020403060903050304030801050603070504 86
    0x207108500002001c54039140280c0c3e000b1035000f002800b9042c540c0482c00c400390824000d03004540d20b048000f4400b0710341400340060188e003080102c1ca800c0303d951134020038040a0345943c001d0214509000443d500d0f1031146510811000e10040c105441c0b03801c0c0d1402a858044c5082d040101240701c1c148030f80c61a003052015280617040080954840c50300680c05850710303038409460104040f0f001c0d03160740c02c2c44c0c003c40e4180380300398010810b102c1c0060400600c000b4500001e0110007082c40045c00007000c0e60f0090342c0002103144001c0c1000e02c01d50f51070390664010341107015a0303007181041c0e00b410f0a0400501c2102002100140400b06018404203c04800711070f031a149035032070703100032182580240840c4044040b400143c800e04007019030301030101c0d88940710f0140a944000c030b0450600301241100d502035490700485000c2c000242e00c8814170301d00050101135025500f00000400150f9074858003000310304c00d03207030f80d512882c05040181c00050305a00181c0103034002c0003041095a8040708072019 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 24644043 1250 24642793 24642817
    0x901020432061e160c06021506010201050c0f1b03030403020a060b04050105100305070e04050705090a0f0e070c0303151202030606030c0913030903020a0b03040c060c03050f070303021e0a0201061208 87
    0x1203049500066200705512280174144039001500440ca040e808126203911030303050f0301c5141445d15031800480c200c42040318011500d05043c082c151070202201d004040c01c1c041c07613008031030244000035140d041d40c1c0103580c120003590154080c44100440c0340203a80418200700da04001d03541c9003502044401c00e01c079001d54101079880340000c14560041c5001c0360160006001000310b440c1c074900262255008141892107005007110015078680140600401e4a001c000c0c0125a0385a0300c0013501c902c103495000728241901d503c40560f164002d28020401444103109454010b401e40c0141070030400e0250025000382c200e508140502d0b19240c01082d000130110281c152610742d00e040860700384945420003540b0114941c00080d81314080006140141d00a822215040b9665481681d416200c4c1c100140801d8040c071200f00070b9000c3d80094498240070781030140c41c0641e001d02903003030741d8041c0132803908232400451a50516542481440080c019051007020802d107151140c0640e80542402600303 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 24645293 1250 24644043 24644047
    0x100219020906011101050a0b0102010b0d021804051c020304061b0f11060c03030901020a0201061509060c06020d0213080607170a0207020604030b040501020c0105070e180901020432061e 81
    0x202c030b07489400702651280042000f08510f06041d01090041d00c100c0442500643c20215401d802d403a150004940056000382100b4056516100b501080c20f002441620203020b8140381c1080c583d040352007154524026800b80d0340c0c481c20440e02520490070000c03080036105500b008100001c9101800c0701e01c031900003504075140a1420b000038038920800214000900010007440514101500136090b04c0040307030020700c100c58450b15191f0000c036841803040300042090600308607103400b4461040455004881c05854900a5940007050b81d200c4c005041000c0000c81d01000750070030070301215800084038a007020312145001c40c24044108003600308803449130300046000455980104035030045901102c3c0c0e10562a050800714001d40001404da03d00e5400d090005003110700c140e00081c00d40c113000742904100421900c06007227100e4000c0055070150f40c2000045299140044103d00c50300b0090003294034000c00903000c807031105c3c0468400c0d016600620034410a0080c81d000301201580b4003503515 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 24646543 1250 24645293 24645301
    0x901030f06080a0c14030105060607030503040f02090f040620041a0c061f080304051f02120310081204030807021005070b0c0403020405070807081501050705100b1002190209 76
    0x2038010000d0354040e042620484821008102c015102031040f5221018415890b490070810b02d0b080c0c9104450255020204010540000b402032010b5500310340596206e03030315280c403580440d0f80f40c2803e94012515079851004c07c0204040380c011a1030020440351f000c6007194158000100c2c500a41c000c141d102480700e081c500d40401e480f015076510320003410885a007400c00c2490502800d9511984400d880291500401c00c1c40001003180e00302d0320064141c403040460444400030780d8400c1c1c40c0d00011401228109641c640601010754000c106540e4550b2040d4a000c1c0307824904802c0b820760007100740d820b1000b08041014402a070300d500d07805450f0450381c504120000c48041c4900b070b000a1001e1b94034028407155000c07050145c01924070039a020001a11010300c01d03100c10108035481c10015034414009006034100c1c801180a81c10306040560503c00c41d80d4900d414103054481540c4101c0c0d0355000542d03246001d20002d403546003140060080b210104a40081c0d45500544c06070090440e403000c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 24647793 1250 24646543 24646571
    0x50607061407030903090605040609030201031d0105070302090a0503061e09120a170f1b0a0504091b021603050a03050310030206070303090302010b0414061014071b0b030408090103 79
    0x40d540000022000c60340510b480c40700030b0300030000150140c1c0025145000402e1581c040c00482d41a01e4880d00d5405000385542d00440103050080d40c0b14074400d41c0c00303016a40c0064240038441c040c0305207880158403242000c0a102c0c000c03d00d84d110600c0396116109011981120080c200c2440c01040004181070f075424541600d4007555030b901080078513001404c5407032903034401c3c000445101c1401d6400556120025148400801a00c030230074691014640250010303014801042c03c0822810080e0500d0342d200d254408581900d204140750042080005000c41ea0602c0844a41c5800f19004547c640c15074450540d03a42c10294001c05211000010078200c01d0b44007544c1c0002d40e8000c19461303a40c3e1451400801500b101d08048000d982045540292407078903014030319a0039600c611152199507100200146c44401c13011020a000c0700105500c92003000b600100300c4c19004a004098805500442c07000618079a4070101c8404002d20034400012441012a15100ea00746030102d1010114601 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 24649043 1250 24647793 24647801
    0x30c0708120403080601021c0e01030e1c0903021f0c06090201030b09010602370206090f06070b15040207080405090601120c1110090804061b0506010306020c060a0603020a05060706 79
    0x260110000740c204200c2090341c480c11283c4501c00030381c00d540b07800400403c00c3c0d03088002a160907011400001034244c944d4401d80c01001010410802c41e4900003601c581601098070342e084840000780588000e0095081402450722049070780200c0d000d00c0511004000c0c180088080002c00b0b55032075040131821f680c8242c0029121482c010600700c02940e441002a549140c290002000c21029011010303043c112007445102000d00341d480b8118083d81a800c000c0d07964081c8001e41d80c001c1030f04c0f85958141d00d9140291a103288284140101820089408020262200c65561003903004020000001e001c0030265412144203660802250300c8a070300517101200500c101c402181e01c0d01c840380c44a01d40c491803400944000805541c0140310003045007041d54440200078040c4001044100100d0b80700d58809880c86007004030320707000001c807651a40e04000080e40140d58442c0c0103d0802201d810074002141c21000c14141003050b1880c2da0b000c0307202d00200f0711a203440394502289030710900c4940e801c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 24650293 1250 24649043 24649057
    0x904080702091312111c03020c0102160309140d0206091206040605100b030603030a18170a030806010314060f0f03032d13090209120a0f0204050903040b030c0708 71
    0x50b0030030618142e49044500a5008400d803503280d000451104150f00a0520f01107010026001c0c0094882500c40d003400b03003000041d0103040607400c01c207000d240070087c4007414282920102e07071400600141030080044c000c2d50041c0300e5120b00d509200d0a260f03264a00204c1c49603040ea016500c1c8c102c040009084020466004502409a07004202c10400b9a510091003030303080c10301002c0403545540b0b200c4440d0001300c4809030541c0c07041180c0000d840c048c0c408404000d0481c010400041c0d11b498880d02d0814421403a60107907804440090100340d04104401d600c020b0038a0108503240300c00494500d2090003420a03130003064411030007241ea4a07401c45510001c10007500700e96440110050307200944035001203102003002c144d016074010325100c1c8116004608070a050b48141d50828080700000c0d84002d52003903010000c1070440100c21000d000c8240c890b40a034030300490440080c0140001e4a200410382d5866410810044c82008001000d40e60440b0060b82ea1300d0b00c41006182030551445081c0d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 24651543 1250 24650293 24650299
    0x5070203010f0f0507030e1009110607050f07060e030c041113080303060a06020c010c0b100f03030e0301050a0e070e0c04350a0c0b0a030609050112030212180904080702 74
    0x312014800302e90004600500c054a0400207075036044811001c07600c42c0ca003078522640100305040d800300d805802c100c661501031401050b8601b010000641158001581128142c126911403020340205000d03010040c2041d0038480c0601c5440b00c00292284010100745100e1660703058600f0544d041c1805071002c085020850444440d241c3c00030303d680307030021900284989003a40010034550310202c0d452081e004c040c0c5410961052079615001e02714402092a8008621584002800c2c41d02e1119840110300986a4050303481003e424542502c0c1d00910054089090082040c9040070004054040f149450000310954641030000301083c4250b80c0100c0105c1d13038090001512142e07200020815010f594001c401039921900704039160220000c018002d04480b006c20440c0706030b20002002e60032842d180c005000c0f0f407144401c100300d80c402e8110003215881c410700c12003019010001ea01c40c89640080d802c0c00c2c0345c52421175502c4003205003030043c028000900440d040160400546039010303401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 24652793 1250 24651543 24651551
    0xb06040b0a0206090105010e010e0402060703200a050c040b06030112030512100602010c110d03020c0c060414100e03030a050a02030c0a05010b01141c090203160902030615120a02030c0d0608070501020708060709090c0507020301 99
    0x430b444196280041081a246401864680c20007860542304202c041d4001034440c074190b030f103081d101c01d80d004280b02066040c880c007003004181001940e003000e480341050882c0c81c04511304041d0300900b101c0c00c0203048014400d00c202e1182c07005d040042e240820011a140150b9102e1900300d13800c0c140a0310118042e0464400705000c00ca80b83c070400608003d05c801d0392407030f010142070b80c01160041140b411443d090f810403c90504080d220342d000b0700c803100b0603004907071131b100200c041c542c540301c1d14480c1903400341d40d1890760b000e0a690103030f2010860294423507a41e05081915501002405040c9544040c2554948065045440c1404203060701c000503811102c40560b120b003000042d40c41103803030600c41c80380b01d68511442d10480c402c0d11602c45041403180d150b0394a03104048001e500140904032032050600641480304103d00072080500f11400281c90300c0f03854a000039180041326009031906800071410400910352000326070003100c2000c2404220700c6901d1340c0c00e60741403050b04000303034141d424 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 24654043 1250 24652793 24652847
    0x2010e0613030e0306100302130621120f0203091017150102010605060a1e09050301020d060512010b091f0902030a02070c0509010f06030b06040b0a0206090105010e010e0402060703 79
    0x807000e41c8003415029480f00502007001504054940c441112180b4084080d0241130016007003d845070f131068544000001005915640d1400d2500190076000c810044520b241c0010440407000403c0e460743c560030301d4464003021540180d201d000d41441d07036002d2042425000c481c1b501c100748a0300105000700c054001410500076010448401c505d100380958203121000500e820404c049070004c8103165104590303400c001d00042654605460441700700141c620000c0b80b2560300b031000307140700705915000044491074601132002c0300a40743c9014402e0307450154400c00765143c02c080e159100c03500c1d031055080380e040000815102426608a194064070120420013140a254010085e60b809803480b11902580c4004008803924240140c0d40081d10380b10702001480d010750810302d81e0f030360000d040c0da040030b84807503c2c201550003000d070400069000005010707101b1310038810280942107444559800758102030158500b5200940004d0044000182c0e04090510500480251007070074a6020800c641e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 24655293 1250 24654043 24654061
    0x60f03040f080c0609070b0f030403030c0210061202090f01080604080c0111070317060d050c0f010903060f021201080c0d020609040b0a030302060105180910020702010203070501020a120e0f0a02060a02010e06 91
    0x8070031141c40b0864886c907400070425600480903100110344202d1042c0ca596115030b411005046440c10440075841034150011328489a4001c1c0d1024100100d03014540070843e00401001600141103440055a910014804014013041c5180e0158101e0991941d076a1903074040360041103110368426022030701241000030507078420301c951480b000c0c400d04200c042c0ca074501002011855050028200d5000301d43e4500d2500344420380403c0c850050400e203c00503904d440301019039030b50032421b0400030b50000303003030042c0019011118050100e0070000c00b560a40300002c110840e95105c4003900c1035602190813031440e03803141c0159078006c8c0b000d014100c041d96649800f80d581c1d0310070300940e07205162240c1c84424099500e110b00b4410001c0000034024043e40a86140c000d501091050341140001c00114021880074001000d100c0b0b4160754400d0045407c90044040724614440c510940d04650000086900c001505021441d011140c4aa80e224071400507401400c3c1044c0040881c0503090400c24066 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 24656543 1250 24655293 24655303
    0x90b040303060602030309060f0702070f080706080106090608010b0906040512010504050105070f09030b1305060c04030c050603040203030d24080102070c0609030b0109050702120705010209011d060f03040f080c 92
    0x140c82a1414040702d030319500c05985900084a0007111980110300044e466502e00b43e480f60401c5c081d006840750035031107011070005600780c1e4001410940c0280410000264800c1c541e90041c000c0d4948290a1410100010441c940620408603808800314030701c2025a03a03c01224010300303000748401300d40c503c4050901e000e040300311002d58882d4030b010001500e06000300458440d01c00155592254542180d0340c03601340f0751000d0420403c1c0c4d044407626000081007040a039000b5403c03103000544991075864a0120028a9005580240418001d010058500000f580c0d80b000780c81300045100c1d250140711030008004042c0350b0070906926003002407a00419401040303485d004030806d200043d03c80c0c0003070310403c401c1e01c8020099040f0800400244046910094020b14584141e0701c840318122800d4000c2c0d003208000782c0d0790382d44c001a82007084d0b800010010080d01403410070f481e128210f10000c0c0c65030203104d92007a810725000000804024024080400c10b0b03030300034151502e5503044003036a41c0d90 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 24657793 1250 24656543 24656551
    0xc0603010b19021f140705040506040b07050f010905060f090313150c020a0f051201050103030e010809010204050a0e010612110318030904110304150209091512060703050a0609180f080409090b 84
    0x17054920041803066204004940c01e585002e4406071401e85040c01040c059401038101391040d014802d900e90245800b0300611007000d0040004010328200070030002c16034140500210f542d58020042403a0440703c070b840190031211040d050004443c40d0900668070108400c00095102ca005a400700d00013244885000650700c3c1a504141c560b2a280d000e28201c030400c3c0030103000f05040400000305507226001265001451100141c1415990350100c1d400b0001d0380c000c90000403030000103001082d0712a60382294544002424040288840901243c40c80b001c0d14039081c0e803012414149005804004480794220098070810140f800b407071b5880b030a90029138045910450080150b07031907582500a4035103c217401000c05800d529030a114400181d8903049070b91304012006c0980d07421002c24008507108840e56240402c3c07510300002d1120860750150410450189841c84224280301c21070032403984aa0f0003082004040c00758106800140590f9010441003070419403500100820001140e001d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 24659043 1250 24657793 24657821
    0x507020907200703080906160f080409050606070b0103030809031201080703140f0309041e090f060b10050306040f020f07030f0e0114030402090415020f0c0c0603010b19021f 76
    0x82c0740b014040d0242c0324400362202822940d070503c0f518480d883e00e83c0050401e80000d100401400e0795540d6982c14600c90b0440c181d6903000081001c002600b2140100c55021504507220351900d140e60303654500313501040c04040c007000302800000b808164101304541e400042180035041c00d40c1c2d41c0d0407541e6507107100e0008480390301a080728000b85d1400054035819054080b070185042120b08000e1000415842402c0901511035400e88801d0301018030844030802e0096200c005003600c0c03400d200c01074a0481c9045402081c441c11440051a40441600d401c100111008290003c0080c0307504068011540054400b400001c1c103e0b0405401001620703a20042c0d803141e070303410b8a1301401034441c1030014002180e103d030308100103001440c1c1005901e42c00f5204503038003650840c020705484100c0e003140086144210000480e1116408104883c0032000740880c2c0061a56041000101e030304d01442c08210140b010341684140e61500038013000501d0b0400c0c1c46040b080c0d1101c480c050000c0d1900d040c41d070030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 24660293 1250 24659043 24659087
    0x30914030c1f020a05041502010b04050c090906031609050402041d030403120e060304030e0d0b15090903070201020a1203180c0e06010305040203300f0702011704050604030c030507020907 82
    0x1e00060b41d4000d441d138099258594504061416011403600c00b2060300b024119562800041c100e6900d5216040c05103a403140160b4480c80c43c082881b80e40300c400f0700800e12a521810f1490f90300904175180d081a0b44001c0408140750312248041005008020313000c9108010604118103c1f18000001c2c00c12640640311518184481c4241075881c0395010710700c80d07009070003000020007082c002c0c000c524120101801d807c0c1012a588c440024041c415500c00c02ea45806070300034482403810800542d0080500000b45d450300c011540040c3d660b000221000b848a109101510410b074003076442040e2004100401c1c421001c52032a007410500094000c0d001401000000320708254030070312542d80715580c0a80107100b24044188007020b428010084d400101010050000c0d41c03988510152611040c9040c5c081d880b43d0076803001629080501d0510b910b1410b4440c02c01c4003040c8000f442c25002501414140844501c60a0480e020312803c1d02c0139400510f260244034000c0d42c402c402400d404100d5682c0343c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 24661543 1250 24660293 24660343
    0x30308160503010e0414030d060e01050301060801050105030a26030109020304120804030c33151d06040f0b0409030801090b030a02060316051605010204030b0109090b0403030914030c 80
    0x5901c502080c051076002c02d840740005000146032801c0300c000c21450808490404411103082800c2e12079035007201d00302c003c1f80300042086007000d0040b00e014010300c60003070100e9070403c800f0031303506c1a0b00d80c0042c2c51244141e29980c50b5100c0c0aa0000c005981003095959940e160b80b034a40180d4000d64046895164a00e84070a010703104654082c003c1758035984200400800d81c0782c03e0b03d142d9000c10700c032a5214220140168a010f80d600303202c0c24412005001c034508107641d503403443c0c5c1c404a5000c902e840692088031500ea00201d00f1031540100d040340d0001d509446116910000c1100c46800da4100d850001a54117240d0001c3c49036048803008101445106889814581c0380c03116008000d400c96801c1c40810940120341a0714003540c0b003a480e280c0d04050000304141c80c00002d40c0c50640f02a503000500380148900f190ad024050401a4400d100108850380c640740c001038000c202a0070140d0b20a81d00d420000520000f0758407890102c1200d882d20181000d0035103841118820b191180c00d030715241 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 24662793 1250 24661543 24661547
    0x308010506030f04030c0201021c02060912093331150302031f0e0403031505010903241505030106051005071e050102030c0426060a1808030103030816 66
    0x201c0c402c0100c80f190004640f2150b40580b811003601c0401c90550080300a4900c81c0b20042060041d1261694010542c81c2401912642052404540c02801e94070420107000c054980e20b11a0000803004070f00484d11907284001c2c040d85101c014240c0d454a400007421140780351012000d40d01c840304050b40406414000240c0c0b9640541c18821a084c1c1d0f81ca00d20942009800f95000e194448545c040c800c400002501d8640c12580340303a08564402540b9000b88814541e242c40345d0501c0000452900c6403040c24080040d20001b00da100040620380c1e0300c0b0018031140701003a5912400184c0c06028060b00b0070080b110900070409003d040d0203507103401c400080d5072404c203054164241a030f4580710301e4010143c035480704081061040c2507441e01d80d001d00d580080c00034402188a2104001215292410310300c00c030030080c1c0302050b1204d901480856000880710003082071504040c0100f0b0003d04020031349080b00b1414143e040150060801200010925801a500910030310500c614a1040442c071142 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 24664043 1250 24662793 24662797
    0x10902070312200d020408030a02010221190f0b04090606051002030403110f01140d020403020901080c010906030c0207050604030605160813060917030709050306010f1406071a040506040308010506 86
    0xb50503c2081d41400751a21056450020410400c2030302000d07207001e46945d00e052440d8051f040c0e50005079400988030040c2d092086070101c8410301d45a816400b4100502c10015a10f101c1803003124580e40c030640380401c94125401500d01c500042d005201c108803a0603e000205401e10826009101303c1110b00703416807020003114250380d4044541d15000c4400c030188601009008034031810711104030f03260001c4414610140a1114030108050b03510703401c0d84144240e902c8103a101d0b100941c0602c140b010160780113034200e0103031002894009400303140c240d0f080386081c1080d44045d4020b2400900481802a290009440360310b0140328400c2c450102070040b168000219204840346541b0300b511000142c454000b40ba90602503956610003c0b044500c00850b980162680804503542440c10003071402d0a04c1818014221074885003290382c0b400c11007040fa186d460a16510418000400400300190480141888034680c1d000c4542c2c3c2c601450000c0d81d4003801d88003900401d4606c40002400c0c585141 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 24665293 1250 24664043 24664061
    0xd03060609140609060301030b191118150703020102030f010f0803071407170105040b010501032306120102070b091c0e0103150302090907140301020c0c0108070504080105010902070312 81
    0x5101c603819498a40030041c54101d202e502a444a010030500d121641e0b404044d5000c0e50061203012058140304c0054400710151100c5030b1740c401d08102022041c840c452040d1000b4009030f51402c40d00e55085400334010030405490b040561070301180030710034160305501a6105002c0d0034400ca039039036200c81c0666455100b502c201419507108014a000049180c2d4918402c007014000310784000351603a0325014000c900344400c0b405a9524800c000078806501692401000c003801c0401c440080079180c3c0c8000c1c240c0010800b10060110046100b0b91200044200c02c039407102c000f1174032020b140c50089000f4000f590004250b114815580c811100400c04840c61025540c4485854030800760054001d00b00d00030000000c6c500c1c000d000000b60700c9d0f009005110304c2e0740744050f11481b814001c40180b0603d48640311802a841400302d01403900000690380b07103a1509080003031082e034170000212458400c5420042e11542080000a41c562aa4000d084c000f032081d11055030f40b01d15440c542c000c4030600c1c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 24666543 1250 24665293 24665297
    0xc06060a15050a030204050a12050d080709090b01020a080304050304030507080309060a0f020a0c0603060510050c07030b0414010e1b061207030509010609110406031b020304030206030a02071209080d030606 90
    0x220082281d103004000a2030480c4003418050305041da1030340040c007607074811303440412402071a0306d07000c1c100b007410b10425030800f10b581040c0c8480e0410200c01480c0e07401d140500d1200300c2d44d41c03202a00d5603008001c2101d6131580300600b0781c1d80b480c0c80c1c40e105459402500c8115101c1c03285070b00101d440a0048185d07030038060080c01c040e092412003502158079482000711a0154020140454007003840c0343d20784006840d003910003244080c0f50400b40501000a0180d8008020052090301d02408000c1410821217401803800e503010b0302d603810001410781900c800706d4800d602c0c3c8010100445404140c500f542d0300125500b00d2940026400d1290074459502c601c240700c00000c0005da00c3c58060b0340082c0d04106c2c0d24000280c283d440c2c52050049401480003044aa50007080400c0a9076042c024040300981079040415010100d01001e5541c0c007031400001d110f00808000a85403140c1070b415075004070f822100c8401041800440034190041c0c5003d02aa20300495503440c0141c1e004c1d014403407c030340c2d4507 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 24667793 1250 24666543 24666569
    0x90f040305030415060b030421020304030804090902040b13050a050703020f03130507050303070302030c060117030703080a0f020d240614070609081201080c0108071d03010609020d020c06060a 84
    0x82d651038501300f10502c0361000c125964040450b807400310f4000b9501c194828030303405903c0700b4007410421045004011300811540100700c00d00010300c204050320119866a030b80840d200e4403030310005005d0800d401440b904103030f80180c1c4960a040c0d0b84c05c4140504c803000b4081025451380d01007201640b00d17203142d51001d00c204001180c07002207101119491180544140c4059584490000c0d045600c54901a00181d0020904d804007101c2806000c0c014816086551668036481c4007560300c0e4001d042c40901441000b600064012480350090721001403a030404650340c0c2404040c2e24000c0160031100c2840f52a001002803041c140e04000005607516504c600c518146103500e440c8541e80b21501c121040360700d6800310000240d010b00a0810044071603005542076040c80395040c54002c0740720000703040100320f405100b0055004940e080e11048598485c442800500010a014007100c0d440000050310000c0c1c0349039040320320760182c100a001f241c00c1c0d50b41270701e1344030400604020780e025501d481e26070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 24669043 1250 24667793 24667801
    0x40302090c0912010e010903020f0a03080115030b03070f0e06180a0c0c020603090d020607030c1707020a0f05011a220b0d060504050c040608010218040f020c060114090f04030503 78
    0x81d00c8050031054600900300701c1c041d4008900c00d42964052400d03000141c2d1182c10070010950140003003038080d46801d004040840942d00c00030301c1e8000c10700c0342030140c03402403445100c1984244c1000b258620b003d070490702e603240d441918014081103445180c20710005640814210f251079000701460840c4600307503030000d407210303075000000780305a29440082c40280b08500006031295405903101e19200f101070020901d00740006805d103e0020002c4003054600340c40c40f480140c000103c00c1c0c0341a00c1c0c0d0384544042d5203540341a0728000c03100d8806030004114110510401005400c1190b81d0b02e84404400402c1c00c11000340b0078029903410304040b41a00f2010403600c01d0034203a10a40038a00e00030031480394203041c1c1c1c94980449209542c1074415801c40c2000a03250b081c14001c01c001030410b00000c6103042c1d00c0d10180c0c29171244c2c01a40078801c03a26207034402d44240300754040d40e03403074030f40b6000752100c550759581922845600e10310740600898400d40025045060301d04e010b032049030146c07a040d1031540c0f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 24670293 1250 24669043 24669061
    0x3020c0f1c0f03020f120412030504080105040c051009050901050d061103070309030e0f0d0308070302040b0a090311030a03080103060504020a0f06030203060f09011202090405030409020f0d0c0504030209 89
    0x454601900d42004041d001070041c4100440c844071818029000c0103954055400c0c028102000007070800b00b15445040401148044203046a003280e0000c41180d80c1d0041c146001c440601c2554000da1540d0300b000d0a100c01d11654101c02011208211005c030804100e0400550340100244541035000e01c0c2400100460300b0304030780c041125807091000065141c40140e401040760001c3e684200040d503115070000415801000032404c405048959030050404180060813814a02d60300078100b010710000700e102140250151805400121502602c81140c180010300e8040c2c18030065840c2d002c0c1c2d1450b0349060401280c01181035030940d0365401160700303544419014080c003404c126000300d540f8500048004007210104050308039a83d015071b4904141c810060540c124200701c2d480740c240000100703c90380350003011485641c2d040d60386c0e9810b55545e0030650705502880c2d00851510b800010096400651076005000c0b0030242c0c5020000300c0004030b0100c1d1140528000250011001000b0820b40b40e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 24671543 1250 24670293 24670309
    0x2208030d0e010902031203010f050604030807020d0302010915090318030b060d03050706060603061404050105030d030c02190c05030d03110901050f0d0614030706030e030703030510030c0e0a05070c03020c 89
    0x41004400415005904e0703010070310f0603442c10842c114841c0c000c401400b18443c5107003580014602203d0460a040c1503464079601c0c0d101d803d00c000d01c1006180f0356501050f000390411038495410014244440380303074089072000382c0b208400c2180040d25220f80085013442e01c80c0044103803900440b00811564540046c0045203015400035000e000b02442000000f4003140201c001800c03ca940106101c3d00c3d220a80d252082c0c080115880707a4140030040c04a5100001c504d030f144201441c02190f2038440c0c80059040480502d04294400c01c520100010300001300304034000c41c0d505408a40303188070502001c03011900f010210520f440410095180c80b580f0450203014461f1900c11090701e00716030400f03040d04540d6180d1041c10b140003154414002c900d414080d4000a08241c1018010500c91241c4030707840344180d83e03000f414181d407000030070140c0e41850100d00285602c0706030510441e48075591400004000c03100903507a01e04182c00100c20b01d00c5581e2505c2d01e19072540041812040a2041020744 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 24672793 1250 24671543 24671561
    0x12020303040e091005070f080606030601030f06080a02091006080106050702040f240902072402041703030f13030c02010c060f0c05130906030309031b0b030703022208030d 75
    0x240c4410710001c1a4960b2400d041c0d07010b0803044004050408607226080300307580e0000c0040040c004003e00303007030246400c1580c075903102e02e040b0b41c896566560a001170300141518844800394a20b48840402c070110f00081200c81d0b07034002c45147c071031a0388440e102001039502d801810000345c3c031240100506070090000d0000035100400104100400c80325840444000c0ac40d0203102d05811500030094030f202c555100c014021307642066141c00c515840d2500404a515013010002d00400000310407841e071076064030050244540f010111491600040750f40f0380064800483e1640d040d000300e21740c144201c100111741d41d4540c03540b6001c0d410f55001521186060700c815200151103010102130341d9201c9c4a18844080f8a0b04d0f21514ac00560215071441130080e04642c9946280490038804650000055402c8036401001884031810307066175000c41007802d038000180f60303a000c000c0c0407000f90590060545c1d0f100701441f0091600d80900020a0480a4446c1c00203540042102503414000c40e0414099 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 24674043 1250 24672793 24672799
    0x1503060103111602010906020d0f1d0913030e04020703170a0e06090a06050c04080606060d02090a060305090105060405070f0c03090f030308070206090d02100b03150406020912161202 80
    0x10b40307900d40e406070306951204807601c60120070704024204560300910108041c0c0840d100400030b220202a02800131b40f981044201402001481b500c22540c03218003050107800054144040b80c10001c80c011052405110304070080345145401d4612405d051090307501c1981c03d9070794001c0a070f0865003100508113000d0500038000e6101d40784403008110400032640940c01e55402860b8500081c246a0101ca01c042d00301000711104000801000c0030008d1b003580c20681c1203901e246d07542842c0002c5030081c4036080135250028203a1800088031a00366010b68808d6240c80021700c000d95448042208072401110243d01140b1848001e04000d03100b692505c002d0f07882410501809034941c0c0340e410500c1400d40c011070009110b10f0800184a0b414080640c10000100013031a407400b80d02006519908007442e19030501d50b03202c851245a54003040b001c428404074204440e914205802c0160195000e032070b403280200300d0300ca00300b489058001082a600c40000703d04503a03075802c10200d030015128501040e64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 24675293 1250 24674043 24674051
    0x503120c09030f070602010f150608180708030304060f20090f04050901090309050306070c1203020d1508060c0901050403020f0102070308030901060305010b0a0e1501020106150504080601141503060103 88
    0x2058804010725103c00c01d0440051445600d4000c00a0a441d483c9070074a50309420202c070041aa030406002d04141da104c0e0600b21050381c0c529988005407242190364410900c5555000611a0f0004c80258001c6000b1f20b4144002150201c694096545940d841008082e51581c4107031100949401b92004980c010402c080341c04850001809455041e1506640c9954411141081680045030700e0300034141500540b26628000601a003001207210015201d48140c04070310624074031a90444012100701c120401130701c04103080c40800d1000b64044c80c031284c413070b54001c26202100c07a070545402e200140c2d82e0500d800c0c110f034244003541d1098400b05040d44940c040120000d0403410145218446060000551500c2d60a040b42500e040c0700104c1e020300400c200c03e00002200d8104141c1c48a84c2c08020900100000c0c0100d00510003544240410300c40690ba010300943e0000c0108100c400200c00c0701c2d06662100080750f016540d02c800c1560240010070340034241c40111025560103481414001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 24676543 1250 24675293 24675307
    0x10b12060f061303080418060303020d1404030b01031203050106031109040b031903110d080c1204050c030f01020408060a0c0905010c06090204060311041a01020304170a02030d020102091005070503120c 88
    0xd41a16084d800865004401103403e2213240c005008449030030034034400511060b4950703103020b500d41441524a004006501c04050807204440342224005c691000c80010305680d81d0901c1903e0b1034459550000180c00c0000010b001d902ca4010320040503138060000b45010144010080102610380000b03815015449025000c003070790308003503075100d40261034414200f4013040c09582412010070100c01802622401e01100400324010341d641e240c001d10a0344c3e410b0f10b90b420001d14214a02414650500c40c421100300304500c10340145c0f0840304540215241501c0d41c6004d1019148290301c140f00103103400604018640c4545a14124140a400c4c001209241d0b038007c941a16099001034070001b03551020280035060a201c2c0042c101c0c1100c44050311000c0c142c0000392640308134840d020030300b100c10842401c890f005200c00800103a00500300d03560500210b20190107900107140491084200c3e503440e11610f80120103c070501039001024610f4000d6020000411080241c840c41c803103030080c0055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 24677793 1250 24676543 24676567
    0x31c0903050115051504060903060209030109050f0f0c030118170d0207061a03010c090e0709050603040b0106080f040b04080f19080603070906050d02060c010b10030b0306010b12060f06 81
    0x10003403103844807a010189a0130041401562131101d8603120003ca4104000c0240c240e120403030341c1c00d907941302c07101683e259440400a40907000507500508030380104064142c283c0700000c1c20241c1c594103101605c082e020040308060032907030012080801160810502e00c000b4a4182922000d1450075104900700800001c08204980248070304480040c2d82d4401903201d0424a02d41d540c8110040f00207104000100b0341c02400310310284549100c807882d41003c0344829000780d02d07642c00360001500c250344910745401c10351001c000030310903440461030100c04a00c1c81d05002c68101e00ca40d8024640034000d03150f03079440c1c0070154405002040c00407020702010300e0701117660200c40c145144542c0c1d02d204d01c0c10300780b08043c00d02c8a030345c3c0b02846403850400c0801068a072110041e598503012181c40361945161091140500342050045506c02050595074607110340540c055140e19006500b1110340b80c0c1c80e0310210b0758074030070742041540600721140054000d107840410304070307420300c00703000c4034105240e005030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 24679043 1250 24677793 24677801
    0x4050609190b0c07140303070f080405040908071403030108150a060302090702030310060203030106020c09091203040c06081302010801090e0c0a060f14040b0415030608030a080411030c031c09030501 87
    0x2080c5000b1100007203140041070300300494030140219034280c0ba2086907450000f50f8906c118800103080b02c010003600c80a01c42c500082e10000c10000e0018803807070784c551801c00100d1b40260000c6a07000700740070442907005400800d490507660b0080042103070b50105100c2c9000303a48010407024003542c0300c5d680030005880ea04c15007805800581c000b50f8590505030800e0304500d01035040b0000715031061004020903640001d03a03140d00b11042c1e6400c907054690300191828491865001148002c1c000180030400c103128140c041124156620300c2259150205070000b100344406c8064001209000103000d00440d40e030040301d50a0008084401d540001700108072001c41075030059000c501441c00000c002c2c1d030018803903003040307803441401d61910f400e05414040502542c000d00d03084500e4891484420350107a030040014000c40b40450391075401424000304020400c44048408007482c4500f244103040c00900e504400700018007800300104800c114481c9500c2404441d0b0410440b13810001c003040c8284a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 24680293 1250 24679043 24679049
    0x18051804030206160203030c0c07050a2c010e060405060414100807060c0b01030b090304080307110109090b0306040311030f130509010e041101030513050f060601080c0903030405060919 81
    0x2464242034602401e0180c2440303002003044a0314044002c030001100d03070100841303601c041000e8040da111411061614036012103504001d4021899403000300c3c4041d400141c80601c0802c101580d528038110306260007100d0000e100c0c80f0304088007480070031900c0c46c0c00c0e00a1688241c02510000365252841940c04040340b0584102030126603c49051103000c0f1300348801400303000319060440d07480e00340360f1324000007100510004c0c1241c0c0c010000f05114480038800c072001084418100ca40340d5640c0d09184604d003542c440c0140c082005554009004401c1d40183e81003500c0c01030140a0503503940e182030321400b5103110030031a18041006413209107030850700a04031081840700b02e04030850506081c03022034001038100300404202d160401002940b40b920000d101c00c400c0ca80400c1c503888150003810700c00200c8800429600401c2d603a944210000100c2901c94a0243d803000310a440c2c8901200e02449a4000b0603015007041005003c1820a50012306814501034122642c0641048203a843d03101e241d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 24681543 1250 24680293 24680329
    0x140411161505090a0506040803040204090807050304080106050103270501061206060807060809061311130b01090f060207050f0609100c11010806090103020d060e0d02070602100216031805 82
    0x341c190070006203104040d44030050200a18001c0b0715902c56540c0d45000030802044c503c000000102151900e0304100c1c8401d074840201502c800184c0340003605c0390098007440c000e6610381800028558442c0c051642c440c18007000c0e0b144c2c03060201c010a0f4000e211110b095a03030350b40f1100005100030300c00705e4405589001c0c0000084260070140200c0c1040d500c0c1e030200041003041c40c2806811200030074ad654000708504455960711403640350440b007580c0000c1c4403a600401c60f0407400b1035002d50307400806410303009a139440c102c82d803502c8030311000007601c0c00f0700750051344000018409070a121040c1d4001c0440140201e09058420000500715010913905200040e003e0440780e041001030140400c1441090070450b12610706603000c156100310510011703110fa2078422001e000c7c80490344c4080044107404041e0745040151500c040e41e101e416108800051144108440132280c06c3c0c802c1da500d0a000c4981c0c001c616529880c111049580c100401302040f0001d00d000505948018484d40707a05040 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 24682793 1250 24681543 24681563
    0xf0b0a020601230d03090312050702030607020607022d0d0c050d0903051203040f05010504030206100b0c060a05060a0e01090507120203060a060f0201060306110403061514041116 78
    0x2904028189001a03000e014241c042c0200321941d01d900319001079416005403040421424241000c60b481c000591028066502d00b2840503001507100c2c005041040c001e4045540c96140c070041240e481504940302001600035038411162a03859001072002c2182201d0804810b0b0348621030f0a0409041000120105600c60644803c0280c24403440c500c8070107900348841c5191940d124161110030a000d01d000d40341001000a00b04401ca0080300703091600b202c002c0200f45040d18020355a00419142a007564015030800a211030302c2d4011504080001070140a00c0c1e15000e0945000d0031000e030401c0d81c07080381d000d07002c01c00761540781895000b00303900751002c40c403804c0804000d00360500c6001201c114134010400c004603511403203800400c0383c149140842e641070b44a842240185035941008080f942010300400f16444508058001d490103402c2c20000411600d40e103440b400c0e1541b03d003640040c1d400c03980f4811490580d0202040c00c100354841450464020005600c4605c402e00c111fa0040c46 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 24684043 1250 24682793 24682807
    0x4020a3e070f060507081c050708090a03050d050903090316061d010509090a0b0a060305010306050601090501140a020106030803010801021801020f07030f050309030303010b030f1e060103020705070f0b 88
    0x245060110180300a04060a0900c0c1040c4002d00709540c0c900560080c8500000c0110030450303000200e8800c602c3c01c840444130040343d541000c014240903100c640004a040b004101c8804000c103600d004a541500c60500e010b2003029000c3c0034003401044044540001e10114189407020311050502d01c0700f80011510342420b054018080049100d42d0450170700195415800690b000301c200c0e19451801c54040420390388081c07500c0080c1400070402a00101140d000040c100c1c1c16801640c10b0300d00c00c580a12107580c40000442e2225118420303140014109010800031043c0040240b501c030520384008111a80c40384c482018641c420390098010381c1d030020700103040c225507510120f50b8007002d202400e0010500e40300d41da907403445030102800c4161010185400c10070100200c034034021025017a81d4076581c0d203032140f041d90f0304216501d05180300b02e080002e440c29116103604144151038581d404441e03d41c207004400030341140d6821611840380c0c080102c1c007412000b000741e0041040c0c002603595510 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 24685293 1250 24684043 24684137
    0x603060213080114060a030b0901111305030105010b070203070b0703110106030c051807120f02040e07030c0908060903030a090204090204060323010b060f0901210906050601020d080604020a 83
    0x801902c1071132000104c0000d0025582e0785104010461380c01c00c4588a854450845c6140142850030300d0b9005a02d000516801d48c020340c4100a0482d00d003200208544c0eaa9040010303503901c50440000d5050700480000c0c00407084450141405a0081c5131101c1394001030042c15084415540007919402182c05040001d807900d4200581c1c2c03940301c14102c3d401c900305114043c201304441311340104900c3e110301c008030f0040c0f03599060720300415107412120154144424050007c1158144640c00580400008038011800084450080c1c40c158011890350340c40c80f036031200074048c400d022684144c45920450140c2c0e51802400060350146c0c0c0141700401d0010710039031107020039805050300c03030741481d601c1c0020340c0d034102c10340c5d0b110a03039108000d56031088000100c44c0340d0400386089280c0840400000c550450582c080850309120700070030401602d6110043e65a00b403000309501c0020304100000d149801d190300034000a01850800180c89000b040c641e51011140800e0328940c03122000d1800c64003c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 24686543 1250 24685293 24685301
    0x9010603060f0c02070509060d0206030a060501081003030206060906040603060912020c0a29040b03070509010e1e01120605031209030106090606050a0c0503040e24010503060105090f0406030602130801 88
    0x103003460104440481030f000a9100e4000e07200d031501c14500c04002440311b44a280900b5038082e801080ca955034a0000840f0000700550300550b4002040e00b4005001a054155000150307601a0010000d6541d00c2c0100290200700410700c03038005032500e40020020f80c483c010000710a2103100c296650418000e00281f402010044235840380103418000c0020050308092171081002c40b5401c812601507403400000d040c42158000d80f42900c0010030405c1c0c140d440b02c041e00300c0340340036680c0081120001c8100f0640280b81240c10b00000c0260040e90210740c06105543c0040f9014140424482d41d1480040c0c200307007520141c5c02d000e1030000b50160080c58288508405019490010804642000c400508070b000d41ca02e58828064060802d40500004005a600501c0d20440c09070080c0307000041c4140640d05940c0b5a0f0000710303644aa502070358040c43c00e0b01d21855040e5102c80c01d04040004220000709180e050039080755035180040701186860006003001c42c0c9180100b281d6910b407401e190f08407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 24687793 1250 24686543 24686561
    0x60f0a08030703350405010207050a031d0301050f01050103051503030c0102040302010305010518060607050c0a03030519031e150b0f040305060108010b0906010f021504051c0306080c060717030901060306 89
    0x144c0420b20090141031010100404e01c400184c40e4626a0390b8500d4030700d0080c4103610313000e08a41f1030b016410f020507034845404e81c880311030b0302c41500398080c00c00280341c00d03203d0554000810000321801803200c2d5210342e010701d90140c20002c11102994034a80440d085901140e0391409c242d4001a003030095580500940f40108000e0329140f0319086240a442802100607000310720551000a1340000d0140420500c03500c510700929048a817941ca25002d0700592000d6080c00041c00c501c030b0001e002c1400303440b4040385c41d494224400b910950002c0620010b0418081c400000390304a00f000c51812110000f0b0b1480502441300326039128154206140b5014050384260205c0e8140b1200c0078868a030700c0d582c01e410480a0070040101149001f09a007004850307401c0050340c4210000304020b1000c0020306160041600303001d1038101c0b10381402202518064040c0ca04254089004082942400c4004109035405002070f03082c400502d400c2c050b0142d1040d04d03103004c244c1d103544050007400700c0e0b88034450704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 24689043 1250 24687793 24687827
    0x5010b0a090609051302090a0f0806040303051303020703030f111002030709050d05030a030203100312030902090a0b0102030f030703060f090b0102061e0a050405100c03020309010c09051503060f0a08030703 90
    0x3c50f8542400551250540d0f100041c00c3c0350041900e21664640e1110140a4480341005019450301e41c2049030f40d641c0111425800a41820040b0304508103188042d8241609580a03000148c1152015641406c2610600013005401100c031b5042d80300500c400720b51070740040005a0342c0d043c1110014505807242e00641c2c41620ba802043c00018000800c48040c41040d00b00076840355121008a010049141c0c40501007a0300d440d04420080d03419409822a54821125910107803140e1045100711307400c017541c3c203016a0041120344a44d0949002844d405505454041203a584590400d0120b0100e40e020440d510b45420307440e030440d0780600400303074480560070b800703541410014442c1c601150040c000000d0640d480001c1414040d00707001107c072800c40d6150030b003c0700582c8940100258002c1f80c03160925482c2049201c01144104800400ca483c001d1851030104141c0203a44503c1e80b003d4581c0d030744400d40e10132216081e1500c500301ca0080400c2d101542d198501420064114180c0c80d1600d01 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 24690293 1250 24689043 24689057
    0x10110c0703110906010f0801060f0309020d05060a0614030304060804020a080d02031b0607080402010e030c041107051209010e1323011502060108030f0705070506120106022802010c08070605010b0a0906 88
    0x110261f40301118034112115852b24850051403000c06138002c2c00b10300c01c003035081420440c0c03410074000005009070141040c1102000580da442c0781001700540da0f9030482d503041d002040104042e0f4810503856070010f00080c04815525039035200740b807501000030688005604045240c4420051000340b02c1081c0ca04c100c080d02d411716202c4402070a442c801800241404444503008001d0b4400700b060510034500540200488030008034080d150b0b8102c07160407141840b540104580000c060750076036070303880307410307146c43d005013407200f040085007000b0454002c00c1643d900c2c01c6111315124061003c0e03460446021040d07e65050500d203420f800c0c0703c2c185180c1950b01500040040041c000211120720b8208643c964807034070b60707240c40d40c14900c1980c02a540300d0408542551000150000b89040301e440c0d40894005600640300c040385075045c11103403050540e0140044c405540542c1d81d500c0021b100300300b22440d00308103554076021200281c100f845280004103011400c560801c5012002e0656420044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 24691543 1250 24690293 24690317
    0x501022b0e0f03060403090302120c0d0f03020f0f060105100203040302030703290a02030f010e0f0103140705132412060b060d0c02010501051005131415040b090310020403020310110c070311090601 86
    0x5070860300c0848cc020800100380d8511000d145c401d0203e15128082c407000d403080444108515580e881081c02981d11540f41d4040c2c0705211400001240c04899014000d0b0401c03030310310303140c2400032600102005454039140d40750054444110311802e2092000100051300c2c1e08100c8504d4444040c16000690400303140d400340b0544540c82062903044943c415255811054444099800c0140d0341d0b024076003000309107111546520040d040815980c0c448801200614254402c0e0320414140713108420058014128000105507640c005c1020400e005e880c40d890007480000800c101d4103e1221000181d540768010b200d9441d100d81c0c800341c1e0300d1541c07408500b080307010301e090500d0094920a0f1030600d24160b02c1c5c4940c603107a00c141e15002d44060f001103034036540e54600d040c81c5035000241640c442c0c024042084a04080d41c825507003907031340140041c40c02030005401140140204561921b410800744400411500100b0481000c3e5201d0a0f0507000320203044140150b1a0003e0060b50500104c4c0c1107003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 24692793 1250 24691543 24691549
    0x51201050603010e1f170703061b0507060b0a05090a2009011205041106070f030201060b0403120309060914011a03011103040323040e010501022b0e0f03060403090302120c 75
    0x84c80d001521480788280f109203440849000f045641c2c0b150981912844060701380c2a07010030460110307401070380144100c43c007454620144c000142c1190000c600280031080108000768020507641b080075101e03170041510b8100003007941c4411600070886076101e0100f0200200f4182005101702202000e460030609410000303480003405628200a0b1a600c900150070b02a8207543c8511004010b04101c1d940c0c0d4507402c058050b4070300b04c04150007541c200003000030100c06031000ca400701c940051840014000f042011400341c03402420543d41030751a100c00001084660b03003038420481a2000010760100380300041d01714144080c4219120382d240110b00c9980d0030030202100e506c00d07454900071450b9608801e10040c07030303403810028512240f00410041703040d107512a84141607071801d03001c031119542803410782c4146a0400a10300c0c004484588440c0c0c4071f601441c0d040d011100004c120b2100310a000c40442e02e4200c04850a9001400100082040d410010b14400d003441030384003d13010883c021408 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 24694043 1250 24692793 24692819
    0x1503070602120d0f02030403050703110d0c02010305041a0705090f04150902090d050307230313180e030f03060406120c031101050c0312040201020705061c050405070f030305120105060301 82
    0x2c0c1e8180b060000b400650307580f02d0740c01114030141c90b4908640380e080c82e0400400c560812036049000c2152025143c55001001880550f0045103075200c2008500700c2d4011809040058001c0310b9401c80840c603201c4000c86c0006040c810f80c586d075203082e1076001981c2084040c050313440c00140102d203424885552102540900000d640300d0150243e030f140803e00c0441c0c0711403620203000d8450300002c035607002081300c404c40003415a2645864480b40380ca100240c075481b4402c0418460404000304000c001d4160603c0580486920b511000292810f980321a1801d560040c4100c0799000b90000400482c1d00c1c0c90b110303000150a04000200004446d6503800e4507021590101600080106076140300d243c1c42101102d00e03884c1c0c4402a079486241d1aa08603810800643d400c0340036014015002c0354a0a02400b61245100c41104806a80c511030080800520000e00306440a00441c20040f03101c2800031051001188240c0e01d0300c5d90341c0d610580003107a0740d806810980c412501040100300c41c000c1221 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 24695293 1250 24694043 24694063
    0x40b0106111c09080604080705010606090503030a08060301060b0d0f0c020a050a03030902030102070204180203070b03160c020307030c031b05010f0c02091305060108011e051611010f050a051503070602 88
    0xc004001c2c9a9091826120903111343e0111204d071181d8400c02c010441070380d02906d0b12520402c001c0c0440d0b6245c4005a90001850090541503030003445425080f80c81400c070513410103409800000d020303480c1c048074020360b40400c2c4094aa1074031400701c124201c0040c40303100310004103031020f8204080c96541e499201d0301c0c151000303001c05455070340c05030541d03900b0b5048519490b4010402c0100e40300d08040364203500301c020005d81c4680a00940081ca8005c107108403486040c800c205007495480d600e03429200c1440d0804103070f815105501001c03000074548000c2c01d0245004220044400302100f00c1c840c480110b0b0703001103042011314a01c0c0f00c1d445400c5902c003401070b5130451b1400100d13515050185040c0c0011440a41107104003000002c6504041d40a43d40e6480c030740e030142801350305002e10401501c8090301e4081380c803401004081c05091107810452004004000007094001004088a041d80c0c0d05071a035045c46584c850600884ac1c45c0c0c010303286203d00b0242c1c094101286000d0000c1c3d1901c0d0088 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 24696543 1250 24695293 24695323
    0x1e0109110d0305091906030507020706120903030b09090c0a0b0a0504061202090a29030c09150c030304030201061502010e0705040e07030206130302040506030f0703030f170906040b010611 82
    0x140d500c00b010702a00548000d00c0e0b000c0c3c1071009611700e4840140074000944200c070042494074011444292011528034140d03825926014000000341081200030503402d44141e00701613662050b0b814540d15002014000c00720f0b0310003443d549900b0020003541c003070300703600407200c0c0d80d410060f840409070000252400c840c0301c1d051189504549104080291040341401795010072904c00204010781e8041c44900420078030b0a0010b080080240120300504c000c2c0c2c1e035103601d040144903001c181d2400421079804000182e81c21400c01c0b0b44040c1c040c0c07941d0010794040740584d44525090040103c1e03600c1c031402c1c02040d84004d00c051280d40781c2075074070381080b4050640102d03142c08030a0b041001c01c000c11002142e014000d40d64406003ca200814510749001c124407490801020403103e28001408990000d010700c040c00c0342030324654050369000c000011210a200c600301708000d4005045c2c808603c5040d01c080075061516043c0382c40441000140c000c0c0341070240505000000354000900b0740d12001d014 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 24697793 1250 24696543 24696559
    0xc02060114040203060a0b07050114070311071403130b0403021305070c02040e0708030408060114010e090703020d091205090405090f0d0c0f05011b09050603060609061e0301081e010911 81
    0x2c01d04160a40d001f542402d2000201d0358100141540011680d0070114001c00243c0c90ba004110203403404c1d14082119240280b12844c045041600741e0140c0d041030000302ca14200503120303940c18005495001c08440b85001c6410420750a190400b0381c8642c042c0c43c4200102d24000d100603040d00404072000c0c0c001e981e86c9229094410013080880007900000d002c903500c40d541c0d002c580d50781c1ea6003401441d20030b003c031080100c25940102498030805800403c0314895550340e1808a0082d0403000110b000f650b10303900101c01160314a4806040842e141c0c0c3c4282c1d580034054240070a0b6000504100780d2a84048801841c02c40c0224814440000b80d161a4005080c035061210380c5400408018242c0d520781205804503070a088030140e0640c031945c5800d06540d42d00c10800c80c0600040b514541c014004001c3c000c060f2414100610040c0c09543c60001034010700300b43c2d1030861f04241c0020303d1541c0521502c280c1109060600358040034020002d100c4080d944d59950400004039060380c0c01381c050 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 24699043 1250 24697793 24697801
    0x8060a0e100e1302030705090408030412032003010e0f090c0f03100203090f07060c1101050a1e02060106030f0204050d0b060a240801080d0c02011d0904080d0c02060114040203 77
    0x9066440204500445040320b4109000f9102c00700d07804035012482881780010000d2941440e49681d8443c0781c01003131950941e0741c2d81c1c850104164211040800301a990a0008a850703d0940300035190942110115102d40c10100d002d41000d0f0043c00442810030b885c1e04101e9100c4c1c000031809418403040e206c400c040c0f01003101103032410030b034200e40e9160079001004000c80880d000075410000c0c1481400c564060350b8882041d12680e1240c903014240c00001161a0155400f0703c00900d103d100c107103041c111161280b00810619480140e8000c0180c1000d401040b07043e81c14004d400c4a52543c1c0c80c00c40c80d003454a800256a80c1c001c0030000c004480c0134000070216501c0c070305c2100c000c150b400f200c1100410360283d90106140c00410040118203110000b15140c28000b91030000800642c680007286961600190340b201250407074005c441480c031008006548814003500d010703622400040c4c4d16050a5200c040c1a1182e0040a104551080300100069502c0303400716982c3c13941c15200103136242c503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 24700293 1250 24699043 24699061
    0x6060a11060403210b030a240207060203070f18050913020d03020607080901062102060f0c030901080703090201020a030e0a0b0409060f060c03050a03050402030c0d1203061a090628050703030b0108060a0e 89
    0x20580c2c0b154250700c0814500142f14061300203600ca08255940c0044640500100b62003e036000a45a404c03803040c11024010381c20070302d074099081f104e0048040b003080a103a000230580f015101c0700b00d0040e00110103124400790030840c1982c12124081c000d00c80c140c140460742020340c0d200351110001d284000120404c1d900c54038100c460400c80ca0704039965139003c000d00c040d9650300042405002603032030340008101d03a1080c0f01e0104213135030503405450912941e4800300c03038000d0102c103070701e40c85550200f0020b0b001c0d030503c0040005019092022501901d41600144050400d510140500c4000314420b80044d500104542d180d0b882130600094544460010030b01e402e541d5002c141d00607c80748011000d0044411518440c88259078041c0581030b240c070144143c0100c048044076103020700340403c0000d4a0010003030014100c950080505c044000b540e4968001c0c4110785090204c0c20000b40b80b803d2603410300072000305c03550a007000c001c0c604000303003c0740c1050414454408402100b07004145200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 24701543 1250 24700293 24700343
    0x1a150703081015020304060f03020301030206040b0715020408010e070b040608011707030b01030303020702120d050301090b270402180705030a09020117040305040503010e06060906060a11060403210b030a 89
    0x614000d020103400d48044081d540394040d010347c0c0d02082c1c7c41d42c010303240c6600c2070088a050700d50140070b50b401c0c1480d00e40e60404c0c0d83c11050040b0f540742c514041d044011417092018000904641c0c0c004a40d584202d0b810707900f03052080e0404002481304000c2032003115040a000c0e41100c184125041540b01001403085c2031413402c0d0002054407841d10f00000038190b2507009440e6950080340c1e00c0000c1030314040c0c0543d440d40c540d01031202150051004001c010400ea10031010010060503115400c00c1519102c3d03182c03031f513240449400f090070400b4041507060100c3e90100c061421400307880a401c22103409840b0740070040002d600746844948050442e48103111450310030070649c41c03101d05810700386005020f5410034010103000b50718219180f200d0790706c0003d50b5401150f000e82502c806854840500050f41e104595000511109a0f024002d54108100480c4164002c1d81c45d502e6041000d0310351066400c1c4280703840c0e041d50600b2514003055034081841021507a00401503c058803098412000b00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 24702793 1250 24701543 24701549
    0xe03011803260403050901030c02030c06010303050901090e0a0e0f061014010c061b020c030111070f050c060406080907050d030f0c03020f120903011410120203010f0903031a1507030810 81
    0xc0342c480c01c184410141c100014050a06c0262002e0200c000e0100080380c0e03900419003c00c2050b48031b0001040480d000388001c02c00608180b40125910f5241c0c088042c0789882030750360054140c0e880c0300034030408805004100065508002800745400c3c001d200c003035041441e0040c80303070815880044458680c00f940c02c05087c0340d030003442440513114240c403024001d00c40f0402d06000d0f01400c0c210003038920703041c4035421214203040c1c4524186600d50325210b078cd92094032021295071107920960455a41c82c60083e00085c98540c0ea41e4055140040040b0304145140c1c7c404ea014200c3c4152482c00030340c02c2904a03c4440507440c1c0007140d1985810101d10700384a10402c01c0700c6004024450f943d01c80d110004000128081d4024003040041e84489003500004607807001c1640f09582007480b800c4803c400000507240018008203d50380c5850140d012681e006c0000c4010a80c0e0380c1510403204c3c1e941c41c907003803c55800c075800f5000307482c1585d0200c524426004000c042120520024500541d0407002d200a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 24704043 1250 24702793 24702857
    0x6091d0901140405160b0307050f091c05070f05060301060e01080415060f0302091501082e0902030f070206010602062d0f041e051507031d0105070e03011803 69
    0x4504013820000e0701c41c81503201a01c60300e6201c40020841c1c005c2c003003c4a0040d4210fa4401c0d1a190160058203203542040c0b06481d0f00c08445580c1c200c282651420220402d4025806001c4451401c0d48811403100740345c0c4400c3c003950702400108401c9403c4409070601c11001e007084020742d40e071817a00801001c00c0000b441c5510f0b280c4078003c2150900d294030881a0f80c400d8842c10402d4460703402d41d4814624400b00d007800a04c0c1540011001c4061071503103640e25001201c40361850a02440c510b40f05541a04440030480e03020040103e00082503003169000119400500003e50501400a441d81c02c0249031007180e42e140003c1c2a10f4080001c10100001c4485694080c942803550354130b4803641058400741c0d05068a148003074107100e0203a103c3c403060359208001b454049049180303003070309820090400050607521035822200384241000c030616030740d0850000a56203001d034005048040e454007024005d80c9451000b566005071024000c60658242c100304060041650704000804c00c0d8081c131070300b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 24705293 1250 24704043 24704081
    0xe010903030605010f0c0b06010c020a030512071205090102070614090409080d0501080f0a170d1a010206090c0d080d0207050307080304120507020603040b0c0405040905060105090106091d0901 84
    0x1410751681c03060040d25000d0b84e4000100f0245402201c90075449480940a105640c020584540c001d94101d038003584003a0100354000da03241c0301ca6080c43c0008140d4184890000303403100400c180d0520b1110348810f2410113a090401c103200007952038416000f00c1081c08116120b802d0400c01c80c1c4146e410000d8010000d1140070300a1600344681d42000394030001a0b03040c440085903040000c1500d0f2550f2243d40010034055000b03032038200555000c401445880d00042040201202140c05400c6502c0c01200c0c41050300c023441c0000a18010008000c0350540e004603042d0091640d0f46100e026040d60444585030700d85805179045002446040d000500c1da2100041207c01c00140402661085014500175560140c4044080e26548105000294451030030800140042c0c0300b9505103810441a1036081d0900d40c5600c045012035450620a6446500040040011b4600317060b20501400c136528180380040d140c0b140c0741404c8001c680c0f0345403101030102c3c0010000300f425030000c008080340b064000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 24706543 1250 24705293 24705311
    0x3200a0801020d0f060e190c0302040510020d1101060501050426070608040507050d12030906060305060703090c050f010504062102072d1101030e03070512090a1203050301090f0e01 79
    0xd10034800c0b60710710b01e418000009411107a84072140c7c480d0901c0340310080d82d008520b0b1414000c0501c010042c09141d82401b02160a454480ca1601c2e03130700c0c072500140060028001d000d800a608a0034a079030f9a0b041c2502804540d0b40402a2001c441d21017541c40c3d032441d0784840c4185070862016101c030541c0304e089000104107a00088071400343d4012020b6171580780d01c6a080c002c1e00c243c0c103900581000000824882603511950240345114010000002d02c02c0d22680e92a0905070291000c00000e5151070b070b40303410b010f8680c4120780142400c40b040c9441030161000038100b8043d82c852182480b440c8070124041d076800c3c002e2581c41c66000d540c1103550740220b01d40700030007560804079541001703800c0e80100c0340c00d2104024594a541c226260320004810302c001117010b0048103800d14440d000c2400308000203141004429605948150080c0c3c03100044028049007800d15072240130020205581900426040001c507030640d460000d01041c4107104144420280c0001c034011861076182c0802e20b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 24707793 1250 24706543 24706567
    0x9120204020c01020a030c1404051c020d0c03060c1101050402090610050f070f06060801020304110405070c050307080705060c040e070503060103090212070302040b0d0203030d022b05070905040603200a080102 91
    0x20f546205598880a182008400c00e031120750080d8060342d50000c0085418542c0040b0300c1c680382e04074bd407008045184000c2c595640885402841e07000301c640340d49502507480e0281e0007804100480b01500005c10003460283c0018403800c10140c50310307005241d02d180041c0898454002c603200c12240802040d0f488040340b501800601c0990002e0750034502c0c140c0080781c1c050f01802200c1c0642e40044000c0c55134800c00e400c0200410b405490b190070700861000503000141d091014141440c041c070352060b1103807800d0405c103007010700061010170f90403010027092003854000680070350000500e24110340c41e540c036800103900031b041d01d240180d8060003108240100c0c0c00009184003d481c820750381400a401c1642c1031104c500721400000703615401c00d00188000c494180e01030f20804c00f0840101c0c400c0001c1340500d2854000a0701c0d510304254441d030030081c4254005446c070008003070981e01008928034540f68442011140e030515101c00801c10003840180e0341e400d00820180c6140002150703130b01d0342501c0c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 24709043 1250 24707793 24707801
    0x18010302030105160f1d10050705100e030d0b01090509010905150603061e0d0b04080301060201050108030a09060806011101020409140105030106030203030901050a170c030901150609120204020c01020a03 89
    0x4901c290308000000d0226100032070f440034002600c2e1030b0500c000c041ca1400f175a07000d8000260303181802d00112803404907580c1a40410303407800c1c1c544516a59482505001d402c048040e400a202d540c1868000c1800101c000215441e200035980001000404500100c5125146600065000d24203400204920041d030303200c04d0055030b245001c08a203132a100c0034000c050104590450b03011186400401d480395114076280c0507003000400a1924031111340d650b20f03425401761030654820301d0100052000c1074091195501500c101401503040c41c40780f59009103648540e019000401c001d040c0460103030b90061507003490381c03003100d002035455030f465518100041458808050401c400741000151a040c18070442c400d40c5d4000d0702541c94802c1440c01550307a40d01c10021a410080c01d40100c0c484128022005401050b1020080d80c0d2410007222244c2501c44c154180002220b8034181045581e4100c103100040b200009102c80c4002d00d00c0c00000c1c0207000e614040c070155400007480300c2c1c110760301d640 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 24710293 1250 24709043 24709049
    0x203240f010905010c030306090e010204080f06010315020f0d09050102090a0b04080a0615080a06060e0f060306010306051f0e040212060108070909150903021e1504060b01020109021801 81
    0xa010082609481005102415001034501003101e10700144900d500c503403400040b160190038041203040e41d8074441400c072807800f0056802c595011900380941c16046c41044050140080200100c0d4110b444900c048141d81d0b9044190b2039000501c0c42040d1103070000d0311020540082c1c100050407003401c00e1400303035012000492040c00010740120305d8072890790035942940c840f04003e1030b001145541c1e0400500407c2e6565400801c80540020402c804000003510030f803141e00045a11450640002440100640040c1c0ca089c01201001019240001c100e411030740c00100100e52a100c60b0320390b9514200310b910006c07404210000114956011a126600851007a14920380c0d40030303a15400f5484880a0041989030382010300d080200d9500354009040b1640070b05c403420a40d441c0540e03590b080360079000c001c40140e080f541d5003d00b03403803152905a03200980d450241441c03105050220005190040c0024002640d80708400600e91003544140d462682c050035030b80140d02003c0340200340450900c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 24711543 1250 24710293 24710341
    0x6010e0112061107060e0c0612060409020409050d020d140a171012050c0a0501050c1902010e040606080a0605010e03100510050d0506040516061403040212070902071a0c0a11030d0203 80
    0x207c40001c1d04108044901d50340105100d00300741d84440c030800020b404029404d0368060b0301c50130039201281c000d0107201c4441e0841e4000b000c2c9030304400c001510285203680c079030300f01501c1400050a041e400007031000610084145801c1c040d40c0b4100d6280743e008003a0807000390781e03901111100800200041c60b409d204802c441e0381c0c1d440d0344d82d5001141ca5110b20b03c04030035039401111112640c11880f46400c0d40841c4141800003080c02c122011800f1501158403c00018110b801030012a00e990b20401000e40000e02c2c01200308445030340444d54034142c803480180318540d070304001800180031880794409000d004088000c2d00740c0d541401541c0e0b80060360113840300d00812103404642261a034049088840e00e4451101130000012140ca9580000340180d802a030329040038140140706000ca0005032248580040e00c039403a6040402410748a00e0b04921a0b81d08513080c4000c0303501c040150780d25403240e458165915034403030074681d00318000e42c00302d05603081c004000e01c0000788506501140c40c00e144 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 24712793 1250 24711543 24711553
    0x3090311030301050d020d060e0303040b010603051b04060e060f04030609030f0503040f08030403170a0606020d0c0503120907030b04081b0c011d0415030506071106010e0112061107060e 81
    0x5180d81c1c80344000e02ca040d50202d4580c0440d00107007000030403001c000c0e0140c18000b990005003c06941980d008039000c50f0042c0c15240144021900751003007036000900205507496030304072041c9038200c601c200d000c0d4000348101420203629540d1060b044400d80c1d910341841644071940d0307141000140c101400220701003414010b5401c803c0d44200c044ea4411500180d24410840d059100e841c0507900c041c006038100311b51030031080c034505021380030540a00060400001e9003881c200d8003d00f000031f880c2d02d10041000141c01c942c0400c1c1e001041d140c01018210a509842d101d00301c0251428001d6400140f000491004000a000940c80074084444844c075000c000d001031401080d0f00c40d1030344060780b400300d03041169560441c0d43c1da0f003011030080e9002d080018a10740c0079a0404e5045856403088a00360f000c54100a0000d90003000e810004d00141d00801455051458040c0482d40502601010401c00d1240c0c0c024070046400492803640031100c0c0d02d84c3d481550600e000030f8811425039403064414 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 24714043 1250 24712793 24712817
    0x316060b030d09050103020a050708030f0114030c031c0e090c0903010c030b030604060c120204080c03120c060f07021606080709081b01030203040609060612030305010f030201050a050a02120307030903 88
    0x1000c01c1084072420340f65141c0001604040040d0025007185e002c1004001c0c06000c40740004002c440250300484244000425940c074107002c140356030540c020302e01d0190f0070450b00b0518139100015008041c200000c0440140c00d4403404c1117032400308a215050744505640305010326070b5144801001d03455010340090141c80c4980e00c0940940b04240d1503a41c150f0f001c00c00203004103031594803c00c0382041500e1301c0010040d0200d1550242d8000e0f822200c8680c01011424415241c01c02942e620700c3d00d602d1070241050200b00300c142d1a92070040007640295002c100151a03588280001d040c0708a40c45060100c00362560340050503020200d44a4010440400c0045154100007408100070a40c6020201d501c20100004401030741020b00103d4003e500c6240100001d2034a0142e00041d03d680d05400102079411300b40102920b4046c0e201c250413440d121000e20150b41d000044655190322070a20594070000310600f00d2815038070030100d49445c58048148421183d2540007511080d002c2c1d640c1e0880044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 24715293 1250 24714043 24714049
    0x15010e0708010b0403060203090c03030f040905010e04020901031e02030d030c170c090607030c06060905040b130c050915030f03030108070803040b0409180b04030917010207030c0605060f030316060b 87
    0x307028010030301104802d11041001a07a035030000c40c0d004001d80c080e40c03001e200c0080803a10b0360308a0512080e141c40045000c0c0b0600c580b80c4202030060480d001500120309080d00480e2510340d040c0006848200c80c1c1c09046c0030845d01c032415a000e00d03405411691043d40f4190700030014000502d503880090344103115100b120a5006103940940040c1015500d000040d904101c00c940c08514120140056103a4007804161940b00b61001450703000b0300841d041c41c00346004807400200800114115424807a89800728215028207001d0711402e40b100d8440c2d48a180c618070345103118842d01a414402c00c9c0600350b003140003101946c100c5280c05d08680e402078540c14140d03200d009a000b030301001c0c5011b120801860b03030306402c199030940407075000b0405030305161144911180102c60a4010a00005080060b40302c950791400e28804440b000314144006594001c0c062141000007034546500c59010480c0c80d520030021141343e810090403607949522404000816544411003030710301174a030400f581d0300342c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 24716543 1250 24715293 24715307
    0x6010e0405060f190e0f060102070b0a080103080304060b04020c0109060e030403030e102610050d0f03032403030309140f0303010e0405070f0602100507050a05040e0a0e15010e07 78
    0x144000c00c41c9400c407120601340040011440c012448069403010f0000d101e44e004421035008500c200c0614a16103091000a45882190780c403803e07602d00e081041d100300341e0707100760201d054a511400786640e0361143d040810240004042080d0711508c0002c111402001c1580728446442c40790301c06003c140201100700d03450b80201d01c806400710f40210413801c1c6e1850f00c0038241818440701c2c00c24286141c803117400f11600200c0c03074041d40032410480e41801403000200d114030b0004c2c0303c12940d5410210b00380da103c2c002c0c0313550303040002c090540b500910780c12015541100c0f1902c0c4000390310309145a54904000b800b034005100300340c175140c03a441040c0a072200702140b50075080e00d181c4010f6181da481c0800b20000703034100403c241d0b0309005060000c544030f40f501000b039000304042d40c010f0214201072101d0a040314809048242441030030003462001a4204040d541104c800015055a03590703a0103140015000850400416026041100118144440d41c0506a40300c0180c00d103c10781d42c00800395094 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 24717793 1250 24716543 24716551
    0x209060f0703020c010e18040611030906011a0f04050d03020114070203120609060a17010216030809100524030c040501032a060503040b06120706120b0d0210230706020306010e0405 79
    0x402d80700c1000d4407c50800800301e41c2c106100b4074000880105c22a0140210740082d56401e00c550080001001312040c05800b80150220001c0030518000011a84852506c00c0d40f00e03850080c034000c52150140b5000b0750091103a56010002028189882c80e0002d40740d0b07210300d2440003107407912070205045041941d0114442c9001034105082103080030000c00d0203102c0c004201d5001d64003048140c1440c104d5911082842d80319850b005010b0070001c9246061490628501c1c0080e4a000c0c00c04c10001080f87e024000118000446036180c500400801c1c18074020404094020b41004000400c03c40d1401d0808502001412a00c0000346494a840c085003014865180010014004240403590b855126500800010011400c521100c680e15082015541c040c002280281094000c0702b400d902078409001c030b04803200002003400d0b85c00034400d4000c0348289030400100c0248000039a4841c05888000d00c0340407940da40b140c08518048001c0c0d0300445c0c08d540000c5038040261f5481c02c0c02d0143d0b0f405 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 24719043 1250 24717793 24717799
    0x604060909120e06071a010e060d17090a030b010b0d0b120c060d060801092d03050403140106080304090902010210090803060f01030618050115050304030f030f0209060f0703020c010e 80
    0x200042d001ca0072030380040c080d10880e0b40400108288000110f034024181101d1000300d840910a42c9050780c040c20070040200120300940303040154400280c01e2100c640c4031526070b40003251303c07805400040350000226070002010700030000300201e101e0100301b0182540c6901c4200c28440004124240702441902280c040c40b10b85c030060070403005241c9003014050700d142006000544039600c0f1410760a54036645020344072407040c049400c1245146040d000640c03400100b04281988441d40c00806922aa11002c1c200c00350005c0340d00403080d02034008030014020141181e0300c65499441d158010008500105c1c00340c801c1d420024005110b078000c00310b50b030340c2050419045685400178000150a218205810103640e60307000b16021b41b4010190b02c1c504407800c80020190705100c114688031000440b0301041c82824420000080e0344030307000d894250039500c0c010039401014880c1c500030b40240001160300600110310881c00340110009800c080c0c0c0640d080351080d00c0f4003401550081108903055030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24720293 1250 24719043 24719063
    0x9051003110d09020103020904050a0f06080c060a030b030102040801140702060f01320a0609140604030b0c0c0705030d050c061f1202030a02040e060609070f080406051f09050604060909 81
    0x40c0c02010383c0c0201091070041c14007524240002001400301ca074101e40e085d07000d80d5110180c490b0a400e0b40302d26809454044000d001105c0300e0301c0020964042c1440e017608258035682c06100da51002e4040e28028003a2000074050113410580011000030100c580c20f005100399400075403460401200c840c102ca800c03c9a214002d00003a51110f008428980c90700d202d500c02d07507200314098441c10f04420007088655541c4580905000c2d00080321108050302510640301400705201061012000e540c00007207100034a0355404552001509121159204a03411b00500c00240441038020b0000d05080032200140d86082c0c1e112060071446031345500c0f11150b0314121075402c0c88443d094019915280380001c4c100d0788520000d50000d07003500c03040013440b10700750072060910101d0308090310120780100082c1410028040b41d00802007040000800141400b13440c0c0e004625665034149182c08040b104002c0107502d00c0d2a111120090310007600e261340154a0000c3c0091f42110706d1254070030309544480080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24721543 1250 24720293 24720307
    0x50301031214070c080c0f0a08030f0c0a05010e0c0a080a030906050a021005010b040f050102030304080d05040201050903060a05010608060312070602090f030a11031509030a0c03030b100905100311 86
    0x1241c12104a8000b00d03462410403a0300003041d12640c44100400c52040141360a8503014184040c41c040c100115000e007a5110b0140101070000c01030f681e00b4011003050540700c1200e182e0707080c43c0a82c1004054101e520302401060000070220380b50140c24401e0310a00740a03a91043c49a1390f41c594484090002002c2c406d05010807441800217000c02642481124110311040444c142141c00a030321813510f00030002010007041403000c4030300005020900146040d4501500c03402030b540f04441c40e02052a90f107900140c2103a004905550f260600503048404500c0c0c061001802072a00707020382000b10f144070000800030b147c000340100c04802e8090780070741082c504d6035501000e50003100340039500a2451440c0152620200500c542c010b004880e900d010000d07031400e04d410410094604516107100d00100041e450000048880d082c0d141e00d00791803201e07898203088005000c58040294000d000344202807440b68413080700000d41c0d0049880c400305640c191001e80486842c4646c5a03c190810b000c18 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24722793 1250 24721543 24721547
    0x1020d0b090405150408090414040c08010216110303070b010e04050708010501050d030806030111030f010306051302060703080712050a06081c0206011203020705100f02010e1203010506130e040305030402010f0503010312 96
    0x5504288200e41b018206141840080d00780c0b000411700301000e000c0e0001704414401062076100062120300300071440c102a49180e540c10b07401c0a40d0150904109502003000c035142001200c86d8283c00c071522894130750f1a58101c0056850550301600c6c0c42c030031040041506101031007618100c1c4c0c00101440320a0b085682d042d104440000c0c04d85a06550750802651442d002500640c4540f00c9201900b11641c118a004011243d018012800c0341d41e81c001604016107501003103a80313280c0c240c200400190b41d40201202c00b5120f00c001103034281d080000340310401c41c00740c00030425280d581c03094841d564003101a9000348020941520016484a401080045250421514102c0c043c4c4166004243c0765800304000002c02e40d00000006c680300102440182d080c407866a51140c860301908654a03030040c600454001805900c0c8208400500000303035080c40180d000040c00b0042820455207020700700507103140c0080b10140d02048002102480041c070850441c0d0580340c1c400300803562000c5002003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24724043 1250 24722793 24722833
    0x1121b050a17010212010303020d080109051009020c031e1c18020607080c060903190804050a2003010603050d03061a03070c03030207021201050103050d0201110d0b061201060201020d0b090405 84
    0x141d0b8449550802852510b08074200000740658000e4009001003c24028000e0103d00140d0002803054a000d0600c09044000b6944008403810514056126401e101925056100b0120b00c060001c0706059107501c2160004050700352200d200c583d000203c00c80075007080c195038010041c0c1000e10000c00740c5034010314112000e000c2490043c5200f50800d1401c0c00114640740080e14944400e51000c54400281900f900c98510003268601c2c0c50303005402d1a0740d4180e5945000d02c401000e60040c1c44400662201c0301401c044400e80c018024880301d03680e030038619102d8140112110010f4204140810382e4100c00751039040040017074220754076554810b181282c0d44910b10008404051b0204070b400050f07a84c042c2510241d5940100026403545546081407511484070100340c00d690419540342107055014054076512540d50b1808104041780c0c200180ba68030528a00010141d03400c400070400a03815806800c1c00300c4040e0b030421880c03000d4403c03c07a56002c200c07070003840760740020344000701640e400c08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24725293 1250 24724043 24724079
    0x21806071113050109110a080f04030e030703080c0d020d02121608040b1c0b010f03110408030a080a050606070804050d0c09020f120f011203080705040e01121b050a 72
    0x1890300c00d80800c541c0001c0100c000c540e04a0400790b00c50006104820b164401c80c4090001c4216a500e400710155001d410041e0050210782805a0540000c1c1418025030031700440c00c100030186c030400d0352079280040d9950001c49940760980304100901030b596000040c0d1105460054009015442d190700280d00154030095203003006a0001240e0340000384d0071701c040d00c0584100080d050300d0300760450595511a070800401d10010f401c07c08000c4c0c0341c5e60014482c020308a440e10b0085011824890600c0e0580f181c3da005180d54880080c0c60b04000e5440003695004501c070360814030540d100c1030300b00f001a014000019000e000200001c01c90303031030b100801c41000c0c0d11400d0400d00943d502c001410481e081341000080d503860005244490200301d581c0e29174000f00c102c0d164011541805d250000d40342c0c100c40c009081c0810348005ca490240110241e50003000b0700c25083e010340da190f101c0e805a400c58203a040b11000595141d4180314181d64000f401074502c081c1500c09480e00d0310b4100300d82942014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24726543 1250 24725293 24725303
    0x503010b0a0905090106090512010504030e0f0307051806010212040302011722050d0207050901080d0507030516050109020a0e1510030605040504050303011a040602070b071a090f010f02180607 84
    0x16000a81038071003c1c4064000c100303907220310b0181c41c40e150501c001c2784d60429040d881e6900d00404c00000a8010400704956582503500d180e81010f0400401e1031705005800180c1c0c8146440901d50031a0784021810740708902c2a806d0328240c0310341d10f0000d4558000c5010081c003042a42141c4900d408038031801540c4000110a154444c0694001000c1030002c10388055510390091000307a92129010000c4d00024101580c1d807440640c940000943c407440d0300810307202003000c005000b9040c18880c034280c03080f0202074003030314058045902d0502d008014806089004000000000412401000d00c1502c218400020b00410301880c00030800d0100c5090281000d065484002080e503888a108940c480d510802c000c41d940d50600c0881c5110b8a074009a03155490003c000920540b60b0100360070040342c02c0e22032480d07141c00c03403480c0501409001c400d6a010b0f1010040400c0200540000c20300402282030000304a40440c0c2c00c46001644201030048a805c0360070700c080a2607003001300061130b441d4059 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24727793 1250 24726543 24726557
    0x607080304060506180a0c1d0d0b04050109140709050a0c02030a030b010210020f12130201090b0307051c09060b01090f0302010c0203100623040603020108060103020904090210050d050a0501060503010b0a 89
    0x1140307aa544032905071001c4940940e11000090450f0300680c4406020070062880300304102e2241c009100000719207001400b11f032b00d10010804011003504241c040e5648403014021807041941740c0c030354400346403207000b80086c10140480d180244520071300d00d03518200d030701462409114000680c00380010900e001e0440c031694a0303d03102441da40c030140c145842c1701c2014039030f01c01501200720f003494400340a2070612242045c0e5000140c3e04103450400320340000c03c280f5182d599010302030303946005403d2280e80c1590307140c03d6660501002e9003c445058801e040c1000f05180c1c81004403682100750013481103044c06500280099070041c4090b411a0384014100da035421640c61194060f82c900d9808609144102c46a110500d0010b5400c0c0400640c21382c2d04000091540e000200800009083c85051690000e0301c007046e41c03120717040000042e80140c10114079504244d0010810b80c072401050a110b0700c0c002c0030501f041c1d0300c1e0040c00c1c121955965402e0440e420041c1c5408203600100f20b1406000c40 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24729043 1250 24727793 24727819
    0x12120c080307110f03090102150c040801090b0403200303061201020c070303020f1203040305030a0f020c01091203060b040302100f050c12030403030516020615030c03011107110607080304060506 85
    0xd0000d502c1560341c0ea4402514400140c04149803080181c1452410341040c024070328181d80c0010303a4041014605550110342c5c40b0540e16016038400c58004040c1c82d401d10600100b03101190340d8440c0181c0c440d5481c809468100b1740e1001c1c1011011425100c103420801c081180d6190041d80c1500d6582040001440e0182c0680c649143c110294402c60150b00159044810440c060092150106561000c54030310329141e80d008003d4880106001d543d513a0f959550540d01e201035041d504405040340c0204241441401c2c80310782c052200e00244006801d02401080048203a410381d0700b140e038060490100a41401e009448030503a91503000304003c0184241a65204c08008130115000440c1c1821f81d20700b0142001015910020652010318400c0380410050a83c00116658030903641c01e04802507880c03101c000303400d20384039034501c6034158244070342a41b2481809006003075003442118091032040500040c13080300e00a542019000c01014000540800c1781600810f9000000078001d0b15a503031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24730293 1250 24729043 24729053
    0x305090123040209090303091519090b0f0606040302031b0409080703030501230d02010e010201060b0a0806030d0f090b030406060b07080c010c080606040b2a0d090e0112120c 76
    0x241401025950901e6028402541800081180c022640c48091483c6290038107034995100c003108080484921044001441c5070b40040250710080058901031040d4506030a01c10380e40d450640d07407110380100c2680441d4a07840d08000715021207078068058a6031803a070004645403c0210542160015226613140001600810081c5034942c803070f40340021154141418003c0c031582c030403c2000c1c1d00000d1a944483d0f542c61103820b219080c0d09182440d0327501c0310078004034054501c41d440800c26001c0070841c600d8617a080342213144580010740841c0e130702c001c10740c0003120484d02924041c0045801d5a100b401558845d200665005003c1c070f1021031119640c400e2a0400c7e4822142038543c03507000308440c842c0100030300401c09010118501048141403032400035041d0f02ca14403c420002c000080c1c40ca01182c100400201c050100f100d600581c081701d003101540b1840c00c442c00c00b000a50748503011510905245040e41038400f841d074450003c00250b40c500000d40308010b0544184040030519030300043d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24731543 1250 24730293 24730331
    0x60c0412031b0f120905010311030f040303090602040f14030d080f090a050601060c1e0b011509031b05010906020d020a03030e01290301110304050d050304140a0303061d10030303050901 81
    0x91207480c003032800741350fa40341c01495121701e500814105400c01d0f5041413612a40c100340e0342c1054030513540c16015126441c1c10340040003603c0e001002140081800540d010800000030b0481c0c0303070000044024150070040584a06103d0031100c0803461400200f512040c1500d2a158804d001008556040344035481d0760746000d40982c840c40000d0007110150007007200401c4145818000380c02c120210341160354945215002c140103a40d04c0c1030660090030001d5120b06c81f14401503400901e1411700c08aa82d036005910b0290b40201404a1240f0340d00040f41e5200042c4018040d03100c2d03015202c50f0708039517411400340501c1d03d9413070701542d02c031120032081100d21080100507010548130b001d0b206002e1400d15094a117428603a4100703c82c01d1080001192020501304c140400904d8a603a0707940d114031700364280703c560200148180c4074a001d0341b4101505540080c0603651f2044054407242c5401446140040d800c851a18400010030002c000282c0640c002a410550800000c00c4a49010603450f03165 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24732793 1250 24731543 24731573
    0x80c040b0309011d010207020a15090b030f0708061e0607060603060c02070501120b010206060d0503280e04060b091912050a060b040212041202070b0a030e060c0412031b 74
    0x40c3d564105540d0061300074504240300d80ea60000a40c2441d01c903400260081c1c039144250442c01b0107011109181078130a91002d13014000c464442600c134102252000118681141c00c0408078483e070000c030705146810001e1101d40c0c0d1b01414401c03600e11102040c000756402081c0d00300c5d2119107490000c00060f04900501c0f00b5095168001c20b551440e0000041c0002c040b41303078000f000e51030401800010390340483d45d9544408150380c2d800840c1103a2034414994450b13001d01c042c80d56116040c04018214181042c80c3c0c1341031b2a070341e10050880d00c03010803088600511910000050802c40d0700240d0405c00c0d200113540e003024081c000c40703681d969822242d450760400115096040044c070402000715610404124010555045083c0404a264541041005800035050007030700300310300060078402c01c0303048003030030341003400d11b4503503920180240290400e500e45005500a1400095910030400e00307840841d450320740c00e074180d858a510300b07444e04003100701e50980b400100130400c008200140c01c54808 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24734043 1250 24732793 24732811
    0x7170903030913150e0c040909050703021c03031103010b03040b070c05010e101d0a080c01020f040b03010311030a0b1812070305130e060a0302010e0409020406090605030c0402070206030106080c040b03 88
    0x20300c8000d0b400340d13510032060790041c449400c03e007020f016100807080d003a601900c4040c480000d096425003811450414a544020740c040250202c00126000c3e286050301030130310a48090103005074103804c034942400240651041704006100080114400810642c0c000341716041c02e840c400360a0300c2d803a080d03800301008040150701c400300e1901c91680502c58801e69007035800792a2403444070440d0060310786110307490143c0302d00d4000c10509544a420b50403212040219505030703564658411403d1542e410920040d5081e84001200329054140441c0c0580601c1c2c2c00b07290320040e80d80764801e4000d4070007802c03e00c048a2040d481c00c0184030040100a019071402511030545a0f01400c9064000c80b0854100c110f4a4a1a4051000e1a15440d40e2a0141c0764242042c2d400f04006c4400709000380124071011394460300b00000040c800100f5403108041c3c0d1400c1c1c0079030f0000c19109041c001a841425002900701c40304100400005124801c45a04184c001d05028940b50f5510719500d0f180e0815540411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24735293 1250 24734043 24734051
    0x30b090901020a0f0201060305070509071106100603060902030411120c040f0e010c110d03091113060608010b130b070206071703011d090a120e060705012007170903030913 75
    0x107601e504503540341d1813081c0b507200070300c420b0703041d5510140c6410043c1b0901d406801d101e40400c0489009454020400b55840d045806a01c1c2c4000e2520b10f495051007005d010a141c50404200c80c2054000c42c1c0c49070f600801000112945881030003c0f8003068810b0540300d00400403200815070340d40c01518071400072a14003286c505036440c07050f4211103840e02c0c00c0e4140080d01d1400e4400e808089240031401c0541c3c1800162035206003003848200344520781c169401012904480501e10465200c0c00a50b04035544044160382c0711490308280388144c0c0c0300d065031541007080400330310681d0780c01440c0a030710143c080b03824285a43d0307441d8420050400c89996010011005020998180d0070140c0340040307a0341c4080050400a80190310740c15604005010714a40043c0c01010030702131410060a001e0281c009582c504076420114000c225107068030000101c04548480d824080b08150742c0c0c01a00f1035440c0c5c400f1903103183c4005955225030145500b6010510034650540c2d6100350442d2550440b8101003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24736543 1250 24735293 24735307
    0x6150c020a05040504210306030b0103051c020c030304262d0309060f03040c03052a0405101e0f14030f010504121803080304050d1b030f030b01030b09090102 69
    0x1007090400d8000034043d5207010b0811002c0380d110000084824004e071910400c40d0300e0071130210040d240b2908054411441c0f90000000c20500040710754081280e200b840310b4846404004903103036441200c0f01c0d941944140010b10010b4038460045003840390040e07416910f04100102681009140001d0f4640e0850510f417041e0708c0030460001048c1c0c02c094501840c81c0101703103000900d080c003d841c146180c404003c8001410041d0100102000c0d40e007140845034108868803000104d8a9164601881c04c25490303a000b04500301070144502480b08140702150140c2403c5001c1c040d91501c1c01d012002c198450b10015040003160206800f40121901e2402019014414189021f440080b814880d030b24000c100804501007590700c1072020754516140800061a409000007200c5503007016142e400000240401c02c034000030000c0f80110551170b05050405038001c0794103010180107029001c0b8041d804e039240c026100713910540d9400014100011244940c00204e0300c1c00b40102c44030416698001500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24737793 1250 24736543 24736549
    0xd0201051602030408060703020306030a0b0405060910060b030a2a0c0b06010c030c0215040503120901020105160207092016020406050a050a0b0f07050303150918031c06150c02 77
    0x11880001c1d003030000b10b14007407606501d56030359100144080f04069000c404030340707581d40038840303031041942081d142c180904107030626607290b503804c3e10680118807455102900b1864140910760842e440804000d081da03076803010034405056480031103079041244103450908800035041d410203d00869850031803803c0ca619000c19201d10160556060080311250940065030225050b5a01c5906444460103000c4194a2074200d00540e04580c0d03141c01b500200c2c00c0441e02003006044081c000b603009100b16250030f401c041103003076480300060040e000000140300c078100030f030400c014110851508515070780c888240d411803900a103008521410100d031810301981b805008040140c442191031b014032614110001d030400d132980c03240015076070012030952810310102041e00c5580e1b030000c0650b035a0713203804c00b4a1a40b01024542182c410400400402c000c84907204400c0f1f41e140422004500d415107862019604a8036820780000b0342e41c40b19004036620400e80041000b000090715514078491581c410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24739043 1250 24737793 24737821
    0xb090a120806030c04090303020d0c030509010f0b01020307030e0109050607030513170309130603081c06090b0109230a080708010f14010303140d110c010b0306040c0b0a020f0d020105 80
    0x4200308110051041c041240d401143c1140b4a03442281e000440088618058019000e02d41c6903522045c40e1000a02900741c064112500c98800c0034001c208100c2e14114020845040d0174030117006070f000740600b10000b4001c03218007100990504000410310b41d038a0000700c90f42c0c0085d600301c0c0052804242e000480306840f000724040c08012680c8030103003942c00480c036600c1c09900111403184e51103140100c00e840b071070742c0848051070700040459a644000c02c031100c10203019850000c046860a440086c811240d48100010540c05940d150141464070b419070b0902c41180c0d010340f03006292000065481c0e954a00c0760360041034403c0103010003524103505142100d50080040001d80c0c200000b4080c5400103402850640346d05050000c100300c00d00c02c04401138021012080c01c000e1500d40311b49040d1281a015003603c0600a0083c45404a54024903480303c6d42527a005151101c240c030280034107100300e80908880c0c1d0951045800c011040a081c40c0790144403032000025075980c4040c00742c01504051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24740293 1250 24739043 24739073
    0x60311010206070801030803070c0312061409010f03081603020c030d030f060f03170c0a060905010b090105121b04020c01020412030e100203040e0c0d0e07050a151b030201090b090a 79
    0x800c07518030746c91070701c0d00741342c2c0d00c0020004001c01104084180c100740c01030685000d089082e40c010007000b0b89422981140d00e0310071045505c00c0c603c1e1400001d03400d80d86001c00084d01e81c090941c50800c20200920017010b40016421030641c041c0003410780d40d640742009400c11034a8107076008601400c2d40b0703e1100c101c2e03004e90020f54808800b0103007800818245824001c550880009080d56003401c40c0e200c81c1002403c50001b0301450a01d89244140b080540201000c3c2804075407840840e6640c90070481030304190f00004103250040b0300d2694002203445076500c80040007400141c038141d003551102e403ca80c0550414a041c1c0050001d1405140d44024001c0000c0030503100c504500064220181da20b00940c0305490b1a4a00702d000549003180740c034140c98628126420a120f040c828031991900c8020034000d442c01103080320b0001900ca03400e248028403030681600c3d406190302c444480c030041c41e04a00e00540666480b11011000251080100c91269040c07502605030600305290042403414155 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24741543 1250 24740293 24740297
    0x1b0406060521100e0405030309010506060405031b0f0a090609050f2707050d080d0c020123061c0803070e090106091712030109090203071d0f1906031101020607 70
    0x201000707601242440b01c44024050048206180b5510306041a0460700c0c01e0300800c01c4d0b0220703401888100710001016501581031900240450b9032560203002460055108642d8141e00c1104003d1140700914501030100d100a4905050301c561100400c0500c0d4059014000c138560f02da50030000841103105041d008a1070440f9600142400c920124024200e4420400320289010390400d01400410481000f0a0060f240d0465a04203041030b80c4181c0003160a070070721606103541d040819106109402c4030b4641d01c001400501c80c900c0c41400d8610008102507000310000d690f00c6c001c0d0860080380e0101901c100d00032540da1802c89001809402ca5005040c02412028010312200c3e40111680081d107420b014498151421034550610300008a03900403048440000046240c06854100e650201e0081d021076101c03550316107086010800d900d1210030004c0e1500040348580c142c40340303456000840882c0000070bc3d03402c1141b035001c681c0309038402c480405400d0000b03501560148012940080c02e4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24742793 1250 24741543 24741547
    0x20105092409030702130203010e100308030115090512061006030204030804031e0209180c010801080c04020304020102030417011505060c0703080903030c0a0b010602010608031e070c03051b04060605 87
    0x40c4201c402080100790000d44001d03100c00001c0c1010001c00a49a159400910080c3d0801101050354000e500c04e0044046200700440011001802078140000310f030b6020100c00c0c0380d84e28000c11201c00085e105071240400445c2000061984ea0781c40014040020310000f420072802c204942d0850a03547c1c1c0e2000c01410b00600080020a00440558040b030b034005403205441c0e03026002d004030b0041c0010000f507204204c041030241e83d4042c840c100240c904c2480c00ca0344820030000c01554042e20074402c0480c9a4866081c000c964203068026581151040c0100d030305147c2c41e440c464448145039901140e40c1c1e99103c403d0b07000485802d1181009040550b04146011803607607030240c81d92032034040601030741d50000340001c0b0fa0300c042085030403030305003e0140d500501d054a060a8503907070a1207000b0056003854000b040002000c0221507081007481c400d00611710090801404135003048400f640d13909484103000001c144140441e0200010018004003e00c1703105003040216130b40c0d50404810042e007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24744043 1250 24742793 24742813
    0x16020a08040e0c0412050606120c0904020409020d080301170d05090d061e0608011d0c0306010e13060203011503060801060815040c0b04060203030709080111030a0903020c040213030302010509 84
    0x8101190300b9a04003600d40501603403124410b41d100d1059078054120498000b228006200e13000c5100c2e801101d08668030b29000010000051385c41c001d8900f51a403140c100310100e001407070158403440c040e5202402036010700300c41703844050f00f54100364070012016030f00c1c0600140049080c0136413486940581031107400d100c20080424064180f42c0c5000b0030300c5076903600786069044105001d9a080700142c20602c007140e29104014041d26190b9083d09485482c00c0b0a01c520f00d001107108620200c02030014800f42c0e01e0204480d0381464054209011040440041c0c00890f03181e0000f1406400c040b6400f4074084506240182210001d600c0300041d64940034080c4054900031408920005000e0010442500d890800c0001814940c0c81030400350000a17001a483d900400034510030700300c0707894074a07415954410131400d95484405903800e501041000582083d1190300c8218903500a2040b650100700e983c002c60203e034803242d03a904c46001c200c0c008008041c0c0c2406060b86c4551194060589446 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24745293 1250 24744043 24744053
    0x1107030804061a040c0905030c0d050a02010503150604060804020913030801060509060f0703030510120f02063117030c0606010311070c03030e040c020307050a02010810030b0a0516020a 81
    0x801810003089039440f03001900300118480c41d0396140c15001031080143c03070751200029000015901c50103001e40100030660743e55103800b011000c401034005000c1c2101030000d500449065000030205840c8070800030300010203480c0d1201503c0a444143c84803403283c1401e0040008601c001040b08812001c203100603000039500000b0300b4115291404c086480711240c02c0050220f006808418203000400b01f142e20a1543c50380009000f0b11207811141080350302c0b400000902c140d000000f44c2043c00600341d2030018101907004010070401c1c0602d04841d81414800c01c83c4540002d80200c0c0e44102d400d1051124100c180b8640850641100045103021900e50340b0649540d001401e16050590380d29002128624030800c4030802a404185480f030261039140c06070490031b0380910b1a00440c40c0c0150111860300000c00c96030400d40050040904441c19801103903001030092403104403140c0500c00100059035000c20340c0c041c0f20030100c0410035161400400b5413590910554108562004111300003141c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24746543 1250 24745293 24745307
    0x60b1308010c021507020f03030f160c03050a050f1605060106080606090109030206090d0b09010501031b0e13020301020d0e0102030402130501150f03110d090b060a0f09180b0403020a0501110703 85
    0x12003a600100c0c843d1744030f000513400c01150305035842c10782c0000010008032500c0d04400a114240542c50000004803e913000c490003201100003e0201d4020094071901e80c0c09800a811280c1d40100545d103800d206846508600910160481e80b0b80d20010052061903003205d046a0b20000036504c09040400702030000303209030700c5840081c0c001e071000114403084e80c49000d80d0004845c0c03caa404151070030051780d9503008100908c4282d1b94486e0342c0414402d0900201d0301181181d0102e4010035003600c2d0006034681c01d04a030b62080303078159400c000110702c50703040d40941561520385400060f101e00d45030051004c14025800310014040c6400c0061220085042d842c01c26403803a1310340034110845040c4180c0041403040d1105240a901058543c03c1d102182c01207800b0620401d100781c001d071920f0041c04442c1400d80210035010000e00030521075800541e00c00074842e10304207444000e140c440c0d1a00928250190390980050f0000c1c04098244802400380001e001001c0e641c1500e000d00d1620001d103c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24747793 1250 24746543 24746563
    0x60b040b0a050d02060909010e0403020c060a090e09070807060207030308090d08040b1f0b0319050105090601050f09100806100c0206031305150109050907050a0b070209040f06060b1308010c02 84
    0x3902040056a080d5228001501d60b40c0101034400e601f01d5864400c085000d00c81264200c2c014811110003012608100e4160389024100303482d000c55040c1040200c038401003000300b42d1007040c45103080014010741d00300010700043c01070348c02800015041d400d0040c8110001446d0702c1e25603100a00c4035034041d0380200d82640c001c0d0403020761411030f140c8030b524200074003a406900d50f0806c4202004948503460300000c60007000d0144c030001400d0743d00c00aa4054035403d2049a51128142d00000d40c2540920000d003c007050304814149408103200000d00482d901c1c000c018001890a000c000305800c1c1807501c1000e10034207041c400700d40321055001a4081c80000c0c1811400a85201c500c410013004012a00e03400501d051002c04540e103502119004200840320315085118030341c4001060304140c01010700b52800c0450180c83d02910f40c081c000a8840034208941c1c0b5018501d0380f802082080c41005d002c0c117950614180e561440e6140d058000311a6002541c03182d01d0030300c4502980741c00146140c00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24749043 1250 24747793 24747799
    0x61701060812090d0804090c0e0906030d0f020a0501060b03060315190207020a151218020a050402031b0703030207030210020a0e0906030c04020d0203061c050d14190507060b040b0a05 80
    0x15460301e210108130072a5000e040104038200c0440d010801da081c0f43c004035019426655040c5031801d0f1350041000e60320307042d103039240c0580200d00b050382d046110b225800c0000950b80119000120302c4e954160841380715030320900b06c1d40f001206128080c6418400c04841d05403c41740214242045081d80030911000061210b04aa00040603811512a1204e50300145907480f041803446007038020151103030890540f080c00c078900e0811010940c103207040804455030340141c5151081418201800003e44c0007910600c40c0b078504020f52411000359600408032075200c1d660150302c8603d10302d0080d01e840c100c1d05d8401d041600601180511039030000100008c003408661142035030303c0701404682404c0c003112035907420a0001443c1e50980c1080d8000b14040c1106640001b810485414000c92500c010b20006000760410462000c25504c41c00705440051000b10850f441c0160742c02e41014440030f4200314901140000c601c0c1c2040c44018851030003ca07809031b6041c007a81d42001c0008111610314040c81d44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24750293 1250 24749043 24749047
    0x80304140103090f0609031107080706050d02070b01030302030a031407050d0b040b03060a0b1905010e0d03110d09140a03020f040c0207031a0609010b0c0703020d0201051903061701060812 82
    0x28807684a50854603e0a81012064440c1491420244098602d07410300b500403d112084081c600c040c00034544d07003181c0300304000d44906804e144040714150311103001040900c1d0280001008514541c40303940c000c5120390001e40e5205a02d4501400380c95040d4192040445100c040018050700101101c0401b07202c8100021002e4101001070001e041500e0219003520070201040504006540030b80366241c07044031482c41d0762600d41103203400c4001601900f0300240c0e060281101500b01f034241468450302c079003400b001e0f03d82c41041c0f40d4a040400510b0000140140008202c103030351102c2072940301102910b401c007000b030030341d00496110b002c4007015500580d07641c0c0354484c140b4801d20040011715071205052001c10005581020520b50a07100c1600c42c1d00c0c070800004009041004886000610101a01a00d4515020001c0300082c640080c0d051040800040418a0200c040740030780c6503160f240002c505007402c4030f01140d005000302c440e086030300d002800c2c00303070200000d15402555400700343c4e55 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24751543 1250 24750293 24750329
    0x80c040303091202130c032007110904052e050105030c031c1403090f060f0f1603020d020d0e0106120201080c0306031f02030603010c03050f070f140406021501050901080304 76
    0x80808101c160307050012031521800301b0342c09500d0341244018410700c8030840500c00d40321205402d28410140003d1104419201c8103540c3d0405100c060751003030050049c0c0c0e001e4604010041ca5200c601311500d9440004180c03041c8031042c041c400c0300d0140c0030030380080c42c0200320400440d0b0f8881131a40c80c51072021340816000c1d15103205040040b400c0081050709612400d0000c0b01c0c594492070050410603e0040800040c1c2c54202d80712100c0c0b088a0792400d050050f02d903000204c81005480414604058003000075403c142c105000030203950b45810800624402071031191821191103030804600c13070194880380340c0582e92204003550401e500d46801c7d5641c4d2112000240ba200380c03030180da040313030710b58140c2540d840c103203136001e10b1241206170001e01c14400c00c00411411614112030014901810f03401007401244900e01c10300001056003090f002c40a45040e0848036500907520080c0141d00007050106621403220701c0030b00500081d200e0445070350402180c0340e103a0066006d09000c1c849154007030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24752793 1250 24751543 24751549
    0x12070309020303040503070803210c04030305090f0a031514060f0402090a0f030804030b0a05010b070803100e0c040501020f0d09060f0203070f140105090d0912080903010e03070201080c040303091202 87
    0x180e001700f00040c1160600f40d0780700c3c0c4c0035481340c000040c0716586040d03803a552121b01e0b07140e00ca914030503003102c1409842c0609590702035445402000f0402c0d00000364541c000f400340c840761443c04c0614041c0388040811030700001c401054826440d290204940d541f070034411035403035100b80c0040d103260403100540c0790348020010510000c2e0f45d621403c1c40740c001500000a02205000500544e4040c4042082e2035480000d4038040e80c82c02c0c41070540c8035408204c044045003428002c3c681050319812007600c80c030743c0d864100207140401d80d61881554400101040303a1760301001034501d00c0c51700402501c005010784a016203280045d110b85000e02002c0c0030b141d401e952090080710801039000e0341c040e100d0503460400801400e401034840540d9031801c80414008980015205802e801c3c0e65180c10304d0754208100400030f49020641121049400e00100486d0f5400b070095643c000b01c890300858030380007240001000c2c01c00c090710f200300d1010100310030b20102c3d0f0300c83c1885041d52605289950048914804 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24754043 1250 24752793 24752797
    0x301090204060308030702060108070501080610050d1d01061e15120c0207030b01050607050d030b01020307050102120f0f0c160212030a180501030e15060a0810050601090b12070309020303 82
    0xe6105150035000f1003002994030182d4001e00d0294212117442c3e032251030b0b06640d4030081c01081e01003000315001411602e041007003c1c000c042c141c60940e00b0408403176854400e80700381c800100b075180c901b09003640041e00c2c240f05d03c034010152804d46095a11018210b4100901c1e603003c3e031075020b00c502110b403d003a801391241440214490b003041022000702003009484004900040b200c070b01c0d0302c00000602c0e20700141a05e00140d041400340211440d850002e9000f440d107106424190700007400000c010501c00e00c083c0a8950708800c0c04c48071464002c0c003490320024000c0c41450003000142c03d200d0b001490100381d500700741200310070b02c7d0001214000641d402444c4040409144000035201500344e81c049e40d0118610501c840620059440e0302c010740603149000c2a030340d03c03540100c0300305d0401004000c00076000000901510102030f19002c6041c202805800c1c01c0101c552580103002c01d55912810703100003000308802c1a03041440410b0352440310400a848403080580380d80e80c410943d40c1c2802 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24755293 1250 24754043 24754061
    0xe031002090a120609082701080702030901030e160902040314010203010807030b060402070605090c01080702010c0c110604030b040308070e03210706060e0703060306050a020309120a030204030804090e0d140f090301 94
    0x6c078252030350014503400344003100f58031455449103464020b8000c15400b41d03541e01d00900640d0040c600300328844dc01140100440314814407244205a1030962100c1c10481720b0000d8901d028015a94a0460502058220b1301ca10700104c0341c1c5c0f04000400c2807010101d002c20941e50301a007504030503100c00c00002c002c1e014403180130b82001d14103000d0008850300050540031104081c0c807074200070303650214240e0807101d172440c002e001b00d1042c076080340c0041d140e02e44e40c14022000401d4070303052603180e480741c00c100201210214042512003040c040d020780c104205441000c3c084000f0450406003802000c0307524142a03070a44183c80210307407c4100841508800e016003445e90191604d4500150020007800244c802501c0261030720010402d041c62038000c4900c07910301d04005004503e1030200e48103155002c04298800c1541c01d00c00031000940c44002400202079411001c0390744a81c0603226814040182e0600082c8812020020303c0000c905081e5400c040c40c403401251104908004203000d000084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24756543 1250 24755293 24755303
    0x3020c040203100e09010911060a03140c090102150c0d05150d05010b0109060e06030c0703020a06180b071805040b03030c030d0606110d021002090f0405070e031002090a120609 77
    0x1000b080f44811810740d0072404c41e03070340c201c290b02c854640d00c00301401c07198040005400203008502c0c0a1480c103000d8002d0061343d4803440c00056290f4a8000300030024820782e1600f1028500284c0300c40d1641c1e04000d412030031510940011210304065900b55641d120324200f4840ba980c4a800040720110b900d506009a100003412b41500341046280490007044840c590790f02140491a01103a070038030800c0e80c5c9108110241240e407643c0c070707a180c001115810003002141103109040034240080c0310360281007006031100c0902e00d00305506160103500c1e030310010424410030120030600f61050034117042d005c01312202a2000030380d02484401007415442008903071069803000096034540400184c0c040800c40d00c442d40e8604407150301c441d040c2d4560941c0d550f07000059200a51034404450b450380145140b1000a0a00c0c0e4401c810034040b4003958022100d034408940310640c3c820b45410306216440b030400340f2039821444c1514560004240c1e40c0f460044031401190401861b040100035440101891340103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24757793 1250 24756543 24756547
    0x307020d020a050310060906090c050417010b0618010305010608040b0402040504031b030203040807050a0b03220c031a090102090d03050306060705120a0e0a060909090c0902030a020c0c0f01021903020c0402 90
    0x8444c80d50b016211b20301c100c04041d072a0200c0001e40704401c0c4221000307a02c05940f80ca15162514803114040c40d03142c000d18006541c5ea40d20000d285d41c44000401c0c1c20a650007101202540b0075002400700d030016030002042c4444041080001140c2c01c06550780107904540005103502c95060854000d100d1300302c0f03038000c1001c00350000285900040504100c8201008071070307120f91904140112251a4882e8110007a41030012950703034404141e218584040310141980704c03208036201e9034000c440a0380f05a44c2540795011046035440e50206d4203a20034031000081d8500107100022500c4518003a50241c1084000b0012a01c983c1e03402c021141c1c0c03290440103c0e08034150801141c21107034071102038003010582c0b080070346180c2d0a08210480454904e07844800b600c0d031074044100040c001c2c401b0116215509240046611100d610245000c1d4aa1080040c1c849a4030f080007441c000082048070721034000d54100c400e445ea400542c910341a0b080751050010b201d402c5c50300342d18204100c111150f00c1800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24759043 1250 24757793 24757813
    0x80420090702150c07080f030c070c150210060b03060d02011704030807110f0c0d060b0d23120910170f06010816020c0105160b040606080c0a080307020d020a0503 71
    0x1c0000c00c08070754045500003483c103895903040d141180c4079050000b0000d520502c07015900e00001e4003c3d41d80700c182011910315107811340d610040c110015411440e140750030218960f003902e904000d44800407020203403c01405090502401c00e9010041402d407089035103000341011039200b0504003803a4414203c0342d00d0349040614010344090300884249002890801007420148000601700941c0391045016000e962400020b0000460111400317564298540310f0080d596140d66000f08402030254000c020700002c01100401102078030048130710075611aaa040840d81e00520072a503070b07801c08807045180c190821006480c0b240e0401104840384032164100300d00c00310f0f512802881410260307aa8661661103002c1c0c14144000d00a1f03c10040c4e101d01e01c0200f855000788000c015444650004148040541e903607000001d07000c0798102d41054481e41c7c100040b0b2010080c100c8a0101181c004d411503007080020750750390150003000b034403401c0e450046000395103400021502410300607090701c9082e40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24760293 1250 24759043 24759047
    0x3061a030f130b0a0b0109031401050a0e0a0203060a24080f060604050f0f060102160f14040b101d15130807060c02040e030c010c0c030906020d0804200907 68
    0x421034000000010110020701010542c0d12107641c52a0700c00d0f0780e820300703031180c504081c0180f2800da02541408210800480440d900380211980d451f07030304001180c0da14044612406960324002c58000d658020310b4a000140d90204103170f03500050303403a07001070086a141000c4003802240044940414503c0502007000c18001c24024441002c440c1244c50588403101400100c0f00115800201205c039400800c4400c0d0715084a01d4204c0c0052044411583c18525032510340401940440e681d051900007c000b208040040503c8400c000c803000c2140c40300346004903a0f0302c0f0000150004106590400d1400802c00307040c00c6040035009011070801c0b40800b0316800d8103512040c031207110004074005c005055040001c403942a42c441307565410b4a450315500b4080503003041200f030b03401800103003c140c04900b000d01c10080344054030b99840c0c01c0d000b182e04002d049488603803c03100454028140000d505500241242e4115500c0f41c1403651102c0c07041e440071210003150025a501c05244428480116 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24761543 1250 24760293 24760297
    0xa05090d170706060b0909010302060c010e030a0e010908011a1c0c0303120f060807090c050d050f01060909050c0a0c051501060801090b0a080c0f0a080a05030301091b120b0103061a 79
    0x152040c83d080000c01e4540d440f2442d540a6040e5980d84001e40c07400520050418901400c0403240003030010810703203003881d540c40c159001986450002481240c00c00c841d0742c0d100402500030440c03107008200c0c0702048529081c07104441809580240a048030300d40101810803200540d080e003200d1851a4a9164a07006100b442c0301c03030b01d5000c80748c200032030140c0b1620780740700320b404a400c208000d2007100d2800c0b034004080c0080c070042c90203001e020f105044001a403800350038410042d07440100c030b41e98146400900000440d8104c10103443c0381004000e524110b52003100c40404850030b1509040b00e161428920b440280f40d08441000c010200010301e80b90040c400e2810396200d6441800881000305c00d006074056688143e00039035200000c2c02c00c0b28180009070008000010b4403800225480d540698500003012a040b40c42e0750000004000260040c400c119502c207a1610343c0300158440b41c0024241000b0003000901c02d60fa424180d1403503030084d03026070010400045038010000b10034a02030025 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24762793 1250 24761543 24761557
    0x1020a0302040f080c0315070c0206070b0f090307030c0201120603060c08011403031e0c0a0507080c03150108030d0f0f0c020f010501080d080103120311070501020310060f02030a05090d17 82
    0x10034490008070351310340e003c80c0495450201400400b9450190303030f030030040684080c2000c4217008142c0780080250b242c1c1401000c6e400c2c080c0c8844441405d00c91758005805400800d0703076103d0341092008034000ba178465020190b1580900c1c0071303680000c41c0107400000308960307800103000c189030a0106007002d800030f510504982503c1d4051891002d2003080c9600e906c203191428140c19000c0c10728a0940151201030b06140403031204940421855544040c40c1002d90303008401180c1c440b114860f0f4034601040286580d0360700f181002c3c015490b00ca10a40d8038040c4801100400ea00e500344071405031040c2d44000100044010180141c416280300652105650345c4401c1265003060000f0844150000309140c00041e17642e200e01075a881d40e1244500c20502c99411401c040e1540c80d4040c414000e40040c180c00750042c0001641e0b4148507411920040070b941c00803042c41450100008541c3d004400c3e20a150194204684d035114008001402c00d55280001881c1c40304200a50340020f40910107401c134 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24764043 1250 24762793 24762809
    0x209011b051f1505040905010b09010b1b01020403080a0f030f05100302031203060303071e021905091005060a0f0c1506030312020724090209010e0610180303031d01020a030204 77
    0xd01e200c0000b10000740c43d015410985000d1203a0000c00540c1001d6100c1001103010f0300c0006402038075500051003454081c6d1048441c0d01c4041018800085900c02c030001a0701d50030001c5141c0b42c40c603954145a809817040c0403082c00800c4035107010380c0f07000c0c0d00b199011180800017003000e4600083d92050b00740481c0000d9009105507510100101d86410889005103001001503080c400356550700300da220304000300710407203c0014032003c0068031500c0710000800303211403151030488d0810041c41001c150041940301e1284460303000300002c0e140c8200710f50003015039261242c00000b0703181c015102c1d1101400c0040401c41101760341c103144100ca5120a00307582c0710390b075444061070f505045078060340110b4174080c0c450500c0c8120446c0e5021400b40700300c03544a04d01c0010a00c8040e5400080031007009a01604003c3c0054003000010303d0544803c3d80200c2e00d50406500d4a007646242c84980300b20380c0002020701d541e604407103c2d02511002042c0d0050107407c02035507151045480200a0b4006d0f02c00c0d416 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24765293 1250 24764043 24764083
    0x60d1407020c030703020d0b04020109090c02010b10030506100e030102041802090901060206010b0a08040c0803031609050402040e0a150512010605010e0d0201050a1d03070e061008010305060403030209011b05 91
    0x2843d18020549900322900145402044002c03915a8410f030361025004a041c800001400101aa003034001c001c490f80494000259031030441061080800120010008040c9003104010041d0b49422050a5030345192800d881c2e0394507003c0104e070080c03213581c10141d002c200d503400c1c1c40b503a00c0c0990001c040030142505d0301c4000340d80e124010b80c0d840000303001e0342d1020782007441300381840b5116500541e8014003c0100141450303460f05914190f40c4291042c0c4007a419803154105110740008041004003025075007103107460318002d0000340d0b610003d800d0b00d1070325480744001d03451107a11280345005458024402c003800c98001c401a0300800b030510495012902d9444141d002d0300e41522004e170700f03d030181c65041c03500a120404480300002224036076100c040e0707000f880c4c0710394500b08070b02005041944c0c914440d0741010410004180981c1c0002030030861040b0051000600200c0c8158103d54181009611401000010380f400d842024610249595002541c1c0900800081e44075590100200001c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24766543 1250 24765293 24765313
    0x3010f080a03090e0601031805030702030105150109090e0a021008040506060913020d0303060305070b280e011107052d01030c020309011d060c030301050a150c030e060d140702 77
    0x354954186030805004180d140c40204503502c1e203809080d600c0340051500050004507800c1c0c1d000300d510121405e9038503510101d00c000450400744a440c2d040a010031078001010407520008009803c10b0240361011500c0d62001007034070000704051541e5a82c01840900d030b1500d400c0000303010004c2114256014407407a40071900d1418003464450043c104e4500e005030394a0241c0034010070541c00881102059035800000001c144c0c18070281c4c01401e102c00103182d650303418990808032110141003031803101405407546180c45410200303d0368107000a0a01c06141c4400d5001c203400d007000b591081e500b09448808546112201c4800c1d24078dc580e0480114181c0742c4003030300440890f1000715003100940c0c02000400b0701036020f030142c0c08003600003400c0504002c022001044071a080601c000d4902e6002100600c031a281c807c1c220070191042740d081465224030305c400104040d107509005014869003162807030842d102d40b0100d5050208844060001001e86d400d00401600110344640050181c10104 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24767793 1250 24766543 24766559
    0x10602031e070206030601030902060d09060507090603050108030d15090606020a060606021614030a0503070f030f02190b0705160f0b070e060301090b010e10020c010806010c1a040203010605060f03010f 88
    0x103a140d0030f801600c86420350341ca20740158001e001c03840d02a40d0104041c041d65101071040d0144e000c0251107140c000c55203060042000d440030fa180d810440900d414900140481e000000a80d046000c099201280c1035004658414002c10203400c2144d40038200000407440a800103020801544600000c014150341c61074201d88800c0c0801200440300c0c2a00d20400c00e02121080b0b10000c51380040030b55000450983d50546143e010300c8c021100d01003190a2282071540140304080703011444d002400d0304410040070442007220900004140c1400480498540745c4500f050f110030b800c41c080c03a4020401c080c2803009402d00d058100305c51240801000131400c0d44076110501416001600d600d06603400c010509002c0e1080d50b1429040042010782003106540d0340e00044501c0140b40c0140c4101122900010b207001030040c406818082081181d000041820032084140c0c084a81c0c41035454540703200080c0905080d900455100001180500380124540c00440c1251051118410031130781d20954 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24769043 1250 24767793 24767797
    0x30915040501120b01030f0906050405100506031504050c12150c09012003090402030f0a0f0212040b040f05011e060f05030a0b040809030703060207060c030b0306060d0804030506010602031e 83
    0x742400203400461000c0d10854a40019804400506002c1114a4051900e8084840207071040e1001503c41c000c0c4000e0090901c031001e0490707800d05003400300b441d02001007035440c3e24690311244444040000102403210620032454203d10007005e503010603c60741e0702c032030303891895910144807181000b021403800300584088030741010701170315001d0f41760203031404442d18504443d000c80d54078002089061003d40c8c0360310045103e1181c803001c081c0d00d03040085c081000c4035441c0600103a218410031521500201041c0341c180c3c01503000295561a035170b1843c10058040303185000904030340c2807100c12000389101e0340304852402c0c40c07000100301d8aa950784024190758021310803d5019001000e040000c110303a880b0980e8001c0c050031185250a01c000d0100345050240d0340b081d150641c2c0800c40c6020896240a4044042c140e0714050209100d410300103034036118090580b900c10707140001c48004005448080d600215001000d0718210341c0c2d1110065100c1d402444040702030141104001d20080240d02 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24770293 1250 24769043 24769049
    0x314090d120c05040b0703091707030c0e1503060f0106020d0804020a1401110d02030a27060516020301090606030203070e07140a050c0105040c05040f02040b07060f02090d030203091504 81
    0x1458140364821488281d00825422040d001044801c010114482070128002c0c026244039031f8607001d81a2402c508410340b8106a18100056040900c003000410740001017841610034101c03c0d00c4d11901c1d4004620350381c0101c1d680c910307054022442000b48010550f88058101c4041e50203075050418580d80480f00e414040364000c0d4407840c036883c2808441c800c0103084140320010b041c003542c40414030079011318208114408200690000807038141c9264440c20402890640c11402c1c41c807040180310105404d80c003030041108010001c288510b90140e0765020354400c84d0050002c014916160819030060000350005034064450103600045e03030140404400d2050040782e940c412000000c159415807a401f840d0003100300102030200148000080c400c80e0700641c4503c140100b120314200034041906d81020130040e00b00d01c10701003000300c80301200848030196440b007000500a1300034285071000b805160700003a003100e0708100b90410143c000006003282901242d00f42404142003540982a02c143c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24771543 1250 24770293 24770297
    0x201020903030f0c0a0803040804090b060703020307030f0e040207060207020a05100503040f050c0603010b2d07020d0213020a0c0b0603010501051f02010603120201020a030b0301050f010303110a02030601060314090d 94
    0x8980c2d280f80e65028100013036a40041e0f91007454142c0380c44081703800c159000e5500710350009041065074498850000c1c021401e4800c80d040c451581c601035100e01841c44040c061004840f00c40100c2c602c00c1010f55841040140115142c0c811070410701d009400c60310040b40116442e520109003450f202502c1c2d800742c02d281d07440c18a15600d968130361508009010080b12144505000c0114540e40d070406140038000000c410764850b080c1c444a640c0c041903070f9485103000020390305c4c50083c00811804884485806464030082d02c4e5840c800702d080c81405140d008401d52001c0303005940b99500034040d2903454062404440d06417200c0c001c260887d9820300c121540042100701d0111070460940346540e1001c0341b4000024003690301d44891112940a0002d82d00603540000d6485000303815104408140c4c41c01e4000300b04600c4d08030b040300400001800040d017404a400050a43c21070108010b01c400c660280035200b40c1e503511180540a4640955a8280540320f00b0000c0c4419000149201a0f11031035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24772793 1250 24771543 24771547
    0x114040b04020405090c0705070510030c02011a03030f09010207170a0507090e2802030105010e16030203090d080910020408060703050a0b100e040609050103050f1203151c0b0403030902030c01020102090303 90
    0x1006c0091503038043c000407110350180204c000b40651710041c1482c1c1014041c0c0380880c000344014402800c44504003d02d441d5003406802d99011074030f0000c00d96021380292125150345440340d0b0300503031a01c12181d101c01a65648032001c1080804007040410f04603102e0130403188081d032102c446406458000e02e0701007059020780b4185600d090412105800114008014901848a074003c242074a0098000140d040070050510400001d10710102414080a16045080d410210300203500c42000802103410025541e01180c404d120510101b40100030f0044c085589658900e81c55480789811540070340880e1800c40010301035842c80c0603400511130003c3c9072151102284e001903070702d044100c1440d80c101e59910404140d41c81d040c8031f614081e501600080c0b4402a522413203030720740090100c081545e54001e01c203100c82092042e45602c0c007020221446102280c4d01e400350098010740b20f001410744014001440103154040c5c3c031440c11203000ba029103d0f00003100b4016401d07480750651240d059070003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24774043 1250 24772793 24772801
    0x31401110c0d0e0406030209090a03090b07050303060d02060f070c08070b09011205100801090803011505040e010308070503070606121103030f040314070504061508010503160b03090c03060114040b0402040509 91
    0x300e0758074082140c0d001000002d0460712a00848c02020781111540c80c16440241e64205141d00f04410000502a0305090380c60500ba66032050b4481c040a403c2c90f0158a2900481b42150f55000540b0301c04d00e903d609084c0c80d02031505284029503940e01c18030300203018804000c1840d28070b5070215420500e040c3c441c44500c030a000e0141008003402800384081080024010903049003c0c040c45406500481489850754109240100340003c1c942045090160030002040144c45003200d0303c1c11280c024a1642d100c2c0035a04001d4218404c1d0350008100360f2130502c000c5a841000704860000038003e00c0c1108940c280a01490f5a81c0304035a80382000603000d02007000041d4503100b203030001303825400c2505c05065441002c90182c651a40220072180c480c8803011002a41c00520b0a005040c1100100480305501406040c0e5240d1409284400c0800100140d4400010060310501d2035016088451640c0d50b40001280041c3d8030b1761003072080741411800ca40c946084e000391400d60b94000d0902c000b5440d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24775293 1250 24774043 24774047
    0x1606050f0103030c120c0203010e0c010e0607020a06050304030c021801061709060a0c090306061511010902010507020d03020a170409060b040e16020a050307030302030411010c12030c020109050304031401110c0d 92
    0x41001003070000c2050384242680103032401c0c02012001d10b660001040070be11948005403c00c08604c01c0c0070b0044505001c520b016950f01003076602140ca40381051656034a89040480d101200000041d4205c01040c40e0200b202c0b03105002d140c12134a03183d960350030403854200007115078a803c1c0c8190602ea031111002c101c1160840e8070032001e207541410101203581d80c030f586003020340b00c05500c040542100c603060000d00c0c54015003000075407401c0380020080b00d40103a0000c0e01d00c2c003550401a004002c40c844250806008112509259403c04001021401424a1450b856202e400ac5503501d43c246940010b5060601c4247c80645520103054061544d03180360726a8007030342c0103040c5411485500ca410000c20b4080c001172880030300079640541d481c03402d4101440650326004520381000b210b031200401103004110ba942480e02c60707250201d094890400708078050030880001601c940070001d800000c00400003030184080d81c4031802840700e0444942041000d0160010128041e0000094151418 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24776543 1250 24775293 24775313
    0x30a080a1d0105101a0c061902220302030d020106030c03021201020f160203070f031101140910030b0310050402010503130602120a1d030306061c060306021606050f0103030c 76
    0xc54001c0001d5044a591680542940c10503902c4101102c4441020f10244c3c2440700084402e12002e0f03191450102c007803150541d41c0400421f200741d62001990051800c140b242c048411049422904082c858860308512010200900c012880b0303110305408010154018090002142e0b04416118105441d40d000d114855641c042d4421903550300f0044941d804a00001405801d0740c0e80c4001c03c6660081e105143c0b0b0300055400105008218410810026103003142c42c241c840000c0c6402e0b10034905011520005000c1c0240c01c42c4e000300018000c0b56400c0e07069001c19450b2000b10100c1d00a003100c0902c401c122001998080e00042c4100001a03200440043c0064010300c0354400502d0113408061a0400800c01d5900c540c94645680c1c01c180b05009200305040b409103480c02a502d1070500c3c9000410b5031140034038220a0120b01d107283c0603024079543c0400015900014113541d500340b8541664400750b4122021141c0c00d2509010036159481514464140c035410703100e45019184540f0360782c0707181d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24777793 1250 24776543 24776561
    0x30b06040209030303010f0303021516051303080a030c03060504090317070c0507060807020d0207050f0d08090a0906170c0d0212010e1501060e041506030c020a08040b03040204060503030a080a 84
    0xc1a000c004845032501d04000450081c44503400f41044a401c500d8000e0518211040c00303000c20b0090001e010f041b6841c1c0d40101c0f8030302143e06000f565401c10140f01c0b82202110fa001900861020072411800c80d01a049a4210802683d0800003203032120200f00031a0312101d40038000840c1100c0400c503215002c8012500401b00d030130041900f8074190b0304c02d440c10b00c0c141c01a00004450005100d40260104800d0500c02124000391018a08010100da800701201e40114441c03a40c1e86000303400e0004036411130307005d80340150600e44500d88403074546000d40f01610444c2504961980342c00030030b10003c110b00032050001003090280000d5502084180000c40003010110b543c2c5040d5425480741c10407134410800c401e072070b11034020740c5840305c040c04ce0521312480a000e1420800d280000044042d4a042030382d1060400060f02c90880c2c60480c5440007441c0001c0c651140044c0c00f042030713158800032b07500c00e0b4401c80c0e05020b00c680300d41c181500c9000b07110100340415070050201d0385d20f8020b81c1211100c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24779043 1250 24777793 24777799
    0x301060c03090b040b0703110307260f0c0705120607050306010302130b0703020c010908011416020309091005090c18040c020f010c120b0a0b030a18021002030c010b011107030b06 78
    0x10b03081d15003110001981c0039510500f40007500103031980425401c0000d051400c051007004e1828029681c44030401c100d20481e00803102038090a542c3c200300030020130740e40c2c0c40c0044614951142c0b001000f03103907508128004e8600c26400424800055400010f0343d91154450f5654513007151158401903029421110b080711b001d03000c403900400c0c11405480940070141c042d034010300e140d00011001401a200b030f0707003140100703074104100048092003102100f134002c04405001e010540503800128103501034040c800307030322031420414820042ea8400c485003d031203003292400929124006044454883d0024940d0400c03106d445007156460940d104001c03801171401510480c0c014501c0007821078180c0d0103000085007140c501d44929260328441c1c259460002d071880051541080c1160200d8003004250394512030315036120001828042e260007030942e0707000c6c01d1802c08a44501c400380d166003142203a0900e40d031810300740114661207a0301c0f0f104068100b0029000310f50070346d110b114502c0b00090149170 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24780293 1250 24779043 24779057
    0x4170307050712080f1015050c0708011d0d03020a090501030207050a02150706050108010c05030402090a090b1e0906190b0406050604090207020907080421020a060f050601230301060c03 81
    0x21032030f4244411900c10302e582d030b035040c2ca151000742455040380140c2100d0300b48900f80c03400c1c450755001000c6c500e035500741030401c0e6407119810030205107020b016800c011519403c007001c122a1b1200f101d058110016064151920940d8198003101240119440c0d2000642c100000b0003165019500510056000384143c480501e07180d0046411105102c480c1c0000181c0040ca0070188640340c85014050041c020080c040d0041a51000300380780006400030380305002600c0800c03c076500640c03110282d1980a01800540d1602240305102425142c144d800d0440600700010103164022950601c950380c200c00d1207105000342d02c8120000d000b09014141c00c10359170340b00811280d40b02d9000c0c100401d5031600159440605106021124a0152458041c03080b45014840041c00981444c2c1043d03c00d4800c240c06a2004a412171610100c0344000d02828138003059041d4006d880d40004d8410714003030300c40e403c9c480741140001c0d0300040d0054690080b000148014450307148142d80c0d184040317019240441d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24781543 1250 24780293 24780307
    0x20d0201120e070503070b03010b0703030213090603051c020c010212030901020c0307110a0b160b06010504090212041b0305070b03060a050a060201050106020606090402030c01141b071d0417030705 86
    0x411107181814180680d84140740401c1603290401050000c7e00e4486241821945424041201130040c11030003024180c0116841c03c965075042009402458203c00a0108da903a904006484d2030041a0051500c1225405000213078000940c1080d25181a0f00501f003245c0c00d0070588035113401c042c081201319502042689110a403c0010701121070103005010603000701c4800300300d850300da070303a00101c0e020310280284901d03002072103094101d03030350800780c02d08950b500d6100407111803160f500070104041c40400ca00c038402c0d510720103240c492403041b041102038500321507a17031810380b40c1403000911961005c0000e0151481070b02c05190040c0700903044803840c588980000d102002d003070700b2400c0182e54402c01001200e5040210b5034001c1d4003540c0700039440c01c242e00800d45414002544505001e035a1891074982d4031103104403144c4140103000c10b120750005010361501d80000d44100000483d070045207000c0c01c05c00400d040d000b03552010b21240c40707081000c0c4116007030700004e10311414880140540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24782793 1250 24781543 24781577
    0x1206040c0e100801090507090501140c0a0206030a0209030c01020f030f0d0e0a05030d060905010308270604150e03060c090909030c0303040c06030c09060e040f1d0106031505090604020d0201 83
    0xa6403845519450b003c40540c144030340c800c12034000030321110801156907420800e59070402007042401540d141056a170304800d5061341d24018030140021b4005000004001c0b1080103076024080040c0101e0554408541c075000480e500c040300c0030802d184e42c004004045100c803120300100807240440038080b40f020108048282880b240c05c8041c0d5054000040360040110140301d450050001c00a04003c4c55045484000080c002c50011030300d610b02d00d01042c0594080803c04210900700100000d0351252070b164140854040502681e0210f080d112180140c2d02e00855414410720011940702d09010450041140c800c01c007520740d100ea4007081000810200b42400158880c0b0f0040118141d418541500101160b0030b08c2e10890800080d43e409220503644406031101c030b12030032a401328143c0e808036954030003032144130301c03400d00070080c50840440d840d810740225048900510701c16443d0340842c0e5524058038011600400c02c0e4201e40700250041c90328154107400039006151580d609280100b030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24784043 1250 24782793 24782809
    0x120c020d0b0a020705070914160e031209010f03180b071209050307020913020a031713030c05090106180303080703020f0c06040b07020f03030105090a022209050c1206040c0e 76
    0x181104240c000450105000c1c0c01c01291001f8204810104a0550782101200202d82c010f040030768002c401a52003500d03035101c3e003030315101e080000301a1503625201d4204040250721050200d030100344950b8841c02854000d00c21800e14481d003080b201e00c1c3c10340591380c0c40c44030703036000b00341c0018400050302c0c1a4550384a03100300e4031200c0c0f244000b580c2d2850349004101002100406c0b50350032507155a010401078481046040450b5400001a0444500b50200c00494050142207200405040c0303000001d200600810b1400c03108240c130307546038a90f2200b004440c00144000c0b03010300861480301c2003001910a038552070b400303602c82c0f0b401400e1118800e54020707540d00107025006260b02c0350342400706000715540b84641101c96400103154144c0d10703071000d0b5124001403044501c104618400100c1c0c0280781c1c0c045071a82860780d5910040403003015420442c00c0190300030704480f50302c3d00000403201d10903002141d20001401c00145079560340c65042001804a1049400c20410307030552500c015143c50070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24785293 1250 24784043 24784051
    0x80c030f030405010f0c021c02011b02100605030105041218030f061b030506100e0d0c061106010909020a0b18060307030f0b030313030b1b16120c120c020d0b 69
    0x303615a520308240c10840d09442d00041090f02981c9400d00020071944c0000c1c2d01c4507602000c800000d150449898140e004102c06424441100c5181040700503280d4085124009040758510030070015071158241400c0358411180240302e01d183c8500101064002c0d01d00107140001c0b50099208103489075a43c1143c842c040f81c2c100e40094480040d001d003141c070642c902c43c00c003410f49001c01a9141190024041d61200d9004406006030084194199243c03214403102c0580c2013120305c440203a4400006060748a01d4102c5c410714040c40001182031400d0b80101621030344c00905158602d810314402c60003607403042007255204464414020503944900c0084c5204041c20380380000c023036400080706819500c60031072840c80b0360030411001001d80d048150a00c10b880c0c00c05151060795684080c426407a8106912091341c0c03910105072055050701800c4c8150011340319003400030102c442480d0641e43c55002070001060780400800e0b840c2c03027a20a24620060a000400700f2080d0081615418036004c0251 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24786543 1250 24785293 24785317
    0x906090b03010c08150d02010201020d02071a07020f1209030a05010606020606040f0204030503030a02070305070b010e070f051e0307020a0c080307030306050306090c0d030323012301020a0f080c03 86
    0xc0e4200103245001c0c403580900990318285401145081414402c0c2d0110b840b40ca0340c8074050f0140300105591013541501c50808904408660703520345401d04d041c0c3c409051044c00c000b000c0740d00c00905000c0c40803078a081660b5542c1e00404609444d0b6030b00f100950003a0f0b0f2550b030107124100044001c90780034083c420083c4481e030054481820140240030998031000d0035212214010001040010320020441e6844240c02d18016120a003d10f011103441c4184c9201400d008540d50001c5901d003400150580150316544601c1e010a400c140150350300e000b4103207040d00714068868901003001c4244015035100340507105490000c645940d035100b03548010342120400d50300c0455038404060f0144140ea000c1c00c4118024045032602c00011030b500ca0340020006c0c064400810780c20f0425000341c00080302c0441409801d1140324500e070110178070324001d00c03034010000550b40c1c01074001135146110100d29032040e07000e0481d0b580799880307192403501c081c41c00b100c8260080103001d40c0840300740003826544000f0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24787793 1250 24786543 24786551
    0x60f0702010b0105130302040c210b01080105040504021309020f04020a03060e090a05030d1e0c08060f01090f0501081e01060c03020d030615111204090207050f15070503090304090609 80
    0x10000900b195004100381d8140041040100c145801d228100c104880c1d040700c0100302441100c408454007a150414841d5449034210340a20101c2190048510786100ba40c550074280e0381c1e001040140c0e1816140650400c00dc4842000a00855003000f92980d0002d004400c0048090020600b240e1090401c0030019a03264024003c0c820700f003040d01d07040340c6000000d144000c4a611500c1d02c920501101440e5a85d803a480c0b100c05183c0c4080b514011001c0c250308014210150700043c1640c481260744a101d0501280b03003490f55030281c03010344141c500803502610050704003001907462940141010741004601d481440d1111001280e0a01a148940d81c070000c00c9030328500039203840300c1c1c0d848c00c40074182020410f016502c4090005c010003030321351511807403201003219050b04001d0300c2c15003043c46005c000f0b804901480346070002c0c002d491086080701e141c03444040085031280d500d00ca02d2540d911032380e0081007026104e2030240d604815500305891030300340d07100400c000f21842ca501c5181410f4032 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24789043 1250 24787793 24787801
    0x60d02040608180607051b01140f070c05102703020a02191a07060b031006050f040203091009031808060105014107060519050c0c030d020d0b03060f 65
    0x221010b00c9800c024410b042140080000440d42c0d15001e00402000c20400041602c250303000d03103840900e52880c1801c008201d00d08a40d8120030441030700300d907400070842c448030116007c070788140c03000110b1031f401101400051444501803005082c0d04a0760510500346820313030f075144d041e50190b807411182c425001071492807032910500003d007040800074041388251540c1003142030040100ca210200e503100d103c40c0c0e03070581c40c50700400920130903440941611030800000b550960590180c002c0d6078044859620520381d00c8208401d038442194010066041800102c0c2050310b2034004010141c864207081d8100d41d03416200108a12090b807000380e8a41c08000108031650300803d06415804565803031140d68001e0fa002c641000852038006444841c00260800550450306c00703035952243d0000313049c00030b4100000280c49100307468a015000780d26204c081500686840200c804002d5520069401c0041211065000750042d0005000d0346d03407a040c440300c00d07903030501582d4462105103144802a0030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24790293 1250 24789043 24789047
    0x1091a01031a0c0405041104080105040311010b0d020310050705040509070302031b07051504020102160803030603010b030f15190207030503190b0109180f02030103050304090c0f0509090402040b060d020406 90
    0x70820308030b00100d40c51142400064031903c012141952070542d4042401030048004400360b11440c1c0c0495400d52078130060004040e802200084401141002440902428000c009a040c3e0f0514000e515500060030b036014018181c003e96401141c130708241e070410340c6e204041012184100c40001c0044d41c000b04025034a2210284001d07225800c405042c204a82e43d51070550b1401c8003a00364040000c004002011680b00300705480003d00740e45014007440366103051321545d80e001905c443d440ba508100e00d005090030300003000160703000e1480c0101042c50b81ea00031746000b070502615800084c50201020740c207114441c0010100b8611035984c141ea00e10707204002440c001d403260681203544d420141c070002e4136a4480d801c44282c40032005441813008044031080010700c4031500500ca100d001000000030f1040c04400352007101d80b060f60601500040b40011112036042c20b800d040820400e20140d0481d0610001c00c40d4890703c060300c002408000f150004006401c529807001c2000d40000c1d060000395 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24791543 1250 24790293 24790313
    0x31c050309100b060405010302030402040f230105030a03020601060c0311060c0304110409020609010513031a040212060c04060f050c10050618040b0a150f03030206010f170a02010503070201091a0103 87
    0x1020b094020000d04400c100081c14070b00c01c5108032810540c000c0003040a5544030342c4001000014074008220b203809400d045100010200c004510f04082d0000000d201d09012070f00b80b01655261340035140e20ba00f400f50030380d100c1d401c000c0282c01b000740074154006900810405075014241c04254640c891801c1d00e0702403880a11102190f000c0d60501c40c8020042e00c070301003030b02c0001d5000d0074900c0d25a01035900d1380c0312081c5240d00107042540c00e40180c00c182d1252600d5540030350b001741c2d8513403240c1d10800881561600c05031004144a00100402c2000902c100610000200a0b142040c0790800340c600072840d0001c001c105088060340c4400b40042880c100c2c2403002254403106034590149403580381c02044070b8004042d103804130f4540081ca100d02900c8440c51001d01109035002000d00d840e13043c002d540751070902468403801c881810108230240d15244104201c04c0030700c010207600c682c80c1d004603090707000034090200359034135032510030000345c50000c0c54000001801e160726095071450400c05012 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24792793 1250 24791543 24791563
    0x307180501020c0d0602030c0c060c0301030b0603070e1303050d0c030509010b040c0504030605130b0411010210060e0a0e03040503071404110f0d0b06070b0a09050105010e060109060e031c050309 85
    0x140d48221035003e1291030740184c6080032a048a001a160390b900c0c2d1580c0362512035103000000034080c240030840300d5150000070798181c9010350b0540229a841200740f680c0c0d043ea0740200424040c04000240c0f59028056114080911a140c42428140007000c0e64080d9014200c0080c0866116010000c2d0b14400744a0701c3c280c41000c4909101e160083d01c40a0014030079404042c0c59036485800080d0741140b10850468440d9010498504624060a1201c5901000b014050040c0204100c03000d0805032030050005a5656485c24150303078880e558014020100580c40300c040740014040052143da007070140c64002c00c102d2030072001c0080300707004101c00c480340829142008c0b074040c868040202d80c0d10b0151045aa149003000600050328800942c19000b040e4009210781200c0c0304002501071190400d1070643d1042009020710307603d407510315100c00021034860780080d414003c20400321348510360036400904c0260070b80c0e55034448050342d18405107054034420085100001407060404c0d00704880c54035 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24794043 1250 24792793 24792797
    0x715020910033c020d090b010605031012030e010302090a03020301051003150c08070507050109050a060221010506090d0c03051504031103030402030a02090a0f06030605010f0503010b0907230307180501 88
    0x600310b83c4081c110409041032500703802e582d6000c102500201c00d035a0082d02d515820400c4450190313504d050090003a070045540c0d1080e15030204001402e100e040c11403c3d4900d0b03240e1104403501c1c1014004400a401560342154020029440040584c074284980b5000300310394810b01442909505104034402294010320f4a03442c44c24861120450f401000e06800c21408d18089603540143e0901d1405094004409002801401035000130058a46e0003007c00900414144440d0148112003401c000401d2044c00d8001d00c08014020091404074007140da454814a10300c2c181684a44a16150015610f00c050794242440280410300d500800d407200c8809120009510b1880c2c1540483d480c2c070884100280928203d02c00301d100d012898018049801480104110032562030030441c020304070a224041000c001d1583c0422581818056144141000391400a01d503e400000700ea0064402c800580e141c14200454051141441c0041d8043e4a80c1e96540101c01c2c5100500c000006a56010340c0c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24795293 1250 24794043 24794111
    0x50c011412040b040302150f0604140601090512120408011505120d0507060b060a0306090b0d0f0b090309150c06100312110708120403110402040803071502091003 71
    0x50402104160310b684581c3c40902e02034992070340e240903850450b14000c040301c14045a01001190004c0d02c88040c45081b0880c0c09003c07003103883c000d040201d0317001e5541c1c5000501036241403040d0f081c910b95003003680c9181030072207424990305545604160415000006540d44414602000e40c9c1800b096202400e030031640701a40524417400c00da5501860303c42281030050120f00d03003050004607804a280000040c00700c80c1c0c0d4a905050050060505000c1d46010600e0311074403000c28204070140c007280d5070780402020701c0d024168403141c15411000780140704922040010400d582c07901082d0405030201014859103482a0054240c103010b00140340003c410501142080400d80440000340e00240d1401d11032003004008003424100003061708659500d1141801100752281860003c1040320f0040c5041e010000b040c0c005c1009034400c511482c0d0455209001181c00b040403505864140052540d00514050031940030803070a150b00000080425950394116550042c02080003071105030800b0012 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24796543 1250 24795293 24795307
    0x90d240c0807030c0201020405150304021005090d02191e0f0b0307120b010c2a050607050c0111010618020306030105071404090e0a02120304150f09210c03050c0114 72
    0x400601c002001d000405480e620381001c074500030350403100505000b07032030303100384050b285010095030384150780c205e010303081031220303c00d00500c82e00c1541c80000f80205004410405502007040c450341c4401ca03446900108400055070203540041846804a424100f441aa142c5540042d000d0340383da100c20104842002000b02156000002c10b803207290002c400500c403a035100040380d0f030700060500280726400307181005003141800916185407804081c040d100f9607031243e05216082c0a4030000609039441080c030b00482d5800703002c41c00c0e150201c0e6400058425602e0008500541e18083c1003c8255400001c5c0140c604080c020b9903030101c0b403410f1502e0300c00100d2083d51101c5c8290b1040c03141aa5030ba81100300f0560f001d2042e02d0342960010500441e80604003400d603140e502c20303ca41d600c21070040c00c0404030344d0b016007024894051542c440f00c02540c0b81004542210300001c02d80d08000c508400e8010029184508100146000d0801410b9104404002410b00c030000c1c120001030f0340007031220f0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24797793 1250 24796543 24796547
    0xf0905090103020105030a0b0901060206090c0f0d0303021b01090804030209010e071e021908180a0b180a03060e0601050306010b090a14010e0306070c0b071403130206090d240c 77
    0x907044a07428a05941e0301d40d20a07941100034408061200c0e03014a141c400000c030f2650004919008078001402d481b81904200200a904040e0700d1400350003207148401d10011030300a9010304602450080710603902481c8030006421105880401c49141c0000b05090081d41804032a4902408188035020800d0500da10094001070018800c0c0040408070991015101c0c424415101b240c0070306032808107903d405142501e0250425032aa003002050003170410700900c0c000404100f143c502c140038915120b00fa000400e5201200214282c01c00e5400300b000002850b80e2103030491141000000c2c02481d41000201170034404103030b00c4858007890501200c107003603480c0541e1100f1140144c0406422003030309070060b41d100e0052518564140140c0042109464000065407240c80c41591801819039401c8015903a03004102d0400111000c00d00020344642940320ba8080c0c0e140c00101150704100206000481404042c8002c6510341007202d618085100d030706c0300c0b608540c02d010a083c0185c1e001c060340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24799043 1250 24797793 24797809
    0x5030712060b22060b0a32040303031407050f0f0a0207031a0f010503061b03100518070219030806010e030a14010614030304121b080114010303020606030120130e010f03030f0905 78
    0x171f0316444a00b40e4503d20312030a000268030305061100030169484503603030304025000346004c3c640c884261040c200000c08040c1302c0c4080700d5980701c01d0145c003801c025140e0549441e58001044080562141800110202e080e41c10142c1d0a8013490350f503009a807030b004006030f0b41a4810b07840a8040d901620038441c800c060101d0810344c2075066058282c80340c1c0c891410000707641c1300740d1200b600960210324003a045d19084610301d01c070701201c0c0c00b100c079400e1510b01d904600c959181e01c090009515500842d00541c401c0c1104107403110024200c510321490b58a0311441005292000c404a80d5291420003103c0b0880520095061040300614101031400340e412041580d441801001804c2a0703180c5054081b440c6038171406440303251f00801003c400b6450b4000142c1080c04180c0152044000040301c81c5014007941c00b001d94507942c040110740c52190050056003040c09500c202501030703000419440001d400c0c403070080600112400ac03da14605000c1c04040f0070718010000c02c24070350000e01c515200d001d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24800293 1250 24799043 24799067
    0x219030905040c0302090a03060207050f070315090602070204050903040611030903032506060909030311070f110105210f0c0408030301060806040e010203040f0303110405030712060b22060b0a 84
    0x40c01043d404400003044000348500030b095039020324840700110034003410303501503e02140326800300c0e0310389200c00312001d686941a01c0003d251010040c04100c07001941d03080102601e00ca20000340c1061070039400502030f5034003200c5070b19081d800410308102c8554046c103010b58401004024501d00908000030039140e2080e089000c1c00c2c6040741026484001d01c0b91000c2204903045603080000c10345404c0c825002e004403403030960000f800c011303107038a015481360215404281d00003080007441c1403d0350380000c881e204004250512000380400003055102e80700c80280c03072842ca400f46242e0310301030521342c1403102d019003007054001042c0018030920b4400800c40341034a1680c104002190f03904070015000c1d0011007595500b950003c000d000420841c0014012014401e86081c00341c403490007500c1a05000d540320392541a80156004c03c4107081e1601000103041c000c3d600411850040d00218140c4100210811a1002c00705800d00c81d40101d882850042e04000807000d143c0006000c004051505050f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24801543 1250 24800293 24800299
    0x20706091b090c0e121e0a0303110c0d12020d0e060402041803090e06130c02030a0206151005031506070f051c0f0813120e03070801090b07180f090b010219030905 71
    0x180301890001003c000c50300c80b506c150f1401d0f83c041c0c0c03440441135807550352940702180880c0c20207123043c51032410603054a04051041c03000300b83c49403002400b2144107074915030380b0003c241d0030070890700c10f1141401004000e440c0100144041e040600c18001103400080c00c640100c00780380304540029074801d50347c1040315011055841c1c292120800034443c0c103141341b115042d1514010089440d26004409482a0041d5030240c618503901e034502802e03502400a60917501c9407400800c1031000340101c1c0030311780204100c05c0b0300714600b240d40c0104820380d00141003903d0984440c08440e08101041209010145800320800d8800c2c0b10b1a0001d404017004403441c901740a071070b10015404954500d04052481d400c42090b03280303051f0600300076111621402c504da02900440c0c078041100001401148241e5030300102000709942d8a45080340c56841c641410350101d41d89000000c2c40c003e040c8030038400381c40d4804c400556944188006441c00d00c00020362003500d20910404800700340c028541004030343c026 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24802793 1250 24801543 24801559
    0x30609061908030a030e0d0801050102100f02040b0a020c0907031401050907020f0106030605010f1a0f0c030d0204060f20060402090a0b030106030b0714040b16020103020706091b090c0e 81
    0x500300d0004501c040390400310051102040341c040250b459004003144604c0081681c030050790030f410445086009020f80350159000716401d42400c1229440701d901540748400050905468022504c504d612803d00c00006900c0108502135602e04518600e4005905040c100815102c10707640042040c414407580d0701c82e007001000101c400e4002c0c0001c03080900040001c00c0203545925000d00200300038081c00c1e10780c46280c2404268903100090204003180305646081c146140ca001d202c5150340321351120f08060005102081c41619280041d1000c0c10941d1180900c2c00090100248210703034050002c6c045404400f4000814100442c0b1660481c0e010340b0300380400c0e0f80d0f500711180540005410240c0540c40c0200020902c01d01501c014000c80d62613540040c8484085101c4c0f44500841c021407501400c20040007000c0d90703456841400e034034410b06026052500710346071a012070b420b1910a485c84525610070350660703030141800da0302602c0d91040410034103010180050181030035001e030700d0040e011 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24804043 1250 24802793 24802819
    0x70311040609050a050a05060102030901050d09030e090f0603010b0103020403030f030515030307031706010908060711071a1903110702120111041203030b090c030f0421020d09050603060906 83
    0x807500080e0203400456010b01280c1020001000101800c941080e9244c0c030b4039004c108650720102c101e07415000160349060405048401d45801400d50904c11414401400b4520304180c88004c50a0720403148104004d00070f00e8003001345030a48034400c40d00c9040501c100b20520000340c00016180710500240390000c6d141d07540340500b0314440700752419a98140b0012401d03e081582c41000040750401c58400c44c1c1c0301d500c8920064035500b02900a0040716000900090250f6101d14000d081e007072070b01c10403102c800d43d451b100d121f4010085c0340020055000081e41820810ba1420f040c111141140b80801c8440c00701400e0300302ca0700545400174441e01ca005000700900b40250400601001c005002559940e62410324020399103204d14100c3c0841e0030300301002003510782240d040f48140e414000486c030319a10031040740ea030781400a1049510b41b0740e000480b010b142009a080c10b00e05896001003003c4180c5401c080d110303414a0f802584a01820410014152500c0e400c135904058207407400a410b041d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24805293 1250 24804043 24804049
    0x9050901030b010e0601111e16080303010b030411190510080405060601110a0b0a200f0a03021b01060b13090b030a08090307150c1703250c05030f031e0405070311 71
    0x9450300041c0500c5441d040760788d42d00c150000fa40910b25007108031401e4a0524103190800c0301148218599900103100410290b11200d0003140c0c8544281080b18503520034000241da9051405803424007500000403d01c410b0408402c030400340300190400000500d42a583c080c1d41c0e800c000c000e64104244000441400d0030304020190000364008001c1e0221f00d4240d80c88001490000010051400741d6858001d10f203402c4003c50702c4030150071183e00d180001c2a04140c0203584540c002d12142e10200300303803124107082032080002610290148a98507030340c0b411038084410310750304984800381c904184140141c0d00003401c9000654030020703064483d0321050009090403d030790300032591888100210108140e0220340e028029114120071480400002d09000e11404102c0e11400100c000d4210000c10a00b28200c2c00b030b120413076140031031001903503a6405045400491549406500110600407030058241c41c4c0c3c101e103001124424403030703c0c0c551502c540e01e181e140301c00341c261021a00d030061161 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24806543 1250 24805293 24805307
    0x1090b15060d0f02180a0b0304080702120604140606100c0b090a051005090d050703020303150402041a0d05061005040605070302030405040203070519020309181915030309050901030b010e0601 84
    0xb002c1035600700020080280c2c144041d41c80803003e520708000c5105400d14524190701d0301d80a54200c24540b90441d0380d20390710007a695111020aa90000780310011074107102e0200b120070700c034502c070303041d00361070104071604c82c0f8078054014084a104100183c0c1c000c003007a0380500400c1078583c010301a00742e41c0d2141c03120305090041e806005095401000601c81001e2015080b19000e01c0c030300011640c9110250340111058020740c100100183c1040000c0f0742402c401d14100d5691900c0240010b190a41d544403a207032a80000311030010210b00850020202503092040b07560210007540d181c0c8012051003801010392041e80146414002d010495505243c42001518043d0602500855a038140400054000d0704128030302940300026016810b40b00d48084160b03072290901030f02641e0728407007405c03410388220340041210803c45841d100c25964007034907000d018290403114100f8031b442030550400501d6400a034001070300400d20040104001800799007128112100601c2c09405625440b004035659 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24807793 1250 24806543 24806557
    0x1090b0d050415141603050705120403090e0115081006020a1b050306011202030d030c020304060f0e030304030308012301020606010c060b030708030a0f0207030203030708130e0c0301140301090b1506 87
    0x10901c4d00664031400c0003190303401c501030101000205800c401e030640450640700b01f00d40304000180188002d52980c0f515543c0701c0d410038882c6c00c0c1924220b855002000342150b0036403040e031603580722080001e50190080c6801350000582d401d2085030301d04040001c6c0d50303600340c004003c240b0001c00b980ea16460f40030707032948405408010142ca045507564003101c0003444503490142d2103070080c507105100c2c0701c2c001d12480d5000030094001d1401c1c10319150080e92084218a142c10600403000c01e120303241e45e01131005002a5109407036818447d410085400c843c0740c0360318650721401c01407840d03002d8103030f80003d007040e408802441d013510041d201e407a055010300891981c0c0c40d0143f08440700402c610030040080c0c002c400350340d601e9a2200501040c00c83e40c50340a07101c06074050708200488030116508000800c0900180b03016000c0742d075a200001d4400510444001140d064003100600148859004400000500728000d02400c1e2607a1980880042c0140000b00d400d9006680b10440d6243d0106881c2d103 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24809043 1250 24807793 24807833
    0x80d02040807051c02010e0f0102010207050102160311060112060203041401090b060102190206030103020411121f060309082a01020c03030f010f180507030b0604080f0c01090b0d0504 80
    0x845556418155441e00d42e409407500c42e002400007681040740e0090000b1003990140e480f1130030740580d070050156601c3d0301451103045540030400200444c1d024001000410040080d0803c0e111941c1802803ea98038180c602a66801010040042104140214501580090740140c2c2da45451900c0f8004c225100c0b811905542801034440520010503c071501c43e040070f80039518641014503049030409800c280003940f0403c140018405400d03e030b44074034800200d80205902c0c1040d00e0b0318102600c0c5048400003401e0440703030078034440740c040c45065030020000381c1070503c5642015070b039510b5640210803400315a48041142070080f420b41c81e011860500c0000021544c03204041102c40d260790044802d0141300c50359100004030b0440340040441143ca40c020001c1000a000c00c40401800c006801c0e14105034403011000e40396500d000c0144001d0004000a110340725021445e0742c101105031444c2810302510340300401100900c642103440d1a88150030001c0d1560311460310800954504c0c180d20f1b0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24810293 1250 24809043 24809047
    0x303010b0f1306120506030609070306050c04030f0f03031410030807020301060306020a03020408060603060c0a08040303060510090602010c0e0604060509032103040b0c090607030305190504050304090b010507050c0d080d02 97
    0x140c6141c205215190080c0030b290306021039580d906c00c0c0340e916041501c000c0e031117034012241080460840c4d406560400c3d200070030146007543d00d031a035102c103080d5210180c4070000c0c0c40000d0b008144e01849030488180274464419280d1034501800070301d190381d600c40039049078000210501103603020751104001d1a03000f101191255060384004000b50860b0184003c580b01c0c0c480071848600c0c0002d00d0320f10480c0700c2c0c4003c0d4680072040c0400c07940600b01074801c4050640761036000c00c0607901d0040c540d110020540e01d8026040c5440402402d50301c03001d03410020301c802004880f9260322801c080342d0070366416080c459a40e8840c00702003440c0100c0b081c00d08102e1151090a5525080b540c0010b40c011401420802d0740360301c03050340300c1615114180c0540d5100d40c081003020000b130b0298203d5940108e814110860543c1549450070550368121011601908001401d0240900610591400e000c081c42e0090a1910658419966262801e2010f205048203940c4004100c40003040356107026207118155 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24811543 1250 24810293 24810299
    0x80403050c0d05040807050604080d0e0a0e07180603140103020111100204030f11030610030f08040e0702010501061112031906080d0e03010f11030601030c030b06120117030c0303010b0f13 82
    0x1400f0703800c0740c040c88905005200e400a01882c1880c00c0e103041d0348202d006440d050250b41400d0303072081c560801d0f030740c0c0058001e54009000300d031a1100381d01c64552519030406080c0600300b180400e1030150803207801e052038880c01d10300c444001c11003641940c0d070a0078410f00344800b08000d40d2038030842d00000d081c1e4a0000030301100f00400220380c0c6036820310500081440c206104101a2121021103c40021100800f01000810f00001c6111001d5019000321840e00b916814219038a540c1194200c015170344075401004070940c03110782c0480d503c046c0c0c400780411320307450310309048648406898050076021140f03070304400b0100f1740d00a00052003240304480d089214146c010341913081d02910580f10303519294691192007030340c0c040d1801c144450a03031145582cce00d820041d40180740f4010b044040581d02d8441d0646611030300b00a007680013003154241d0096151031180368040000500f076000340e0300f003480b8240b0201c5000054a054a40c1502004c2d11101188445084d5002c0c9801441940705240400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24812793 1250 24811543 24811547
    0x706051308070608070f0e040501120507050405010b07020d140307030c030201050601020a030f03090c030b090106030203010f0c050301061d04050f01091a010914060415080f09060f07080403050c0d 86
    0x20035000091103284050345540c1d8403095100c1c00345101d003001041094000469062003420041c01802c46400c0042030031100c0c0c8081011500c09800180881d81c01941c0784013803000810888000703000803941400b545d030410f01a8107260041d4100280507198000d4070504001841503a507920404c05800c41c0d0f21503c91742002865501108010b6001d9444c1c0f1021882651010411698440d055105d00031b800e462140205c0c018010f0301000e48100711440c2d07010000404060b03003140621511800030904a080d40101821140018121100070340340100c03102007290404107503070469246044c42c0602c00b0307014030309412420881405a44c01884c000401c41481030038040c1606039401050b0402c1602c40503600b01c036040032460580c50105441000400c0302c61903444250038129009000315040c1035440a904e1100d064004010005c54100c03410414407600074000d0f2544280e52600400b058101803d0310103880d10b010341032004200d00d60300000d003414014011542000e03224002c40b51144c44803600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24814043 1250 24812793 24812797
    0xf01140405031c08100e04021002150c0a0e0a0f0302040c0c0516090e16030b0601030b0301020708040905100b04060f0302070503070507030309060212030f09010902060d060f0e01270e070605 83
    0x19030000c03841c0140405c4c25200d00e41a00419a01c60300020a95074845400b040045004000c01e082103100303042c1d03000705031040306070903902441c407003c0100e40301e1a071103401a203401906d000c1c00380101e0358110100510328020030501c08482d0169000510503524420844e010640306078040e00074403818107403400c03844001607150b0031204032031001c1040d5600c1542c21074a42e40f9600080c9620003003820180007040764450980c1d0800414140064103002d0341c5c02181c00e80e002468141c0786210089010000c0030610700840364403a0030f01201c1200c280c180181c2c0307401c501613401403070100005540400d02040c001d5040b00c03440e41d04082203030384803007062800740c0d0b4400c13080c0011000145034550000707025000149040110407003907019401d550700d603060f0030007039500104031000c25900e80004002503100d0070024012400940170200350b56082502c480f0490700540e100e40c0704058041c00400403418940005d4100940d030028451000c20709290110103020150766098150140b03081c000740c000e0308000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24815293 1250 24814043 24814093
    0x106030813031b15080601020f1f0b01030b0303041503090209090d02010614030a240e0d08060a060c02060306040906020a0306170303090607080a06080d0c050c0904020f0114040503 79
    0x180c400000c4410100c02d001003d900e10482d400c1c803039403001e5036210700d01031042d803644520f042c4101c40b900c0031000382c3c5074a1700901415a0300b4945100c43c2c110341c0ca0043d400b03010401d01082c02c040c46964007501c00f180d80c9201e5485140b150241c2c016984080e03034840d400030400603070018029240d078140840048d461b03040240000e00950710701000003d40c0c24400c40006041d507402409001c260700140c42d0304070004e0340000f02c104556901c001d04c002d0041d06204080d1615544401001c40d4282d11501410803075019041e00e1151310444020010030303074007a5190f41d0450381510229100e072030303d8010401914003174a00400e00d0780086051060a54140d00030002c0720001051600503004425200e6240d10040e200c8070a20342040d40081c1d01c1078000d002803a0404180203000a80d1a621005e260900240c846240001140300340e0302424000c003001441c4a08030102c450940508150703001544100d0307000348250500055200f481e00c1c3c03c0c2c801c0c017510024074015040e9041c4103450702c081214072444c16 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24816543 1250 24815293 24815303
    0x906030a0c1b080412050c090a0c17040b0a0b061309021e0f030a020a0203070503040906030b06061c05091009081b12070303050c0714060402010908030a02030318010603081303 77
    0x11820360081e1600442c000c41035900a000e01d45014180004903c0c00c1060900588845c81041070654094590000c064407070f03502d0800014070b407000300c400140480f407006203a00d91618044188000b08101440182d0800b0714a0000200f6041110208100e40141000a0201410710100058840058000303000c020a44014241c820602e40d1a062890085c0e550308040a00b00b0320000355049400c2d802800924100e0040b01e080c000a59252840c550141d003202605540f41c20040080004590255400c01000c4a043e800d00c040c0036043c040020711800018000b5403a0408110034120a003c0030880590848040c40180c100d0f04200305c160380300d142d10300840130428200f03600705c282c08502c6003510a1801e25003854135103541c030b0403800b418000e010105071510400c80070340005c2c1c0b1141d4494484401c50041c040340c0c41c0034000909504481c1d44105940d030410070062002c60703808811280e1040da000440012103541903c7c290040080e904000c100d000009503043c901e018206220044038420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24817793 1250 24816543 24816557
    0x3030703020607090b04060c020f0a03080c0d120b030604061a100314010902090102030412020103110307020f060a051302130609151a0418020304020f060a030b0406120503070b04080906030a0c 84
    0x180c1503030003061046104107c00070329003401000052514140c6443d00c3c0c00c001703003070325900c6031203441c0c050300c81c2e0064880c8243c0740d00c02050048904e801004280e01d000c1d4481e41000203810b904003082c0c4a480060008007913564844040710344003482c031200c1e8400340003d0143c440c15542220f01800801004040f4071040d52588000103400080c0c0c02190614001a8041e41c14149000484850014410f008a040c141c680030449017003901c0310090751043c1c44a5000b044402c0c1d807a021181002c10242140c5015810601041201585141e0850341140d041e51020440320307140c28180001c2034283c2100c1059820121841001c05002c1405425200b61060760111715034001404d2016105620810b420a026400385160615003a4051a07000f40050b00340c0300c0302e003106000110240d1002c004070010075520340e0a2000e6050031b1003180040e018030140003080c42025120140e5034000c1c417400030125a01d28000404108035001695180032000d040c1684904181c0203120143c0503d1840c40d0016906e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24819043 1250 24817793 24817799
    0x2010603060501080703021f02010603080d090b07080114060d02070506010f0302090a0c080f090a14010c030e0a170a090f141e0d02040b01090e0109050117060405031210050303070302060709 83
    0x1c003085e44012658000c01c61034940e0701d06111f00211030711483c003440555684d01e400102040b02c0c803009202000c0200c80c00522491240b901d1480413030302512003001c1010102c0103001101740b4145c40d4000000480d400c80d00c0e085010840c40191003028802070190213203a0000031980c40c3c05085000b9a0701c01c440c52295076485041c00c01c03c407010b05a0303242c001202800410a02c1e12410001508104602c042d1440c2c103000361503030b1880c100c864080f4600fa03035441d1502c2d040240e161061600c41e80340b0700e000d0700700d500c503940381c030700e01c0e58450f405c402144000013a202004c1401303041404020f054807001201c4090707541d80c2c05900c000304400c0701d42c087c803000c00054026080c0e070300d444901020001d20000f0052913603001d000042c00c000c0070b61410301c10580408075204c1c0042202d640201441d50000c03895606014225140701c95981c1c052416600000502000590120a444020f01143c0143e10259112280100e40c48001d51001e034041c0000940c2ca4217055003c03038403520900b81c82d19600f81080c4c2e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 24820149 1106 24819043 24819059
    0x306040908040509040c180c0e0f19090203013f03050c070803090307090c12090c0909030206040b070206010b0d02220b0a02060c040308040e06180702010603060501 72
    0x8140d1b10200401034030034485c0112081c6000c8280040150b0f840c0142c581ca150500c140c2c8907452900078070300251200c403900124900d4402c07044401590744e40c05c0100a600c2806180c010780766814010710720602c40c1808030010380c1e8000030049000c0f03100141040701c001c0c000e411405c1060801115190140801080019059001c05907030380c1c0e44403804151815410f9030205910798107103521281c995030400c02c80750342301c07400a0340401c81078524600850b420300a50015800c2501c0c0128100906500159440c411407050740303882c2440e150070909983d580c0003440707000c440501c100500100a42150003805802401c8079019202d01400703558030303984d4903040d003100101d0f190100369640081d0341003003241e42014194916902e0542143c840d0002c602c04e0340038002c914448480480c815454003908641801a0306403090041d04144a000340600664402130301d20b41e090000100300344d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 24640293 24820149 := by
  have h0 := BRFrame.cov_init 24640293
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24640293 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 24640293 ≤ n) (h2 : n < 24820149) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
