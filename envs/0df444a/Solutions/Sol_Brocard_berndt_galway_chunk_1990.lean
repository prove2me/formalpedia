-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1990
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:23:54.622125+00:00
-- url     : https://prove2.me/submissions/f116d3c1-bae8-4512-a1eb-7083a140ac16

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 357733812 ≤ n < 357913669 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 357735062 1250 357733812 357733867
    0x5030108071806080d12060b04080606130e1e0d0309030516030302090301020c100506061e18270105030f070303030b060d110307090e0402060406031a1201270c0b 71
    0x1864840c60ba0b82000c1b11078404d9591039402d000641c2e89014172000c500651003294102c5e005540018003d20b400410b10023040100784000591100030240c15107407951480d04110000180c40540b080310204002e01da00c0c02d02580341c144040e4000e0b94004003103024900d42c04040c24000300142e000c15000390140c40e40a14041d001315222113000d01015500c99010103846030b690301d0580410a9803d00d101191502103082031075104245000c02e1982c010340c000c0740ca0b4031075140f0500c010280356851558a080441c0504002001c500f5080100104458181e008038460b07400360800041490022540c2ca00b1281c00d400e00041d00450180800c2e0244101c031007801c1034900d8034800300030800b0001d010b140951480d9903481003654039010b01c10201282690084d5000b02c09000420900744213800c882c400808c42071404000d035082c030000c02c008003107200503052165103450200c8c1a0701c0010724440340428031001d00001031388054803460350980983c0900e000d02c0384d001810002d81e4a100b040c038210491481e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 357736312 1250 357735062 357735073
    0xe01030b19030308010e01080c06070302160308040e0610020d0c020d020a0608160507020d02060307031503060e0f12030103030f051201030c0906050105071505150a0807060f0503010807180608 84
    0x140e09900201070720b400210045441d640c00410741c078001c0d00205068a02d070b040103003098500320040140b1034104a40171021445890254401100b800000c00c00940c490940030f500c560500c2c89100c04c0400080c0a54016651a038060a000d9400251805c80c2e1110b820040840c0c8d2287c00841d10282c0c012a019420440700140000c4040e4000f21582c450b490124000d51544a400007c03034581c400d80c0c0020758007414a000307003c050315108001316000301d89403c00203141c0310000100c0c030209000742d0050301d806a44c5d008001c9048000c0c0043c030b5000c842c04002c3c014000d10011054902d0006000203410040100341c82141203020398100c603032840c44903e09042030340c1d481c501480f104c1e40d2402421340003401c000380084c4a5000701c050307440d41640808000380100550200383d000341401482c81101c5280c211402c9810f4030703099000c002800c1120043c0c40820b0400c08050300b07403d00c03003181c101040420801000321000105103101580c42d690f43d01990026040c4044014042e83d81240ca43c1340900c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 357737562 1250 357736312 357736339
    0xf0901060302090c1921051005100e0a08070e150d0b0a05090c100804060f0f0204031511030405070603230f0609060a0609090f0e030f040e010b03060a05010e01030b 72
    0x6202510500403100b14100045881210841b15406510401c000240f00003c003201c1407a0680c0195038860310003035140d07044a0b039441c0090440c0c0507040000c004505c0d13860446400d8280241203502800d040310040060300d1502203400d280392801460452039001022a003445981c0346026070392011b40002038110340d030600340a0580100383c290340c0064284a003424044040c2001d0355455400220f584641d5210f6999031212070142c10108080c10210f655445080c010881c6840500b014602546081c4480c0344d0035402002124000c20806109180500170003000a0000420206840007464007040c0c9000391000c50a003a00e00780c5001c21204200000c10490509954065100744022200355070551201e00500100384014001c02d0000392843c54140900a5160099207068018a40c00908002004040303411b40e002542c0c295900304c40068100410740c2c5420110f80904000e66865186042c50b03400200e59105030f118041c103002e10090004001da02960200c0701c211800790080741996072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 357738812 1250 357737562 357737581
    0xf0f030718060c020108150a0b0c100b0a0528030206070602090f01030507231b03120901060b07060b040f0e01050a0c0302090a05190915060f02010903080f090106030209 74
    0x481550390003000300104000070b00700d48a4002c42280c1501a160806d41340c4654000d40040c0440e00011504003c0c2d000000405001c1c0d01c0040185030a0407014100b000609401681a103100b5486280b140c405858284019a10114400c811960790f1200c0407512441d004040c3c0e070b10707540b41d0010750b00860124404051001c281c00400884a088401e0000500024010340441d00d083e00c1040001394035904c2410f51700b17080d43c2420300480c03444c0310190820038030040411101e000c14150300f0031a040400c1001800c3c10440303803181c002225800170301180d0b09003449241c0358015024041c100d41d4681e80d40100d0b035100d42e4404011032844002c240458008901c1d198082e0400303841c45942c1620784003501c41018460300c241c40c5500c41c0101045c61242c504403c005842c900d41070b0a00f096442443c001a42804500c98010b000c6c00403401c140156140800103802540d18403070381e0b010b40e41810b1541000035840900c590340309142410550480e201c1c90542070050803103800003500002c103082800011803 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 357740062 1250 357738812 357738827
    0xc03070e241e2a011418030c10060e07020a030c060c09081501080c0d05030708031b03040c03030912030203030609190603110f0f03030301060804050c1005030603150106140f0f0307 79
    0x3d0048080e402030543c0010250884a40301c0304041621880c902140e030310802c0150380d00210742d14104072402e200d820b5503020309050584e41902003040d52400104010200d62441a6000f581400585800b01c000c1d01c000c0d0a04940c400c2c001c11043c0da40c00d0702c1244a0107104003402524410040b640c02c000c42c0c40c1103291041081c05045894070800310b001d455403810401002c0301e40d500502650030401c40b03540b609005c0e0805042e81140704680f1703048403800c803174200103544101d015000000d040e61443c140138204282c242c2000b08224100c03c0b041011940000860f42c00070820b64a030f910b036036141840809000040221004030900740603000007408182c0440c41072080e0100c4048411403000003c00c803614070300304c403801e4141d0070520042050900526a160340300307020344141c901c1101c0440c00104d00310303403401c1080c0100f80044140401820200202d5480c18881669218a9414010060075100c909440140b44007000078850601c1a5110152455a603000394a9a00e0b0b040c88075002c0e1080 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 357741312 1250 357740062 357740107
    0xc030921201005061c030c05010b1810060810050906030705090703020408060901142403030406080a0c1d10020a210f03060f0302120c090c03070e241e 66
    0x460519020401501d050200001034031031000e106402a5031aa50947c0c030150701480c281e540c0c0d5643c03d031000480d00d07094003188507003c01c031081031a9464008400720001d0455003000c810030004a00308501031110000d81070560780704440840903952100d001a1400e5601c4e089540c11540f0202031000154154003d00b0070341c0c1e940d1095400d40d555841c00703107003210150032550f551111903602284c1031016106400c0f010750020f070f001d2003005503000b010a145070f0081e0304c00400603004504000d12a2518842d00340c0c0200146004969891504118422042c060500c2071181001110308800ba038020401000e44a038046141d0419035003203c41c45084011500c410804607800103074880d602d134400c2c41444141d032034804103019000e0070b6400b0700c00441103040185100d807060002c4841c0903981c22241c0380c131032035000016540d24501f13000000c0c80d040c005000140202203007021310b1a018100210040e010041c140040d40380c1c01142c554030643c199040040005010004420239003050328010b00503c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 357742562 1250 357741312 357741343
    0xa0b060913020d110705060a0203060a030f03090e0f04020d03200f010c0e03030c1c05040905090d0908010207110607030513030b33010e01050f0d050a0c03092120 71
    0x75100f134140c1002041c80307a118020010b030081c10000b020030000754051504820301500503030b811600d07690f0355058081e25001c203401140000008000c0f00046405007688080c046e40940010f00709039000c140883c0d03044400805011900309103001c1020803001070601840640e088420f20804d02022034001c02a4400c8000012000d00c1100c4c400d0500100702c40340d001c5501d008000b0404031f10303e601300f100801440305041000c200400500e090175405014052461800a4a20310b200c1d4000030300003554a50020500d0390052100b40301044404000c0080d0f070b1804d58001d541d070748140c50100d0f224801c003801d10501d840c1c612004003e0122212066114402007100c0030914a040040401b00c05010641c00c080342180041c1c00b96076500c91b00550042a0040c1801424040b030481800606c0e08117100d2400b50503501e07400c001048006000c0c2018100c01410704100b49440d40e1140002c0d0240c1114400405148280e140040b500c65118031351009403600741654802800c1c0002c0751101c04d070007021000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 357743812 1250 357742562 357742571
    0x60f030b09060610030b060f030109050a1a010c150e07030b1b0324010207080607020a0314180105072909060a0b0108011505130803090a120201080a0b060913020d 71
    0x4500c0000580c0c240038810007000404601000340c002c070017409141b0389498002400703214003d044145c000295004c0e0900d0391000c02d6614003111281c0803141d161045800746542c00400c0d8400344d130400c0302e214500782c21046c1d40340c0302040041828003909500c80b0009140c0701d90280041403280a00e6040c1c06540c0d11014520032282544c681c0490b0300080d55401e003984441c0710003c400d130110007403051a1100600640707000301e946082c500d0a000c411a02d101c05604130154510400d0307441f15041c6d1b030328035040b40d0b00c90034405030780c400100c81c566a0f8103da041c45000500581444401180b0308000d0990711101003410074191002c13050f0b01d00554000045118110101d1648441401030200c0d1503410b95500b02c041c0c4c60038084330340200301c880001081c007008200301d000206003214404041c0c030001004581d140100c100388036441d000c980c401001c0d540d00700030307000040c0e03400102d940e0000250880814010035a40010f0520312844e20043d074442c0008500070700408040d00a800c03162a00c920800 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 357745062 1250 357743812 357743821
    0x8040906030201080c090a050103020c1c03150b040b030609180109061e020304050a0b180610030302070f08120a11060703050603012003060d032307060513031706040b04060f030b 78
    0x101801b80705e9105a001107090401d0003d035100343d015225030071040088644003074a00b0380c9804160050742080d000070752030300b4849801c0c80210300c884004000040e90710745001c2c0f070911504440e010203000701e4880c0d555103020030324411110100e80394811000c0000c00904145180c000001d00c0e22907003044e2858003c0d060891030403100d109403407203140c000001d0846098666200c012800c3d00600341218000c02c1d011034034540781e00b044214800c0b1168640c2d00012411400d019250160300e40c0804c9944490450501110130b000c108054014040307011541c031140c2030b083c10b581c41c1c50a81c5207070440d4800c4104001c016941a00010302a08055008005000e00d20103400d00c00c2c1050720f007031510b048007000410460700b42a0a10000c80d80203140c0910410011315252000014010700403034894404241c0b0414407002d8454550003040c1c0a980200194040d07501905420900808a45008203800003e101d13880ba0380208032405002001081915203403480c0400e0f42280d804199080c008080024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 357746312 1250 357745062 357745081
    0x1050a061706060412060605033a051207022a030c0105090f10020610060216030206030709050901080a030201240512030702090408030402010806010e150c0a0804090603020108 77
    0x8409452590759290303a240340d907240c0501001c101504141d04600c0c101301c0096990050f64499120781d22800e008201a81390038101450050700000e00b502100150500481030110713646031040c1c44445500d091600904001c003a10710303000344400220350511040800098607030100e445215901c0c03c8520902a640000c0440d52001d01d101d02c8039003561000b1030b03521256005001526545400904c0b982c055284440896038060300021450702590243c400d0040b80024840c0c001c010706414402864914800c1c2046d01c00d01000e0300c4080c1c003602c03000000c40c07003035072140758280c010303120160160505580d60201c00380d80d01072842c001c0d0015460812100c100b040e45030100450408035040f00e1840354104010000806011020a0301a20040015000503103400c044103200e203000d0207034151070785882d000142280100801d524104210402c0e0120f07a43e17100d40500b8a1760920300c01c4291100d071a503003400c2ca000307642900940140408a0006625a10364100a0a40f0f100fa0380c2e001240c7c035003080d0b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 357747562 1250 357746312 357746329
    0x3010f15172b020d030606020c040b13020a170c130501050304031101050c030105120c10030b01090918020f010c030f0305062407050c0307030f11042d1803090306050c040806010e09060105 82
    0x601006809c115051001841e00f0f0b040381c09041002421880c09102d80007030352040742d0110300a41c000c030305170140602c5803c620300f011540c41520380300200c0c81d1000390134001c0f415079030750b00901e4144040400410145446428414a480010301c020410b506100398080c0b03880e042403003080e100300d0401c1d4035007a00340e83c0400c000322901c20107010552601440350040d03020b004154000e40c1040140c40000900e03030401d00070101c00480301d03104010400924014405d01c4595034100c28140720194400500107940140503c040c0da410307183c0055a0740ba207d0009000c4c164144404070800812002010007542070300043c1116407040c01141e0040721201c081c940c580700a40300c00f5220640c804415004100280407a11000200400016030761955440d590856014fc5040c0d103e880801c0c00305000d160072382c2c42001c20b42d5142440d80c072450403440c3d40c02404500c8901009180ca80c03148041030001d83d11106403806070101c801510b01544e1281818043c80c0002c407000440c5210b020300014142c10122171 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 357748812 1250 357747562 357747569
    0x10506121507030e03040f03061b0e191511010b0a1203030c230d05010f050d020d0606050d05030703020d0504061418060c010b03010f15172b020d0306 66
    0x1034500c10320701d090901c0310300600516142c241501c3c1c40f103007421080240001d101070500c6440360003c050031418018115507400c2d201c0400c051892010124441d04180b44041c0540121800c8009d605110046050100940d10403e028240c4810307415045400055a0081c40d211074001c01c2003c020b641000145820b51062070400541e518020010900c00d400041c41070055041903800b00c50084078035a01c104074400b03a04d0b00c900c80400c01d1a0203030128050b940c014a0014402c491a43c01d0800240c00d080040c0c10007031041c03840106070010003c003904480c0c0180002000c0c1c08030b003001824156101e50250740120014018201c051074054007030801d0710145d980315910880c10500d8102c5d14101540140203840c00811100c1c00842550303201801020f4000a0400104541e070b031000500d4207544501c5070140202e401d0030400c0c0078004105480d2421290031184400116160f402124240041e0319000c031000c4000900342c3c0410401940e41ca402e03050242d00700c80e60305c20b040408400b100c1d142e01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 357750062 1250 357748812 357748849
    0xa0b09070f06050a170f070f021203130309080604030503060a06031112060d0203100c1b1106030601211e05040f12050408100b0109060906080a02160501021308010506 73
    0x70050008521032070240040c00410300705400142d40d4a1810b03c800030b4216014604110342004010801350b0040400c000001e0707900003480070045400503250340c0c0c00018002001040c466500f50181441003910030003d10300d4400b035816030f0510342002845984111203840c01510f219000044c400c0c0303e0301c101c607188140000400d06028a400c600300ca40807001e031141b50700980d00c2d8010b0f000359909004141c0450143c1c40001001880108081c00c501d01e2850b07108249000f40201030040b408080d2107c4409004a80482e520361342c0754016141c4164091f0700b0480c039226241900580784982e03003c0b00140e0510b0400e001e41e944102d000005640c41100d0090178526031500c00d10004918a2901145158a041c03c074207250705c41080e03e241c181c0c0c1769290b074109902d42ca00d00441d542c0068001e8050a072501d08540400d0078003202030444400640303446046c0d680001c40f005100b80d030007220420150302c04001e565824140100c88049111806070308403d500c2c0c200800c080d0301d8045086140c104014 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 357751312 1250 357750062 357750089
    0x131e080702010503040809030303070309150606090b03091f02070516052101020d09030801050405010b070b18070f1502070501111513050105161e080c0304150c020a0b0907 75
    0x141d0045a19070009001141c00390810702050425a0b030a0003d5803041d122940e00240d103000c2c50411800103804403c0000b8003a02e0b0090512032554854010025150300c0a1412360300d480700b8503c41d140c03203510705a00d048560042100010140550000c00800d030292040301c0600b0080c10b10071800700d90300c1c441e60b680300c090402c00f41c0104204002540c0e01e44040c800040c10320a000c41250306641d614141140024203100c0180300700e240c2441280e014040c4000280c2c103100c02030791030842c00900074250309070041d040151980c0d444000c0150002a101c21044c1113a15580d844000921030880230481001d03018018000c00c1030f51141a641e0781100702880203110b840b000351908110000081d00c42c0b116135180654000115009000d00d60003500c80c103081c8004414401c000812802002180c50408a02e0740003118403654400240c039001590b0160190f80d0f0384480c600014001c0c00002013342090a0504d950f60140d00441c00f0f10a99000d90740740c0803c2d42d64010702c69142d0009001d84040c507103c9 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 357752562 1250 357751312 357751327
    0x30306240f0e03191505090322081f050f06100e060f030f0702190503031b0723120903100510030c180c020c010804030e010302040e131e08 61
    0x307184200380384005003820301c0c8401041d00400d044c901042084c03d45075203150302000801c00025540c88080030081d00c10041810301c5a9459102d01c80d05010a01804421017580b01401d01103003130038001c1880901300c030024205251089000c081c0080502140c0c0d20f000001040002c814010754400c1400a0641078141c032404410ba4050041c5d642c3c0c540c0007003003170020141e043c803848000c5010740380d40209083c491800b060000d00c1e03c404900c0f45107080d01110322410004071f0000a80b43c200580c0159140c051850304012100c9015800d0003900d0860b4042e00c0c29520460500510360000d8a1810784e0203481555108101500c60701e11040c0c2c0581c020b110b40d018540c070070b03805160400d001291890103255aa110180110300d943c200c1c503a2414102c08010000c1d45521815030140b40a002400c45d886102c00060711000c402030028050045041414443d03a109a0482d4060800540c00d00c119081c039014900300c825010303000312503c000c0b42c0551034114541e101907403a415401402c0b146007440 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 357753812 1250 357752562 357752567
    0xb2101050f1f0302090c0409060f360f2a0906020c03150a0608070801230105130f0b040e0f0706030e1f06051002162106050408070606030f03030624 65
    0xc01400081003100070b002c04941c95031240149401400800340c000f0340540ad16160b0442c0002003503c80222600001e46500d11035007103030442c0c181080500c40000c0724cd0a00401c1c202074078419540800110009507403c50125080400b04810314040e0741d030940701e90b16280d0580e656020000055810b9200480d56202c4a0580b500180c1c04820601c010410941d1401854502a000c1d042004daa035120705000100b00702c5c03084003940001c0102c4244200c0e501d8500825800341001c00164500d94407240d00164141141d0403a011075400a0020495000311004080d141c0c58a100b9580c02401003420024419210740a1600180d14000c0504050240d04c4548040384075100e280300a0030b5214400054560f0b1019605100000960080c08060110f59900003e0700c01c0c030340100c06c4001403c0e025001d26201010348101c113a521034000903003030300c1d9410156030501a64400814150400304007004110510700d610b08030610a44003030011035281e00c0c00024450681b000c1c80c001d00c4240807010441403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 357755062 1250 357753812 357753829
    0x190504050d110a0e070801060e060702010e01080703060f0b07061803020715020c031e16081c031103010906032108040b061314070e0406180b2101050f1f0302 69
    0x203200403c0780004698400e048078182e1003c886241c0802e41c1c080c0104440358011840780030344102150000c0c504006540040c00701710b90b00d45510b040118a01c00106071178002e6124201078034019800c22000d45e40ca01e895a1389a10100040b21400d040c0010320105c40c031206031200c00e142d4590007514095040417481c0385510300041902d0118407814101440c9030b2001c1c001005540303442582c1d0513983c0742c0d03841c5551410780b0703400d001c151444800f0707800c1041c003001094000068440280c1c0d03844000120000310060440140b1a400000000000048681507648050202c0e4407811404104410701840203040300c18502452001c1003500d40000d0000d41010780103548054028607400419118414001c12203440d500103045182c0b9807014880d40740d070411401180044200d500384015828207100f000d4902410a8914180e51225480c01441e030300d0141150015189001e5151401d6201940138040d01003034030340b01480452203010840a00e01c9200030134082d80307200c250100031480c40d800e104068 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 357756312 1250 357755062 357755093
    0x1140109051e090c010e0f0310020307020102220503011d0d0e01051209010605120d05040b090307030b090105040317040209060d03030b10020a1211061302011e0302190504050d 77
    0xc2640300c007507042c8409141c0350500400c690740c0100780200c6088005424240c007480e0052150b04081290507032a9000038001e5294500c0100143e00c0340c507540d005a029009002949142440d0035035980b214a0380c10740c951086403003c500a003c030810703500396039102e4a82040c0f0424540c10400100c91540d0041d982e000e0000300601d01245840c0240d03002e0302d02130f0f000340c40301441030b5114441000707a8130340744a03420740001400c000703030400c1c16036000d000d01144290320444903810800319006406960502c00ca00c01103403c800c1c40b200713030302d02034400900a210444084010410480d44600c4009089101612440e4080e04441c041d4817100204284292600710850406844180e6560300752100803002e03100520340e80003420f81401c11b24000040b203103424208010003515206404030303c400040c0c0150084507140040301801c0482c00100c1c4d41d648000c1504081d02d000341666140c90b54160700402d60801404d114800e88102d01508603140d104520070150702c81d04c1494281d001c070b007403880c90030a607 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 357757562 1250 357756312 357756331
    0x20a0b0903040e04110108061905012619110403020105040302091305010e0307050606180105010507060609060b07110d0b06041112041109010e090303010e1807031b080114010905 78
    0x400f592003007002c40c240001c9a040303820101c2086a00c1031540c100c00280c0e00700c40c040b108002040381c0c1111000318130189104ac54100046856038086842d40604406c0c07800113200c04858491924400800118400400c1c1d09509440e042c0c903540031b04607500c00d48068a0303059581a240c40c1c655020440204009044141c040f426030704110002402446a8031081c40d680d0301440c0c556801c1c1c20002d08002c0300500d800e015900704036608410018038030a640c152030742400e006072110392070f050001c0200304c56044411040d24010011911200f024003800d1114816894403101c00c040c070080c009000c07083c200c02072110450b100400e08520b0680c10920403c2925400b142c07c0c100d86403511120300c1c0c1c09903010b0b00c1c0d0a40d900704a00184c240300c1c3c40c3c1d5014042200c0ca2002a00300118000d54a110504c504030750ba000310404030311201102e00e101d8200e4010501251805c0c0d44a04040c04841103008800300d80c903514480001d4603030018018004000600728070103100341c0c40c2402c6113001d054010040b80c035 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 357758812 1250 357757562 357757567
    0xd052a0313060905010e060c060103080304053306220c0c02040207081206030307030203190e030607081017071401030b03060406020414060f16021504171c020a0b0903 73
    0x1803104201024070000c05aa07902c151800b8500400034143d141c58003102ca0040340104411251040300084650440ea07100d020340d5560f5540381071450810021211500c40350079442d41c035000c44507040c206030854010a4040c562103886100030801c9200702040765034500c150900034120b018540764030102c0c0d1941c480c2001c1c3c46600c0c890b40050202c1e80064030441d003652000c0f844507200c201540165900110a03030007545004207586020b55079029050032460a110010000125184100b544a01d4900c005d0308840e060305007000c0203001c82c00100d8102c08954001e1100081100008021900340b240d15005406400d043c241801c0390b1364842142c41e41891b4844140700b186440803c11503103d039010307540043c0c546d030801c5280300403081d1140381c0b00d00c185000c3c4010f0701c0c460380b202e049071022181d00141502e103c0640c0b000c20641180e16801e503e118001090015404544d074000003a003190680a444070813062208403034025207000402001039010400d002c0000e0340c621030480c0c0104071802142e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 357760062 1250 357758812 357758827
    0x1060f0c0f110a090e01050a0c02070b0a0306050402041205100204060e1306081f18121101111c05010e1303140c030d1a01090608160e09070309050d052a03 68
    0x303c1c80d858992102c603140381d942daa0108000f400f88669030304000d4a07803003803000c6106c14400030f640e4813860003220b050040000359000083d0195100b400100409081992643d075603101c0700140801721001030316980506103405250380d02c5842141d0a503900c2d610b40c0c89000000500b03000204133340a1243c1d40c40707a40c81002280102e800c02141c0400251502488180894400407005076404145406804940b42caa04800100b4201400b0000310f1240340181e110341e85c540e10180989043d0301e802002840024220158000030044000001c4240005000ea40d07078601c21403815a82c112100c0b0008a4100079031130000e88147d540032131f51411102202c0c01c2611821149045034030110f8180b44254ad103001640381d204044440f0400c0388000d00700600102d10b490b4015298400003400b55054084441c517403203580780581c101100001021300009014038240ea005401042c2d95041074030b0a1150300300c008046481101250078100704c440c45400d940c60107035003c4001d1215010b045186010900c9080d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 357761312 1250 357760062 357760069
    0x20711030a050604050f010c0e060a021e061b030108070302090405070e0702030a081609090b061e1b0f15040c03080715050a151202061c05090601060f0c0f11 69
    0x11030600402c0900150f00301468140d180140444000342c1507418040c0b148012604945d4003c90504203645650356010b1b0300004074204418684a440446586140101c2902c070004405104005042c9904a660302400c4811114082480340f6221503200031001d00050070442074668100340304808603106039032149003400b2507100071559440103a201260070181d00303911982054202286092000041c000310b48000c1ca120500c1c091085680d403140c030540240d03101d40c2c00712040303036080c0483c3d81001131105520251590002d48601c00c0307603503041100c50041ca8007182e001040d503088070051842c910000041c45d0350400c0240b050300c00d0400d00c4030001c04109108001c00c206845040d1500340c900c800c1e0001012680301410500c003880c80e10480303048122441d03241e20151000ca010607400718851f84009206882040780c401c240342d044441405940d82d0741c2d0000c42c011000c80003a582c0c141e0301d0701022079409040c411004002402d04552038007081480e0907604103103000d0a51b041a184030701c07022 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 357762562 1250 357761312 357761323
    0x1b0302010e060a0b0f01080603070803040609080f010c09090911092d060307170106211103011e0b0406090c09051509010906050a02160311091b0d02071103 68
    0x1500580d44546818501e01c0090000e20741c00550f02c0010402d0860103000709510803c044885030602403140040344040d0f504121400c002c00b51482125a160303100da0b4010800c032207a1040c124180b10340c1c2d440c80e44036481070182c8046401250f440c3c000312440c00341030401800c001a015690942c00e10840d2640c6c1c2c45141d00e481c0314085914003a004002130200d0704000e600c8118458040c40319820500000d5034012489100300ca00d030a9245d40d0340300e0380c411524010001c40e400840b003058031545c00c840c003c40c179242e40c244c000d00a000b102c05c01605e140515082e6050600024034100c0c031a030303400c000403003590301ca00ea207510060000549241c980c00000304035003142500401013807d440d01000186000c88005921068852940e07090031030002c0064401041da004e208284240070501028547c07003040b40e04640c1d141100740d0f880403640c0f03080c030346a584003004140340106285800a121040807950101010030411b0600d0310713000d0f814030b002c03000703410111049880c04601100d0344041d603810000e = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 357763812 1250 357762562 357762617
    0x601030b010e09120a120b0d1103061b030c0a050d05040c080c0a05300a150c0e010c0b100b030405070f0608090307060902010c05010c17010b1303060c 66
    0x649020070350501048004421008003211400d91100450083c904d06030030aa4442d103681e07040c80507440050300040c41c040c00c0d1000d1940e03000520420110280300008402d2108035000382c0c1960b28544404800c1c04100720180071504c0d0214040001c03810883d4410000c2103862103604c0c0043c02c21400d452803100740c0c3c1c003d4070199400410f25905201c80304040c001e044813030320121140075503240380c10040391240c001c1403002c8203421803805003080d9410742884040d9404502d28140c13000000c1902e4009004a480c020040840f45880c506040150040718824000c2005860b02200710030560707100360000c0001095207409120a00c4000341010280380954043c41c4648046d0031003608020710025042003a60202040001403802d210003100f002c01200d101c6504460b011032003071024001a034468071007001c004c00541ca070070403510991f50b1029269455105a50440d81c907031766a180c2400103401100240403d014011008000180c42c0380d00c040b09042881c103000140f201c01c06140c07516501d0340d16 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 357765062 1250 357763812 357763823
    0x5010902040c23030a020712030b0a0b0909040f0807020d0302030703080703060308030610110a050a150204050901090f18140f070812030a0f0e0f060121110315071d0901060816050903060103 83
    0x3d401d6030f12f8034210407031030060422082c680d800e00c800440000c05e000000303003000c0c22004100b042c01081c40300c1182101d10040e000340000c9554041458025680d51000c44c0c01d0300041c80e0700b0081071580c1e1190085000726600403000758103503145c0d0020810394200c149245401d200c4540160303c11500c0600200310b071207004401a084100b581e05000c00c0c03c181159106900c01d00c100300600466480c1e1081d1815215405400aa41e0441d002d00c90010701e20384441e1001d102610b1301d0501041440c980c5411a0301811040d50b2502e08902d60040d0794400c240907012030f40e042501c4001c642d40e5110040c42c3d003c128050041007000485011004075090081c000c4610380003696080d07148035041100350b004000340800c4024808104041d40319050b00c4040c000c0032540035001003030840c0c1d0200f0152034100c0710329035140c40c2d50805000160842194400707400e9220070104522400d40340ca0070003141240c0507600e82040d10b5851f1030000040e5003000703000c901032110911a02c1c0316902d08005c1c9178042e501c80c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 357766312 1250 357765062 357765071
    0x15070c0b010b0a050a0c080408190501140105030d0e04140403050a080708101a07140c030f0a0506131a01260c0102100b060c060405010902040c23030a02071203 70
    0xa080109080c0c005030420340c400441002030a00301580001210000c03070b194586001d5503140f6142c4000c45209a500c045c4244c483c00050050307102506000105661290008100d104407201c00701031212824403820b54982c004005c1c1031a007038020039581c030403807000600c000766000564031888803540c026541640012000b140d0409150340009c10fa41d00302c1c60505149a1034900a540011600d00358042c07000b01c6209203101c8101d4038813040c25a401c130f540c0a9101c3d4500c6002031429690380045454241c4640304503070309101c880d1008540b02c2421a00040900034583e80c08507282c0c8130072544102101e5495003950500d52881e500b07500b09020f007000c039080203240d18809450060200125a418000d03421440c9840ba0f640e80010f000c192410072000b011a40891003000981c90f400380118251032802002d081108024065001c0d04c44544200c50411000350581001c13510005404076007150b60180624900b14001d2000c051640104086005490301009039101540c098688005001081c1c48 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 357767562 1250 357766312 357766337
    0x60f0705060604051806011806080102031e0c040609140d0b04050303070320030a1a030f0f101506030e0a0614090601080303090c06030c07050a0c0f150906111507 71
    0xf90140c641c21503001c20302254030140c2d03200e0003900d0390418451080400820304041c0447e0240d5000100102032040086440b4544401d1442040380400a02d03035648a0a0300000c0b07061500505072000e46070182c0d249a002401d1084030f029490030030f4220340c0d00521030511440012107003080076200b14420006552a8205900c01070190f844182884848101246494403882d0065090300d6004407003280c0070a8005941603800402c130081c2d0603494260107000c283d40404040080c1421510400d50220740c64903c40d030309450121040f0078055941030500c00b80400c8401d1003904203002d91809a426540d0385031090361003004a03902040d9050001e82c024041150390031003440ba4900400040b00550700c0c0d85058001e039500c40407032114a51040e403020011404141811065812440e030020132500c2106060070152a4a0040d02c1035035041c400040020030854072141c08400000c804d070b100c1c101e03040d00f4210151003200a42d000380059128031006a0002c1c4400700030a0702914203501c50285c00a40c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 357768812 1250 357767562 357767569
    0x1002160501060e0402091306090803070302120a06120b0903040506040306091103160504090c05120309090a09030c11040b09040b01171605060310080609010b0f0405040309060e060f07050606 83
    0x541d0148551400f404200400350300e84000c6243c0c000c00052070b1140842c494505580100904030000d1700d00c400100405c4003441e0194020a10300700d05800794035040e950b4070074070303000c0c2d030100e01800c1e20016145900e00d000401c0144e405400c0703070701d00050764145a00d43c4d004c501650815071041d44d0700c9851307038088014090302c400581200309007030b009040ca0220034002d810f1411998840c0ca03004640d20305000050020754480c4030080c042c001c1c21401c1da18030840c0031541d80d40100145510031117048000c943e0404480c41342901d101c0d03164440510104864a911303560340c000e0110ba54006da00d844040802d83c1c0d03070500b01840f80d407080c48510895410500290400103c425403501907034004050b602c0c0e50051041407804840e4201d4286541b552902064005071120b50700201e07040c07281320140141c405041d00099070702c1c1000e81d0300c0c0c1201c0300d804d0200025644140c90140204a80120038001c0510414264000da01c0c00341c801480d280c034040b2020341d030f6480400309407180d8111b82d00340205440c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 357770062 1250 357768812 357768821
    0x80a11100f06090b01080402060a170907090e030a090303080604060902070c03060c0908030d0c05070503132916030504051e0a09020f0d020a0c02040c1e0f0c02040e1002160501 77
    0x3401e20310404c00070480a0000e000b00c04041c2c006403142c032001c90042c0390244600d5a548070048203c107640703901c0c28140710b260b5403860540074a60019003043c1808140d0f82000003543c0b00d1418a41d2041401c6145440c1a0340e441c00152045030001d444200100310780742c550000700790040c85028866411441c505104007203504060a05040107030f100001c0001ca5400405e03544000200d00d80040c000b180c00005a40502c91002c009015020120b802940840043c401d442100c0d8a0300c001300061900c1c0070400c03200041108590b000b90400e10840c0380c54001c03503001035006482420701c20305d040d03240c40004113520305404003000040c40e103010403940c030b0401404840050007031140541c202804106a419140150384d0075228807a404070301005541d1040c8480011290050410094040c5118000b00000c41015800d11800c604040340081a84108403090f00710b5060380e82d0000710f2000d40d080002a0010180c1c0c50554440c91410f085c0b8210584028650042c0d409501280b05200b80741003400c0d203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 357771312 1250 357770062 357770069
    0x507021c08160206070504050105090a0e010b0301090c080606250b090d03110903030306010c0c0f150e030601030c140a1503020405010924050c1005010e07030e0a0807080a11100f06 79
    0x54218130700340b00d00c41e6041800e403070681e40c0c2401c15a8407019a030000c141c03403540560068a0352080c10000080c616288002507041e200100e40c00d00203c2013007030042d51555412380d040f90f00410100052400d0a9840d5041c00701d20603081040d90005805e03031a040300611007a180d110213900040c10400c80309800d84500181e0a060540030f45c100121200080d483c1d00000348440d0600080c501880200801c843d0701f0340140004002d036403010340d100c001c0100200300c3d600c0d10b000400c98012a40d030745031800017030560490751f02c0069040c1150602402d007544440c1240c20035045a003202c800310b12880e845803141000242c0c0d64006840d03510f0480010110b4016074440200c02c000300c29400401c0c0d07a40c01c108a10f519240c00c0069030b80c041d00020a2070149121950b140041c6454004120501584034890041e8181d940034032a0105141000307803a410072010080491004008510016103548047c01d6802140d0814240c8084400c1c3c8032403c007c003105030035000c03550300c40600c2c4c1c050013a0720503031019 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 357772562 1250 357771312 357771317
    0x122505210703060c140705030301030c0b090f01031a0405090109030206101401050703120c0206040309171b010225030b070801052101060b0a0c02041d100507021c0816 73
    0xd03410040c11164541605000140c80b00d0b07280da40e00720746580585e941c10b400981e0f24400c5681c508039800e05c0c5891380c00a0208503031004400074000f40a00f00c500c242e4001680040814404210740c4c40154001e00d2042d580d0050b400742120007024951750303841220f2251035808000718a416082c43d00034104a07005080a074800b1494005100c1c0442000d8624840e035000c3c2056a40c4000508007559000980380b050306c000c3c0d040140303844440e41d010504a0140780f00703844540743d064072205500c4143c1c07076000020740940e0044440808080032907102e0024640c060042c7c3c1c00600014107900004081d403403035580a400951010420088012552a03010303c1e6480c6c590300c1541050300284e0301e0607060003400c0001c042451050400b810a51000d13005051007640c0695980c0b1568000d804446201e03c140e10491416241a041d80c92514000f04c070401e400025140b10303000c1a020368020070b03000d041442103210b00c800c4120510f401c42441d1590307e005440c7e441551408100100320003500661308003c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 357773812 1250 357772562 357772609
    0x3050606061207080736080c0303090127260703020f0d02132f0906070f1401090f120207082a0604090b0108010b090f122505 55
    0x148000040b034080d4100c10149010400c5481e0010111425404020303940132500480640c1d4401c10458400c0a45c0b07841d001a40c2981036a030351810684400f00e00000c240c05070020441c50b1141c3d84a00c120019040b45030f142510000360f80c4400f0601d0303020a40000c95082020403c910b0032409a410340d68000c0c4e1540c00410341c02c2e0840d40882c030040d50070011a030069010f44084c0d02107566450b00d04100b032804260410171001c004039003000c4030b4030503690034083d24214268240c8002102c022035480c40c1003d00541c0c50607806030b4400c000c44c405100b05072441380d4078103a030745044402130051204140c001c00400196a500b030901a00b041010a200320655002c80010840b8080200c0d541c00321002c50102c54400c40c40e00b8588601030501201c01c1a0310440c009000724140c0000c0e400003017111400e90b51001242e0700e0f0401c4494611643d00e55540c488545c904055540c03074030007640c14a000c4004191840032043c0480740e003038945c10f034522002107020281d0520407030030b00b409161032036040d0400701c26 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 357775062 1250 357773812 357773827
    0x304031812110d0b0403081501090f0506031b07080904230c09271b0301060903080703122315130209010c0c060305040c05121906061706010305060606 66
    0x2080640d00c070001418034015400c002001c1c1d648805420455410401e81a114541407500030328182d400c0b01d45450394803445c600d01c407241d4802c1c0300510035240b0105201d000799050408015068200400900b60145c20040020400081901a0015a214468540d0ac48030500200300a48403a94104000c2454134201d20541034201191a0f070401080c0c140799948041c94030120b04081c03407041c2100e038440c0d40d0080550005820454041c07084030425030201110b074000910043ea031100788544000101050410710106001d0300017400f130948a0308250f481c0061550041050300c1c81003084130101c020340b9280c0071449c22502c0c00749900490100a03011000300b0600041c05030350004010145096011078060460303406140c0621030181c0202110b0620b075507441008010b860101e1303088a100d41d50f80310000302d5040480124081c48100070141083c03485a0519000c103250812080e1260780c0c403200d0001c2e040340c442ca1000407000b43c50740a40500e40c1941001c43c545400a80200d003c1d00040080f43c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 357776312 1250 357775062 357775079
    0x28050a0b01110c090604020c0d05070212012a1e0c060b0306070903030809010b18040c05030c060901210e010e060606030c071202031c0c030e1203180a060c020303040318 74
    0x9a000088900c540c480e16990003050090150352a0b8282c64440c0c9c0442d0700d28650010701a010041c403c50714501c0300c00d07202d0801400e03203040c500c88084c02d42d8846c030f109a0034a0450081c245000300d92a15048a80705900d8210440c007500c0c10364004074007400071a4060060300e00400c058480300358000d09040c10701b8580205550024800a410009140c000c00c005e00c01c2034120629020004007070580e9410b0100f01c0180240c02528121600d441c0c08100040c80c0c1030100e951060a2401000c840c2050a10001595070f030307035400020b20324203007404220700646049229221a152007480002a0004901c07130907460908060152482800b0034010401207503091802c030760103964001080e0003480310301e00b0181d2850041c00c0c1c504905031900c601e400102d86103903100d0b42d4036203d966030921482030340b0701d5410344038041c000080541001c00c100089034a80c9840440803450400000c0381d540ea011900c0307044c01c581d040808240107810000c02d020178141e10880205008441c0c440b004401480d00000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 357777562 1250 357776312 357776323
    0x60507230a031a3706050a030203091515130227120709150608070807082208040807060914040902041d1006140a090528050a0b0111 58
    0x280101034642000c101c1e402c644410311030707030030700054a9a0391241c490400000515080c0d0b220b0841000034806034882d13038280c448584101e031388a40350f492a1000e0300390210043e60000780030695600c10844c00020303030520f4a80140c881e120381101c4029031201d04042181c0500448010841c003401441120b40c1c8208030035042e01d10341086003048001c1c0350914007060350325182401d03440e0035000d91031001481600765007002ca8101d9030b110079400002d45800701512054006c1c0c0e494000201c04600141556025044494004c07007a0f688404c0c0c08185600a11401c94507408111011540458200b0000904000d800054103d50901e008424142450030401081c6946854410f03034985100d0801d42d100d540c8032001c41202c07120740084114200780040e90f2104d29000d1151380c2407501200144c5203a90680f41b440d881c1c4028002650700b450070074403070083c0401800b070b665021026a01c100700041604c0c03841a80194954020455141030240700049a0055500034148812000003c440480c04210b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 357778812 1250 357777562 357777577
    0x18040c0603180b1807030c140102010c031109040e16081c0c030c080f12040809030d09060512090c04020a08010e16142a010e07170303060d060b03030706050723 70
    0x81c40403410701580c5241c0703001141c6e0b00160052514083c0401c1e03007401c842d40c00048210a0f0000c0c00f180da8140c0d412401c42c4c2004000e100146000c1c01107181c00d14280c0c00017001c000c04001110800d8809452542c9128020381c040440c5900141c80007008480e04030040301c0c01446810320100c00011603d010740031040c07428004100101c0044c007000d00e80802c105440498091054040140c503040c41d000010381e0140d40e07c54840d00c50030201c0c84c01e041c40b500e400015074070b0030380d10030b0308000c0020ada6001140d0054411007041c00b8225122000303480380c5c800380504281e0f9654652455140500d0048082c2c8003402c50034202000b0101c100200360894145040204403000c4140d4400c0444015078030140e80c280c1346103007141c600c0d071306e600a001b05410480d040c240b00c400382c81000e5907070701401c0038004403444450010340050000036aa4034180100c0103c0d039008150100724070180300b0019007903902ca42412201c2c2680c0e641805500c0d40c0c042c5041e99120792464980c080843d0641c1c4e504618044e00c00c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 357780062 1250 357778812 357778831
    0x150203120406060f030c17120901050a12050a020909010b182b0309060e19050d0203280303140f28020d020a2a1118040c0603180b 57
    0xc0104040124a600032401404240001c00f400e54403403402c0c80e02c0800e10f10848100030180300d258602010040b9118800e61400d80c405d5151140c410015034481c0c210800301e8092181c408142c000c0495280240d501c940c250070401655500ca000030044c02d0681030f007004201c40c40c03d200760340005c0410801500c8040f421200100d0001e034110017189191a455020040c0040842c200001c05800000520a54009444840801c584c83d01400005800100351042e0300110b08000c0010f418480980400d01d80080d003943d5001c0100d0302031001c0c03903d0f400c00720303074503000b03c18107900c04c0c5503152055060344031114200c40600d00307140c00d94103034940d400303031440018400c41000040d1401c4007812143c0c601200c0241551a09901042c0000079081703140c0c041c0c00300f82070071222000c100308001c100f1881011031034610443d0109403a46540102e01d08a0f447e0030446c052030000130680c2014800384950b1080c201c1d03104031800c1c414010183d8200000d0340c0c6000301410b100d01c001915842110b540224140c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 357781312 1250 357780062 357780097
    0x1180e01090c110a1a0421020c1201110d0e07080303160206011202010509090c0c0109050307140309061e072f010305060a030213091e030813150209120d030204030b01150203 76
    0x2807e0200c0ba1600615180ea40c0c40e8103c0d0001031002d8011600050b00d583c00c46a080301003200032002da080e5001403806050004040004c00440b220702d511510946004004465500e9200c8541c1459503006464812002001c101083c0c4a144d0400520303015003045402c040c000590b903070000e043d40c0a0b007140d4610030a901c10016562400000c20388202500000003840400c07400d041154032613208107010303504c0c2c100da04505400d6505c000222140ca00002d054030b443c20744014592180700031510b03009150352200300316480c003041c038103030184010841c0c1010005084c050344100c0208a10100e500c0750605041c1400c20005681d0038000304212601950071017448040d50600100034210000c00030035480c40707500400e0000008200c1c0f01c0780903100f40c44190598580101c4200e0032240d06100415500c6c04803684189a007040e0003800000c0d4020f00781e45407000b012150b282c200001e40c200c2900003a8040f800300180035071741403078600401c510400c440741d2002802009480388242c1c03080da144090203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 357782562 1250 357781312 357781321
    0x5030a020702010c061118120604031206150302030a0b010e060f090102030708040e04031101090b2d0106031b050702090109111303061b02060603070501180e01090c110a1a 75
    0x25200b8900700da511042c200044928504116996040351031040b194031600e400c42449800e14002c003201c501240310003011303207544690f0100d4003501c0c54330290445540322078000841300041030900c11150226280581c607031070480401c01c122080e01441070304101315001c03410100d446050480d48418040704500d0b076a50702c4980140d00e180b0507010010600000050300140000c1e1742c1d04514021032182c1e50300401e14800211040c207032410b5400141c00c0a400c64080340a600041030701484910025000350300882816180f400101800d070b0107000843d445913071101402d0340360b0100b50319105041c1007080c00d120890300400c14980c01402868007580ea51503030f6810030360b4000103a80d18032250b11407403034a40d5260318002018004901000c180324494078040d5400500114903144100c80107001004030600d48801181d119000f00c110111500241c0d0000c92401c01c2042d1080c041c020502010984500c0401c00408007a0541c0580d1215000b500381040043c52914001040034038000d0050702d107469 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 357783812 1250 357782562 357782567
    0x604090b010e100515040510080705040923040b091905030f09151b010b060c0a12050d0e0c03070501020d0801092d0506040f0b060706050a0e01060f03060608070605030a02070201 78
    0x542c0e41240394005d12145440243c901ca210080003650f1040e40d01050000c6420002e4030f080ca0295042e001191050000340648912503100d00c0a281000509010f5011480035481039070350181c50540d100c0007098100103550404001c1d0041c881d00f4610669903021040e160310307459001d50f8856aa0809000810307803e1541c075806113920500c141c8103030680d642c052001401031041400503c002c00d508180700d4104c00e19200d002c1d181d00e420003d000d00510400e1f03070f5400d00d1030441213042e4001d012050207084410f490503c2000740300c090220041141d00c201c9030415290405503441641154041c0d001d0012007076000445a0468107a5400400e440b502089107400801d00c80041c070340c0410030400c04203001c01060b00498042c441c2501d04101c0459a4420746094611000744560407010412003040010345c03680c0010390003010f8001c000f982d29070200c082c2c7d0030f40c2c1e01d9610510a1b820303202001d0040c02000e00c0b034000149400b40040c0f100d1840e042010b04680030041902110741e60200b1140203690 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 357785062 1250 357783812 357783841
    0x1e0901090209010e04050c0405040f0f06090b09030a1409180c07081305190308030c07061e09150b150c0f10020d0f18060b13020a0806090604090b010e 66
    0x240c0c018000c2c6030640c1c46048046043c1c0b0125004c1e02d1038495011008060708161051501980d00110801c1141d40c068880da10104815501100c80b19501d070624004039465121190250602c240a0340d03480031482001405882c03c640e801c00251410400f0280956071001d052883c1c04d07038062044080e0780c40492402040c010810003914044e4002446040051408100c4094980c212884035100280c4c2c0203800d003000150100810000d41000843c0b040c40c0c45c000940307a0644100c0c40458120500c0d41c1c0030000002e212072111000381c581440c0310030030150300d94004002f140140c0801c0b0b1403007183c0016040400c010491641580c0020b2400b040f0030041c400156460103403c101c1e400c482e1078091a4000f984614031440c403a510b450841c50811055020f402210814100c0e445074491054480a008107003c0b00010740c402900010200c0c0109203001070411400e0b9610ba444992524a05001100c0c00003030090f071203907203444250340002d900000000c1c150345902d500145141d840c41d00010f484d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 357786312 1250 357785062 357785081
    0x3060924060f06020307030c060203090a050a050105070e06030411060f16110306070c0503090f040e0d02010c080f06090f2d0a200412020d02040903030518061e0901 72
    0x95036080c0401090300019084642100e894040c01c200c51595400700b2030f12070280150040008090181030f00110341703107070007440e084260f0070240d46102c039181e6186032800049400849159445504012031590019002c4103403603411769a2902d0340c0b41590ba81c506d04c5050180c514441c0001040f034060030b403950b0068a2103c2035401d964240d100f41ca092814420220340c0b40588a4412407000491451142e100280702c168080021410030000108020010845055040c1c220344c0d00d5400700d06081d400c01c240031a520140d0000541d1140101d8010020381000f4200c0710701c40c07000024011136480d00b1200581c0404200f441e8401078a0381c00b14004040350305490310400703c548a05610001c1c1c4000000c2d03025403802034007004440700d6060341030080ca407900d0301c00300f4444081c8030410506090080e2132059501c001c0c654240c030b41d02b550006d070448401c00c90a5000a0380e40301040043c8c41c038885c00103844146480240303080d04d0006250304c074540100040d4a458039400e004200384040940294420 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 357787562 1250 357786312 357786353
    0x2103091a011215090212100b01030b18090c030313060f0215010303030203040f1211010f0b360a020d0b0a0807090e01140421090f0e0712060b0c150f01030609 69
    0x80c2c003074010540e43e485800c0080a404d2608e010b5401d145507002e48241400c50101402d1441441d10424004483c0b175002440d00b080c2c0c1c007600d150000155411b100402c02003031005a007160301800c149000300101d54168041c0d0543d400881160b8850030000300c840d04480d0b26240c0035980b80d0b40c2d498900b03102c20601c0c5009150b03681c1d80600c03032011600720580002c00e581310802000310350204000842510509203489070020f920400c440f80c1c14100c0340c440b80c4200e200d010030600051802c0e14011180708102d50221a02d80c0c0410785842040150003181c5071b252007110781507011070400e4010350300e80e56079218030726030b8550b200050f101030b400c02c0d001200c1c1c851036420010304a00e4281018009001946e8100403c20402803019942c180030700000e030283c1d10440c5800300e101d424042d486601400152010044c00050444a0f030116103d000e4000135203061405141c6841031420390b14074040d070031008040c00c0d03410441003003421b14801c4070702c0b41100d0300400d021500300900d003030881080410218040700c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 357788812 1250 357787562 357787579
    0xb0f0d1107060c030e1207020a1401021c020c0f06030f06040c030e10020406140c1c0302040519050405161b11060412020f060c0c0d2103091a0112150902 67
    0x30144e050ba20941012800405036500c05021260b403801c94401c4000081d4401a00b103410700c4184458402401c02c2001801121451003140440c0d550031200c01e071811006030303c0210741d0500e5042100f40c0700b485400c140d845a00318102032154410f10040203144500855640910202c80d900c29000014907060003c2540c0300001e81e8007241c03001c0e5205005513004120207007451401e040c40b13203044038514141a0701419a104820041c01c00c2024604003000800d5024440441c0551b5551482141541e51840b40170004d0714045c28041642c0004001602120303480000c20a101d0308070840740c5404600710f10705c120600e201d00c1c2c0440f603003507540c03002074114070041404140c040e030111410692600895003221115159000c2041c1032041c3d2029401c0ca401a00114025091035402010300c2480b80245885908248a540c5108075401060400080d10744418500f1b000300c2c1691a11440d4181844000541c181240e601d02070018050040500100030b9240d1081011644401034143e4001d00c13092 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 357790062 1250 357788812 357788831
    0x609020f04060f052b0f06060f0801091a070207030320190525030f06060506180109080f0606060d020d0f1409010b0109050f0f0301240b0f0d110706 65
    0x11500190b500034140250498240303500c0f40034241170034904c0c1c6080011004200c22981e07031000c16001c0100d508803507503600c074034020030b8a4103030660400180c50100000079407801141000b0f5002d18508c4240b003103042d00d060034004080e074003040c010260307609814145040c04507110700c8070b0300b841c50011003505801001c8524000c132080344100c00000d40a542103440c4d0841701c0d4844c1011030100c1598003500c6601c0d000400001c0c00c1a020b807108513028900010300c280e075039400308803070b9071000d4007188400c030510701d0070b4905603003002c00000130303003035020050030000780e02080595250320142c040c41c895000400e8464903000e803a01147d01d40d918043c401e1046120251501c00a8254001c105805101040c00900e9440c414402c1410707450050b989e046006140a00340a4500d010074819a040342e0784044109141c1c809000d42013882c5000000e0840891030070407964070540480e04030311542c1c41b00b040069170034000321003500e070303090445a000104d003136108000ca20288580807000785441c5c280002c01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 357791312 1250 357790062 357790079
    0x2100801080d050c0714030a020d230c1309050703141c0e0d110325080f03180f010c0f12021c12020306041103130201031103070206040609020f0406 65
    0x24125074222007280c6079003050b80c030103072903500440f03c2c03d60040d0b000c6202007100c644030b43d0001c50390801c00340a03110302900c5a00401c40869481d5015a0740c540030440040c0782c18503000c4e20681500400018108102c4080001a5800480310b2140c1e0460307105c5401000780081440844000e41d4030840300314103e0a072074012510f03205681c1070030301440440d10548010600410011800d070100500c1070070f403400b4075030303903c06c6d1040340000b01c3d5014400d04482d030100d01c00300466884100038845d0005030261802c0061441c0100880b5405800c0d002030191300d140c01c1c0404c840440d21802200c421110084000041b00c01a54201c400b600c642508000d1034180f00031110320070150410781d429500c9007050001821500724080c1a5a00003416103080c03204640880e41c007941d04421700400100346076150741c456915503041540d400e245003142201480856816108440d0000c580c0e50642e0300b54580352401944034030b0010005400f040e111205001151b541043e101000c04008204010903500c46119 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 357792562 1250 357791312 357791327
    0xf0f0a030302011410080a031103040b0a050324030703140109080d02030601110105061302030a14070f030b010305040809100c080a0207050319050d11030f180f0a14060f070210 77
    0x110354a80c0f41c0130110780381c01c44440380c401c00d03114007100030803200216039000c40b5103000c106041002030000341f10200d80d0f11191002849140d00325600c8903200e0800c494100b5180c2c21600e140c1c4007001c04120b0500703076038030b02150107811642c0010018240c000480422400b40c41c03032540c014001130002842140782d4050703502441c0a0350007070f0303100c10100182c0e9000d01d080711020303145103501c00b01c8515001444042c40e0001e41d804802460080358410300300c042d0fa40000070644080d80480c00010164041c9907061003000880e80c0309180602c500e007402d0f110400030f849200c028600840d0200c0100007050f02442145c00140d0740500c40c5a41d4001c0158003e440e540303903000301c6209024404e042c4100800300e42072444260742010180c072107628248403e8880300c444030910244d9003c20700c0701040c001c080740090a0318000044903100c40070044020014001e0481240c1c6101d5000c900b82801a45182130740d07811031180a40360700d6134030100002c20100302c0c00303400c100942c050b2010440c4007000d81c0c0702c101b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 357793812 1250 357792562 357792581
    0x203010f060e0904170708120108031b0705010806063901150e07050903160303120f021c0e010603080304050106060801061407020405181c0f020c0109050f0f0a03030201 74
    0x1150140806080b08000314040241d4028000000c01c420750b0050310128002450401d114003032491030840400b08541c3c01c02001d030709c2140d4a03003001c02d20a8580c1081c00414400c4444034010707081e078a0400002a200d614003810080c00f80602140c6c0292018080801510f83d028499400c80c140c650819240c803652581e040780080c40d403c1c0100d007100300c190041d080f001c0d1106034100c02c85595030400300b200c854010404681c0d0502c42c81c0d1901c075001d012414500c01540c000d0340c0d07520080a10720000420780c0d07200b410f2006814410000f100f0195940c01c266008000f1030400861101c03400c0d0046405400e43d0707000a42600702c00070602c405c120b8154001030449581e52580301c6980e0381d6100a40700b083c01105420304a6404001000051a2562120764010309007581e00e461a920711130402c4c036181a151003000308800c4147c22074540c80d0401102c10100c01c07544001d00c01080c80c0c01c0005e0440701c40e0302c2220301445a4603000d15448e80d4a09802400200140051023840e949043c004d029118108 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 357795062 1250 357793812 357793817
    0x120a0614030c090c1e0c030d231303053007020a080f0a051b010c0306171e0109020630040b040f17040f050102060a021315020106090203010f06 63
    0x108003440d0501098420705000028800d042c10303511400c001e221a840000c00201e0b25641c08446000f2085003406440100301c038200850b101c100d000c0204044a00d00322001500180f010743c11a41c80c201030f18041d07401068075506031014001b0789816101030186107498a00c40f003580c07444030b041c0c80c039414403450301c608040c03080c02c1182c444c1082070361a118625405080700300b04000108451035054002c005800c120311300307107181410142c100e5100c120004900740c03035a51a040321901c03280d031600801d400340245a40380308502e800c0400c92607440b02cfc0100c1c1d106c20a02960400d06001d0f50a501900c0c4080c0c001e00010b540300e41103840000b400e031102002c43d064400d2202d84000100c01120b140c1d01c1142d21002d460300c1520366031580d1182c848140c4d0120741c2d802c140c1c2c44010b2062543d1015200a084250804540e1400c03c40003a082c000d00034010030805205104500040802d00810002c41340381803803130f614856041c07000b24003401ca0398004454581c000400050b2408091072170704115441c1e40e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 357796312 1250 357795062 357795089
    0x91f170f060f060604170304080d09030605240f0315070f08010b07030f0509190e0a0c021902090c040305030301080601060f020d090501080a02280807020303011d0705120a06 76
    0x124000010b1650076248650000410301040c04104d40082006020a2503801128101503a4051191800014031411000206841d200700100009805020b42241d85a03010740c4030400030800203101021440209403107404c1c1e501a425071502e0900842c00c0b8003030311250f0300459207007281c00a032a1400758860440020a42c0c00001100c1d4840c10aa51809605a82d0320306450786500b4110383d070380c000092955000114400b085803030a000303d4903500501d0718404c418100c4c170b00782880c241190304450084056401102200d40c00040d007615001c0e045a04603210011030f2a0041c0b0205903001f15000181184000400030030401c100044503812200565528540149111012a101d400002d1400081500c01406000560150a00544c00a01103c0c01402d00c105180200169804032414142205400c00c0d001001540f25407150303070050507070008501d15458003880306145c03654079424081040d42100030407560b41c07041080b01d5500010f0340d00c03844a810000c030510004c14551007003214bc280038 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 357797562 1250 357796312 357796321
    0x402040e04080a02210d05270a03140406120f140910050c0f07120509040c050c101503170d09031d0103110a0e0d06020403121b02091f170f06 62
    0x1540a8901d0101708404914204141038a5560161401810f41000c5600d2000140c080c0410529040c8020400100070101e181e900d06014000c8600e1004400d00100100401d010b030715000710f040c02d80186659000a4205040001c50b07008001410f03950f042c0400510038001c1c4c20701b00240f85032030490400340402961316102c0c0703081854400c0301d4092081c0c910510904011801c807103a0459402c2003030515901d00b01980000a0480d8618408017000c42c0e030120b20402c100004220f20000205040c40c1000200f0410081e816584854403004003040402e02007400400700950a4990a420031031085c00803101c2450040e003614030800c240b8204401c0016124a20341c03003401b59160329140800884c2c5000d64810080381c0b0981d951000369003190b408041c9400094081c401000118081c101485140f013007400010300010a01c001844182e1350500341e0005a510b02202e5070700420f41c0055180f10340d807040d095036007100017036000303c01c42e00782e0548070f100d00c40d0041002c64000100e501500c507260765 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 357798812 1250 357797562 357797593
    0xc03091504170a03060b0f040e1003030c0f0501060302130204060e0405042f090c0405030d0201090c140f0d05010209211b12060106020a0611031509060402040e04080a02 74
    0x30100d8001d4000741c0410314407080588240300805034410640b801060440e201c8243c90451f500c42c2c070b644c6489010014082250078800d1100d16004590008003161441c61510b0042042d29810710142501003610f02d800c080020950041c0019980a00045d82480e03021007048004e401c50710801020509c411004070f5249054481c2511403640b0018000f81c0502806000506101d0107c44019013101a01c804500d40c0e501c0c0d03c0f0900c282c0143c03010b50b580e5030400041c141840d05070b80c000300c156810a000c410000c0c6200e03c01c03209492040c2c03015002089890300003407419400040e880d81001d8030203080400d00c02c0c190010301c5c014100303542c000d0b104000c0042200800802c8070101d2202d8101341c0c804280016050413011401c18001c0100074210306400300c450a00e031080c1d10101c00b40e48641085810003085009074212050a4440181149000e0307120300c80c540081e8500c0b9204030500c0c8005419503503140c1c107540c0a40714064040d40d413403801d490500f2841d40499100c030054829407221151091 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 357800062 1250 357798812 357798853
    0x6050d0b0f0a0914010527030a051602040f0f061406040510020c0306010e19050408090108040c0b0a03050f0f04020a12020d0b0403020a0c060e0105220801050c0309 72
    0x1588002000441d81d200d1458104060026042c4800d407501d44030341c8004560300c0a40051201c3e0004000203081c1020100000c4000888900210412048080c00a201c60200a030f420295507420119954031040742c00440303000100030300940c454034186410010740240e41c480b03c040003072050b040080945800c00000110003034421070364095000c202c00c0c0060b0030504800c0e51f0389040350044460352040000000d052a2098020070703400041001005032158100c4c00d0500c0d00161554100154100750b200c41308548134890010b03040c40b0280c004074041003800b4203014000c140c900c9400740c0784d106803c4002d003e8101562403c11900406c4003164403055200007050140347c0c02010b403031681d0701c1c6c40b01c00c000c0782c01014003daa00c03a800866120218014100300c43c861031190307000d0b0400c200149050682c5c0441c0d50400c90402119203045609a6000b80440b400107400c10b4043c120307200c450320b45400710300054100b11900e5003008240042c0450b0074011f103000700060ba00340c943d440c071503c4445a810 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 357801312 1250 357800062 357800089
    0x3050c090f06161a07090b070201050904050621070e010b0405090708041b060f080906060a06300c1b030905060705030705060f07030b09010302092d0c0d0605 69
    0x195080000c81c4245000d03001007100d406405416084946580c580d8080350400c1c901e030000800b2000200040300c0e501100b901d02800200e034807203041c03020a8000a00d1805540c01440c00f840d9a10007244041d51840d940e015080304080410100141d80100705444020a110f48140035204a0011911500c900d09840a56002a01c0c03401c2a9459080443d01414050015182e031042c2c0305940c8150091940b004003d0199030301c3c0c1489011040c4001080d01e900105408442e8100708140102c556900c901902107e1241c43c0003961990501c0b074480d003d02200c1e0001d15a00b241c840c840000310103030342200b1000003064480d5003840301c64021445a0b45000440100060440708040c040ba00d000e00152045078002c41c01c50703007000c03140e0340d072036103000e005480324110340064000700690303158180038200d00c040090322546803551566000c108459400740001003004603100061036141e0740703034000e04800f071a044588545414619003140990b440f010300008260f04080f401700e03050810b2125503555 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 357802562 1250 357801312 357801319
    0x20c1f0e0609032a0f030415030203190f1104030c03021804050303240907120506030c132703050d0c080c19030b030d0306082103070f03111903050c09 66
    0x40c0000c52013201da82400d450303600010100d8440080c60303c03000810420450800c410001c5030303038038103102c1312100e1024020861010107004008000d2100d60324124544810700611010548110304410007028040036541c006407000041400424042d146280d50100d038000e907408610180c082c0041c040c120f1085401500680c07007000811207034203500140418140b11180b00b21002815880000c0c4021415601c40c800103407000840d8502c42110321600c1d41204048009026000910000c43c4c0d80c28202200e00d00940c1c1c3c0c61a080440294550580c030703072100c9010300d030ba013202d40b00c2c500a030550304540f0b000c4028030b203801810351600e40504143d03401000041611814012185c02c01480c01c1c44468200e030816403140c403c0185901c0c1040120440f6140d81c03030100d00710b410544650b2511040248080c080c8408540d091807401c1c2c0442201d41000d07a80c64904014080c805d029405017940a01c0440390600009099420b0020102180380c042030030340e0140300584941c28056114026408041d61 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 357803812 1250 357802562 357802567
    0x41502060906240402040b0d06060509030a061503060c0903120207261c05180604060804021e0306010e190c0e0d031205041b09020310090203040204020c1f0e060903 72
    0x440301c002030f10110404004402400c0001001c0c00804c00380c1e00158003e04841c0c00214211803c8180c0d4043c60380a0007292500500700b0040c040020b5840000070f00251a680c1d030390308803464584a40742e800002d035800150a102e40b4114400082120419200039909106500d035030341d4500740b021442008850250860000c003000c2d10f69462500d50602130390301000d11451156005d60f00c10042c1c02d0030024002e448082c2c07240900e602d8410b45500c4070441d907110b208100010f004a40d004624142c000390103540b16002c5004038194100e4981d40010f100e030303051080c0000007860940303046055208021200c00c01c900d80d88104400700590f86e050441c071000c990071035000402c41c105001c00003021070080c504904200d1480e008102200d409850648441c2c004010b100041c503644080740008108201045140d440c0c5421500d85003006070085a080540000200d002c0d9680d9806646483e80100103440c803130340c1c0201044184030208003c641d042414091800c202c0d000120380c85100b0400382d8051361 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 357805062 1250 357803812 357803821
    0x9170705162301020307050708010c1103130e1905010b0706060e06030d030b04021e07061415132408060105030c0f0904020114040608070215150d030905040908041502060906 76
    0x5411400c00c2c00c0303641180f00500040000c210104040701c01405000e000040100100718000c00848205402d0800c070b40c0201301d008512201343e003100d0b0031101504130701c88a0342c075110103c2e403000064403005c0c081d2900b42400030641d002d4541c02484150700c42e140c101f00c010303500c0161155001040b00c0315927058002200b041101c030701075004244071100003000145800b0581c81d0300014800c0c0c514070306a48460120f81d680410141c0e00c5045958240c482d4000560718102c003080204107140703075a039030003056921240f981c4030324181c00c504000c10520011820280c04041414240c611512544d08c07144152000020305040100b60301c0c03041c0a0150080d004540d0107410310511b001c014000304c1c104080c400c0070014a400040c0a84054202d03555803612605106800910740341390f00268507264080b00342841680b000e0960521541c80302503e040d0501c1d4100d060580d01682e0651040750010300b000610303420004c0b2080103100f0b83e841e110041038802c188110407640c60600326009110396001d100801c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 357806312 1250 357805062 357805109
    0x10804021315060c060c020102031b07051203090a110a14150c0303040807031e0e01030c0e09130b0a05070e120712060e0d0e0619030917070516 63
    0x80d24011070074900440c1c004440398048110025076400280003542c940c401a08004090058605030542d0340300075411800c1c541d184030035a07aa80c003000c0085a100041400411906000700941404d01400c12034072442d1212000e511403120000c103c0c2c0c10b07280758800c449103292010701201a2001c50a0100700004071106101e00300744209103030751350b8004c140036044104004200443c8110b11403506039882c4c507034600d405000c142d08049031aa194200c02c20910160717070300a844640e045400d10340810504d509141c01d80e000b40c03251515513040340c03002040203e1842d07400d5040b05040d00c111006461590b850b060b0004542064900d54001101d007640c025140c608940e615002c4219401035aa050740e4030804450140b89401088492540f02c80032418010028021401008401d04000c94501c107603800045d1180715005000110907100c89400740344510076445007100700e5215005240f5100c0349500340c0e00c50303042810119401e200b40380700000346500711103001088421204510381400840d1440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 357807562 1250 357806312 357806329
    0x5070603020913090f03180b1206040b0a081e070e04031808030403060501051f08180a0206030f0109050105010507030504050123030f07020f030a0c0b040c1d2401080402 74
    0x581c8030080d0a5800b40f01c2119108140c50244a54001c4030001458940a04180d000c0e45001c000d18141160030044c03800780034104c50083c0c0c001482d03070b16a0351301c00c1c0009000b44140e00c0300319007205d040400490358041c002000401c0c02140d0031140000c80d22030700c1d5980e81d42e034039000d001d082c8410000803c0c00280038089003818201c80384a095002a128407140d403940e0445e51050320920b1b02c5e000104050f00341003800c95001c404030500040b00b444c01c0304005e801c00d88050101c2c160140c0391007050421210600c120350000307900800c0d090380c0341440103214140b07103000e0040013659403501c4000141c0b503002d502101c410340c0c1d25458a50501e440c000054a09280c05080c01002c00ea00780300c3e0450f0020001c0040d84034140c00301d840b040c68140741000901e800f5101d00b9158850741704001115120350880c801811030356101e41d030b00c660799445251104424400e541f24141c00c07050070310002d00c0e0803100000184900440107403000030503c824041c034020031661002e60301060310000458090b0a000d81c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 357808812 1250 357807562 357807577
    0x6051507060603140c041104060c030c08270a050102060906010303030c0e0a0306020a0e01140405041a0414010603180f03050c0c122103011a0313020307061707020601030507060302 79
    0x400085503030341c0e070300c98180c401351480d0482c010360000b030303040350061810744101d2404c5800300703101904250400038040c00e03d1805040c05400c0c088070504c0b400800410310202d403c6000292110010410f00740c46c1d0013010510014103901c00c40314500f0202d040d520025015100d681d4420080481d64030b5601c00790300401c0c5a2180740100b0042c082107007036079120030035280000e42c4500340040e9200300c07004c00100700d845910007844c10013018501203018406000d06a5082e80c404403000150001010300500d00c0c0b0038541c80543e006420303d00c0c0e9400e58000c1013032043c101c4141d91814040010b40d589007110504451707800800204180c4070f00000311348100040d11109201504071141003014100042d240b107250894170003180d03c24180b81004000c21903102140c040070254113030565050080c010b8410100b2120103000440100004158981c1d54041e4400c95070068151107401d80c40300340c000c040340c1100b10585003511900e004660010310002c4c5440c12070340c1110151012a0409408034040e40c00b100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 357810062 1250 357808812 357808823
    0x702060103125915090d0c03021302210406140108100f0902030307030503090a06050a020909090307120f020309091905060d2d080a0801050f0406051507 67
    0x100c4040000c20785031240b40301000c4240d543c48034118015140c01d54a808215040c80e41c0034401040f41e0341100100d40a039402c1c12910384840f02084051103220340108003451754001c180400d19414010310810500549000b51000780b81050b0407403144050f44a03441ca9000da0f01070000d440316101da00101070315002445a0390106240e15860348540703840c002a0440820b0f500090380503111802c140c42240000d0814400911078519250002034490003500700140034040c2c00400035041000038072030303408401d5010908001a007814002a0b009400000502e80104104030100356160342c004182c6140980c40715180e00411044801100c04040a00d004003d500c01444001001e507200c50702c0034030a807022911600b50310800d1404000f43c90300039000d6805410240e0040c0f0104243c0d046d4040c0d00381d901040060041042081c410340465104009403401c0000300d1480d85280e40161641d0490300221256542c400b010b40401040360750768031442c2d5000104a031400cfc030700304690000d88580d50241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 357811312 1250 357810062 357810077
    0x309140d121205060a0e0103141603110f04050c0d0b1f0305040507050a051f1404030506070801050a0803070b0c0f12010e1f090504050705031b0a0e070206010312 71
    0x10754440394800c40820035075010401600000032108040d2041550046080319007000d03151130203003000021201808040c048180418152120080400c10f00ba100031409856035134aa40c4c03400c0140210b1380241d82d0302d1144243d19009500e030314045c05036a006e0b10381050131031315240008807400005c0504001081e08809480d039500c18407102038409010042807610081007a113414680541889566005641301c0c0c40442c4061080d81c0300e80d4221410140070094400c2c1d45018240300b51074030000f0b02454444610000740c04020800e021841c03d000304810f440d45066a43c8034020000c0380c0d4150300480000354010b001900100341101251608110558211494480048503107490f6901070801303c00e440041e82d0041046416415071558030074401c0d14100512140d183c07507950691392070310134070310b149032941c01042c140581440503100800c03006044030145100c0c04400c40b90b906019964501c903202184000035403410039100c041c0b06240580c05410980c2c2143d0f01c1000005151100c0320410042 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 357812562 1250 357811312 357811339
    0x903030b03010c18090509060f0405150709030b3103031d010e060f04050309040504050c0d03110c0102030711210102040803030402040c050702030a0b0c0d0203160e0d030914 76
    0x82c850004040f02e2603072016007040c84200501c00130f60b4954089008203242c0780810042c440d000c1001c075005400c1e0403070120323541c42d2410128074180f26165070024104884046c02542500a580c8500b00e070300c542d545003280e90326240d81413a220044001da11003601d4108600300f0b090300d401d80c901e401c18424200065075405040d4501d07a403c01c0780c04442c1080e9512400c000001c00308114195006000020030301c0c02c3d04d81a511a5101d000e03981041b80100c0d01c03040030408000c4148540040c2442c00340140304081e8890800070510000584640624064043e8691700c0e540b01004490f00c05401c40c41d100043c07a00c040910007400e91b05d004050b100100f49406c14031400003130004000911b1a14011a280c2c1064010403049402220007030043c800100b000c01c0060f24007003100348507160841e00f81217260b40c460750f03840081e10880d124260050310000403c007641048043e0007407002170542e5081034a110400030301c00c480110400190104c0c059840c10042500745244011b80804007070500c9603081ca0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 357813812 1250 357812562 357812569
    0x103080c071a040602060903071709040b0409030f03050702070501020a17090a0902130909050616030e07030b0f011d2e0308220b0a030b0307080d050703110606060d0903030b 76
    0x8482ea11140c00c1031001608205041c4d04002c010b40200070900a103151200690755145820500c80c100e1824100220f0400025030700e0341d10207100040d01910620520119180041c429003085d080100400d00e010080795140e840015240280d42d41038006103c048029107a5001502880d18001000c2c07008004d103c805455881c903110050a8104006d6104c1c245008840c6101d82c46400c40903c1c2454200c00300c01262000031050340040001c0041218122000000ca014104130502440d8a108404000040010002400c0e1183e140905c03242c0c0143d881d41e5242200b0149400900c44845030700700403441489118220500d5404544252108046045401001814194011748094401080b800d60000800c6404880c1d5603040a04080c03403800c00c100a4158002c4101090070503139107007640340c455181080804d0242569200300e0f1071b04000b40000030f106078444241180000e41700402000c8030200011f88034003441009240900344505281ca102c0202140301040d030130141c440c3c098440946 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 357815062 1250 357813812 357813839
    0xb0c010c081311041d0a150203061810030602191e0c23010501060e0405130201090b09060d06080c01260c1606050a02040f050f060a08040c09020c1f050f0103080c07 72
    0x84282c0c05001ba44282d803e00140c0005800d0001100078010410410203950b20408180e1a650503082c20226860f5a4503a0015441035040109001e10015030795a80c091200d2881c03c240c0c02a07a540382049400c071b10b85283e0b00816401c01804203014002c030b5400074003610340f503031350262a40c0030f00c2071400504038056003501d60a070b0001d07002c50b002141e400118240f41c014246d000d6800c80e0f882c0d082030010b038002000140103108150741410040707050101c55032034038229096880d56200500825481e04100790b00c4880c20503469010484405482d03059000c0c1c08802c4040c02d044110146407941c86d05a2084140c0c455403224032580c0c500c601c3d02e00007883d6849014003a00108000684560900304001030800294102c0ba10070040000700c5013442d42c07001e04039142d0a215140c250300e030b51100e24100401040035003240c0300160000c11500410100040d02d40204d40b1880340103299100c100718143c0889030183e505041c000020720045c00882c0b5100c0c010504e5a25030400c850340700b641c40c101c00c280301c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 357816312 1250 357815062 357815111
    0x1507080c0d120506010216231509010905120c01050702040207080313021504081b0406030b0702011509020c250504090c030b0708161211040b0c010c08131104 69
    0x7801c0100080142c84440c070500e503000200380020032401403000000b9004103030911580790000801c0f1200014a02c10f9217030305107100c00107059000361015012811000342c101480003800652110b500080c1861702e0110010110703030810240405440309401190261712240042e82c025408004000020799100c00a5102d200e00801c407280f00d501074410401d4412200c02e81da45040d80601c01444140c0340480e2841140d448240b80740e008207040070200d03024080381e41c0050484840d40d81000010f41d0190441c82c0300381ca040d5100700c2000c1d00c0782c5551049005440003240a6030180303205c4089070560340c8900c95035684180001c0c443c00d5079540044c0654030040e03001c43d5110301c0790300104100048066000d8000201c0d06108043c1e15010030030b40b204100c45404130042040c0381c05003280d82c03a15503010b007401c0340312203051540d1141c90b86411203c56108aa86070010f40c03825a03243d2440c0d00ca03004403809004266030701c00c44d0210944030302140071450807034140e009984980c0c45209800d609503000d540f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 357817562 1250 357816312 357816317
    0x403120507170c1903020901020c09100806010f06020f151302010c05060114130203041a041a070903051501030305040b0d18050a03110604080912032b0f09021507080c0d 74
    0x1d680b903076030384000c0028244c1580010305005100300100390b178000c038170480d601c2d0301175401d007205558410002a4961684e8400500b03406004008112095822000000c0d150341344c080701ca940b000c42800301c0d84d03207076010900d0700c0e60542503002c100c8560381d100c040c6030058014903207201d1860454031000c1c24140280d120098850928a02500fa810220f40950b11181e0001c000c500f180b51644850b4114214040b01c032040220201c00942000015030246500c554030203140d610038540210301034079030b07041400300b500c1500c5411500c01542ea88608086d0599602d036842034103280c504084070010390480c240ca01003941d240ca020450340404080c0032092980200010259280d4a0034080e201d0714480240191941105040001180c5010201c4030000c030309850103868144d0303040085065001d80940510b4241000504440751202d200300300c1311b12040544200140744c818205102100c00c0e07200004d4101d01c00e42c8030f06e0782c001480d070003400b070705400303001000d10f0040407101c00390900c80111100401f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 357818812 1250 357817562 357817567
    0x1215100905040c09120303050403050d05041a2d070504051302030f01290307171801050903040602070902280305190207030c0212120721080403120507170c 68
    0x902e1425000303001c5070554600b06144450b040881481c8000401d4502a05168444c030206007014071400407180b41001000040015003464501a045070303c2c0c003035070701142c2d91860010034a054610040c04450303c01c032290f0b050102c003208020303a00544004050f10700340705061000003100c0d1186400031050180070b910041e582d203007502c290b0300d8105040e0010a0358054100c0c11078601200d0250f0103d000b01c40c80d410030303140d90710b00300c0c22074610110703044516055540200340300071040701041e10036200c0ba888009012039a12000469900e024500c03c040050340540030412018a2a60061000d0546200c410184018006009007000c80248040000958500420090540e5900a00c08601c0c1c0400254034100c5180c0b0000e00d40e10100300c4c0a882801c20fa280f80580441c1005500a4140e1209015444070b00720300301041c60310780c0390f45c056444603100001070b0b02c0140b140500c3d51150b0f5250300e511403004480b40e9050001d04004001200344280c9403a051041008980d80d540b16808180c222907 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 357820062 1250 357818812 357818819
    0xd0201030902030309032d010e0a0609060603150903030f1b0c021212040807060c0c050402030a0e100b040509011107080a03060503071205150f150402091f11030f12151009 75
    0x10000980742c0440100ea450020b88410481004c0ad11548040e0000c3c00825080e1003420000024806640300910302c00d480741c119003852411f50026011140030307440400c143c00c0d9006c01c240036580305d4101c21680790459000c03452100e010304215490070340050801c90011a411400324681038040301d03181140c09000c141001501c4080103624050708403450f0000c4006007599444100c0907050092a2080ea00400010b5440901c4d51000c41080d81c43c8044860f111180302e5908001c041c940c0140340164108000079035071100500880c58600d41c80d514062900c90703640c440c1d40c000c4d040740940c02c0405071200c130002200c3d030342085a40050210941307040a024550b240c00740c50701c11a4083e28403000b07151020480c82d14500c3c005160312800c005c0d14003d4000210300014006d200d610021a403190032684440130302d5460074100c8160154507203c4541c510990b0711001c2d0b503800303147c54501070b5034030401481014007854580d80f03400450000c01c0c202420310510000d40000c003100707180000203a0081080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 357821312 1250 357820062 357820123
    0x13020f0705010b2817010905070b31060e03030417070512160506092407060c0503040b060d031e030f06050a03020307050405040c050a0e0603011a0d020103090203030903 74
    0x501c0340b54150f494101c90381841321118100f1149204007452500d44d111030f480107070002e40001606540c8141035401064813600c203003503035400a0b507060b964594800c000204035034240440c3c942105441ca410100d051078098211103414200004540500041c0000030344035a1082c00b80c5180c8903048040c102140c2400c00307020b03408400600001065010030050b03024000856140303010359000792040b6070b80e01c40003c01300c0c1e11109001d00000307401600c0c1c000200d01c007a1003800792210358803d40d01444400103000c800c49050009503005404900c0369400f0426501d0001d8103040c00511030b091041241c50440e040001c10303103010059401282d1030301c0540c000c0c10910321518014020841d22511200c2c1550013203690350b40d10340203480c004c42c4e9580108050080301e252440c018540108640403458880710b800c2582c500956440d4041c0d03090403a581b030714840d10010504102e038081c05103c1c816006800460146c4801c90003642c160108200000f5a62414080c0b01c1c1c00c4030951210000c9000c0c0c0d000c0c0c4c5d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 357822562 1250 357821312 357821329
    0x3080301050114180906041d06010f05030a02370306020d060918141002040617011a181f03020c0f0a030c0b0a0b06040608041e08030613020f0705010b 66
    0x1070000b00203198a589200541802c0000140c0d951071032507507900041030003011035042a001c0c1500751b1232204400702c000620f250607a1841e41184800a540c2c4c070074140d0b41c03174a4900095002c5543d210045201000d00f05420600012000100c00e5140c5903408040721400c0e50019109641c0016030301501c903049001f032000904440d0020012002e281c98511070031903441400802c2039100420f0300100e204104000c8402081401046513143d64030700c8060103106200106113030b81c50a034070002651101e4100b80c1d2220003048120180f404048508403a100d00d2869407090f80300a48444003100c01208241c004540384142d1001a03440c043c0307400c21803420070411500c00b0241c3c00084210f000035070180d42051100d9008985880f552910206000588008100e450b00440c01260000715940d2104400d40114000d160002070038032905015000c505180e400680100e10030404078010307040600400b04030510300741d40103040149480010200354010701c01a1001d81d104d038140503c92800032031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 357823812 1250 357822562 357822587
    0x30c0b070317010b16030c0b010b030612010b03120c0a060510080c030606031b030a05120403060c0206270109140a12171611060a050f1305030f07140304030803010501 73
    0x48200d5298500340300103019202e1014151a40d85c4864004810180605140012260b120704c0f034181c25a161458982150812500720744a034143c1050418961010300c0b803e508000c0190103041d00756001d11544400d68002c0c0000300c402c1c40340c1c107c00008511941702d80c601955148042d9103d591400e0042850880306940c0c4506c03c0e040501402465500012010000e000000c2250055035840d00028104081c0b580040c10034000c501c06510000750007001041600c3c8548801c119102003078078226560201190144c5400040c000e810a07041c140c4c030521140155003000108888955603100b11000c07030100d2001c030281d40701d0120702081044000b482e02c48442c85191401c05040806034501c0b107190058083c7c03d0000ca8628040d00c2c20344200320785031001640740102c40f00d40c20402c034600e0040c1000c45c0e6903402c1c0148403011820110314028130b02c082c6030300180211308180400713080d4030311603000d810201c41241242144080b031075400d01c085c0000758081c0c1c1000b51250300d0200003600c401d10888 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 357825062 1250 357823812 357823847
    0x6010f02030a05030a050604020c0604050c0a09060302010c0201111006180c1407110312070b07080f131e050a050d091208040306050a0b0a150e04230a06030c0b0703 72
    0x40c02c0d0701c03140c1c0f00080c2e07503100d88140d0020802d42c4607500403038024480e85001500c14080c0104200030300100003001c40e11414181c90000c181640c40000208883e03032400000c1c00201e070641303020003542c420031a0005080c1c415003662030316a41320860000704c410355800821050402c5918601c100020300c02c040300243e09040040080e4040c10702c2e514140701d0044014110540745c5500e1180ea2410000c40d1105d101100074150303190741905080d1604202210100000b03850480007071580d64803401d02e18001d810443c81000820850340c1c490021004840b142081d00bc581070000000c0b6078208062681280160301505d040e02030140024101300b9160014044c1c4183c0c9a07285002030364040c100c50407280c000c06c0004182d1a020303803001c061b0842090055020403005000b140440103210707141d041c1c91041e15145081d042001c1031106960000c00f221800c0f821195092131204d20010846074840700001e00007801548a96443d4a0b0046940215222400100702001015042801d1100300308080 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 357826312 1250 357825062 357825067
    0x3060f240608220f0303020c030a110c010309031b21030903021209150d0b120f1b0a1208040f030b010f0621020a05090306040b06041107031403040f140606010f0203 72
    0x5103003c0a003200802d200808050340b1210704418544241d0554802d010980e080e2640d0f440210001090307198040e07026482c0c0e0241c42c43c4500158080d226019249a068440300b086d16040c41c820040b0000346101510283c3da9000c94048800040e42035281040413a180000c07480d80504000380b030005440ca011240b500100124a0950744840220240c0701420058640d00c00d04901200c001d800c86a803029006010480652020080130441d0681c980341f100880c2d07114200100008007181c8000281c58100f55440c1c400e01003000b0310b20322000e105010301c0e001c907c2c00d41e448003000d030051a0780d032094590b00c200d45d0050048002041d105c00062600d07181102030f01994094131141803d000a0340380d90507500142d50a0401e00400955a05e4400142519150300c5d1074180035004983c2113451522903440c046424040d0b83c101010388441301d07016a0b4ac0182c0400d40080003a035a40302070804e9806c0300740c0800d40c0300001c131a03030880900c141001000c0c289509010b000944000c0038600c5240541d00203 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 357827562 1250 357826312 357826351
    0x1506080706170a14070207080d14030f10080616090605190e0a0906080a050106090204120f0501180501140a20070206040b04080d120507050403060f240608 68
    0x580c0809a0042c1c154540c0c0b041c1d2503c000041c01041064124000e00d102d440c1000440b50700411042d00b1200600d041d25160340141c0c10407034442c0011402060000740600110715080b424044140e40700900c480480c90598403405058900102110402d925184c401e20000002d68410751120003407d290030954141320394007803c9125151a00900001c102c2e0000f004240b40c4e8403580c4c0d0100508868900308502510f68140f1078894100b142d00341d0f0250300700400090320101034405c441c1280c4e8040d2580d0304d80840c0b5a10711400c01d020302419110b03503481d009101510070b03030703c05032020540c4180f00004994412115000c1044030041c10803090724600090b24860008114520300a8010041d1362591820280b002402c0340c02240c2044d40350200106020401c21000a100508111313140c41c9c8200036a03000902109a071401c46810300042e00c00d10007000000d64a0300800140c8101c11408140084071070307881060000040c1416903012110f100c1005207a40041081d074000304041e445007440b102 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 357828812 1250 357827562 357827567
    0xe18240a0303050d0b031507021608030901020c01080a02121315050c030a0c1e09051509030d08070507020312040501030c1d010f0903080a021605060304050703110415031506080706 79
    0x240026140382c0a41741d581c040103a5906000342901c40d00050980c000a0403c00c3c00299070744c4030b104425080d940e50140c00305030890000183c400c0808140d0040030503625990044441480180c03c038006140c0070321801d0301d1400e210030803078410394112440e045001c0e0281080b07411488282c1101d03290720f00d84409d1002e1030944804880d88852403241c04907007002c0c642001c440647c3c2c0240148800c02c00b5850002d002503120036000e044440840f10700001c007001d400b18410b03e02c0392104082e1f150340501291200c15000d104940d0340b0000504029052911a8010900702002614400358048001400b80401d6030507124880d100c901c02e05d05840c1c1c25a440c0e0403850102ca5800e4000d060222002c81e4440042c841c81d01d04024542c000c60907a1526243c03035002e0340c0d0314102c545200b090050700c0c00200c1d00b418000242c074402d54101d8020202203143d40c031196944c0c0301c0ca22075150001d44a1811245400e9007003114401540b0926145611103400034502c3c04603401d5400c0303804103410501081003402d6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 357830062 1250 357828812 357828817
    0x2803030b27060102030702190501020609060907090c14120402010807030213051519031416081902090301140105150418020f0412080705010f1b0e18240a030305 70
    0x284500301c01c102d8440c00c00507480c0d8051650000c0d80510002d440e05062040c20b0b4880382150303002c0c0c00b10f818a4071050305060300c0c3c5503321880c031400c3c0d00c4148200070503401a081a0b040070781504092900ca09803540d407004d00d030302002d900d94468031403400388011035038040a030640c070281606d0110f081c04c1800c0d00d84031540240b8480c07244542d60521210307400780720320b80841c1c0061888400c0d80240035101140900600310941ca0440711174603a40000e0381814004924408106403030382c502d6a140d9030084d50302000b005103080010312070350a20016800340c13030911843c02000102e0021200662506040042c0307420010035039071801320140030410110303440c98104a460003803908056203409080e0840e0301140a142d00c03e540c0885011034400c140b202c200000c0c04450b02550007440b0b0300b50441d03c03400c00e494001c000b901e0b1960301c13414164200c40c0308040c80307000d0b20001403000004600b020f10b904440d16043c0c0e000140044400c0c03400030801040014858442d01c1035404000c0d0314610745010f003290 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 357831312 1250 357830062 357830119
    0xb1f050d06090204021216090e06011b140d0e0a08030a0e0d0f0501020712080a050106020d110102040e0906070f0206060603060405220b0603010c090e06060c2803030b 73
    0x1640b5030400c2d608642d02c1e50107a603002c044c2c9029072030700f5150444464840590800c03039840451080702001c2800b00304802d62501c650810385175100303401d800b103030f071a01107500f0030009480100403041d0b140034491003440b101c0c0c5250950fa44000c40c100c9420104981a1155401190903500c108800e110340c41d00540b03000d01c2c0b5242250284103840307a41c01c1001c078140003e5802856944002425070402504484241e1900440d40d1009459580d0a14950480c0c1e401c1c0280c00241c4d1012584584c50351082c0d02c0d200e2040c00440025040650342d01c0c00b01143c1d0010340e1024000d4001a0401038180e030f0201d0303c4040e4408501c0280031f641400d00114000b40f0001d08140d010380c0d03c44000401c4041003020705d08134100f02d80c601c0e40120b245401c040c000e403141603944074401c0d403c000c18140d8141c4101c1c0c4050035a00c16503210010340e19084108826688000d5010356a405503520010f1240400810180d0740e11051802c008802140d1400a08991580c45401d128121020a8030006c3d120390b00c4100c8c00 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 357832562 1250 357831312 357831323
    0xb0403030c120903050a0f0e031203091f06030b060303041d0a021b0115080a0206030a022817010b0f1902030d060314070b040605180406050a030b1f050d 67
    0x1c551000011980040350440c8900900e050194000030143c0c484010304c1162a1680d07039003a1910082c10407a0180251008140d25500103100c903081490a0002150860621b80c12203240907400c1d151903208140c0a401045055500c4d1130800a015004000ea940070303a00b1030185141508200c0c0c000e4a180084188118420990000501c2c1d20700c5130741103034240c00324103c610141c10000310300d1601801010042d140c00c2008a00005019440096080c00c1c06034020403450440d03031410304c5040203420031481c0c0c06895030890030b038968040305903c0300b288003030f2195500e006072840300300002201d085c1a406440758400c208403614001c0010002d685000c00d00380000c484138040140100e01c0c41c000d800680007000c1c40d0282c0081000500c00c1d10545241300081601e0701c0c0c0347c0e070302044a00c0380950310904000c5081000903014400803010140c082031002000000c1803500c2d400030803401080d5070802c5801040702000e001c20304843d81c0030b080b4203000000b00d841c115070504003ca0141519180014034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 357833812 1250 357832562 357832571
    0x803030c03012d0816080d020a030806040209060a081815070e031f02090f0604060e060304150f0e01181e051203040c06080f060913140d27030b040303 66
    0x11880c1420b0410003c050707010410718499204c45480d9111202d01d0021100200b80c84000507100e0004075031201e1207078554001d0130104003d40c9090300c001c9001040035500560070009168a40d40d114050300881195950f810f0340e600d402e07110b0364500c41c068800038440d80e20074903410060340d5240810503445016803829007008814030300481d10380015440c24000306a400c1100c06d01ca010320341c0c0a010350b040202d814540404102c000d2142c584118090440041e007414242c141a0404000864219104101c181929441501c902003200c100680310b05c2c0c016114032002801090900460204801c032180030180760000b9652618210038109070080120303d040700c03020500100344101501081d1000d00c4a40d039141518200000503400d000d440f0103d11060085540402520342c0705100310b0780a004184607880d030601201038201c82c02c82c110b4505150b905260704001c8248442d801d09515901c89003481d400030303080829884d0004949030132a2050807010804688458080b80d04540c06090009 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 357835062 1250 357833812 357833849
    0x1a090f03010e0703060b280b091804030201050105130b100311040306060b03010e0702030c06041104060302030a15060602030703021e01150e0403020106050607120305070203160b01030c0803030c0301 87
    0x38050030810090900768054a000081405115000031340d00c4101200d85500500703061f02007a00702251055410300b0818403000a01518004030003c1054030030080403048880310070705a00215460817102180141d440d0740040000b0304008000300c2d8410710b200018420380c8210030100b05681c0d902c4091108043c0c50341031003c80340920404071005181c210300240300c419101c00c61700b4542d5000788141ca41080325100041d0b00349201005650054081601400c055221625011010301101100c0355001e80d85420003c0160b0f8100709040c0600d100b012500080d80030004440112043c961007501550000c00403030b00001c2d07000c5040ea18440940c0c016000750f0b6908481e250061650000c0e458000100400224800c88800c6070544141d1082d802400300c9502c8200f031000c2c034014038400a140c103024220301e80420f03000b5001035602480b144101e03400c20f00e41c86400345400c044640182c1d0040102c10040c010701c000600031402811701c00e0011032650400000e070305514030052107444400d4180001c100c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 357836312 1250 357835062 357835069
    0x501090b360307120b09030408060c070507091805011505010e040e03090405010b031503010c09180f0203130209010504110403021e10080a0510030210050f0d0606020706091a090f 78
    0x1c1068800140884145a8841244403000f41207080d055607503400c0e071170005400450000841e01030b110001d000d4141a2680c040b002e0aa400681c81106c003800740c5540442c03000010b200c2c200102c1030f1104003805003496400c2283c2143d5407020711501e4400b04403c140500c1c2d070030008090001cae406a80005501e82c60350f20311400c5000b00104581c1c0181071100001ea2202003101a6002e695481c601c803c10600120816088454440808010480507001000b42660310900d600166204c0301d00440c1000081404408907441190080c400c0503400d244070055080800300030740035000c00e86080027a10300d00d4214990301d020340d1200a1080c2003048035502062000c010f00040000040c2c18181c1c2c210342040d010f80425401c0354039843d03903482e10f000a071400c415250701c041100e030041c010004901312441c00300c4455001d06443c1da03e906080001422109240c8103880050000e40e004c1d2001a0821034024109400c035032046d007030039810b0f244041c407918000088460700c01c0210749140760302e10442d011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 357837562 1250 357836312 357836407
    0x6040b13170d060608010b030118180b011e062c0d050a030c140303040f0219050303070b16051806071703090f070b130e0403021504030203040501090b 66
    0x1580c81400020402c9a070303218407030300410151a241c0d00d4602c1c50380c1e07c614050056000911610840005801050700001c03004d0f48000c440d03441ca5038080660441548518442c55400e9028a160700b45a5142c420103a40c0d81c1e601002422541ca40440052598541c8240c1c1c1a8090781480c0c5845902c0c2d501d840a60303a444040000c65400703020b4072803921203420007811a0040c98401e079201f0102e0420204100c01c0881100d01c2140e01c0035070400905015001d05c8a064a862802c6c000d155540d131001c40d459404002514500780300391040c0e4540d14100c8501d00000b8600203c0c042407001c140444940c0c08081d081040300072006541381c1e5110005801c1c0010440030340e50042d4016038001003401000b12010408555140000c1c045600351551088031034500e200d190101c140c07442e45e44405100607180240120380140c06441190450100701d40040013012040d10100e02583c07000508005d1540c00410600041c60400ca0a9081244c00e0b2a000041c3e006080c00600050b9810042c056072100c0426 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 357838812 1250 357837562 357837593
    0x60309011b02010c1b021c0c08122d0301032a03060f1103010f050415210b060102030403021305070210020c030d05060604030c03030f0e030d0f1106040b13 68
    0x1500060500140081d000303040c13050041300001d0baa8031400315092004841d03028010340c0a42040d9401620034900031030390070160070480d5074001d09040041d081d8000c02010386070600240d030f415074840c1042541000580c0761458180c82c0441004054990054002643d04503908100800340464800007880b980c443c4913401c655400d45410400710510503a51300030421429140c600704000020014200d999000900c50000d076022101c10a00203420b00303402042480754904680070410b81c550030074203107010400d42e80030900e001160300c220501452000054100c242070004d1b503c1d103400c0da008650303620442c00184071000c0d01d401c041880c1c40e1081180003240d40000c00d0443d291015540300d2600c9901c000d200c501035a081c00041141480c0c44011a01200da2000580064510f1580c0c00d9514030001002d200900025510840441d10184400354918010340c0d20085e002010000290105030a450b5a1a043d40254104000141c0a6402d250003128000d50090000340303a2810301103612000c2d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 357840062 1250 357838812 357838841
    0x703020d03052107020625180b1605060703020a05070803070e031f0b0402040b040e220b0f28050c0c030c0616020d02060610050405030a1401111806030901 68
    0x1100200c4161441280b0f0740035030484d9007903a646440350308408120003009500d41d10700340a9a9082e6080601034074030032226078044c100c400000d07642c80c038144049070061680f85900d0344004400c0300401c40b040c080554040440d0504600300580541c0081c01d500030200c0060900e400000402c6225001d9100240c440c03200408481c8420720500c19003980402c00017949610b90b0401c20321290901d000c0c000d8800b42c929041115040605d03101039400400303809410130701900320288801c440500c01500b01d00c9424001c00e000c0241e8201089190906640101128075889440951106010709000e08081c0003442d154042526110b1100c40c00e100c1c41a41c540300d00b944030001c0c02c1403400341f0210f80c2c0c0c0e100b411503000c0c0100c3c0c50400941030307032140580c2030f1000058000d40c000907018508401c601c3c0c980304251030811308158031040400d2820b80c004c0070903111000450012031441c18240280c80c06910981402400c003640c1e9100003900d0b26001000510a11000c0001441c000c0250300c0b0050600011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 357841312 1250 357840062 357840097
    0xa1209020d05100e07050102070e240d050c0a05040203040803060d060204050d0609020a060806130e0c060c0c0901051e01030b1201151701020301030c0905040c0b03011401080f090703020d0305 84
    0x203c0c0380c14020202d81986a0386401200740c009095800410401c00b203444002614040c2d90342c50340b5501f02030021866000740c560060b14101403d40b40c4000b10202c0c103228600901c20350000404208400c8090ba110390300c2640100100f000042c05081560f402910a0b0303092003c0065514203070019005a4001d1038110324413220510501c00c0303582140103020f009480740c610007034507a002140c0049044800941001c01c220f00040810f085c1d602903400c035031f8140b041d00c00c00842100000c00940c090b4070070000c6940146444600380c074140b0241c0740180421540d07140d8240c3c81c05070640081d83c0096699040c1562604010345a850320051001d20303400382402008031008a0001d85140e1100740965404000c090161000b5650144221b074141d9403c801d074006040d15017041003000d460014002c443c004943c000010b85040d41c480074602805008251504500c02c0500040080c1001021102179202c400305000c0f803c4004a100d00a03a50161091030184c2114281503d5074803481001020320750a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 357842562 1250 357841312 357841333
    0x50705070e100e0a0b0d02121c0f020607110c0f0307030606031217040503041512061401030e0304030b0a020a051210180515010807090b0c1c02030a1209020d05 70
    0x5a202c0c0940b401e020400b2419282c103c0080125101d61214039040091030503034002600c1c0844400c3c6140e40da8504448000c0070011060704000d038005408001b241da403120030b205003501800600c2d40020341c4d1400d000c0300c03600c030303d101e07130340c2e00c880c66034090040c000110843d405032002e11a0178090740c4c005401b07000903a075034a00040300341c0c1c100d03820100203201422031000c0740c00e29291440c060b9401100550905040c0301c0c500041e18201d00030341040c400750f403a00b20000c081074000d80380100942514002c1720780a40c0000360660f50b02e11a600d50b15003041109000043c214006070380c100095200043e199220f403c000e5034148602c1281d02c080340303441000c012000004241c0102620800d2000c0c846021a21000a060b200c041d1100c1c0d486031100450079000d07510a00813660700454031300d003180541d81e42d080b4800e241e03801080c085101e504a101d900b1601003c3d680794449243c1c00e44011407a1420400c0c0052010a01e2290401690f8031462400150354a42e9a400039464000c1c060754440c3c0701 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 357843812 1250 357842562 357842581
    0x60f0b0f010302340b010f030c0312050904090c0f0506090d110d0507090f150806040b06010e330f0a0e031005070e0a051504060e031905060405060f1303050705070e 72
    0x140c001c04a1786203400d032001107188454145214220707680038000c91034890031a0344000788004141d01c0c1000300882441560345503035440c052010703c1c6006261031010b4904000038403610700f14642050b030088004015040264a42c0040d00701d00c5500403030144540c180200018910800190010701248101c07400440c41d2140750388004090035420ae820080c0d410744103480b01110907284030780881500310800142c042100100201d40c000b41c1454011000511100010b040c004c010340f030b102c0390804c0110b079405003440880e0b040300c04c03002a007072690500d1280c401110751482940c0c002020001c1c810721854a0740c408100c40d412880000000303100780c1c640280010146004225110701c41da51f82d043c0020281440a05107014500c200c2c3c84900e820b0403c00c040d0b034008405a1a03541501c00c0d0102c48802180f090310360021240714101501041c20b00d410240d1802d00007410081c0300054140a00154481e032161810507140d040c141a82c071108213051103070602c0b15a502010944441d01c0c2000760034007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 357845062 1250 357843812 357843907
    0x10b19080a14011e06020106030807060b010c0c0f0e0f0c04121a040602090f010c020303090409080f07240c020a1203090c26060402060301031e120309060f0b0f010302 73
    0x1607411364500000c50361044100d00740c8034103200c080c0080e902042508082101034002803044a0181001c3e0140d85031980c0d80c04c5030100c280d110300000d5511810612100607a4902280c20000320b8000c1905400c02c050942c10910861041d400d03140c141800f90300402007503801c600504010310000005510b09402d100c0e01a41c0225492841070701032025015072503001d8056039449a40140c02503041414030030500c00101113004064861403010f102d4401402c1260000301440e611400e41c64500e40b8001c071104c6a12201c1c095040070340390408018440d120780c0003c208a01c16080380d800f076000400e010098004000c8080040d200341403050020510550104071852100819440f1680c0b4031820300705140c030703888207450080d8000c2d404c00c010400300e402890030451031440d044069103074202036582c0e14205084c7d61003107030100391a014514213221403840365101240220b0000d0101c071081400180202a40c3d1a02c04c1c18945d010981e07100302020051030340c501c21150680c0d8200142e0250950f01c011 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 357846312 1250 357845062 357845099
    0xa0306020a023a050a020a020a030c0e0c030f0703020307170405060709080a0b27030403120305010509040201020c210f1c0e0603010b07110406030b0a05010b19080a1401 74
    0xfa051110070b100858007a24000c000303141d0f0900c0c00301e0040d208580c00c5480e580311002070005c600c584180795001d40da48003802401184a000c1a00c0c0051a0042200318914020300d004c1480c0c405200700f210b06484184042e60120503443d00694aa85c1c1d50001e0350003444101c0b480400c4c1030100104801c20100080351406202191a8020300541d2003128658944136000b00030043c64a80012442d0001221103a030403201d10441c114022014140b1004c2c6927801076031043d00c2108104901072545a01445520701416081e1481c0c0034a140c02c0d0001307540c1d80c8002d80c91900942d03500081400e50620000d1051108408009943c405800b5030903041d524100d21986002d914003440d46060200d000e00350520358079a01504140c21a843d1140d40f140300e030083c500942d0b20003280c0d01d41c6140c0e44d03114428080039511400c0e0701c500d9802c1001c564401c8460580010144200030040003140306000180c169940c1c541e0318000342c0e41d64610001314043e240004139a4542c01854001107559881e07999018410f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 357847562 1250 357846312 357846343
    0x602040b041d090f0d030b0604080a0b010608071e0c020f062a061317070512030a0e010e1213090e010506100804080f0c011d0c01020d03020918060a0306020a02 70
    0x103984541c20f206440b00c04442c0d01d85180e6100e020010b040e28041d40008083c2c21005008074149940c500845003045d0855a00f1030b80e06e4501ca00600105030482d6100f50094549c1c42e0504072042d190511401305c40109186030240b04911900e001159200311440200b02e0740900721607110001075680c02c10b490350b0808818a000018000d01c0003281002401c04e00c901002a020003400e80c0d00d0f03c98082002043c902221030490411004011640400030408812004030380ca0b40e8910300b4460b0181120082003241d1000e9061501075408810006601d20440134070802050356401d03089046402c0040b81e6001010740340c03c02184070721950301948801d10540c8282c1d0314400d10402c15a08403002c140445004240c5035061064040311600300303000c0e100842500000040c0d2a441003802a01c180480741c0303102080d800f84900700b08950741801003e81e00c6103641815418a42d24400141e020b08451140ba9203070744891001402036610b0403900d10007160450000c40d41c610900000944651510741400c09 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 357848812 1250 357847562 357847619
    0x60308040612091a130506010305150c0304032001090b090313150503070807030b19030c090b060306040b0a0b161a1311190602010911030d02070b03040602040b04 71
    0x703402e840360059204880e84001c0360700070441980140d820740c11010308003d4034450b400281d88001501086618061400381008150140900034007040c4d1042c0141903141c050010701c10311000039009118100d0202c0c0e414880001d074144070026038010075820201501d5070846d0000e121401102000500d034403c901c0500c41841c9858003800f002600b074400315200054010070005907811b105245258000c81d103850701203413504044001840032080e0310700701c0c04400084d1004000f0454100d00c40740c010b01c0703072003402d0005a0360040056818007005103c40d024031380710448096180d03900c070310351806414640202342e05c0c0d001a0081c884d50410010044590030301c807418a1480a050103040b03846000c1c00e040303011580312a95282190b03a0241c24010750403401507802541c0d03503d10110b00c04058403a0780c2c00060030958905004070106401d000003802500440302c000a050b40c042680420789034030035500e0359079403074910303240000313200d030350f2220078000c4d004100400e090035030040c0c804450421406290 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 357850062 1250 357848812 357848837
    0x30b0f030106080d050306060706050a051e01080a080715050108070306060e061c02240909010e010303090501081b0d0b031c0503060d030318050d111c050c01020d0603080406 76
    0x600b2500b6500640080d90712160034900558855070096600000c041c0040c3e090000d00d58642003901c2090312a8000c864803070b010441004441d03c2c0541c41c50800c0341401c105075151510b819115200040040e00e441d40c00202c07a0188810140c1010118500c42020001980d4800790291204100c2c0000ca80345030901000181e1221418070305402801c00802c03903082000280351503d1449450710040b60440a0740051001c7c0c01c0340646900501c11390011110303641c1c01681e0801c02c45442c1604808500490280103001180d0b0050082c01038a0307080c00c0c00012034540d00d101e04003100b5800d080c50340d010713400102c0385071b112110703080b84400450607000c035049400aa400c0b1202e01810021140c0000c9042c0000f6807039180092000018a000e41070016800c00a0106c00000001f0010191030030341c800341e510701409078811007003941e81c0f2076000980442e40d04083c0e0010302e0941440e2141c02c000c00440c20030700004003941283d0510700900c10030025640e4074a00303080039030050f100d64404501e45680c8038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 357851312 1250 357850062 357850069
    0x60507020d020a0809060a03150b04090e0a05030405060a120c022b08040201050a03141302090f010612090c210507050402361207140d03081515040303030b0f 69
    0x901da144d50203c850760610700000140a456001401420100340d221039521040204d096070b21805040c01102103507817a0309007440b15064a81240320034040ea0f0155103050085407010003950183e0b101140c0c0ea559807145444115915100d040ba681c015030301d00191490000c2c0c0000707016040e25136400300404154081d40800c4401c608420400020400ca00c00060041d0b10500c028040c001160800207205801301d500200c04440440d070401800d0105004c520561800318500e40c0d02c400c041c000d2103d10341c10013100801c4000c02075400c0700c3d074070740f6450051308115400340d4075806005c0c0d181401d20b4500600b448040001d081d50010707203050003203030b102090350b08103070007260311012851413110500c004804060b115420416506407140c01c0c40f696011345a500c0070800e00300101060300509c0403500381100b0041015040700503a00c01d001e0404030100203038024403020740c019510010307447c018002c8030102d501090800704280119400250100415400d680b0402d8160402d44d202a603240744407061 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 357852562 1250 357851312 357851323
    0xd1211030403020c09040623060a05060403240908030406050f090c0a0324020a020d080a06050f0f010207090c03021e070b010e07030204150518011e030b010c0c03060507020d02 77
    0xd0010703004040d1070511030400000c1c82d03811601c640030000d4200b44d05640e00010040c44d1090120102d140e230180002031030882d503000d0103003a01700c0d07031a440d1500d96a0b45007511200c5285100c5001a180e007108040c20850f400209038a4200c441c0c0341c0c3c3d030b2916182070b000901c0101d80d101c1840d2034120108000c5200041e03038a00040000e0881c04010b42548c80340c80e025540001e10300e004010701030300c4c001e4188090010745801206a0000c0c00c034070400074005000c5c4a40184030523046890014100705655520710040540c55080d05e00303003807941031200101d04006d01500a048814100140c100c5200c0e4180d004148c00c0228806002a016a04111000d82e110b822009800c030b620364001404000c51112a40d5004400c5040062419581d8240324208100081c1282c5c0442c80100f03508103802c080034040b02e00b24800b440d010344880341e07003080c803d0b54075887e000c040201569071141da11035900640c11608074a401c4000c03e00540c0d076034a0800013038481154900014001c248032400c06c0707400000c4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 357853812 1250 357852562 357852571
    0x60510050a12110a0b071203020901050702040209060c0604030519020601260a150f18020a0605090f18061503040327091d0f0307260c0d121103 63
    0x107214040ca240481d42d04002c01080b0060f0345003400c0c580d11a42a64540c1c100c0c000414040300034a48490050130a82c800310701c2d25040d40300303040c0108440441a80d1140c211005a81c1c1258016211003456012410501510010039003500c5070509000505800401600c450b8654000e40c2d52120f0300f07801e089850b0340023031080c0400d45810100095205542c8035043d0303030300c2d40c054080320314035602619440113228200302c6490f03034030741d13161901c4540d404140110844d44581da8601400d403640359021540341600c038401d03103081080208190b099035403514a0328200c1c070710040c021010b40b4034400685004003400d4840030300c074604c1104035051042c100700a480c450743d010344602c000a1a801e40e1100c4280c816000405c043c104008041681c01892064400300794854004000d404c0c0b866003100e02d8081c002c01701c19485e6109200020000f070220ba000c0486480000c204840307800e62074404080d40c0a9680c4420704c41c00345142d1a981c1a500040007101d04a415009200864a002d41c1054501c01907a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 357855062 1250 357853812 357853819
    0xb0a0509011a0906031306060501030506030a0b0403020c030d0e0901051c06050702011404050a020415050a21060e03030a0f021201090c0c051e0c040e03190c0b0403090306051005 78
    0x1040b558462103a81001e40551692140c03801070040000303403a40d070040f5601c1003503802c91107400341070011510418011381800c4c05d0030402070601700002961490402030084c0340350b44504c00102018420b0107110390b0100094104d8a2703240110b0b5010300660000000207002c2c29804000080900d0720500d01c100d21011041c0068801069481da0740160000074160001d44d9224590140b4a500312244140725a0150001d0030041d603192041106884003401c8962103400714800902643c3d540f0201841202c0344800c0c40807101d2408409691580092030001c0c2880e4a440c055000460001c0001c611a0ba1485002c1020259980ea21000c070300030306182501c04c0c440b510047c0486406540140302210040c1441b049012465982615080c030701a052407076100e1700d002ea510654010020300507840000c9070240240e07242d011034103607240a043c0c0108444100b100010503940d0040719040320054218141129901d064103002d091511188001c840c2503240c41c000483c41c4002c440d8907000d55078002e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 357856312 1250 357855062 357855079
    0xf080c09012a021905130b100302280203120112080702061c06141203160f170c070e01051915030209060c0c01020c01020304080a17040305010509010f0b0a05 69
    0x400810450380b61141e0704100340040811040050313902c51065201d40c44a00c2030318005941030105000a282e14400a120706074100b00001440e65a002c01d80c007441401b500d001621030b03022100304001903e6180010000314860364031202c240d82d005c0004c000700844500d4003803017a40d0301e40b1290800141010f02030000c803000d100010041c54508024801130303405015401e00c408640743d1100c115009036220058031108440c0d50041820302d400e004070b042440c035001e54103250b03407044d01601081314140000d10440c02d50511004002d41ca0030229071009040203040e44804d44035084680c5c81c0154002d6083e5940003000000d060728200d01200c0481001d41410210302c0c1c5400c07162541c2c0c2043c60125020b01d9000e00c000ca800d030b199400030346a1560014002c0c5404100440064140040b034210f80d81150070402c81444101800150440819030040d0501e40700b058600c00c130170301c0d4000c0303030401003481d400c0500b0700c1041103054001c06c803041c20890040045840100401c0048080c41c804c082c0c008652 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 357857562 1250 357856312 357856337
    0x1080408030f04080c0105190c03020403030903020d06110d0c02011803020d200d0203071e0b01030b0405100c030b03060105010908070909050102040306020708221d040614070f080c0901 81
    0x80c030303440a411500c140138a82c03c08400a00460a50b04100c40c2c142181000f0080944442034900807480d4020503410114030b001d0554500034440041800041d000303159030aa41e90400890f9488500e4a81810130745548428481e800c0c10050814482e03d10010340c00c0c0001070b0611300349a03052014495143e0014107285500f0001030350b0b819484184001c0c070301100c0d1100040d0303801c00d004001c03040025601a6a50306581d02d4085403c8110080e00280d040c90b5030201c00002d410380055905503030300b2600221090386d581c60502d10708030421203a95401c90920442240303c0e900360f0000807421380c0031000d442c80d680e00c6100440309024503100d203900c55445410100205900c03540045003043c01000007520b42a142e456a0b010f80c1c0c0300e4001280c03151000501c5198150094081000042c004008182c8052a100005d0503004a130300c4c410416025400114041000310b90022030091145403089005140c501c2c40503258100140078100030610440c0058107801c20b181c110b03000d801058680d40c890412 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 357858812 1250 357857562 357857581
    0x5010b0306150d03170c0a080f06030d050304050a1e020f01030903021b12120a020d020a11010f030b0307030606061b02030a11220603020109270e16031209050108040803 74
    0x500c000342d06000c0116170750015540c203007410921411400356a40e98a0b01d01e028010000080104170200c8140b0410600550340d03804a411000b11002d443c0c141c3d2641ca560802c9800c2c0504584024111040102045010b0f81d14022210400b8001c6810508090542005405413500707034100400507048180e051017480360103da9464841c902a0041c0d44012104204620700414920085416200030605e400b04c2d507810010301c00c18071308520181c1403081d6642d41d940e5491500b00c200c24117100c60401c2007100c4612030340c002118601c005040340c8020307a0300d00700341004129600410300024605050200081202c2c100b0051055025008004209454403520f07401c110b0110b100d035000c242408094441d54001c4102c80101d031240c54002405851440003502110140d0f00c1000242240101c2d2807104440658040e11410714010104a0b4210540302d242000a901d10040420469080120078880c0e0041018112800c3c2d40307802c0300320341e1204015100c21100301c40c02807100ca400c000107291070341c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 357860062 1250 357858812 357858829
    0x32512060b030f0f0702012910140d0507050d0c0305071b05030415020307020a030c150801060215060301022b05060d05120702040b0406060503101710270f05010b030615 74
    0x10246c40001103815034049090b00c0007890044142c000061021078116620781000120344600c0c8500b80401520800c100d85c00d40c3d8080c0d0326030b1144803565040001d0340d1902a000b19207865140400c100310440d001c0c80090000c08080d2100e0b00024945a05c592030107144440840c01039400c00000c6080918104051b00c2000c2040c504070110300040c01214010303251114420051441223511164076800c142c14001021483d10741c90302040b204000400075150046020000e030740400500e07000703954410b8080781c0a4402d1021505815249441c1c88465500c000d140c1c0b424401c00c604244865120700007004210f504920010305540c0241d290604585600e03c003e100030380c800740011981001440014040718a20345c85100420070010411203440012451000503108212a41300015165885107995510510459080940e90b00308002402c407803440301041d07004482c3c40c3c045c20000078a800d480c00c49030000103d50541c00c1c0003020070315260200c0e0551052402c28100311001d00301c0c504005450 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 357861312 1250 357860062 357860071
    0x60910020319050408130f170d0e10090314010c1404031208040c030602040605071104060806060f061213030908010612020f040902120615010320032512060b030f0f 72
    0x725403c00c8a03a41b40c800d13240b06d0f00300802c82060720407525450b00d030b00c0c8805298884050b0696410030751a040040780c001a40d8041c190040d074100d210318400b0001a62509110340000d852072543c900c43e6240c044054104049421590782d03080f1400042010000480c00b0300d010003808145000554218680b00360149640b00b4000e002182103207550303465800481c2e01a400c414005000050f401003403044001406518070b9041e03400f0050940341c400700075154100135101c907209040050704a240d6507502c40a590088100460b48640d07410084c45184031807005440460200d80c01e413000090700392042c450b050407a04240d014086042c0946e00b00704031310072000034055000d40d40d10303c0200036858505c11000900d01d0600104000d04005400526640f6035010041c100360408050303180b0442c003060030140d460b482d50b0115441c1e03241c40507041100c07095207410401510484481c1340c180d682c000d41c0000b01d40501030003008a1901e0308011103486c8401c984100807030552402168501031180040c5910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 357862562 1250 357861312 357861323
    0x714060f012108040312022a0108060105030417030a0b040f1b050a02100225031809020901120506270601172e0906030308010f0e0603190201140a020609100203190504 73
    0x404150700701c23217a0028882e01c0e041c403580d000303a6400c824650b004045e80e40c11600900704a411407600c1d0340c8100314446e01a201000d101e0000c00468040e080c0d58101b104482c200034030a00c004210607080c40004c0c60010030050410502d070b05000b030160700400480d44d040007540c3c09482000381d10140030000e0341c08000074207000030000c110007608001680440d0049072082e070b80d03101c00ba988000544500013044d003008101d98070401200310141e80003045402d00c16500107011441c1d40d0b42c000000c2d41c11403544001d0780310f5240718200e04005421182d00d54070441098036400015580603040c41050041120f40340c1315240303012664001e811820811120744002000400626508c6155040503545140e02c00c030080b80ca00d000502002d079041004802404051a40300c1ea9850281c000a036100650b4171400d106064582280d01907900c9030803035452601c071002c03d17656121945207000750f41d10822104100f0700d02482510880312061402140c0c00741c103e07400040c06004d85442d29000800e0b001e0000c9a1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 357863812 1250 357862562 357862573
    0x50304030c06030e0d0315030b10034d0f0a08030406030e01200901120207050703150c020a03201510051806010c080714060f01210804031202 62
    0xc4107140104003419003958040340d0310000010151500070404084003c0c581004a00b41020341502883c40499412544026081d100c40d426030500111a40024100d4540001c04410750424a01320b0a80181803001c2c2e17620b01a10f0303031580e4858012502c10380300341038101c01c0056102d01e0104410886a180142600e40721580c40000502d9030340561f001c04007081d00c503802c1c1c4440800170322030000750003129542004000c6081e4400c1d00d1501c2442c0074a41800104c0704903802111752581a03c3c3e11a90140c11240901d4a0f0b09200f80b40c5074031300c0200c110701c81c204002d40302c4c1140702084075028180d150302e03010070303a00c2c0c190f0885224810405001c85188210a00200e500c00900100781c040d5255031005c1001034141002d1000c810020302015004103124010b104191341e00c41c1e807584802c0d801099442d200c0c0014906000c184042c02500f00c0e00d480780b60140070f41103445541311812120344003060314103000c1c805000f000e5501d00d00e1010740490024001000440c00d030800001380320400340306032030303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 357865062 1250 357863812 357863819
    0x1060302090315070e12280f0503040306060e1303021b030c030105040804151404030f151e0c020708060604150f03060203040c090501150c02130609020c06060f06070609050304 77
    0x51820822601d480c00501c88640050f010b0600e0b0010005401480b800343c01311208449405500168402d0340c036249071f461040d0107042c0510a03408141d8981d10030241c980c0c80d95a420210058041d038010900b0400001021030145002415000402039240c1c01501129024000c022041540ca030750786174142c040e6158882031644e0070b101e02449140300c0d000c0b8a840d141001c00044400c1c00b01c0c0401e81c140f080c1d526174001da455010080d1000c59900040d014805550b510340700c0c0800c501700780f81440c42da0411400c9201d100361604203440304082100300b0003008400d414103e0b0385050900c60194150130020124202c0e05050f0486501554800a60b0720080d941d07945203d841e0003107520503100c032a40442444100000c840c0c40e00f00414016105100f55414080200c41050088500005001685c0c1c101403c640f140754000d2000540d00d04100003061f600c84114029601c17481e020078440c020355000400074135002c46002181503028000500388205035442000610b4ae000702a2104d200600000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 357866312 1250 357865062 357865093
    0x3080a11190801090c0509090f040203100212090f19030e1f0203070302060609010501050f0c01112a012003100305030f07020916120b0f0d0b1605070209010603020903 73
    0x246200701903a41c2c554940c50003030034008540c0e141da0101d0411000304030340c50040e540e1007042c603081482d00000c3c02582e05d4600c0004d140080b40402c0003400b90010940c10b022150080280c3d22400e0b810096518112403901029250300a10081c030790444690f100b4107020074400d0034455400f04c00900744c03501c00841c031032140c0002e08880600748010390000903c40d0405a05100c015006901176030030b4031055041c071001034120300481c40c010095050100f00d01030010b4007500b040301c05102041a01d0358412032a841007183d44030754815020044610686504413200c1481055040c3c0001d10304017106010210080280d540058907900214140c2c00001c07001c20824170003401103140290149035501c1c07040c818071240f0000184407024076044007801ca0b0307109070421039807503042c5111000041e20340808030004d0104000c0703034869034110360044202d808010001103480c1c007982c1820140350350103038001d40031102131045010003074200a514004006541c000d4001d480c80c46002025541001c5803400351 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 357867562 1250 357866312 357866347
    0x105090304180606020705040509031b1c020313150c0c0e0a050606030f0415180b040302120a0f0c030e0405040515010902070206190203070b101e0303080a11 69
    0x282545410004042006442c0195082d908501000c410710200b450300340040d46549140c454203000f581c0b1000081c402510502c100c1e02c003c3d91107295090000ba20700100e60baa00003400c900001074205019818019000006480c203001d0114200e2800c40d05000e00140410300400101017072041a400a000207120b143d0500050111901002c0d80c03440c142070410152130300503000c140540d1040007800085040010040e030301c039400036034405005e107460007518000c1c00954120200d45c00890740310310400000580c200e01550007503003100c0c07001c40b466245540c20b00c40c403030540000c26500c513048400c0c00d010ba00d41c4400d80d8064144181240401c03000f01c0e090307650071a800c40383c64021600c56107842104a4015000d050308500860420b103142d1f001c100c0501c1401a070882520b003994500c0d400910130011290781a920801005d40c40c00c0400100400c54104e0060460f05c02240201ba03c80c04080305904044a805aa460f0516210545080024040d401001c400c17103c041080c0e05018245010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 357868812 1250 357867562 357867571
    0x30c0d2604090b0a0e0708181e0a02030708060105090412050906042c132d2006030c03010b16021c050705040e030f0d1401060e031c05040b07050f0105 66
    0x20414540c0c0c0404c02ca1001c41a8101102608420003800403c07a806000158007e5038007020034407074030a41c02024a4441e50717251506450b07007045010800318802240a42c6030620030380c11600c40c0d94641c01d016890f20424003c0b1a0071007040000500440c02541c0c11509240352820089e10741142c83d004180030390b0198029000d00044403c004e5250408000c0520660030314960001c0715042c06904101e100b00710010103801d050220407030f01d0701400c075090140503611485182e0058230640e0310701203003040c4414030f0020007191080030030109400d12200310b902c10840440d50714076684c00c02c0302008054004141c0190313403844420b194401031321000000384241c00e00480d0318030602010305e0103614040712604003d00503824031070008241000003080d10300e800c60004200da198440c80074110001c200702682c4a43c54805a00000b480980103000400300541c10f8013951070b0500c01e000c4084170121541d02580000f402001308105611055024091b05885a000e54183d00004142a400c0d1a01901d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 357870062 1250 357868812 357868829
    0x603020901030803071d06160c0b03010e040c0f030807060c031d010501290724060b040302011416110d020612060406080a03090b03190c030b010806030c0d2604 70
    0x410700171595040031210782d45008076282e49038502070201c0450715902035580f450092500d0001e00c0010000b0030701e01180070304080e030720464481d030b07642d25540003425054505950b0110006008644507800304c00c5241640d070001003051820b80356a07581c5001f81506400c40e000c26941b020340300d89103425940520300c0d41c0c040c0b100200300795040003c4143c0b00c0d000e0052810020a1302c0e1601404202c01605407042e0300d8000082402816901c401108903c400b034501040c441d1401d8004166100521302501c01d0382e0003030b642c50b01e0790079248581041921400c0d1090055480c0364168100041d407540c02000c0b41d440144c40141d141c24180e0105606802089a103000c50203aa010011542414426240280b0651005108652080e18042d000f1440d40c042c000407800004005000d401c040b070389860b003070503403484104000e205902c0000c0041c010122840e00113040c04021400f2803130000703801c02c204440200800c00d4042a0340e1454060580380c0e040c400c42031864045170b0704d0020008060030050030102c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 357871312 1250 357870062 357870067
    0x60e060708031e0703060503071802090a030507030614040b190216030908010e2e060510020a0204060b090a0e04060e0109030c11040c090b0c070305160e01050d051f06030209010308 79
    0x30f5070340262030b10081c0103404040c0340072020840ba540008000041319440380c140a0700044400d29480a84500e0380480d402030502040003041240020303120046a0090343d0404c00e0010703a02001b00201f0094078081c02680600300400d15009005201d10b900f4240b10b000149041d403881e01480c5110b0100b034050b4045810000b003003000c04420f000d0f446200c603110014254510300c0034080c1144175040c48802c844030300c41112a12103020075603c140094a001484885907610140009503641d090349002c90013141030610002d02401c1d044180c80040800400401050f03041c25070300000000000d00c1070b10f0081e192103030040fa5840031f00c02d58442500a82d900f48411036542880c1da510b00038803612a005a16050240d0660f03136001070000165074145000300d07a104c9030400a1450160a5040544180a0f95560007850200c21480201700d074440160450140c1c1e030f41c1c00300042050612800b40440c0c000103000b40c0c401340c0c00c1c01a400410740f00b1200080e143d4594000c1804000260070898003102c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 357872562 1250 357871312 357871351
    0x60b0f031006080705030a2f031501090b030601030312020c0a080c160815070309050a0c180b04090503180d17120a18030809031c052a04060e06070803 66
    0x244819005041c051b80245102e000960361110100260f4445141c264103038840f03001500c242040004121800900303c0c0c182041e840ea00031304405003071141d5420b56107000c0c0101281d040c0810f81c0c038100d17601921594a6880202c140c0400703540b21614689090060301c0f0018002400d9901030944002d10320020445a0280d01002c490820160890030859000c2854040940c0d40da039181a4450341c0e514001c1503446641c9401450321049001c0100301405a44001c01c409072410703031000302044501c00910a00000c4000d20084a0100d40b01034041c0c2c104000307006440e13801c0e5513100640e09018003010f26040032a1508458070751a2010091070101c00294501900703c0380c014950891503602040000c861030485890f0300512103c0010244482c0340005540300e2014010751b03642070843d820345144d0b0035501e10303d600106021940341006c010400025614000f450421180c58150f0007225807801c0d06003034095030328a0718601c1003030b0300001c200142400240c0482c083d500445010b02c0e0f4404103140e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 357873812 1250 357872562 357872579
    0x120403050c0f0306010b0f0d0609050f07030c05163206041719080a0b04020c01050118091203020c0a15020912030307120509070e04050a030f03020f07060b0f031006 72
    0x2c1c06540500c02d034400001440381c81d49200407111454101c40382180e5074590f2544400c0502605d0b8007000d032007840c1008100c841c01607045880e20486807503a08008141000344241c0780f50150005403038251144001c4540002c4a10a5920018074850718244850b0381070b180751800003036054480340790307504060144420401068a080000150070384694103110400341c40410140b0b54991b104204071801010800152075944003801c1c103000603006554480c0e584031507a001e050288100b00c4541e422080c00f0220344000d1044503034a41d842a1080b07001030b05404120080d42101c0b180461501504030b40714002500004815910103403c200940c60300d100b00304008004814004940040e0000c000300810f043d484000d03210000304103000040c05490358200b003881c0070070a800034540d1002c0d2406100070b11000040303e050b81b510036035072803981c1c40145204400b64007840c0080420000280107900014540350082400f001d400f41c204070b60000302c4000240780102148420008035075944040c820f100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 357875062 1250 357873812 357873829
    0xa030605011d01050d060b131403060f0f04050f03031e06150f07060f06032402091c0501090c0b0a0201060801020733050c090117040201120509120403050c 68
    0x11003420b050a14032040b5402e280c01e2005403011a041060024400d41c882100c2c0d407100020300701e2024807a032510811700c0c001c1900486030240c00d14008200c0c418441e5842c0009031544151985e0b50505125211003203020711111000d441203406009070180500381001c204040e40c41158660000e00c3d01451004060500e03006c05013480780220a4010b52074400400d0b5412107070160040014569030b483c990500d503009143c050450000719040c940300100384071510348440a0260b40b0328440520140c0034161070b04a01c510079400380c0040e641e001400d04840c50038080d0310003601840000c030701c4100c0c0c0d60360345e106940c2c2c0d50004410002d010a64240440d824402c41000d001c00d280218a40101d94941d20f00464180001640a1002d03ca032114400b5041f0711b49a80c40314188002c2c030541c1000000c503135050b008640903500040c20304044404590410003040d000d01c0d0181c5030b04d010701e145600a0405004010030f4603416102e03aa400c02000e4101c81d009000440c0a940070303089030f0200307074200150007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 357876312 1250 357875062 357875069
    0x7060f18030c1403210a06060912020d02060f120106020601080d080f060402070b010308070b0f070806090a061d040b2511100609050609060102190213060512030a0306 73
    0x41604810380e100003500180c0310044290403c0811001a9a180c103140c5940b1030301100340b440221002640007884c040302010340c01040500c6081c896251a00800c407103542080c0715079039880c0003c4100382c0150515185a00ea40c50000e04464a0480c03240000103413030348000106080511954010085d9680c10f11855000d4103101c8d015240e542881c0400030400400504030b2052012920040f524075940d95040f141d000e41c0c07000407080302d0b44e5039080c00d2149400caa4800e407080d80e181030006680d0a000340743c840c86501c2c1500d82400c551540c106004400307600078081503040b41c1e2000040340718a281c40700d0b60311308090700304644c130a031a2624241581c0000030380713403c420401070458440e40740d6001a00e12500112803901c080c6084101c40900e160080303400740200384034541080801c44c20820f801c503d103d00d4003540d107059a41c89185c01242d59039013486440e011144545094801031600003032020400507840000708007035460328001284a04969400861544002181186180c00d030140780002d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 357877562 1250 357876312 357876341
    0x90602030903151834030201050f0d06080f01022808010b07051606050c0f060103020913060f020313120305160507060f05040636170c0307060f 63
    0x7400441804a82c0e0303140d820080683c541030710f1000074101410403c1c00c0e840c0000e200202c0b4100304521a81840500020007444940140344c2058440b076640d46203110122036040c2d403014a0082c941080141c10b030061100d1000d03143d111640018504020441d450b110100c41c000107a460083c596940880d218521a41c2e01c00005070001c0c0141c1a0080c40d02411210f000112a684007103a00d0b2003401d00c8808100381c680c0008410b0f0204071a0b5008000c0c0091490380002c41d4061003521043c1c6035181000d1000035440b8510704000380212a00814041034a4800c180102c0c481120205050681e041107640d84281c21160355200188a1070415078840940c0d28242040039041104280b80d43c980c0809140d000d1003000603681d803c004407a03000b1030031425214003c008905180c503080016100008101c0d030040c22182050700324100d648240380b0004007101440c1c0c5202c01565071041c14513040c00100da0b0010b81440091500e10041c4010624617103d0480000c030501d1a40c641000c584031080c0410300b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 357878812 1250 357877562 357877567
    0x30e010201270809130207050705010e040207120f090b031e0f0c040302060f070f0b0901050c0a0207030609030c080703210b06070b040215070602031009090309120206040e010e040309060203 83
    0x82030004203002d0182e46422600c09540c1c0e040020104400400c400b0745045802e100142240a2000101e0346505a4009036107094804003490200810703801101ca01801200d8900c0812075114040d4008a861340c407103090109172269100c10540858008440c2001495002500c040143c603141180552100b40050141914141a5081404c41c026070100a0148400160000d95502140c041d40c95240d0320a031180d007902c185107492011500203445d500300640c200b40204040c4000c0340b0076140400c9031940203040c0d85280d511500f000e0420120b059007400455445000491480300050014a0013074440f00e02450410a000c0055240c4c4030407a17903074a182c0070030840c1581c0c60200700c404040d086030240c07a43d0340b00e500005900080203004e07009000c2001403140c08128036600918441c0030611659494030341d980c4403400139101210700050008503481000d00000103070f5400700c4c11450020308800c0c1000d8030303207081c4440030fa0300703800c550915103002c4200820582e00c03001103000b900d040c2c4041d60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 357880062 1250 357878812 357878861
    0x211b03090905011e060f0302070206030114040506010806180a021e07110103063b18060f04050c1e040501030614150609100c0f030306030b07140a0f0e0409030e010201 73
    0x7504904c031800740404100c80da5050480c0c0f581b2a4065504154004000c541d072540c0d211a500804002d001e8018080c074144000240c40750700401582e80701e040d0282c03c0d06840c0c10448105d040080c3c0080080c500158284400d0842c5160f12501849a03003401d03606694500032405c01d1707506010200e44487c10907060100910a000d941a001143c2c00344e11482203c0c0d0007040711152245c2812100d40620612020081019140c0c008450301800401c201c190307035464680300c002c242c0d00f41d81150050a0340d40a02d50340e20791800d24410704c4180007100d05202107030080050004082d604282d0041d40d9041d2513031402203542c00d81e0518203030400c000d854209440c03c0600013086842c000e020501d8480d50100170740200060207034042c0b440da00e030301c4200403424415501e4040d004000d00d010940d41d448540d0000307440320b405a08503d004d1a08a401681011400b0f070007282c1c642280c020000402100003940300e0035031aa801502c00c0075210392141e290806c1010002400c5845102c40409611580d00809 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 357881312 1250 357880062 357880109
    0x70302011e0218040b040b03160501090f0302090105120a060e160b030f04032303130b090f10020702150a020d020c040c0504150228020406050409211b0309090501 71
    0x2d003c2c964096502207030280118002034004c144034088a034042c00340003000304102c0c6c42c448080b401c0d540240c82c0d0307000f51078589484007031080c0c840c04000c3d0031504600040c400c501d461220401e04d04600e404840001c1c9013641e8040940d5883c00119075154024003800b907a502001d111000540b481803002411442c1448020312808000b50010b01402004e43c446042812a072100c54040d002000701e42da6241420300840402524910090b140c02404201103001c4500c00b10b190460002003400401c0c5911042030244000d62188800300d9000d032103540c071101642669405040481382c1600500140c4020580184c18031000701d040d184500e141100d9450301c650007c041c0c400b500c400303809841e00c007000400107070728265060701801007607141c042c6062072141400c0320120555109603020710409540301c00b8402540c2e000c0310000c09046a0304003042040311413101a07174400c400b1b45041c00c440051b440040c5500490f111040e40000c044038014400202c07036016680c0142911003945605040d0040354 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 357882562 1250 357881312 357881347
    0x60a0807200c010818150115030506060708031312030b04050105031f110f0f0c0706030c0c0b04020102070e18011406010801360608190203030301120201030f02070302011e02 76
    0x2e40341448001c2c80400d068000a04012040c0310000040b144110f00070100d1030442c0000348112405a050382d0401d0440034070a01905001d100080d001742d040c4049651944100c0c0c00040500010440000c0c1e41d2021541504249580702070715100000c94072051400e003c00c1c4c0b001604814025408034007108204101650b424000140c80c10000403901a05010b06469100f207000405c12900042041d90f118451100104444d0003140101c890389603407150301307805640a0103d0000841e4605403504c0102c1c580501721a485803052064440320764807100740491000e01500c2c545849004130100d81041042446041030030203c003900c01c54186040b030002440301205000302d050255140c0000e500d09501c401c41002a00c603c48031401c0f1600c5103684110040c81180701d540000d109100c0329036100d0800e40c9a444c3c041d9006000b440c81c5a080c0341400528094404d0101d0415940d81034900840550b880174100991084e07002190b0490401454005012421881d03030019104101c0306000013154640c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 357883812 1250 357882562 357882583
    0x813020609011b0c140a09050708070507021818070504051605090a15081b03070212090a12050307030201141009090f020904030e0102240c0304020d02060a080720 71
    0xf442031102840c40c404040d250100c460092202001440203d034040d51310b001d600c80d10105549225403281c0d603090860a882003a41c036500428490400320b86007600c184000c3c010640040c11142034946440190a0002d400700c40500841b044102400c800c81e100348809030080c00304490074000d9003454034007a212245102480014050b00245e0510103880e11165003000f000e0000c0c0401459420321005820100100d503000002609104070300c110301c484c00140c1e0301925046d402004e842481c83d001c80032a9010184e5240d02c10301c003400010700c045240c0b041c1d0400b076105801860300e8182c2072402a094440044da00c800101c650003c200184810402e0081241c1c00ca03900402c2810301414464010040114040e401c0070b031740e1003080103040d04180400050802039089440b40c180440711a01090400003510880304000307400710f60f03102c0e0303160003442d00a40010050440c4482a80c00204c0ca64040915403002c10484c0d8204003c1070342016a02012034609800207120f58a00445142c94070380c5ea91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 357885062 1250 357883812 357883817
    0x6040e210315030a06020901020120121005031b100302040303080a36030905030f031206030118050d230d090303110412050c0a081e0a050d0504030201081302060901 72
    0x144080800b10300e206110710064280d4a40c0e40e01400c080e0b01961040300d2540c013640c2440c0700c000590030046a0b0000f0000b10900a5051440c0b140f90484800005051034144001060020803581e0b001d0202c0e103208444281e0704103801d2132500074018001800012042414030502c000c102107a00310160b03070340c458044440025291003107007103052109040242c48035500045500ca9015031084490100710300e00a4854420f450b0352041015aa400038500b40600c5400c1032210704020080d2282c203e030001d5004001050242c80302081c0060308815031410f5034503a1041202140e000e0b008011407050341e0301c502c0d00f545440320400d101c0c80c00b40301e150314607420303591f8030000d107400c1c180300b070340412000306103808040c0da00d0b69a01000841580302030030035a13060140700c0c40007285140c100103000032129035401074001210031010100540e07600c580c032141c0078000c0c008440b0028800740040e40440c10b1944485031107a0660000411111004040c0781038068891456400744ea10201600d002001c00d2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 357886312 1250 357885062 357885067
    0x9030605090304140d060908040e0a0509012009030f1203011706011a0f160503032212030e10050103050624030a02060a0302071b1a03100509130803090606040e21 71
    0x34034004008002130b0703002802031310f00490042ba01c12100502c0b5406046800b00c14080c0b43c403a5800d590880da07400500500c1c0220184231a804440501c000e0308c0d00010007030641f8420006468503908002ca4130b07104902c201400801400204005401004103050390b0000702003940c148464184402c1d20782c00d6072002201c02281040fa11404c10b8202ca00c2111704403c20521261180390541d660742013a02d480d4500032030100480c1c101a50100b60441013900701d21002c1104850480075801040c08402024240c0181140380350a40c0d1103000d034500031442580240034500d0502c140305001b41064440c41700ca180f1444069071169800601140c90381c4e01200c0482c0e5440e00c00f90250000d2050b1000245010140b05409003881d00c20f10681c1c0c120b403e035094041c50400e54a03089003003440102d5510081c0c1058000c01d01c00b9044c4028156400040200170a4141810781c40b0441c1a070011903246080398800d0342000503138100360288406140306440100315851a642d29100200e141c5080f031036144101 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 357887562 1250 357886312 357886339
    0x41b03030e211b030c0103020f0702060903010b06131a0903030d05101508010f1a0d020703051c0b030f060903041413090c0914010303081302030f0601060903060509030414 75
    0xc014a1102c11441d000071240310071900d00780b403030050072481040d510030701605281200c154000c5c02103071071889000b0300c2140f034103144da400c0040e16081154907541640d613900044940d030b1115402851080406500c00a1641c94024100d0618100c4400084082418080d8140b43d071000000c3d10342030440355201140e2903032106030744691503c2c41e5205143c42c541155103998142e1300003000a058801d800c41e5041107503141c20b40980d40415011046090942c10042e072051301d02c1d81c1d400b50420038840d04d0880c0c80d10100741980c11f02008140072041201f44ea4460043c0185020071007904034040c1c0c03102808241c0b4040003010788030b0142d0710541f03034482c41104a50445a861a40c003013608421100200306026040c24012000c090034010800d0061070708040300e8003c000000018101d9505036100007850f0340322003030304104d030081600807a090300c1100c81482250300f007408018080c1c416640e410811a1560070500c0130380d00e000c0c00b28030b025002004140310100f42d14030000303130f03001c000e940084100a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 357888812 1250 357887562 357887599
    0x414010e0301090803070f320d0908040b120609060f2206030302010501061b020307150c0506070e01020d08010e060603040215120403030606021519060e0a05041b03030e 74
    0x642c1c0f00200301000c00010880010780050030504d0001d4a5603da4030320907011044807181c0c0f40149924240100480040d50100c1c9010006010141030420003007600c014503607601029400c29041703506800e1020035885030302c0d600390346040e61180b07086a003040c240c206203000c02c000d02d02141c6058011403036101c1e541c0600035500444003110204500810407180c0d80d04009000703080078020f10000a20403603041d00094420610007182070b800401030b00e141031a20340015111845011848240a0500b02035800b02c1d0b41401418400c82d0a5105c00311041102000281002940c20075902409600300c0184801201c0112240c1d00031410f581da265a900c4500004003450004070240039000000035100b1a0300c00c003001c0250250780719403400d108080e11400c003645c655102c1e540407240903800600003110202e40c101d40340c0540442d03220004415407552a2011500400c40f10680c441c2e4840e014031041140d0740c02c4039440003528240a0030b6103070540ea0020082a22048020b101d5104050300e25000e50 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 357890062 1250 357888812 357888821
    0x30b010c200d15090b011a1210031e0309090e030d0b120f0a1203091a04020a0b0c01140a0e060c1309050f2421010e06070804060c050414010e0301 64
    0x1500030741e204032400c032000e41280290130808803c8502442a80c000a00305141200050014010010036810000c241074002c060010007001215454400840080410b4045541850b007414042c284241c00881c0c0c14040c222100e55800048402d140603018881050048151001403038000800310f0302030383c00f070001007000007100046542800303840c1011802400010f20454054030400c640109210f51580541c11121190b0010340121480e0441654003446600780b117a00174801410555510340351500b50b000381d00400b4000000e40c0d5915135420129002510700350b07000207005d0b400d001d4200c00c46e0314540c0301c140180c614240400d012900c00d0b01c0099664008d000740020a500300281d140c4090324a080410545042c58a00031031503aa0305109501420904109405004014203a01c6105003848105022560021555842d00000445e480501002e030042c046030351003000320b003402c0c20801c088136004d2050405011041108121940c0307003040e42c001d05802400c0c07509000c0c0d4001e0110b405071 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 357891312 1250 357890062 357890089
    0x180303030f060b0331020f010f140d02120903040b04030312020c01020f1c0506150903150708041a0609190e0a03080a0614060928090606030b010c20 65
    0x14003c020000e4501d0404881840c2c6062942011000a06022140c0b084601d03460080e4001c10b00c1c6903001f90550141c04000d110540070328000c02c0c144464145c07900103400c6401c0241d60a60000382862400701c540c02001c0d080880e002c080c618181c9014141210782c8074500c030040603c81406080b12007500b056054030000030203070000755556000ca20044103554400361111540e100c2c1d802000380418060701c94148600000f40026a0382d6401c1c3c00e902c115600000417807a818820a01400e141d542020322a5000b129591190350b143d080c1441c0c80c2d4440b04020123042d50300c200000401c441e6640b191180c9400518a010001304030b880c100d100301c0a0002c0803010400d13445011a00010140e1020310781e440751a2030701d401c005598444461a00342c200d01c0d00c50b6035001006002181c0707280380942c401d8110814040f0340c3c4d1141d802804c0100e6124a0030380c80f4031811541c4142c200046505800303005400202460401c0500c589980c5d0b014403110300c61070f01c980a800031072030104161105204010300c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 357892562 1250 357891312 357891329
    0x130b0a090f06050418020a18020903100b09090d0203121302100216051507060506010c02030f030715050708070c0611040e0a151a0c0a020d050319180303030f06 70
    0x81e00350358142140540740c1c62003007500071450603401c84041c0f0f041031036051500307034002e100e59407070303440d00505000c021100041c44030031035800c000e5202aa902000f40005014210700c01090400d00a802c02460642c010714500150300124a0520200d60220441f00d924400b401d040100b500d03030b99101c001d039290a103402900003640a006000d503680014201e40a60541d0b50001d40c440d072110144103108000c2c0c40502a82c5609000204c00141e01d6004ac40e48240c06152118280486400080c0b401c4050016040242c00c0054103a05000d08541c00100c1444003420138032003810310030b400801c0c0400c0204184100482d190f041010440d06030000348000312040c0d49992916210720041280321416a0340754282450841c2c425135001481c03070381d6002c981d14440d03031030070010076500101c2c0650b100108035581d50007041aa8001030395400c048036606e9020344d00554542240303072254024804407260030018030807007401c1e0358a03030411041d82030f003070300e0341440c0201d6184a041c01080140044e608101403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 357893812 1250 357892562 357892571
    0x50903040b430809042304060f050f0403050912010e16080604080909150a0b09030d02070b0a0c0510060803310311130f02040807050a05130b0a09 64
    0xa0b03092401d090041c1e05100ca20b640b03088500082c1d145400c034400020481100310040c1d405800f16007258003401c00d55001400124144580540c110028126510009403841200b8140701c203104a512524030120104c000c2000a41805041c1100c1000000c1c402420882c1c009040038031603c400c1e141840070300254009200603d810300e4100e031540c040f1a1401d400f004104400600400000384950103641c0141c20703030389400448070031303ca55241e004003070020400744002c0a414503203850034000000c000e8a41a41e48071203caa04050505c04240300c583c00710340c014481804201d6502e4111200e0586034180010070500516201741003030000030130307501c200d8a0444006003a24010006180d00c8151802d19161031a080d140b94000c03450500808240d4a200502800040da6200c41c1e0400d07881d0007031103000e1070000980344900f940c004488201079240c02040c00c21600504000a8011702421540181d206041401081088460401151006440b807400c28001c1cac503501c42031406488070400910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 357895062 1250 357893812 357893827
    0xc07050a0605090c0a241404050105091f020610090209130b0301090218040b07051e0901270f050a0815040f08040f0e0105060313021002030d090609060507020309010f03050903040b 79
    0x604002c8100c80f82086550488500842c031441000d047c4007a91410421a041908280c011151500921901c8ad045486602e1a4003255421219400c9100781540180b003149000461240f580c0800d500c468081c07801400f240354640da031030700507080c2078001903c006118000170002a014020205001e9000307121198291600059101e00382d100d11302452880034152a402000c4901e0f01c1001158204101e68003058a00502c07100001e10039048145050071030038101d81c9000f81e2071555030b40341e5201c407014020104201c02c244050740d401003808850310f19a0078a0a0745581d02c8020303805605403074400940014003085030f00e0001d616080d0300002800d84842d2611820304000c0f1480c041c0c90102c0850000001d02d5181c0801124801c03440c04869110000c226400e02250760b00403444003040d40800c1c081d00b4414400e520400041c90700490703002c10816050300344001140c2006d0200750031501704002c000036503600940b00325100d0f602c1d40350008166403617000c03280c1140100d40000b000001c1c00106107 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 357896312 1250 357895062 357895079
    0x60b04110f0301051e0a061101020f0408031c0605101103070503030702100f0b150705071703090f0411250501050f1806061023070c06080c07050a0605090c0a 69
    0xc6051310425580c010f45203642c1c50401c41c0100c44540d225920044880307080c80709500c51012440015016400942480a000c4103200c280d001038000c404103920210326800508802250055090406942001b10a0410011400e6224002418014448121038206c8039400410071501040c0c0c1050a60b07859081c50500252180050a09850344609101001e0b0383e4509a10920840a5008208402120300ca5001c1c40054020748800d4880780141600000d801c2c0c008842004e800104d1000f440d9100c91900c02c0140803016803090314005c615104c0d580349030f40b08440840752155072001011803128400072049038490801c0034028629420f01d421310000701d0f00215080c0c0101001d040b50080c0c01c5014805035500c200468400380d1245000000d030114034003a511102503894100c2600c0c0c03801401300f88948456010b03240c1250b684e0325030f2008101d034030303400100a07030000110600945481d025484040d510440b00402404155803071000c5000c5c8082003004554099011b80091200383c0d0b50b1020 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 357897562 1250 357896312 357896317
    0x513050603040f14030c0703200301060602030408010e060603070501030902130f02070c241d15030406060501050406090303050a0912110306070c0506130c030803090c010e0a060507060b04110f 84
    0x4580b00b0b040c4404042c903000b00482038425211404d001084012324540310403825501040d25102101e0003130a42603003540b0f00380644070180c2416001181d03a0340ca050070f80390845a00100c420b840da084142401620754001c0f4041040300c40903c1c000c952403e0301d000007980c0c80c0851070440c81552405005080c52200b64016194076401006180134007580c030b20307021800c4034044084018240d0307020100c00c0702500403004149101380003401f4100051070718010410540e04038196041150f00803081008100446c0200c0019040030b01c0d0490074140b0300000901030700d4203400020107111020400008040c45107841d1401011b0840c41c440302c0488030300380004d84c1d06400d00818040d00841c0300085240d4002d5400022855003c03005008680c0c03a2888004400d1000000721000d414540b030000204a040c00a180180624400303090ba9a6882001519500141d0f00c1140a40d8510400f0000700390048280c80c00c00b03070410070105540c01007400007002000c15802d440700081c00400c00400115541c0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 357898812 1250 357897562 357897593
    0xe241602040b040209010f0804051f0b09070f0f14190c051203270309030d02030a030501080604020a060f020c040f0e0c060c0319052a100e060601051305060304 70
    0x1420000402c41c0d0040c032040c0d219174000f05003c03510320300d010b40e10780344220b4455501600030b4003501d000100c4c206090001d540f07000100310b10203443e481304104620b407101c0219042034150a01c41c01803a200300c009010190200c180f00240701800c179400740d9000840301103401022000d0000c204880c80c855001e080c4072550b04060301d280c401d80544440c8500ca100c2200d00580454801d40884003141f220f412181c489005104618042805810341c552810462040c1c0418560091a2100e5820710000c0450b10141d0154550f035101e0401e010158a400000409440300762420ba00c2031240441c0503403416030341504650b081854000a12241d40c1d25501c00d014030006002900c15203400c80c41044614000c4405117403050300304210001240c1c1a00700844542542030a00c10f09066208031100078029003092000b40746030301c0c0440c0460100c803e0100b160440d02da80c02c03c02118000c3e0010680da24070060045041c4000015080f40e01d000b4400c00c00d00900c4000c1a1a03500d29103881c01d081460080c02 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 357900062 1250 357898812 357898819
    0x4021603080c090d0b01091d0c041d0105010603230c0f180d050601091503050d0804020a0b04090f14151e0a031401050c0406080402040b01050417010522030e241602 72
    0x3c0310724140040c0b23044609a100401022500410b01c10000104141102c0995040d80c2c1542d1180c40722007800748038001c1c62640c03000640181030322515500c201046200520040c500301c104007010440c40c0035030702100300300f03403a003515580742525041444611440940d44001010202e000b00400041e41c2c070306076540e00d5010f0001c8030b51a01044104595808010016005540d41d00113441c0f01c0d130705059005000900030180503580780380100e05544a42c10912031a920355801d2440e08007103005030100011090709140261409a0f03007041d00001d0300c1d032070912581c01102041011901c103034002600a000404404000d5030781e2410540c0f408102040c0c40710782d42050006642c0412002c00d641c200c03079a68440e050b0643e9141d017040024495003a015052042c01c1c40b0100301c032002005a2070301d24445400000d064105030b8200728464644001c083c9240da038400010300001c3c0e200c072584070444401d0303440ca400345a90403113545a40f00c00f0808604503110114003400942e141840c0c40e52111b0007034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 357901312 1250 357900062 357900071
    0x20a081009062904020a03061212030615120b0f042c0d0801090b06160b040201180b0702061b0d020703150501030c050907020a0b070905090604021603080c090d0b0109 73
    0x16641c83c0780c0041007901c01c4240102c2c9901e08059810f1a4000705090520382c6000501180c5900c1088d0401e6030180342600e61043d044400c02e15560940b1a5002410010b00f50048070b4042c50001000001070305030310104c1c65100c451400c103d4aa40b4040b150b90300c0000c1050081000c0c441484d00040b00485107040b124203403050703046154402003462000d01b00320303a50303120241e82070500000240c0b1b0b1405046400c071608120700c56410110079403021590740f01d20051000742c181400014005070900c3c51807004014901010020200e01100b12150715606035841520350402006a141c101c3c5001440c0085018402032407000c564046008801d4a2040108a001c403048880c0941140d101340401048144c0301001480035140040781c1036402001807044401c4c00565a45440c60b00c0030903034952002c034820610601540c54020107440c2d120000b03640450030040c1000701e007400c0176884900603062090550224503c1840c0c03400b2200e40e810081c1109a800c81d0314540120030301000d101d0800e169140 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 357902562 1250 357901312 357901331
    0x18040603201e09070c050a0b040b18070501120908090a080c2b062f030a0f0b0303031f08010203100302090f160e13050903090a0510021207020a08100906 67
    0x2c08010340c207009440c800c1141d440c0c083c25980c0c00c140b1401900c05100310380c10400040c030030040862042c2c0c810002c82059081070102c00c8080d8010680607031450301703c0c007014040c0d41d0381b024003030302c5071a00140e02189080303e03410055401e200e210070080d008000030700f01240c98040090001101c010030703615440c4489a0500401c0a0440d10301d0251083c2e1140840340c001ca01d4941001c0107050010250000c0c02c600d428010344840b0340c0c10414091290003100700100700c202440b840700b092041410600c49500500c1c0003d0301c1e4030009001218100000070100300b000c61000e13100c1c01508d80c1000855986c1000c215818460100e880121310800003940040c1d90f14080f403100c1d80c01040346800c000c99000d04180203681c1d80e001c440d500c5800c4a0f600300031004071100b9004850182d44803401039540c815000062004d10b5505402c180e025800c1c8429002074164002000022212030f01c030150344601452000600981a5a01c44103542c86007040300c4411002580c007085c481780c4144400c08c2a0300d01e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 357903812 1250 357902562 357902599
    0xc10141006050f030c090d060e07050a030507150309080f090910030819030209040f05060f040204030b0c0c0304091103070809060108030703180503010507081006141804060320 77
    0xd01c0c0510000254144246a19032050390055034002e010804000d040060b0480422200d0703500c0081a21929155490b00455210501110002d081c041c1c90f06c030101411034503503d641d20b1451207076160f04c4440c914890f02075407080e840015a075a01060043d9180446050014103400c07900c000e92045501c01d000c54521449908400b08990340003403100e04054030442120202800203903540d09040d000c20446080d84d48a03c94118001e50301900003d56061410a118503044900005c40c01284100800d001041ca8002c1480c0d001d01c607100c1440e070395095459213506501440c0e000c00ea2035414400302c200700701d5030100590321881c1c141c3d944552030f0f81c5400710a50303284000e214800241d003042010300e022903c2a00084649a1403c48840c0c00c99039030800309007114012503001000554610901445591584545008060b04d10340103815500d0714140712524499100d03069041d0442c9025502c5544461b0025401190403004100d540e01c2d024a180c15000900702c1494030902d11030942441866 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 357905062 1250 357903812 357903841
    0x1f06030b10030203090a230105130b0f1302030703060b030d0c03051606060e1303080907050102191a15040f021801080c0c0d0e13140408030c0c1014 65
    0x900104580200707403002400703500130341c8060905409401000040e1000c18440013100480b04142d02c41d006104003080451800c5620180c480c01896a8100c29000032444010055812100000a140c0c846e100c0301c0700d00541c03440c0c0c1c00c802034250080352000020302c4417980c07050f41000c10a800b560f00304400180104d505030b6103000001c1c04104140140c02005241d1000c0c0d4005610841000500300d03100c185d101404a0b045400d810a0070034840703d03104065001040940010f41ea00c0108003c505010000c3d445810b803800313200021900b002c401c414406541c8c40303907032017240c10303002d01440b800c0c40c0080c071003070080142805000d103003000d1003685800c02910031071b002440c002400c04100c4481c040115000742c0044c00f02c81c095803003400040c4101c00b09000300b01c1885400e8032425805038182040c44100000021a102c01c00e18240c0702c402100554204130381d01c107900c2501c642d541d6460003031000c100e00a07100071112030700c100b1503c01c10b44a01c41e407040400e00c0c541d00c02000169070725241002c017034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 357906312 1250 357905062 357905081
    0x12060f0108010e07050702041406030d1728052509031509080c100b010801050906060304060c0917030714030c031e070204050a020715020f0f090f03061f0603 69
    0x10340704100420820340c0c9008400e4015209103001850f12507176400103020350344580341e000d058201982c280009072a041101d001d1701c103e5410039488040041140da5060000241004075080e40c102451643c000c0d4644034410300a41c0354010071041c207258a0f1241400c0781c19454403006103030b100d944c00a00340102c00704800c90b9402940b0014071116401142c02030844d02108980700700050013008401401070040302000014400c00240e200384441c00180300d40410390000f8020344250f01442443d032104004c03a40d0150304030501150700500e001040302c81000030b520480000c810301060040c00c020210051010030700400190094031502071001c2e0b168450b5100d0076000da44100b01840c1c000c081e040150255400740c4d4011424200d60750003007070540700101c0780100c44642c0020310364200407100c01c0b8450420002e54046041c4a9001c030340d5480e9200c0c0740b4648103490340206002480f0303500c42048200303034400502a1030490030300001074101c014072042c0c1c4ea00c90102414010135002c5c440d10a19144 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 357907562 1250 357906312 357906317
    0xb0301020f0a0c1a09060a0f1e150302190303080c040807030210020703060c0504150905060d02090d0206040816061b020904030e030d020f070f030f0209220812060f01 73
    0x42160503030081d20490a00f9600b00d6048204c106000c4d24071041c000700034800d8003030b0809443d80d4682650800308a514041078107140b28544079881d01c07500f100502c1060030304014480003403034154448111200000aa000070360003000f0344482e09250700e505a030402100c0c0f080d100d140140e121541d41a031079009501034003801c4d81c0030000400252030f00f5005c0341c0b9a584240181c42409840e91214000c1d00c080d403580d90040b902c000307020008807a500c0080e403840c01c098a0051442800c000001e0194410030300360800c2c00c1d40214500c205a900d00c0f03090590298020442a955569506010788504c0001028070103445604800201d1030300580f2000c8541030741004e901000c445641c05c10411103005413041e01000070000300301095841c20403080002d030009400518504131550010342c1b4012280e080207000b80d501700c0b401c000240c0d00310760036400b055040302c001ca91903036001e182143c0301e00c4c04142105003d403051491024403481600070401c4422044d0000030307959890080c8007004580f805050300 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 357908812 1250 357907562 357907567
    0x105090408030606070605011e15080c2a01060303030b03120a0f1b0f200105040314031c060f05010516021212040e0117010b10030b040b04180302010b0301020f 70
    0x1428901c025503200030000e0a217401e2020340e03150002101e03001d07008a4034419403004a080503100c0c0c0d0358000c00034000a003005200c444422401041c141c0c010b4044207100308049071800c104c018a00443d19240341040b141d803801c07400b2101c4240648001d10054000c00e186c1602c0c0301ca1070034040341c3d0710070b40303141d852070300d8a8850400c0045404981540300d11007040240d00c81041c0c446050212205070501619021900c3c0c40e150506100d55400c0e1412021049040e1868042c16600403094404403074108003443c2d40b101111750b030182540f08201200c40d0b2040702400c9002c1d02c20b400d07032104054882501c408225207031110015103184c4501601080022651350744003005250070400e041c12180a00140c5801048041d102c5a1580058011103041c4130308100500050302d9042c481041c000c00d08c0300038486651043d01240305a090800740d2010980c40f41492a12521107402030780700002c1c040d00810200c5103c500c1c8014030220300c030044005508001c44541c40c3d180500039201c18540701004c41d031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 357910062 1250 357908812 357908821
    0x1e050307120c0504090b06090c041a07020a031406090106080606210c061b150609040206070309081222061409030109080c0307030807050f0d05060303070f061b0305010509 75
    0x824821034003a0803100105002d8002c25507494500500319001d2242c03400000a0a182d42048003660000340f950302c03206030a01041000c010000d8003c0e404182504060f59180382074008514400e01680004d040b041c18514803040c4128005001e03446003482600070805c841c0c4614105407103c3e03046d612140e00403c08107210306235141c4c9141c401c0301d030107280c41281d0481c03072408042040e60300040c040200401c0c000c030900546140501801640c80c40b0401c05030039514024000484401c006403010380200d0020440304101409610444040c0090000b00c41c000140d19020304c100b54042110100c917543c5501002520400da0020315040e0b81c001d4581892036130824084140c250024aa9940e2542d00c84486801052040000346140601100616580d16803170801400568003d400201004070030403000d8040c0c2d1026040c0d0b07980350b0034158040f44540364080024990f0056844c081c16541902c40321208009103a0301010703c45061a6030284480012101a400c580302403040d00e4200d1161070004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 357911312 1250 357910062 357910079
    0xa030f0e0120060114060c070603020c030c070312030c050306010e01260a0605030c0a060e09060411030906070206060d02010c0f06090803010305061005040e031204020102071e1e050307 81
    0x540c440001031600754000011800c20480b41c044415401202e60400c0700103005400d14640384039500032007070f112549041340400040365108410f10480d410141d01084055904100b4011560685045001c03550240e40b28140f0310100300010541d180440e00e0001222490341c00b40b015207129080c1611910f200000700390041d103910350308115900304055840b003240000c505001c1c0081c0101c2c500200014880e041c202803524000c1d296403018418100401c0801040d54000d011440b0005e056a41a4680d1624000b180262000d00105001d0210210030014801c6d00013843c00e01c159029803c0350641e40350502800550219100c020780014010344c1080b000c9022804040c4030b05104440c0020004082e0310791250b1034000382c100320780d00c0d08110188644c00c101e202c62000a0700044404012007010210301541ea8801c01211201580e6104002030a580c0280000710003000c48060311005400d50081c051281c058174010700a05101201c81c00d1740c003036007014011081c1c0700003134000c268035070402211 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 357912562 1250 357911312 357911327
    0x602150906181c09080c09160c110402070501020901030606030605060406050310082b02010212040605070c02030d0c0212240a0f02180306130c2d060207170a030f 71
    0x281d8070742c0b041c00501501d02d28012008550340a06a40344c021071410414010705264020000c0b921800b0b1007800e0180c080001c842c23018030b0300e02c681080c29103015203207007002030a0301c05c81c0c0da00da0052011411005105040d001080583e400b60703400c0183c143c660704140d0444602d03001d010f40cc10420f01003400344038012402160051075107102d109050783e84000702440c1c005644444600380c6181014000d042d140310710b041c4110031840c0029030400b41c02246104030b412004201038103d41e01c40703006c11103e82c000c44a50400e00d030098141e80c000e504441024241407692f542c200d0242c0902e000b00c070402c04001c0760201c4003160894014007000310305001c002071000d0241201c07440e1942e403040321a1300e595a100a06854072a88402040c0c14640001c05083c01801814040201d80c05541e501c0080c22038080e00080d101300301400007003041c0c4114000340444c10b0520103603c102110a011a110744c0001d200d40032111000c440c0c600b540820000c55480e140300080040210ba100381c0d1880989024105 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 357913669 1107 357912562 357912601
    0x6080114090403300b21060604200c1c080405120f0d02040f080705030f030a08062d040507050708031308130e010602150906 55
    0x1c1804910300410080030800c846026060700c00d441c820700841c60b81e2900f40c003190340010450040090034a425502d100c0c810100c0c050f1124000c00c4828008440030708007600c155250082400090007420391002000c16075008156100c0c80c2e404058140c110f0303544003c104508207912807030048000b0100950401c15008100004541c0005820308100c01a43c80385a0303032103080c0742c0e580301070082c600181c62090000500250258010402c0c50a0f1855101943c0c1035603601c104044e500d0801080a00300b0742c00900442d2a12401074882a0380081c000e0901c121414111041d804030a0384545048881c0a40c284180ca003804d1031311481e5484103141c2403a5207011110707184c1074403038080104100c181c0d052184030401004104000d0b1211040003421269003e034980140ca10b6240c3d01340981c0d0700600c100020410406100c841403030060002e200941036940302d440c00720102392800403 = true := by decide +kernel

theorem cover : BRFrame.Cov 357733812 357913669 := by
  have h0 := BRFrame.cov_init 357733812
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 357733812 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 357733812 ≤ n) (h2 : n < 357913669) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
