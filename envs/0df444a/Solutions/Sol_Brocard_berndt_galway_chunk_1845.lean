-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1845
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:53:03.19054+00:00
-- url     : https://prove2.me/submissions/bec7ffe4-1b66-43bd-a135-2d80c3ed6dbf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 331654676 ≤ n < 331834532 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 331655926 1250 331654676 331654679
    0xc050307140a120f0c0e2a0706110c010504080406080a15050114130b0703030c1103070b0604091a040c080c03030706092f1905061b031c0e07 62
    0x20a100400240210003403016404a2800303080c86844881c580081d280701100600680000741c18801d29801011170380f540d40030511f016504ca080940340d60601c0310304010950800c0c2c0e001c400304e904845880d5400303030000480824817400040103000e00340d0450001c0d80b0f88000d01c4203211700344001d0011104540e4501100b5075615030940183e0740180c501c80e400362058401440a036002d030742181181c03d09400010309101000310002500c044075400000c0700e4000290201c285a494014041d20190341d0800300c2001c13100d03481e1700382d49200d8a50701529009c03804001c0b94840c3d44541060754070580104d48200c0b030008200c0000c4030142d0507501107071041c040c0500000c0300388002c80c0a86840300010090f60400f480c0e030f1115406410148800c9a00e2210484c1c5004941000c60144125444190b480302000d00c551050003525441444c400c5c161210144041081da980c030400c9412451041c001c00d400300d610280d41601c0c60050406c1212044006180c0e42c0000c8a690302000e10f0b01d10b00c0c0112042076 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 331657176 1250 331655926 331655939
    0x527031603230a1502090d0c15050705100b0102070905010e0f010e1b07020406051203041a0301050901090c09030203100b0a0b030402010c08130308070f03020d08091009060213030c050307 82
    0x6003003000c2a14458003c412120080745550400100e40764072420094a81091680000d40400d1381c602c04868020080c0010b02540700780c07904000c0c509100b41002132a142d00d946865a440c0400b403001c200072511240c0c008802d9100380800002408004001e018a585404840084d040100e803924040d052102c000110802100c0600e4020044082041d4800eaa508280b135015807001000340d80098a410b0b000406881d0f0032504070400201034050350712641032003100c00710075110b89080401214244010311135aa1405900c0341124071406001924100070b0700141e445d503c050b84003a5040c014407001590780103054003c20044d031400c44013203050380d483c0c1c0c90001c164002514040c0c001001300c582c0c107002852220041c00c5c0a401104e24900d015982d0307407402c034581d016000486514070f0410b110340030150100503180c80030289003400b05091400749a00d994680a90b11440400b584034190380c014400e440d4100c60511039450343c1e6000c00340d140d0502507001e0300f26101f828020b01c00c581000603603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 331658426 1250 331657176 331657223
    0x20a1d0603190209060706060e0c090a06080a20092115040c080f03070311060609070f14030901020a08010509011a030402040216060b0f060a0527031603 67
    0x284000810341070a54485800415265040500b052507031075080001802d5507540304041e00680b4171802000c00c2d002e04000d030300181c1d000043e00ea00f084010030300c4001004c0d5100f40e200800e5444038a02000c495842402c03640150401da030080980e00480c40d41003034120a40401020385e42019603070408082c440e048003001245460382080840d80000400440450514220303d4019000d40902e0b5a81503d5004442c104880b0382070340340c06680b0000b845000c150b0410130740f030840917038200980703c41d180400108030280310051680c020070180c14000700103980500c44014a80226120564a074a00004140c2c001c1d44900c03135400110708014000200da1401ca4005070580d10000204121607035044406175a58001070000c07640140c00384814000320134001a044d0710b40b8000e0b64003064080b82401070280c0c080e1250312041c098a02040304120280d0401f086403d001d6141d1008040100b03960510702c1040c035071901c0107605008200c41c00c0044552f504107402944d0103288250318043da1407090304517 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 331659676 1250 331658426 331658477
    0x1020607050a053703060302040f020c0c01030905030d0c02060103061119301407030507050f090a0e010b04030507121101120902130207030e0f090f040302030c01060603020a 76
    0xc0c50401404240e14510a241d016108103d102c44c4001c2458540c4680060490380001000a80e564020401e5141500814090f44040b402c01c52070304158156a940352004014a14107040c0c480713103010200001082110b82a00f54000100098002d86400a498440070300c0b05540c1c0e281404001081030a07818200c0e4104941c4e8189240c4162440303d040d00d03440141c00da486900d0207621205254045070b010b4243c7c06080b1f04100051a90490001c1101090042c14220405142a04004020381c01500300c400b0665070f101303e03903117415202c0005810594107412520312907005000016220301d00030060010340c1e22520507a1b00c01c2e80c50300040040315480c6080502540507010b903602e90340d40203020180480e00c4d046008941c0401d43c5e00072814040340b44035545402540003d211091650102d2a108006002c0325032000305803111000407140c2c50080c0503102030085d480089010580204202e64080302c402d002442101d41c0d84070090000c1d0003901d091004500e03080494550400c0c4071000c00ba = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 331660926 1250 331659676 331659697
    0x10b060a090312120606050304060e3405040f020a1116171009081305010c0803062e020c040506011106040803150301021b070b04031a150402070b060102060705 70
    0x280351074590b450f200c00d88040c0b00d81000a101c464101092020f845003d20030140031141c41e00e42d0389040c40d203002d1049038200d0b1351103500c5170000000034005004207500304500382c01c2d544142c0740c12404a01609a050601d030f02190b40b1520300f424a440d40c110326000340601c6051511456401c100383e0174070a403100440100300e9410509160144071100c0140500103007074466004907a50000c1411401040b12031515040e036507000c0106026801184442d4500044e12081c039041001211541d5050528000a440e40e0f00c201140014044110705800400d140d008280060411680c80000c01a4031040b014018034011424200050132950207001c00301d0b00500000001d049590342d644031101c0d560405007191003c1d00c3d48403c2c403460b542d003d0000e031464103c03155103c0781080c528510607181409940c00088400c00c10b0000f00040b40118007401d121013001c0d040701c0002d0317035034041c21b00b074451419460540c41840440d8040a111403e0680d510584003a0210340d00b84d20745400545141c01003040b0384 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 331662176 1250 331660926 331660937
    0x815130605040e0a32010c02070510020c061903090f03030504120e0f0907020c0303120109140103020d0b0703020d140601020732030a020301020a0215150612100503030a090602010b060a 81
    0x22144004030042d01c002503100b40503a01d8176080188009400d6501c2d030749590b001a80600010f00c0245006814265445101d0000b803041d02031003c04240702c0c3c0500000c0003200ea144d40c00701e104d258069080003034450b40c8000400700610907454040c0003403a0a80341034511880c404030706d00b60b00340031381000b0310103000081000032161141410005030000003031041045010b84054031200b5207080015046c06014404100801e41c100105401202c98920750520091170000040000d81c0f00c0100c3d988007030b034100401030303044d40da01d0388103602902c5500c0929201c5071400e10a00f910307900c2d000000d170003250268207403035021ba9101c455111000b0704200c1c1448106070030711075174140d542049200c803034602c0c00740a0b5182c43d80e442e00020308a070421400580903822103480c400c208001da200e050340c800c0c4460b841900c060345c1080420709030b004234800e00c521444481e011034030080c42102c0500007404000c00722560b070400800010a00e11f003a00c00d400140d0309241c00082645095010380b8104520759464 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 331663426 1250 331662176 331662203
    0x18051012050c040203070f17071707030b100e01030f05041502130914071103040806280603060209010e040212130305070b09011509020309060105010815130605040e0a 73
    0x8042840104103400c450700d01c9111540c1070a6100c078005580b040c2c4098a520601441c0c021002c0e008914007810f00b1a042001420403005a8002400b035400000c03104646009030341e41001a002001c1c03a1200e598404c001d9440004503a0f4884e2001c0800042071360184411029003900d03805031902640c1c001d0010055044030615090142d014005a0b08002c10075642e482e602d44403502295181681c21100c030a80ca4200400c0d0ba401030012011100c007000250300d424902039040381c031028080c00100e188298040c901c0303118010b80d01c840f801309808110800c4455038901c1c0110080d885060030602082d2180c61600d25407401d8425105000242c0070340c0c01d83d69562070030406581100e24412014050280b10384001300b01250030140c8551001000012482c2d508030f50303003a080006501441c815070040040050464020901a04503a000c1c24012200d40b03d01d415210020b030004009500003600510112006c0d04a401850446005880401c0000c0c5855069501d4940c021000b42910303000800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 331664676 1250 331663426 331663439
    0x903060b0105040b040b041a031b07020d02091e15060702040b0312030903180d0807121b0b1f0e071b02040911030d08130813030b090601180510 63
    0x1620100051510038a89612920031004d0764006030052451410301140030f00002ca1492100c0041c03441c0451490300b1850545020341c08007003e00d070610444600411441c1c110b44500a640035410743c0109030300e400e4507200701d1911a22804020b00d1600320310410108103011400e503802e2400b81e8002e000c0c01d161040640a2101404000e00896010302c6040040c42110f00b90302c020394040c44c0c0b442c0145da039480359009000c11041c00c00e0030303c0e80310b100d0802d10740001500344000c0b200000d5111b12001601200204c0c2560000100c43d152544422601004010000c2034528180f00390445141480c00001800111181d821280201074101e20b49a0200325000d000d41051130080c03000c0c81c1094004051680402c06545e003011049903440c1c80e42c5543d00b03a928050000b4a054245441c04010514004030b480290001c880c8001c1d0052000054141c0d0620307070200907070040c58004101222908025054680d2103809220f0200c140c10301c601001000000c0d03004075805500d00c0c03c0081340c5541050b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 331665926 1250 331664676 331664681
    0x31a0109091104050607050a05010506090c0d0905100507020c01020f0d2307020a06080105040b0117011203170117060a0e0c010e040b120d0e240c0307050f0d1707090306 74
    0x70304081c50007070030f10000034603644240080c1540c42c13059020b0042012149005070940d81d01030f100320f11425840041111400e149ca0940d000d680c0d440202041e0b918003801c190b4180507a221008040c103003864100040180c0019815065070800c1c2e08458401800121181e2241070442c290b03c0051808404540340070702130745240802040e855281c074601425a4005440c980a03a40701c000410b01e41d8004201d2494144940c0111410070f003080659400c002d45024a24101401442c2c5580d107426000024907100e94000042e4403e000b00300c46455848465807510413030540081c1e10140b203800c2c00552803200c00d00400c0c0341101440c00805004240000541e48690394a019642066031101048125a03408844540d504e030b00401800d064080040010441e03407115134154001c40c80d0fa03400a08400361640454075070284c1c200450b4640003804005400c52142081c046d1a80c880c1c1e400e01c10040a011410440014180d143c12508540c0ca44070031904000031900d40000c200441010000700b00b054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 331667176 1250 331665926 331665941
    0x61d0603060a0f270b030a151d03192a240e12090609090a090f0305121303020a0308100b040f050f0306060904062004060807031a010909 60
    0x514158440f0b45489824100c80ca15070301c080040501401c000100d49010f8036480c03644070030701c034050000c0b900c09004250380c0c1010003802081030380c0c03d15030203941d00b0441d804044c180249504a036180e084039919256039801c20071b002c0800d040ea40003901d0805002d400c1c011800f803080a07070090201c0001e1403210729a00f000c4800d840b6a0740092185108400180d032454a041d0080c3c00040c880700c030441101c4c9080c11110b600f0768080340401c0003400302c1c0e8850094400548048543c14040c0e5900f40c0910041c01040200624901131582540100b5820001800f104000400c40311895a16080f0b185000e01030400701034003503006200e21002103813141c2c402642c00140c580e1024501e0380e070b0b00c0c640445540282d108a01e994041d05050000303292541c00740040a00480040c0f14a040003800030300e03804d001510060045541d4541c0c0c010421000c0f041e010603210001d6603540351a2746481c0500f1410086078a41c0019141201d480800e8584104452850340103a403000901c0d07050004443c01030110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 331668426 1250 331667176 331667179
    0x70b040f150c0803040f030e09010f030615090903120507080f010e070e1306080c060301030c12060b0d0b040303051003050303010b09011106010b2703030a0e011224061d060306 77
    0x1101a442d0226459200440c0241e106121600f030804d082d08006114040300e6201a208240c40c50040004082e520650400d0b6900004000f40440100740030705400c00450b400500c3d440d00300000002450740010b0741c82044201d040003486540d489030300488054104440c0e045c01c001c0d0100c01400502c451480c456404145400c20500340300402000521080f0001410b5842d82d80719601484040010301c6107440c030740c0003912414190f50555888003141111400343c41c03545406401004144601d580190480d040c0c0a880242224028100804800782c1183c0507000f181c18007000c985403c43c00e02c00c290489400501a505590034001070842c60750003c074400d07040000382214100061000c0c01410300030b00f02100c40e90364440800702c1004801001c021021010103d00c0050f00c4035440202c21140010b401d840e1a414044d1082c1c0141d6054503c0203000c48040d240a03005510002a4411840386204280b124503079240d40303990480740b10184a003421a405642d00d1501070a0500341d02454000c0030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 331669676 1250 331668426 331668437
    0xa050d0309022107080f190b060604031203020d0606050c06040305160206030c0c1e0a11010c0b0708091902131a030321060d020d15020f0406020f070b040f15 69
    0x3804a403a41c41d80c8954101c20144d0043c800403c04503004010b00c2c16805420701c0904110082903500500b00c400c01c01c4043c02e9041001c000034110f070340d1b0700c0c2104d01566210071b44440c04a64074400070000c2d040700340181180b51806002241307071401441540da4200801d001801c480d41c0e0383d54104c650340c1062203003041d45000347d03141c64016038852000e1403044082c026a0340e103520502c801580f8000d26080d15414040d1320721a44141c0e00c0c400310320a902c094202007286614898100100c60b420b5500c18060011000c0c041401029544221218051000402224446030740090400c101c002e407500002d6200c01e030814169054035164100c1010b016100c250325855001040120342194050b2208001101d0011308049141c50010360301c0d07400010990340d004030350340030b0745c0850380c400000c4c0030281c02052206840c0c1504070f01030f01260900d003492007802c2e40765641c42101075940c2140c0c080320b00c0c8500850030003040100c0080180c600f00d40c031038846982c0091130900100d8524941d61158410003a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 331670926 1250 331669676 331669699
    0xd0b0a0b07052d06070f02030910080717071b110402070503030f0108060c030109050a0f15030c0e0603062707181503050d030e010905070305070f080a050d030902 71
    0x310040c028141841c05800500500d461640780000d807034410040ca0440c040c40780e1881c41e120400001d80c0e0b030740641e030340c00c03c01d0071102400c1041c4c1c910300888194aa000b038002ca9403d0841c0e03409152107001d0882915000f201d021403601e40c0c04c0300103044840f4400228021280c4048501541c5400710711801000f658241070405d40106003640e0140b0000d032031560002007881900302c5582801401080707031030301820480c2822143c554503448180319803503105454030081190a0a01c0c0d010b0100c10401d184100500c103d80412405203d4841c8000d83d03240031a07020020f880303581030041512030382c030003000f41500d0f0791600c07180d0141c00c00b218100781a090088809000110082204d403000c1c10b04541251102e81050201105a030302c8003505c01c4411000117020000030ba03001881c80d1401c0481e007000700d038034200401d0503801802c0449015145109070308000041c0000825400c040d5a090819050026140d00c0010350f92084818000e000c2da20044809905500c030ba4421030001d48010054068032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 331672176 1250 331670926 331670939
    0xe0411041a0306090705040f0905250f0210051302060a0513140f010f092612070201080f10050103020d1e0c02010c03091110050f070c0e010f0305030d0b0a 68
    0x1d80e504030540d0580000c00d10099151100d5055031244003490002c0ca0715003483c0c2d0508040c41d0a21a1012094903400403c8816030040c2141030085050925528010003d000c01041010f094030210054040d01c1d048601c40f540754002c0911910200503070440b00c510542c24031019511000c010360421609009510b03268072403401c5171004001a00c0d040306000d04040410011940c1d10192030306100304922402e41c0184c0200c4204100c405404000076052096121a41c3c4c86040c0c0031f10340302c20b00032965484460151103024000041c001c1e03881c40200c0c1d8070100c641010302d60950b003045131040d0052082042d5846078000b07001c80b40d080500407840d01410b6050340d00c10003c0c1c201105440e911884042009582441808841034003481d091210f0034094840120941010307203014040c0354000301007010940620100c80740190054050740d610703003650403d101c103145503005007410040144000105420001c60f082d00796904070703024614101d030050f21103004140003010b1940000b186035002520 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 331673426 1250 331672176 331672199
    0x20f030a050103030e090114010c0809060d090606090203010b070b06010306230301050a02041203050918040c031109012102030f0d0903030e03010e0706050c011413030e0904030e041104 81
    0x200d108840104665045113400741c00c03000100754041c0901c144100410541c0c030201e0007001e0554013803c00907460100c0c0e080c03040f0789201c0c3c00c034003503000300000070014800850f95000d0441c0502450003042040d803904d0381001644400c3c441d40d28446418028000803642550070f072904000141000900c0e596201c4000c40507144100350191412104d404802443c02c080c05501e138030516610f411032526060140b0b0480c3d01e85110b10180800a0100c0ca030800b07074441c0180c590204036400303c01041d624041c60445d6180c48075010480311840100d4000e580c1c2d0034a925240d0507504071160400c104c020b140300c0102d44607081001070b0303070501c02c1803504501e408040c840b014000001e56230b02d0010a0442c10050310403450500054040da25091600c2090300d0041010802e441040c50126030b10040010603a0141081c54624600491800240014190103500100500784252079054810b0801d000700401e902c07003282e020700400d898102e070700d0030352030541e0102c0d00610304900c400b41041e8450800b90b88 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 331674676 1250 331673426 331673431
    0xe010c0503070206060102060106090b090402040815040c060c0c0b0f07020901060f030606080402030616171303030b0607020a0e28020c010605030303010b04060302030c0415020a0c0609050f060d020f03 88
    0x10031030000c20300194a90510000754040d00a00051500e0352401c100100320b600c0c144980400c510300803803540060b80c0c0d960100d50080a100040f14440b0703c030f04569800c440001ea8003101c40c001440b400184460050401c01102ca800402084c0c41e14604003240186034070401c02058044400c101c40d100503a15410a507010740171a540c1d50650010a0340b014003251565000001802000d00400c40140e4001442c203522203440608041004500d480903600500c1060703026442c5800309082180340c0c94000b0321609014041c0e602400101075843c00e102051180c1e14000c0d40014400c0c41c1031101300302e50b010850304070159940f65650f104410030003504c03050005401c044d40c1500050304440042d024000c0300040c00c012006035245501d0301190258911541c8282410705401000090000d0170075000d440041402d56440310102c020604000d403649050081218440b035a83c402040351445002c088090b10009000003c14007a01c008000040d00f00c2283e00c3e08050302001182d035040c4240c0080c50 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 331675926 1250 331674676 331674701
    0x1303080d0b01090807180c0215151504080607030b0f0a06050315041407030b1507050d030c0201020f09060f040314030706050a02030c09010e0d080408030c0c0d0c180e01 74
    0x4540da100000180010f4082d0300070b00b800e42c006002881359113454020164108400900001c40c2c84074080183d05105108580e02c40741030407070341000401c90107103480190384070088400d0855680c84200c106c1e8917011b40d0040c030219030700020000f0f2441b4002e521214250400820f000d4114499000288848016400080c0002e0002c02800002c0c1c40c025414081c00320102c4050004861180d04070018801c000d0000c41015143c05e07a10300641c4800324824101a04025155981c05441c10987e90700e041c207480b54000207142c4118185482d2040c820303643c804c013107550b0061612090500b0407015402c404410081010308210020004000d038000703c0e44000480003554442d07415040035030450704001c0558901600400410a10a45210458102d0402420540c070042003c0c030200e010340c00324030001001e40c20001404900e107003001014229441c000f0342154103680c038034001c0c004903422400c4000d1148502184c2403114980403007403504a0304200100054984600700501d082d0792411a104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 331677176 1250 331675926 331675931
    0x905090c0301060e01030f0201140d02070605040308100503101d0d2703020a0e04051009050102030604060b0906030a020a0210090c06080601030506130e0118121e141303080d 76
    0x580d5a81400e00030b1a004040b000f46a201c190b1640e115003080b0410300300e00a042105013101d01c0000c052040c261211000040403c41d254049460300400901d010758068010901c650005002a15a0044102540c0002d00600400128076060170701500090941c4d0829080807504182113810400000c500a02595070f081680ca121046a5a00c20000440101d02540c1c10409001580b00c030941c96049a40e820a4840d10760348a0520034204038401048850355804c0000f008280141500594002c000c101c6081108a039618410360a61150903104c41e080107060001419100c00da5000c1d0440201034010750354032034455642d010403549181e0041341c035800e62010a01c401c50348001f9040d480381c028242080141004800210300c030840c00000080661148103130035441c0360030342041180c0030341005200801d400e14500304001c0001c000808002400d114001120246c00e10302010590740c85c0d460310070103450707070800d00e48c400c0d4400d540907009654104d400000040c01c4100038850b914188400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 331678426 1250 331677176 331677193
    0x60309010b120d1806020604080904020705010c0c05100c0e040509011b03061503020901120c140706020c060703020304021f170c030609330d0204061514040608061207090509 76
    0x500440201d00d202203041410030303070174002c0c1030b00001c481d45c0143d0480a035507255a903000010b0040e00c29058020095401d00e140583e40e1a0001c80c10360141d4030034011b4072122032809842c901280c10350600900000c4518031b04001c18100360740915008030903240042407010405105020340404021140002a6181d40402002d80034503000c4900003500c2c40c00758582000e02000801c03400040c5103212404d5aa020810070446c05034036041c40d070f55214240940c481020b8100300000b9004400585014004d2000090b48140b1034821244103903401003070100c064032910081c00c00540d4081210052141c449000490700c3c1600c00c2180c403441250030b60755030381e286c01c0c824820301031005030069a60160191190080c450280c510202e01c1c5030f0341903034050b1600b01000050010f0b03030320031010307410610b0310380c020845c04042c5003624400012500c0300000710300001686030f800e1042d071190314005207001c404600d0610346516416000c81107081140e406d15124140901150300584003c055039016025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 331679676 1250 331678426 331678453
    0x81305100c14120f130513020a0210060506070f03210203070215040302060a0c0c0c0303231201090b0102030c1533040203040c0905090336060309010b12 67
    0x348030905080c2c500541035480d03100c04446041d0280c8811000040d001188690100400103210f00003410300070108131003010390301111802544010424001805080c00c4410b00310004e02600c822a240901028506461602c504c0054200340800302c0070001b03a0b486520800030511141c216143c940c0070016039908145002070f280c0311841c0484c1d01954142c00800000c60303000300e561940040c200d00080342070369031428100c901c0e01c0100d200030815003800f04c000c400d15600629880342103030000705070300e0300c24100100b807041e41c000e0140b2114410f0070b4600611001c001d581116102e0403041c01164104084243d0712420001750350f041070100c1c500f0008204841c40c40480d1000e28000d00e00d0709003007a030401c0741c1595001085864150041303400201050421240280b01c10081401c080700b04903504202150381d80701d03070040c444240c05038080815120040300540c880e40a403080d03055000d16000c0d0000c1801950740004003009095580c4a455612907226101601c00081d00700c8042d0416441c40d64 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 331680926 1250 331679676 331679693
    0x4120605011409040203150a0902030604080307090b0c1002130b030f1504020a080a150518010906051c0b2214010f0603050a08030c040f090b01030e010209030a081305100c 75
    0x401c070701c42c3c0d02e102c060102503140800d039001806074000c051400756036801401005041003080c003e42521907102000240464400170714060411903540c076144a90360305000400f0b0003160711401590300300c001d034505500f485070300070160a0901c10700c00405650b00d0100b0703851a00100d80105c1d082461408012502d01440c410182801c4215021414600c00f1a8010301d000d1000389104d407441d44c2d55a0010b80f2030084030100d030003002c000309170805c1500000000301c4001c200b88503002c8401e080541c003054500e000e1428a22155030709408401d0182c041e12000906c0c02c02030301402a0003601c2806c0076140411180c04000c1c20b008010141028084501c0d10b8211030110f0740c0120200d00d000703000c3c000242c0c04a40301030060341103900103484e0384401c690300034030f44166440b000000703108000000b00c0507078940008030610400d89042002140d50380205080c0c2c801c01401640c0340c0c014030385000c002402c0001401c00020506d290241c0942c868000c690305202c98880c00313012505015801c8108400070 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 331682176 1250 331680926 331680959
    0x708040c261501060c0b130209041a1e0a1503050d0e030601090e030306010804030e06040608151f03180206030c04170102040308090d050f07061101060b03010506070210050412060501 80
    0xb1150b152007802070000c0d140c03200003080d602090b004641c40c4810500742000164004200d2481802d00b40b90007641005544100904060504000352890911461031450300741000c01078052640d6440800c002022403c8100c03184d01c6040c1008404580104009468100d0640b25592460508400c03d4604013059001500c140c3c1000858103c1c2c5c0b4010080c0c9800000a00701525651201d26055414401201800303801000c0410002820743d80040464010300045c94030420552011080c03004000b000c0b00c04076188040c0c40c1e04280203a200781c0c8109080c104900801c1442840d9a000070030f00d920684415040540129013800324100b40d0700500c0c00c50040400851070300d0701d185d640c070800340200505103208504803200e0b001403000a1000d0100d4000d24002d4a0a45848102c09890341c0b8400380815455803900c18086a224002e00440e4182c0344011318807802c0020683c05c100c1c450714540c1c04032040040601000614030000c0f2202040300c0d1148402294540c1050715500754a10003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 331683426 1250 331682176 331682203
    0xd020f01150b07080f2203120804020904110d0f15060602030408150406060506031008061006140d1e020307021207030c02010c06181118040b0708040c26 67
    0x1c004126407841190340c0f03150300101c03c0340c070780501000c02c110354000d030040c20402c80d0414882e40010100c000c03140d801d4901c20b205641400c407201d40704a0714400c1c04c0780c0c0250094000d10205011030640c0c90f1500d094040140b01e46901d2803260f0f104e0000c01015601210140d06003184141001418040c50020388000c0c402036080918181c0050790f66214030342d04410000c02500894180080342c0c00c0540036060207083c065803820013021010083d2070321301c9001d0f000e004030808104030011004510045030b04035501c102c103901c8520460b01582e40801e80b20004a6031703403080d101e503000015031200500e180510005840f4a40381c072000c0e01785003030030704042d611403804c10140d000a500102010382481d028a848055a400b41c6481070040080800c020302190304009807000f08900e080017500084401d0703c1e04011400780320800700510301c0c1503c00904d2107602100289083e807203100e8a1ba84103028481c0348820554a64905003801c0c0302001c805400d101c1d0074240503001c00c00b000500c500101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 331684676 1250 331683426 331683461
    0xd0206060108010b0d090804030819030e030f0c0a050114150a060815030f010203010b04051f0507120903060c0f030c0f021b0d0210080402090c030402300d020f01 71
    0xd210000074a00d190500039510600c00c04500c558146109600c0304c40101e0380400c1d0180d64039220f0808030ba258008103806118a500050021100e41c030a01414018100b00c0000714149905c02221602c15004a00f0201d054131400c02c540002c20002d0080c12401c04002e020b8580e14180003000340c1940010904550090394000820032406a128902c0d591003103418215007011030f41c0e8000207080000c48c001c100c07410341c004800440c4400307010300104200c3c0d20486048005d030b40340b0502d80c1d20b00c40000380400e006c65006e00004010840c1c01c4031030000c1240034649951065103e58448040382c7d03000311807030005046022600025070301442030b120700e01594200341c03011206642000b9900e01c1403070781c501403a80044094100d20b403521380501c403090398010802d00034080d04110050114001b03c03000c2c1d205410f81800301d4000c0503441c084034089c82d00a031182d1110240c41d49400781280041c00e500a030030b030847d000003000c48800d105c0d07a0090742e92035002c0d0603045551100d00d801e40f4100c8594489034003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 331685926 1250 331684676 331684681
    0xa08010905030d0c05091e0f03011503080313060c020102091e09160504181b0804030503150a0e070e040b1009090f020c0609100f05012d05060f03090d0206 68
    0x44000060310f05201880b80041104c1034900c0085a142c000c09006540040c3d89404250740040504011210303501c0a4907000f40902c98003080500f680e69014409045211402081c00400c0f003003401158065401541c4281e0b040e696912078088903c5121400d0050354082060141454005d03546501c00054200c1c80304101480c60000c1e400c040060480800111360211880e04903001d1029074008000c14541d4a00c1c40d003c0711400c0b0040c0002e0862810a80001851618194043c0d43c1e8907002d1a01070351843d056540d200a00030488181d4050103078044650200006d0b00c46000d13180c40e12132030155441034505c0305080280000d41c0c00288096100d00c28400b10503640591100e01102114455107000c5218110501110000d11841c000880e480c000c075820051071450004201030044124101080300041105260046460a008010101c0c00f425041c0c0e444a1320307040d0080e56840078515000b003103a0354200080c1ca640c40b110760300c9861034011040089460061001c1149000140007070419031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 331687176 1250 331685926 331685933
    0x90402030c090a0b120f06010b03010602070e091203010305011416050a080c0403060c08040c061b08181921030f05160c03080c0615060d0905010902040216020a080109 73
    0x90107800d07001c03401010010001031000e40329401200c21110b000d8175aa803a980c0020889460700d07241028104107115503400000c00c200000c017102d04891456010300720a42c100360447c6041c5002070950102445015400c004041041c1c000310300031803048000148902000c0109209000e0007412603400f564100040740c5039a070007a00710b81c510031880ca071107140c40da80d00948000750b020355000901441e181c046044001a04000e100c0d0003140101d12885086070b82d40411194004102a030b402c4181040c1c820b40c7c0003400e84001b60640070f8030002c5030260040c03040003041840350740003115124200004402c103c03030407461229014161565100e010188429100500703036000c05d02140040201c005500d52105190b885071170030345a80700312002c0c4030070781c2ca0410b04941d800240407000107008490101e00b0310b010600e100c0d1496180540424148252803021070000c03d01c00100303441c035540302c0c1c90503401a51184024501a181c022110441c50340c18014410360300381e650403c0d0013903031510b0700da200030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 331688426 1250 331687176 331687183
    0x12140105060715020d050403083102010c1407090608031e0c0f0f03130801140711010b030610030309060f0801600801091a0d05010b09010509040203 65
    0x5440d000d80700c1c0c40d501d005902d040c018200c4a0110410070601c0800c0040203041660001e5003c2c60082e66035247d0b035100c1c02585104140d44030410034029204801da5900d007a13841c0c90210005005040600d016501910342c42e0381600405000d11040e00b003610140000710305c07481024040d0001c40001c40c140700c1d0000c031221200c4001070078554030920100380b4500c20f03d001c200e0700d58145418829619840408000039590380c11101c004007030103985083c0405e01030014425091003400d550500d00c1141c8070800705a0b145040000001610b540307400c0c055400746c40c200304150240148010244045145040080c4210020f170441300811034641c0c0080e041316404501d40d415030343c1d0148046c0055200340030a131005c44a810f600140c400c41952030b01112620040c001031440c0e9241d90b090030b40c00600c4002004001c904140f1008034816000500c410400c03903000e00c502e1072085600b81201c0110760300007081060090340488d00381e03440388115074041c2407031170056004000035103000b0038a04159000075203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 331689676 1250 331688426 331688429
    0x61b050a0b10270f1b05120109091a06010509100206190204060206181603060212060406080d081b07140d030603020607030507030207090e150c07031b0503040b0f0307121401 76
    0x280355880c0c40d000103140f107542d8403081a00104040b004a070030b0354007a003d401d0b90405040350001d403075006e000182702c03051806501070550740182801280d0264202c401f415400152419041180074040d000d001c0d200d0284403583d0168a8004040700e290a0210340049001040f80e002554010301c0f04106441e000503003241c005000f5011740342000c0090400c50314101501140100e0710041b074100106000c1c99034000e04640d9403540b0342070000e907142030902c400d42d0990f1190000c036521203071561401314403034024690412180702c1007000c4444030b15114111070b04014415140a0030840007107031440010890703508001005d09052280a1450b000280c1d24005c1e541c0142c01d1007800141001018400e0081c1e00152041c3d4500b0801c410404c17802542d500b040411001c0c180b0300b031001080d0790021070300c241d919a9500d40e8650080590b075032242020307860364010854640c03000748404640710080313070003803c142c180038408036841e8580160020060f040203428980b04900d03240c004c1c180c000d40440d4550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 331690926 1250 331689676 331689749
    0x51c021b011805151914070f020106081e0f070303021e0105060105121f15172e080d0302070210050a0c142401090c0801080601061b050a0b10 62
    0x41d40e840c0007082e1491950b280d0440041d240c070101200746c8140403011806103425507a024945200018203900720340e00c0e401103046ca40e10031031001c070760082e04282c00300e0000390603416207604424a02885d403900c2c160b41c00441c00b40c2c210101c504012059441030700355140c4a20000e100508021002074a18450180d802c19207000c203000281c4049021410b071203002e45604c040781c111554a41d082455111101c2ca40ca001075403000c0886011200840c03018080d881c103242c066060381a8007050190700d6000700e1806450ba822080001e25140c0c1885898105a215100966201403501c100710100e10401d44441c1444028440f9103e91540440301d8150598042d00703003810700c551102d1007850214407064004808010900c038003c5105403407203060407141551002d1090304900b800a5031450310901517101650b00c60070040013a24410410340503038048000d0003034007807030303150b1500c80c24031116134801d0fa040c1d0141c03802d0040c0d8004012543c0000c120000c1100c81021102c043c030022401e4110520 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 331692176 1250 331690926 331690963
    0x102040e06060310330e0108010b180d020f210c0111102f070606063902090c0703080105060a020a110a09022b0c080106051c021b011805 60
    0x2130901700500c0b050781400481c42403241d941c5017a1030310010b10740c10007078541d01c1c00141000000221100000181c0b6180a071101100e1440000c600c18004030124811003680e01104d25134410515488000452648000031050311180c03407030707002216240402c03070012a0304019405a650000fa01c011603910031131807030000046159800344480007200182841245e142032080da1b42032000031087d000a10801d8130440062002540ea81c00a88d11204130760105800182c0800c0100445200c080c900d405034021441c140801c41341356004144145001c5545600d0f0000c001400350905812110060050000322082d030300e01060020029203c206c0c41d0760040c41c01800040707842d10340d80c032210030b00701510503000e085454210b5007800303811800b0400300f151411122000d0945120300305004256030440180c6420784c0c0c6900e410b17001c03262039100b50b40720260343e100d10b002c644444401d800141141b003051804540070108588607682110440b0100c0003c020202000b04002400070680c0155420f115140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 331693426 1250 331692176 331692209
    0x601080414100c0210060909030e010c03050f0403061e06230f030a060b12030708070b130f0501050108070b041202060f0c0a0501051806091b04060509090102040e06060310 75
    0x154940180c0c0802d1102850034107200e080701c00d0303000400001035082030100744043c0351766200341022141120030180000e4405501c001082d4012049a0f00071446454000d00d01140c41c0304100782908560011606240c554501070076082c42640f503444a190188001c002403450700501080d004414183d0600b07040020342c0f003403020b5170740c10300030800c5803c0136003900c2d4103400b149030200007010141060392040034460b4a070780e1011800400c4e0307108194040c21082c0b405000380c5130400b50010041c907002a96040d840d120000905003084000e00c280700b88004201541071081c000d050129a41140703508000034002040310300700d00d8500c21036258040d81c0780d50f641c07520000c04880b284034084141c001446a000701904000d030540c4014400c1038540300f2074800c200a0b2402d962a070b00146e414084603488403031404042c0395001c00140d1860002840024030a6407035000c10940d41003211400c1890f58007242c01c0020340e085c08a410780c0190200e070010b2440ca0001c02e00d500003443c074080c502202480014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 331694676 1250 331693426 331693463
    0x90f010f090807090f06081212041e03031a060c0304090b0a03170c06073e0703031205060415180209090a020304030f05090a030201050306040f05100303020d020606010804 75
    0x201ca01c0074003420419100c110380c4a1010b5409003100100005c400741c982030001408500100c2d0003102c140c11030414030b14003d221581d614600c80060404d40d0b9000140703200000c405100c00200c4019440781d14042140590110405824000202c10781c0c056002048100e810b207502104540940d940080e00242034503442000c5601c0c0c0c0d072540c000501d2240c1078403901c80d4050800c405080b020302d0324400c440e01035076200d508856488c0501d6100c0e031a51f8200c1c680d060600044141e4001072040e106924054a2030341d44a039141009941c020780c013144101c0200480f0581c1d901a2540c405d00594062080c20180201d240300300d0f2140c400c0b00001851408083c0c0c00407034540440300203142c002d006910900b080d40d21900254410b0301c0c200c0105908804d40b0440c00e01035820b4405820000701200269440d58005642c140c1c001001541e003c1c2c1c1d07a1075243d04008251040501940020b0f82c180d40013420b51501034689078207802c010003594800030402c01140e074412050399110b0350015148245498129 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 331695926 1250 331694676 331694687
    0x2150405120a1116060c0b0603011113062003040303050c0c060a030506010e18060d03030f020310050310050c030604090303090b0408091903020907082a070611090f010f 74
    0xa0a0003910740300000d820107040d40c4005400700c600b000405403210750f82108003056180e1142d1084401184040099001043c0740844c070325400340c070160010550510450042c032055102240203e00c003482e845041c000160f03c000510008071000820301007910b90a00000d0343e900031031200608000300014506582c00042c002e1425807840031344910744a0030b030f106003e00500340460700180014400210301209150103440b02c510031204241e40a410b8681d0380500c02d014a00c00b40507800e150300c2e4002a19034054a100175445510200600d105c0c59041c001054107080b0050a40304000d400d20090040345480102101d400c440f0854001492600a00d0290060065800080c00172220300c0c040200f8844040c0090020382c4044072403034400031800a0890024819010203500f110350744000502160041c0007141d00320102d0300c0b04d242c110240141c0c1144020409540c5100e508001c1440030800045000300202c03801d018801038100449031010400e11a00c0054144c10010211500c680050044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 331697176 1250 331695926 331695943
    0x612020d021903030206010321090b090616050a0b1f05010f0903050a0507090b060412020f0f13020d0b01090e0601081b120412030b0a090f14160f02010c02150405 71
    0x1410100b84003582d80c2806511148248410f4440301000c0c00702528800c4407412007405c01005840d100d04603410008043c14a4001d1240680c01100402481d2021030030368049885581c031801c01810320380990b182800341d83c000640010840d15280e448211005401c2000f1815248286040c1e200b508044004561016041d44060010701800c4000c4041c401d011504d0390031344041820500ca840704010074000c0300d1286100d2808206040034424005140c02e151038510400010048a42501910000f40202030240b0403200301a0b070009100c8105400c6001c0d614401c002401c103c41604d14012000d62540c0000703110741d04200c8000000f80c00100d08201091904501000da141c0300e140d038000c00d01c0c1d01c4005440996024440070b020050300f0344a03004600038031700081c0981190a14080c0d52801a00030460300144c201d0b112045039004240c0302d0b50f81c510800041d01c03040d003800d0100c00050070840702c02c6c50740c0341164101081420344540024000002468808120001e40d44070f040c0365041c11441c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 331698426 1250 331697176 331697209
    0xa1d031515120303060310240b0a090902030f222a0f0f05061303050a0c0e060f0306011a0403020306070c0c090c0804020607060219110d02010612020d02 67
    0x80005001e01001000ca9101a0540560340c00c0c00d0106080302e0103540b0701046075100e0349075008001ca81204140c44d04620100e440e07035004a81401c501220f0341181000030341003082408008288403035036503070102000c0c000f13007060749046146060506d082c01c050a4001c0c1010320740340500c01d222400c0c00c1c01c240c00085d1560030602c40203d02c04403a9404d80345c40056400d61120b1242c4c42c00c049286204080d1800c11201c0303001d40004040d260a09014564016403084402103c2c000c0300000802c2003401401410b03845901c1c074170784981c184010381c020240050700450180c2c5d1024402d088a4500081c2c0d03506403951031003d04a11510300b03180d40b5603032180e03801c001d40500071141403100241e0840d56010704188a40303058035099807540d10320811603403035152100000346404003103000350800c00c004283c507a0107040d02510b8640c08030400c0902e03521610300c0c3c1c0300107644040c0d00003c0103014828080500d40034030080c04050714060b403180b0803440000004c4d02c1181c00b4600b0b40e085540b0780103007800c8500c2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 331699676 1250 331698426 331698463
    0x608091504081b1c03050c1e030105130c1d060409060b040801051608012105060f0a180b010e061c0b06190608130309170a0213020a1d03 60
    0x10310303251150b0b42c0c2c2c21000e1191801210840d032a00003d8011514a201482001100c8213810b10b0070421030203000e000d07007100040b030002c111100202c4c207039180c80c80110074602c036440da1b03e52405d814070003422000c0c0940c04030305141400c1c80000e241d00102d05d03041d11001100381d0900442c404c0003c0c802c2d02c110350042045031b2800d80001101d54442010b002280d1038000200601c0d6142d00c0b02d0050303981031094620020749074600501c0b031240080c011103801c2d2522030540095000340e0341c03041e14205098031031303004101d00e000c01c0001240d200d009131420f004800b442d08035010841d549514000c3c1040c010b0128021400000544c01d40301c1e045010004251129009800c04482c20180d0308035074151516401101d4410600c04401000440c007011108560349001c600d6030b0300302003407500700c15180f412401c00414500005070400d4030b030340802c02c0036024400b40003600301d46d00c10840b40c05911304812206500512101488036048200101e41c00b12100c4032201054000001a0610103102910f654620 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 331700926 1250 331699676 331699681
    0xb100f060c1a1f031a0a0203010b1c15060c0507080d02071818080301030c090204060e010c0201031b0f02240610110111040e07170c0705070b040801020a02190c06080915 74
    0x203039000c11850b0b500c61a544403998492007100c000341e00c000d002b40c698103c000c00c49059240001d6190a900d840d403594001000d03111002140d5145440d94070450000e082d00c0320180c2480b2040c0064001040c0320350040c0012062064003946a0145101d100c1401d44041c81c00883e051060704004040d00c00400000c1c1c044420b40b0300078400341c1080c082a603104224100218060b0418070890342602c036251918001040340703000442d02125503040032810542c031480d08008401c3c11115070606003100f0307220100c1241e100100246051410204512484600c0704079141740c20407180c0c0c1c070307400410903900c000d01e070602403005880071908526145225864100b075024000400400b03071054940e855800e4010740c4030b455003195005044100c00060080d180003140d20245c41c680180b401a120700e0a0740d5944e940c88071400c41980083d807000e1696500060b10311010740e030620070003650510985484940004645030f00c0b542e81c030a40101824030a4071800b051469800b04400250070613021031f51001803 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 331702176 1250 331700926 331700933
    0x307091d011b1e02100b131a040b040501140d0c08030d05041415150f030f0102030402090928030509060304060b0109050105210402010c0b100f060c1a1f03 68
    0xc0c1d501500c40003d05004110100d45107518260010488542c0142120baa40d5540b62005042e084141d07688103605140301e0302d2900e0203008031100841c010710304d44c05c540d0125007844291003031003104903c960b2a1a0050148442104203250865070a642d5040b070101585840c5907103d4007030b0400820307480007103610954007040d03801080c03040b4800d51419610a001400e8282e5400080000a00075601d42d00003c2c0c8040d030f01c0c00310300141007006200814140031080802d00f4240d2002034200942d400100300401d60904589090f0003615080050070349803a14007001f03c1c2104120a0710b80700e180c10703c00c45010301d44514181c2d048180000d207807950340d00f07007850182c2c000c0040c01a07241c0400e8071084000f86039030060042c1c1c1c1c140c1145400d450070a00d410007500701507840080089060010400b1110045400610364501c102d01801ca102109030802d01d4032062405a44c0c0510104940c444100001174810910280030680f440c030840c0c2e2039222010109100282d00150031a00b0032034003070000c1071 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 331703426 1250 331702176 331702211
    0x12090703030e041109040e03040b160b06100203070b0c07060c08060306011509060315030503030c03100803041a13030b0a020d0b0d030912030e04090605011809020307091d01 76
    0x2128425100c0d9000400c240b400c0c4002d541c01d141402210f0341d020b000002207402e0035041210f154040200340c0e843d26855080b6800709411119007440800c01c10441c181c1000666408250040c0301250346225840204400a41d240315950000340f4004114000ca034062020500351001954025070a01501d0703c0c041c0002c0010808482652181c0f080b1800003803406d01c2100b648051540c55920a0342d4a030a02c40180d010741512200386503110590b8400001085040c00034600920806800c50b549040c4001000d414051036007045003181c00401c010402140c00001d07101c0b440303c2d450380d000d40318040055145082c54243e440038001201a2003000884e10455000b4100c9171222502000042d004005020462828400c024040b80d400d203418030040e10140d42c2d12080511910300084007100480208080c0c4004940c100c40383c41d2540b00502ca1101d46061103140030091b0b0500300000321041c0c00081d5550b00c244284401d05a072211400c13003180c03600ca41c910386003060300024040d4201d1072081511 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 331704676 1250 331703426 331703429
    0x2011e02040b3a09060b10020c0d0c150509012a14190305091905090708090f0102040b070201030b04021606020c1002071202010b0604030b0a0209120d0c0615030512070206120907 78
    0x1c0e005d1510710509054904081f07100c01650f403a0340200b140c010800140020301711302c440190f078103694010307000694180e02c1051000c0c8031010307581d04c0c4d00c410f88840090702409815400c7c20500102c0313012500d04034082964500d51980000d914401d090800d02c50504000000702d080c907c0007400d2800c58145604207000b08519082524401b2584440040189900e481030203440c4d80034002c03102103174600b8810318007903412601c2c4109441d802d20028411b5801c9902903800304c14a4800801c042c8190368140c40361350900f0308180d038190300e4001098044900c00700f1112004100c3da0380401c0d0003121039000c000c00540424080f03000c641ea400241094024504003c00c0540150309014101c0c285080540584d004c40358806041ca81c10380301e10b81d4aa02039000f40281c1da401001d072900704501c10008020144485c0c0e80ea0320748044c0a02c035800c1c1401500c102070105c540e0f90314155410070000b4000a6540901c080f81600162103920701c0c03001610703078420120207855a1960405100c000c03030700843c1280 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 331705926 1250 331704676 331704683
    0x30e0124080705010210231306050c04050d0609060b0301060909020a1202031b0f09010611071a040e1504020705030c060a090804260d02011e02040b3a09 67
    0x603000d076480350340a54511203401890700580085030203405a054542140e00130070440c0e5004203617141000c0842c3c0d01d03914102c2d82c40c4404003000f2100424010980314860b0441e10030001d092505041030045241d00b45c010b10001e00540e5100c010209100c09540400980f2000400034004255a0307031440340a07101c800f0702a80b2810002d8000a942c03400740c991003001c1540a00a0121701030400c0d45040009034010f0000c4c1c0024020b0407580d16079461404141c041d0804c0d40382c91194141e201407007460f1244135080154042280740f1811600540642038a00701c0d0740291001301c0560b200107400341002c0100b01825001400850703a4801c222001c405800031215240485005c0e0b039880c902c41c004e03909064009030141c0d008000c00e000300b034090291582c4c0080d1046000680d4404801d00700d103421855411750006035512724846907400082d0315121803102c0d000d841941401e040c803003036401034442d40c9001c02041c48040400343d40b44880300004002c2c042443e074241070209407082e00c0c4c805443d003040c049 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 331707176 1250 331705926 331705991
    0x50102120702010f2106030b0403020d0201060b0913060e25020c0105040b0a020c030d120c0804021008060d050102040e16051602010e120307050c0306010e15040b01030e01 75
    0x502890324110640d2100c0750140d59582c0e501c0d503800029601d59501030f0300e03d16146640408007011200c5802480e004502c1207401404524090a00a08103540c9480072011039040c5403041050302c4400d030a84400300003c41c3c05086400c00c40e4100710060440d503001b0388911241c002004610200658a4100f0013060701c0c0800d60780c00010f904a03201d0225203092408900c0034041404640c4144000e4030a0150900440700c001ca08400064a060204c1e40d00c00700092201c0c001207060340f2030740a541d00002e45e9062402d800d0070309500080d510101c00010504114881002440d150707620210a409550880021540c983d00c50480c1040d000084405801c24240e00c007440b040706200354211641c07a802080c0190803030100d030f40119012480e2800555014141c5980c90f0024072701071008000091280c0000d0030040044e001341401d02d00164409030701a400c440422003102801440002485c0c021a40000c0608c0d02d02c0041c4c00400c12205805560b600c4c1804090300100c1c00d0305250342161414042 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 331708426 1250 331707176 331707193
    0x51509040c080903030a090f0f0b04060606110c0402030421080a060609031104050c040906230d030f03050618040809030f010c1202070809060c030a1107030f03110f0610050102 77
    0x35074541c1d000b40c0f202811035100f0030005211000551040140e10300c152000d4901f0001c6854104140325050400e803490001c0b401400200312036441103030018001402c007401681c01d030340c0c3c0075912580d54104141c00345800100150030402c8443d541e01411740100f9010386049007030000240841803c450703252400740b8103c3e002c180140121140f1040320341c0b0406d0b5035486591982444040d1502a2004039440018040811551002e02948024145004010f0702034024810400070003054032a2060080464440401c0442d40c0021300c2600038100e8240030078142c0744c500c0801c0c442c0100201c031a9178100c0e00c4040c00304100d071304002440510000c134101c031118400b9242c01800c9a200c0d01043d030119401c60745614501d101074016210303441c080d028050509903040081032065110700c000d807403550000a48540125008404c4000b205d00e000c0051402609642d1600c0d400030455101809115900d1406032605200f000043d24948014040e0340043c28040324100300c02845d40201805030140642 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 331709676 1250 331708426 331708451
    0x3040f060c08060f0d150c030c09050406060806120c06031303031d031b07080307050a15052802071a01061101050405030a03051003050a0503030406140906070509010905150904 77
    0x1502d409800010503c10000760034600b00013800f0f00a1800f00d0740142005100c1c0301240540c806e181107464075071008941c2400d1a00700600100300380d0801445280f4201d0300348040e590001036542d100f0000d0f58400541c51a24580300e00e04400c01d01c01756400030300003080001d005411114030f4481071280e1400e00c031422015480f02c0500c11905500d001075402803100e50303a1a00c800c0c2e03140700c076031f5076280680da45551212002415544503000035035050780210b0f180340c10000398040503855407560240130001414a1000310f01c02e02c558508008190000000007564031100d40c3c1111550759208001c40b0b003401008007001c001c07503002d20842c0d02003409074078a9a980714042c09a0362080380e024001c1c518014140d50240d00500f005440800c80041103440840011005c010407a03415020320003c580f289042d10701582030365a43d0744181c10041d254810700c1354100e4001509074003c0c0b024106685c5625140300120392000a80d403040e503014003005aa00f0480b0341c028003d04442c0010345052256041070306 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 331710926 1250 331709676 331709687
    0x31509020a060527010e090f0405060610090501050d0f05090c0a0503011104030212070803030103200111300406110c0f01080112230d2c09041703040f060c 68
    0x204d2030181e803100216015040c4c511141a01e00490050600b20481920136001c291410303012030b01008540c40c241c041c0001d1080401c0320991006080f600c1d00c0c41e0022098004144a2441c03158a050180109188010098a4002103812030314408100301070302c3c0115219580e0382d50407040c0d60140b0300041c0046801c1c01c040c0505021100c0c000000c6e45040d1071907007800109402840e0501d2103000ea0f11001c181c040042c4000d6008501504003c82540135a60001602c0c1c8006103206040c4840040c40c207604000106400a0b07004c20141d901014102107440342c83c104c5003604a51141801c006000709207103810840d0b4014154070042242c484d039201c0c106000c4440f403200c5400b80459081c10040000592440304070380041c0c8104071141682c0009071a16000a481400c411600e0304145001009140c1c05551004426007602031a003e903128039044200000c401400540102e02c1680050203111484044500110384401c105a0303038075103400c00420014450350704481075420101026011071044 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 331712176 1250 331710926 331710937
    0xa09021314040c0f151206183608070501200703030b0a0509040b06030a02063405070509040501090b0a05010e0f010b0f0703090b0c01090b01081f020d0b0910050114030f01091104031509020a0605 85
    0x81604600c00c0280d031f0ac940d06d10342c00440c021a569900d41d0040146031208d082a940001d049440d046e03240c100703e10300501550051820240200d9540c4020007640c0d603031658168200e6000300086a5540310f440220b03080180c807002c06034110700e00180440d86881c00c2042a904286036824616860b0191107a048045806000280240e40000c80501041c50b00451132508a445200000b51908140e0795000602e035080303400385c4803d40d0b5540100060003900c4da103254007541c5a030400c4c010f0343c14048544060b00a601e40f00c440b03041c000c201c0b903003014041d11810b40980740d5013090340e480d0b01c0c5940206000c0d01e00f40201700c400601c0ca0000003902d20740008c0010030512401c45181742424a201d40100039048400070401582c0c80e4442e5403400c1d112000c0d00740c000c0041441031040e460800001426140520228a000d11010000c203c2c68507414604981519410703c2c01007003115440802c14054040d50700042c0004090054600850700e141d445110131505c01d60b0b206580c0360f500c0000f500c0c01d000c0c4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 331713426 1250 331712176 331712261
    0x610170f030912071211010806030d23040503060a021b030f040b031b0c0c04151212091d0a0b01080108060a09021314040c0f15120618 59
    0x521002e81d55141400740c0d5070011030810704031002c999644190301801c140d903090a4410030143d042040c075550384140490b50001058009200b40070b03070400300a21920a21044c1c41042d06295468000e507203413401118000c0400800300c80c002d081125400c8000e40c00242200014030039011404100d80307011080c2c0c0e1124041c2c42d911800e0514001ea06040380d80b00928400d1107001104407000c0b00802000079003400c113414001410b1008404003032004a0b64801c80c5480300d0702e02e20740c003000b880154400220320705900038425110b000344008151541800b40d00400c1540d800091000950350749000c1d264411001e030341e41480795502c41c44c01926102e001380910b4505811000004440804031307040900c0075480a003040c14561341c25807000e0129028411103108030b003e44001c2c8002c0c44080407942014088a20030001c01711300c0c001050a13803005100c1e01405101001c00107003107910066004800800d03103110151fa070358000c000f10728010092009061001c0e00e140700541c60b010380b96400240c81001c0d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 331714676 1250 331713426 331713433
    0xf0302060307030b030a021f02060601030513060e03070515190903080105010e0d080f09090a0608070e090f2b02011109061e0a081006050306060706020313050610170f 73
    0x100c0c120b0850141c02800c3c102509446030080110040c1c507140e49138000ea085030b0402d0b0207441000d5500a00740303280a40300b241058203140c01c5c81040d0301c1018007203900a03808400000c5c2c040041d0601c0b42180500d5601406030700610700c071460f43d82114400787d0301c03a0200218854001407003800034022a40400700203000280341c0b10040c00300754060540300440000007444081c1c547d0541d0754162080e809400a1181c9990204550a250804c0400c25802080e110818000b66003460440d82e0b44010a104916800e030300c5001084030801e05001c0050221200d80548240c14003c1c5141401810b00c565800b0030200a032030800d401c80e1040c400d0f804125064603440780790078462030030082c80381c121002900d006040c0814541503a1250380080ca245401a218800300d458070890300743c2e003403005074030502c00d0100400800c40965200400c8401c0c00d94010310060b166245c6000030349600d907401000a1503881168184012519a050414120707003580c000e0703112030351008100382e448603694030310a1780592 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 331715926 1250 331714676 331714681
    0x50408041401020a1203290f0f060d020403030504180203060907110f1b010e060f1e190c0203100e0703170c1c0f050306010c150f1d01060f03020603 65
    0x111541c01401d008144121084c1c4401d940760005005803400c4120040303a0f40b80f500c01380d542c0112a4241901c0010080400441e0900003c100c40100e060300991003800c0f105483c020a55400b001c0d50300468030760400b19125030f220315014000ea405401003900c11546103c0c25035280465008507031044601912400c002e888580c820390f400c0c186d4050a0b1403502a0f49042c9103003402c00c000300b8200e14200150301d80d00074104c9001400341500304094500ad40b0b0100588a5204407110403038402103580c1009000c4802500b10992090040c05071020003448404050f1100c6a4450182c0c0c110354003c0382900c1c000032211204904a5044c80c015001d180c001c10310030000f02c2c40e1b8041d84d00c0440d4234205c005d4644401440505c2c14681150246480c0c811003801801d021030f0f10444000e0300c1c54503030030f001d45113041c25000a42130b401340940c0200310070180e180c0c0004030316240c1c2146680e02510300050210402d2a9005540d03120140c0c2c43c50465881c14800140300e4510380250001ca90300904040c0c40c64 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 331717176 1250 331715926 331715939
    0x2030411010c03021f2c0312060f0402160311070602190f17041716090906060806010b040314010b0603130609020619030f090c092c0f060a05040804 65
    0x80b0030074040d03055004008695100326030b852000c4000c5201e9920010303070062002d1a03140c00c40c0801c0d0054560705400408440f81820000403584446201f1900c020f50f03a0b256400542051014100103401a00105402c40140703008101008401e1207034451400598000c4205542c030754042c4144001079009641c820010134000700c0a0b00802e0080d8448540707010140c4594003a40d00c0301c142038224003c001410080400c00c01c41c221440300d40a401380800003800c4500302030702e94960255400f0580d403110b04c51304120442d0300aa00504c400781c10707141070b581d41c0c030314662240e08144000e03108031810083c0161b01d240180700784c1c900000001c2000382161900e80c81300080b1014141c0443d00c0907541c2c0a05000b5a4910010b80700c0c1c48002c182d80c01040c0c840600080580304080c0c180e40c1d0b00d030b051944510000711303414403243c00c0d02e040b110001011552180c0040030190741031007500440c100000350117202e10011900403420034011040342c101d5201c0d0070500085410440f400351185005000030f010303c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 331718426 1250 331717176 331717187
    0xc25050c1f1b0c12060b09090303040213020307211d0706030b0409050307060b0d0b15040e0f070519052d15070b06040906020a08012402030f090a030c0b0408060105040203041101 78
    0x1203406178000164a5040c040071690101302a00c00010951001c4204400c601c0d0440d42085044101a420350030350901a1002e8502556240f2460151642d4011021a16044c1d8070441c1070f01c00c14031200c1100142a0700c1280c451040707000e200b0009090100b560480d0600d40070724501168001c0c0158900380e035549650300140740d05540e583c0d1100c4068000804600074900380c82c025255001080283c0f12000200030445c0c101503504031b01ea8202c0d0f12a100304200101d110001c40c2d4050340c1031150089240760344654200e49800c515407001036080d4142c50b001403202895100e4440da420348005141031800c21070841c4c05a1107008042c4001c1220400240d85199245d41002004e070000c1103503400c99842c0e10581c0c002d034003010006880000100840e00f400006081485140300d04004465580c50009441e032080b80f01c09000382000089103452034540d5001500116040500c4481c000d031910322060456100e032241e82c02d1403103007100202c0c051a040c400c80340030310b50006c0b0700c8850203148401501d5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 331719676 1250 331718426 331718459
    0x30c0210090c15090f050a0b030f0405030405100c0c0b030c07080a0e04180507151403040212070f03030f0503070e040c091a04050102060c25050c1f1b0c 67
    0x801544a042c00aa41c114040d440c124528181d1140c0d4001401c0211054021407a90f0045108600c5805c0c100030b01c00d10f01e0304603a040011002400900e644d9400c006140d80b20715270003603800c8148200000c01040c2c4c0100d070100c6562240100e80b5215940b68200c05980c00150f8002c0480c0008200c0d9000050307142c8000d21100a040c148094240340c00e0b8001002c0380d6203d08040d41c0c4010100500c001c02c48244400c1c000b605101800340010492410300500c0450b03503044000d88810000041000e40d540d1117500d000c030440910484000303030b031540050300d00c081c02440210007180943c45580513850064040d40d110790180c0d034844401c1c0742440100f2010748685040300b018880c04600100303400f1100031444440e4040b4404c0315950380e01e01000241741150040c143e000c10076042c4103210a900759582100e02c0951441c0404000f1816400c0490616100605003075002c845166054410f01030700c003240c402d03004d07d5200d2007446101c4992101c40700202050050540804140510038020520003104 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 331720926 1250 331719676 331719683
    0x22030210050d09063e0306011103090a03140d0c0203030a120b0907110c0102011401092003100f1706070305090a2906120c100c06230106030c021009 65
    0x41c07842615103400e000c41e069941103174440c45036401d6007464900c00709800e02c2102d00600d20f45e05078106103141d98113207000150540d0f0421000d00e0528100490420540314020380c000c00c10003615035a450a40a000d40507140c00303060303020303c61100d2615406891116101c540107070146103000c075580e100b01c901901515800f2107259440c18100c0c040d44401203906d102d07154545404075160b4013140752618000c20110000e04580c107041403600001c0d100701e207031411190108800b042c880c01000000281c0d0307103100610402e040d004401c0203041091101000219107903440140040c0341c503140c0e0190701e034a41210800d03d6501550116924600c650b02c21a44001d24006849046d20346540c2d103071900e8944a042c40c01c007030310040a00e000304941101182c10820480d84a87c11100d1340a0254032081e084e0700c0c05202d445106e07004071549002c1c4444400a1350301c00010012000403241c41561b00144401070407400b00f440b030010500303a0191052940c00d102e1900208000c042468022014003204001103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 331722176 1250 331720926 331720931
    0x21e13030206030a020d090c0306110a0c020d0812042a050904140f070602030409151503090309030b0c12060f060d2316030b100807050904060305030f22030210050d 72
    0x10f07101b03509140b288809a51280d5490b64190345941082c030182c0d8100c49600e456140100682c0420130340008a0060f82581941c40b42c0c103c4005040851f4030b4090056109066451482040304000d0001019607070710314024242015900304042d005065a401d0040c590403090010105000c00c0955075405802001c000445000040120f80141001d1b86540b02e034000d03a101050910260b540e034001c20054020316040c0d45d41b498a4003640f1031010f01c20302c102c0070a0640c0c695600d01490f01c24007140c0c1c0515045a003482190030451500310195000c0144074100303420100210302c0d01c0c0f525106040340a00c00900c007034100385c0c030300e2585030042503210750003d80c14422500700c0c200035000400c4940715244501c25020205418003002e000d490b052212035224000b2040b1000105402c1848550030601c246001600c0c0c205503800328004080d1034102824600c00441c07041003d10030240100400c031103400e040100d05496010110103880079020003540001d640052440091092003e00110311065002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 331723426 1250 331722176 331722187
    0x304060203180102040801020909060d0f0201110708010507051801020114190905010903020a0302070f030507151b1101021e030a03090f0f0318051918140109021e13030206030a02 78
    0x2c490881c1c0c403690024616075000700e160442454082c013010391183c0b09503460189e0315035a035581184071420703000c000d052000344c03042d400c0090001c100d03035806007600400070061810029406081900701d0041c0aa003c2500000c0840a5206010302c0c040400080a4101c064038bc1d54034002c0d002d4244480c40304000d0303554107017102040e024081c0d58400c6000742c02400d4000c1403820001e0600c0b1668202020700304800c80100001440003808104440c1d6000c00307280308101d540b0045500345558011000c4002c0c0745d510300303024802166580145a0026001c90700c19420404c200c8400d184489a2414140c10900010075014003d40183c3d031000c4c41060070f4900f00c1000d503641c60441c41480300c2900003c40c0245c0c60040c0c0022034440034045c04046841d0210040120013050030210580030304618680216a4110440300f03580250a4002d14090380c154650b0f1503590a1000390004448800000080e544030112000c000d02180d2501082460720340303281d41550244030403940054115481c00381d08000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 331724676 1250 331723426 331723471
    0x50105010e04050f1f0911060706330512070e0c040612140411150703110d0e01020316030c02040905030901030f0209180c040b030c210601050304060203 67
    0x622406056005000800c50400d810b0803803a1481e50501e89000d40d02c090001c400c4180710403803c617000146110701250803041880d04600d040c6900354401c0d0000390100d00306041004035013240d0380134004e8102c0711028102440300d2611400e02ca1180c0300c04203a44600600590038446d0801c0c41c605180c1080341c0081c0c0d42d41c004013203112000c030f600605d0240082824007640d903010303c001615104010051003101e00b0340091800356040680000d060703200012842c41a511a000d290300305144d440c010300e0302d4000c03604004d4581100036601120600408510140d01e50140c02000d00c4618183e000394100b901c5403008000c0004803110a409100721216030000503583e030701800880c9481003000d507407120024000503080d41d40c1c000d980104030340148400c00082e15080c1c80b035031422a03070a903a10400e44a103001c416851045400200ea01d40b0000300b08404028910010a0300d80c0d1191000251082641c082c214003510669250740054410800b081c0410340540145070400481d62100e00100b20f05030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 331725926 1250 331724676 331724681
    0x1b031d06070c150509010e040c2309010207050913150b030d21050f06010f0302070c0e070212040e0601270906140604260721170a02060105060904090501 67
    0x58085a90100402e4140004221060040b2042c90741e41001402d010b034920000e84000300e1000c0f0580219902e000408510344541d014000740038540000010404480e41080c1050340b10425060241c412490000341608241544511840d00000300c180000603c0c0c1d0f801600d10b510480f401c80e482c0d2200e40d01c4c200340e5800d00041500040d80c1e25491046c251422101482e4001710b20326000141c030b000100f000200380f14002c1d0360b02003000d2038400702c0c00742c9000d0150300a02500303d01500c1d00000800c04551102d440e404503004840b1502260200141c5650101d441c1c4140d00400707800880810100c0c07219401f0310800a100c60605034030f5501648986203c110306000d40e44040c0105480c0d01d000c028600750150210110740060301c92070b10b030030b080c805108001180b000030003800003180b803a40482d4800034001c0c0300203000c014032003c0d083c80200c00905004411840b05031403421181c82c162038441c5421044a05800880d006070106a02e000c007001015007041c080035401c542c40b000315900040f4280b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 331727176 1250 331725926 331725937
    0x304080a031407120305061c230604052d10150b1216090e07030e060604050609070f120e21040503061506072f011b031d06 54
    0x144540040d904004041d80501410031540c07060070041d8001003140030400007200051400d020805450301c40100e81401d01c90064007030760700c4001003507030108403420f4003403104000c101d1080481020801c0314036459050580c3d0091840e405500c0d106403802c0d100d011543c89a019a400c0d403101041500f0090030301e030300540300e20403455451000d8078121501100b418007625000403454200350300b2004c00082e130302024240c144480c3c3c0461800c40028424100da501034111841d46000500341860702801800c02c1c440610424000c0c0c900092250a01c0c1c0b10369442414014880b5046d500c03418411780e01d8500e0b12041404000c44203007828504420340c016070051404800090107200d4207080b2200700c07040c0302d03220f0105a510801c410406681e000032120340185020f4400a0301d0f01e144400128144203004008085a0034280500e00c14901218410b00000c4d081100110b0b2031f419400444080c0e004507000d01c905842408502c0110b4400c0540040d10001c008031000c004091100140d82d80d0480d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 331728426 1250 331727176 331727189
    0xf0909050c091c020307080f12030a0f020705060403020c01030b060306010807020f01020423040501030b1b16060506040f05060907180f0b0c0d0f1b02010e0907030e211b0f0304 77
    0x3c0341c00346002c504080202900030643e02019203000101001259150f18850b905545803040c08070100758411406da00c0030a80d040e40080442d903d20803450700c940c41d030608440a4001d80a86080b1142950183c0200406d210005000500d1544c4020040d207012002030800421841a00c0da0400d100109200900c081c10890300610b05000750f02680010714001c0344401030256040000410008150a54490b00000310001402281810714241c0d50b82c1d0103103924a01d0500c0210000005104040c2c0c041d0340100d009840912074600006890344c2680c0301941c416420411120000c1c001500c641e601c03803c07034010200c00e03035241c95442200c0034071480284c2118401c41c900140c4040d01d160100103d070450b000c103040140101c001010054987e101c502111450040a074003480211f81c4515540c813030070000100500c001c1e01f84401c0042c001c0420442004040c030403484c0400b2805048190429500c058513052854203900052060340d0a003e01c14140d102d04c50208810701c50395080c401741000c8e002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 331729676 1250 331728426 331728469
    0x70e07030606360e0a0e15040b04030c0506011d0a0e0d12021209010605100206101802120f011e1a180a0806272e06031505070f0909050c09 61
    0x800c22100d02c106e426940004400e03a000e00212501032580303149503580711ba001080c0ba850b603507075070405940600700c00400412a0007404c00105481282118000d990007030702985c4816035450007810f03c101c0b140c0c2c00100d680d55000070110390020340b003480c80516104420101606290400306042c0c250241a180b00f03a203651241030a0025091500303407071001003000e200409850034882c5501c2c040b00090b0013a800908400142044003a505070100d88031403c002840f0b15607850075110149081c8420f0003641410300c494a640b603090128051500280d4903070400510040150803501c0b0700c280d0019000a02d00440710250a100b0381d103031201d800051020320050b0005160030b64062045d0301d00786065555038202c11600d0200700c140015882c40c011149250620078004e0402c800600d1010307054005620340c14680c0102c00c018801040100292100c1d40611068440d000c0c1580c03280900c0e4141400151034050400158590380c00058001c0f400c415070515040e56000820307020034001d400003c3c40340 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 331730926 1250 331729676 331729681
    0x509120102030619030c060807030b0a0305160501091805090a020d08070c050a06080106051b061f0b040b0702012118051005090c0d060e060405070e07030606360e 71
    0x2e0031107a0b10303024400d003540320742c4440c00e6a446c002600018000e100403c656600041d210038080d5001001418000707003000c2490781c0d01c2ca0300641d120f81c07810700ca0078240814040050954007648660341500e40c1d044d00f05411520b07030003004001b808010034900d83e61207400d4038500981c560289600710b080c041d002c159981d50040c00c00342901c1e007142e40450300407a61007908100c1e441d071010711141960f449180855440701200b2041d4200003291020001c54010740c0140521540000020500015402c5006e41c0c0700740d441000c00321a000d248500110303500b040000000561140038416121000421022280002030401c02e045492454522806045102a540c1800010406144c00001d0070506100a04e40302c83c110b922105511161030203403201da400d10b4100f140f580c20424110550800301d9400e40f505080c8559140c005104415001380e0b10008601c3da103109005a00030b441d11030b11401a21039042500c442151701001c0d0b810503100c002c110304250b501c044818003004100b0ba0f070b2420500e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 331732176 1250 331730926 331730929
    0x4090b012603090f190608160c110603070c06020a05090f040b0d1e0b0c07021906230d0e0f0609070f031101020120030f010b030906150105091201020306 67
    0x110041c0660151403650354a010140c040000c101c2c0d01c2c0d4002564112440038000001c00d0550440001543c081c65144a001c1011944500c00c581b06841c90364414081035074140c02130b1604540040c0161800c42c1c1294552043e04062009640000551501107469006074440104a811503e21080000d90004403034125180699140400e91000c690801c107030141d190010f26225108400280220800f040041c14140b03900f15140f0103903007051074480c461500f03545900b0f0303d40c032000080703204041440c0400700a8250404220990b52642c64084964a6480207000c1ca2480a0704583e07800004004030320201c400c7d801208640941c042c001d102130032404034517509069001b010711039039501405080000b031100c00304d100d044a41180303003e120001c51100407400b424010f0a070300030022078406424200402e510045212300c00c00d02500e01242d0326040480c07c180700580b40c69040340d128101142b0380d140651000496407105040c0603280c5040d041c04101d03240c50001003210103075808000c000f04c030b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 331733426 1250 331732176 331732199
    0x14010608010b0a0e0118030c0f080a0305030c0702040603060614030114070f140d0207033b0f040e160602011103011208030405070b07150b04050c0405120a0204090b01 73
    0x252256040c029803541c1807184419080c0540c100507070030050781244000c643d034016081c295001c8034100e11a9500b540740e0402c070440d83d21078842d076007810311940400150400041511401542e2560b6114915141e0100303810140c0c04c50f02090344d0007903548400000140780d51080b0801400204c520a4040000300c2c105030840b070141250300d180340f122030201304c60190300c4400629111161309209250002c440401d96050244035070742003240d44002185400e040e08411040b00e510342a01c2540400001040061510b41c1c890503030044501500358003890300d241051408958050240c00051000078141d03070395251025092101541e000300c03501c1448150360a0080e52410441c0343c009510710351405090001d07013400141d0103007001902001140030000c0c02d2240d82c00500f40043d0031500d0b00d80c01d040c603080800701c021715080c00600e4003400c080c0d0760034240296172190b141f003c1010b0615160505004070b18a00540c0c01480303024081c4402c00690f84d07032152440c180e001d54040c8100790305000a000c407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 331734676 1250 331733426 331733429
    0x130f030f0b09011a1009081b030f01020703051b0118140f0109023a060209040f0902090a0b03030714060720060a0f061203080601030c09030503040512120406031401 72
    0x8040c1d041200051051300742c01100505180251442c100c4038590300001c54855035160071807031442c054400301e10042c3d145540d12090844040b02511000141c0301c81d000d00f01e1041c2c81008020079401c4c48040901c0b8021071894011920043c00032811098a0a02d48021704000404445846180760030003c0d8150801c400505100010700810040c095900029111031101d01072030768071400800800305027607484071160250b078124840080804201e1822202039041062180e028514101e00d0000b148424010300084540242805405031511071402002d408504969a00340c03004110510018411900001e02c00c0c840202a001c5070800360320007810308641401c01c000c00c0e01050300c20403841d13030b0201c3c0290b08080200c1c40001c01694000080c400b902065014040d02c0602180420a05801c048814414a000d0740c5c20468040000380580f61007903036000240c07096100307210500103414072035549140807500c034040b90380c00d038100903c416444e1700030703001000007940b5884c2c80c020034011a52010b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 331735926 1250 331734676 331734691
    0xf030c0c080a0b0f04020616030206010503120301062309060a0503090606030d020615032103191107080d0f02161e08070b0402150301080c01091205070605130f030f0b 73
    0x20b50080340d845110a202020f03140c10340c00031150010034110750300c01040760400001035143e80402d00041c100a51202c0c004d124080c06406100c1001810390807500407a1306036486516021113205051880e81e075010b410510714401490200700d81c160564a10b00502500d0080d591120303900d19105181c64203006014103880d001c7d0380f14a556618158010401c0ca6005076050401c40b080c6040034000f0b8a040348a90804140454090b0319024002e01a001140302d0b41c940e14010b019200310204020848800d01d20b02e103046503060003c41c0010f280000282200d01c406c010118440e0340600c40707a000c907400030000d440004c40100140040100f40714083d0943c040f0040310181c03a104c1078403442c0a03849045001800e021301c0200043c1107507100300c01000d032440043d05403034030303583c5600d811655005458441c5000c2884030500007030310354020802a0400750302c41b025000c11850b0203001d80d060b81001c04680100700243d0780c013155901d00021003400940c0a0018451030f5203060030000c040140144c40130 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 331737176 1250 331735926 331735933
    0x2040906050d0503040b03100312121d070605311a0702060f0a020102071209090605060309070303030b060f1201140612070807020f0105040501060509130b0a0213030f030c0c08 77
    0xc2c0c021a0002c020341d4200c8001c100d046030340703039542000b0300041c00c41c542005060f0340440f0880881c01d940815051150139403040108483e008614030503980c1c1c11501c0c0c4d4544290720841050000a104002a084800049200070104210300c1c180c1003410090842c4410580803100c01080321006098084000400f004001071820740c2c540c010030078920510000702e07118140014030000642c0300358120717070744180c0140b10440e00a2040790001d08601c1d8070b21443c06018140000810b03245410400c50340642c141e0320040c0421440c4d07a9081e0054102081c4907680440c00380300841e54403508100030180444d10b001c4070a815814819860403121600c0c2c81e55010b41003d00003400b5900302031303400ad500820941040d8842e59104c060483c5400034200020141d9420039061104208054000c0d40650303408490304000c583d10102c0f60900c80e106401f02420000700344010842442e1158024020315042d0228841a00d40b02d4581e1000c541e03c0d500e08800080450009005112104070020003425105014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 331738426 1250 331737176 331737199
    0x70c03291b1303080a2f060406050a090206070f0c0e0103020303121515030105131e09030e06040803090a050102010204180b040b040e0f010c030504021c0203120d0204090605 76
    0xc4680503000d0080015aa410014000641c02e4804000300c0c0150fa008441c181d4422110740000c14240303482d00c0405c040c000d26450440d42c13003840300c001c40207030000d03100801c0c813642c43e07850300e502500c40036151300003c681d540b21b04400768072400003c003482401440354080e07202551a040106080550096140800c0c00d0011310040e50b0100c100c032500c00b81c0c0d8440c02d40342c0d107925000154541e00c0b103051030790211780c2c0c0500300c64a1001d0b41c00f0310f040b00d0381203400394007072900704403070600351200307000c00b110500e1454210000f041c0a036405000154085e141610900c0c011b400421f9460f400754001c28215800420108211300d01100000003403e400e1009600303142c9412845403200d10301880b490790460311080c410b05242c4844d409403088500040c400d11080d59005051a250745101010300103550a2802c24100c4034003e01602d4051980900100c1103d224400b2004100c080079600301ea04d8000d4120349074851400b94080c021624841c04011790b26454100c100084508a074415405018600303203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 331739676 1250 331738426 331738441
    0x6062818050f09151f0306082b170406020304140d140903010b040c030605090106030b060d020306040e0a210201110406050c0a05030c01020405090a140c0c0102070c0329 74
    0x8288010b1001620340d0301482c0c85074a040041010001e41160300501d4210024404258601c859020710001d0b0300e0801120744c079841c403541c944019142c1c4151400002c04442d02c0d0f1403001608042d000c01601d020030300303c0d907500791800d2041c00580e025034456401001b0310003400356403100584408000c1c4000c8c0520804030901508141e510010b2016018001c201450542c500b0f40045240c2c6000400800008020b070720040c006003002e004080c000c2b007042c0004070b5924001d114041003020b005180030b04003401d0072202c002035400104070766040b039218441d583e4050020041850510321401810003a0342e00b820101e000c8480c49540b0f001168100344408212034442c40440c0c00b511080c1c600390b0341c0d610621134030b1890903104400050442c40000750108a82d00198007810642d00211000c1410340c44119081c82504d0110701004c0f00034121034081849450071000420100540800240c1050495115a9039101c825801520705d040d14800c000102080e50699010a5191840b4034050b8100400d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 331740926 1250 331739676 331739689
    0x605190305040f140705090f0f090304080c0904031b060c021c0c06050c0405030f010b0f041e05042405060f0109290d1d0d050c0a0602030606281805 65
    0x140190004c2044502000d07608418401000a410042c1c120a001e0400d20403071030301601d007250219040e440960115845180100c120b030201c0d8070100003041c20040103820442c12003c043c00443c1809864105003446608001c0d10100150094000091000d041e020190a008162140c0d0140e40210342c8151103494001000d80b032a40c0e0400e000041d1952004040401c0d485940c10085d4184038424440586440540001c440b0780ba080d240c10902c14500c0d001c0c0019100c091b04404180c402017580c0d00420001540425442030007004030f9080261103407203012100b10084142080c1582f01c8041003a14140700d120140d4140003842c28555403441d024985071310060f0b41c80415000720300c16054281c6c0c407080805455410303207200810428495a40e8a004e00c4c0004805040c07940c4c002d460190406601139025101c0100354000079012425650baa020000c1d8001090075074842c0c411700040c0406440d44e01c01101207041400d0004072050b04560180005d400034820304040000e0b05014059501d410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 331742176 1250 331740926 331740953
    0x1b0901050604030807050114090708240708072307020103050c16080703030905100b011b0c0603110706020a08071107060507030c061d07090e03031003080703021204060519030504 78
    0x2400164a4500303510704140074010723180c1d10302c0c0944003a2044c000d95a001042c00411204c0c8102200c16024104950035145504681107121790707a00c0100040015004e8110240d01102520701041404100d10502c041524035101800d03a1040120b592021035030940700e0365030880001d070011824820702ca401002003d0250900a20f082070100d40d036410140a90042c3c03190f95070050980b51307010088907028004140350b02150340001d02151511600c20600d440c00309142e50403d11610a190a0070019006044c8900081520b0b180802001011a61910262503048400e6071030380400c3c00c140f0401000c03240c0072082070b810b030b41000c8000c026154014017264a000d9040c20030115401103410150700500103140c0c403002d21881c0700c600080c9000701040b03241c02e840703000c2800c00001d45c965503219070f2030104031080c225900c0b08020601c040758004020f804490b1081c4112070900514919013003068001d6402072010a0001c110b80d100c03201c0e4446615000101c030320f400c01c014a803540b248007012051 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 331743426 1250 331742176 331742183
    0xf0b070c15020312010b09090105061305190b0c0102040905010501050a0806040504020a09050a09120e0a050603100b040801021e07030806010806130c110c010206070807121d1b090105060403 83
    0x81e800007181450090058901020019280c8980c81d0713502c141ca00925801600c00380e100d40c26690000c1018901042542d12a2200302c1d1090f04960810381440710f103590101c680d01821021001c0020500f040c03100502a00181d18005610b892030f0110060590304180c1110381404030501c41c110205500c0500d50b030f0b00440844020500780c0301c60003c01c506410f1034014407102d40c00e00040141c1d480d0980c00071004240300d071300c124001d9002200110307500c00c2164200740e803184410340104018900b500280d50400c01501c1d0140712141e03101000040b6500540c41203480340d4020030103c40d4000d0110350645c1d10320940c24150f11703103501941c1c01007018800408c80b0781804810b40225440d500d5101c0050484003c030b030410010395100b14006060082031b80402900c600c03c0684000e003035403010500f07900078151511703069410344800e00162040f441c141070104c00941d40300e030500100400442410710b090f940e0000382084003e000050b20480e006055a40e0051051100400032602d40f0300440b0b007207070f40 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 331744676 1250 331743426 331743449
    0xf0715050405031018140303150a08100f0f02160507060503100e070c02090a02090a050418080703110615040f0e030319020c0a03030617010c0c0204091b030605010f0b070c 75
    0x140d400c40e80c0d2146a201202500c422664010801e85010007c000c0d40150031340040302c40903046500402403059020700440940341c002c048854914030f242e4028401d41c0386480b0000c2101856040100220313048400d00c00900d900007074450041c0311003400f56070082d010900c1c1080c44c5140200d4098680700481c840c1001140c08403000501e5184240801a030035079009040300071508060305410040e4001c0c03100203104500b000d4000501b444d16120f80344039810200c1103682012055260207040d074011040c02d405203d00e00d245d204880200b0701c8541e00c5036449000c0c407180c48580314103200032507440f1140174401d07500d00b160300501c0d40800001c2c0d9600032002925060102c8030702000002034016200e9100552245800c44c004041e01504600f0a5070144140c2d00d085100e030142c200d00760303010a803000001c00c2d840071441d805401c00e90080d501544c00b4942c180ca0030810302c0200c500d103c18503030050380d0560345c0304014828080c0301d5803204002e1400c040e80a003449181e80310540c0113580c47c072a52401a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 331745926 1250 331744676 331744691
    0x41a130626060319080306100c050703032003130e07030e06040b0a0603080408030306190612150e07030e0d020109030e0d030216030804080106050913021009080f07150504050310 78
    0x9904110085490b044c20b4507002c10441c952528070314507041541c007144901e085584410030300d44120f104c10500c680010007070115500c1e54a0690362a80e00701a00000310502d0120131502d020104000c201301c2ca04d04482038481868005020604200030303000804041c2441a404640e600c000355140e001a00080f00080d15110303c0064401410144e0000b82220808540050a0304001c409503202e403074161403c03084100d4401d03d4040361007550080001040079900020b203410031582c000e641c10440070910508040d200c0c400c2c90500d03d0200d62080000345ca80041c0b410100090081015070f020b240020300082102d80e0f8050900c00d04805028022a1840030507001d040c420446611040c004080310307000c01b901ca04001c1103c1d41321b4064a4099030030440c00241c1c5050000000f40300c4c90040c8102828011598200101c201d007610368402008098000402c240c142032005107600088540104202480d2504141114038900d503a0000d110701030004000079100451180342c41d0140040000300e07035 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 331747176 1250 331745926 331745929
    0x60e040206071403190908070806100b070303090602030c0304150612020105030a0207021c0516060e0103180b07030e0f030306090601230d020705160f1a041a13062606 73
    0x5004801c0601490b0400c031043d0541c0c07a801401046c1602d01150980c0d500f00d1303d412490740c4c0c4820a1328514200d04005000b080035001c5032014012180c402e02d000320781010251074410590300f041e18403402c0319000000b4003080010080880755070707030f40300d070300c284091880d01c91004905545204068113109001001034a00d403199811078100560013413941d10030035039041400e040844000d60841d151f120b46102c081c01d503080c09100c041141e00690740c0b6081c441c2008011000703032009000da13002c0c00320806441d03c0014024100365100703805656000800580e800304540c9040308000c0c03500f5850308104144100c648800c030995912250030708004c1100785441703601c031020000d8401c500800388004155458210a41c0d0000d014440c00350044406491001d00300390300c818003c1c401c0d502c1d07185401108020300a0901c003506440206d1070f2503181000c4d5946130160680b11038041032826030200140c040030340b00a80219101078441c0f468006403400e9404d6091021a080500c20b1681e01280340000e00796 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 331748426 1250 331747176 331747183
    0x60f09040f06030c06120e0a02101e050d0f02040806040f02060c03031e010905060306040b0703020405061c0e1501030f0204090f060507090501050921070308160501060e0402060714 79
    0x41803800c076420065980c0d2800d003043d140845014040000d15491440300803040140a81030202030007401900c82805180c0c2000084c0d983c002d040d00034490860002c03001d0888a00360400181c17225203502e9a10041c0e003200c8030454101da10040f09091040c0007d002c1c0c032100254066209030300c6403c0d04000c3c856400010082e015241e41180f562200204210354000c039104c1210540ca4201c00100250740c80700406016150129015501540404002400701d00030351400354003c8482c4c200180b0740354403140410540d074030080f803c0c2c5c001d002051120b6031400083c03041000703002010380508070300c54a254046071070000610002d03001c1c240021003403065650b2540101101030340110601201c000c10328044003c1d00d0125102400710740d00ca4030004280d40660102e039410a001001400c50807070b4581845070701d4140702c02824161081200100008013080000c1c0b04205c3d0300740d07031388800030241d00d402030940724550082c207100d0520005010050321048103850105900004c0015014002281c0c20315 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 331749676 1250 331748426 331748441
    0x9090c0903050604050307030921020409030e1503042907180909140709050705090d060e0303040b0a051023010c0209101403030c0712051c0519020c060f0904 69
    0x920f0103004288420000008000e082c0300e0301c65240e01c2e1006a507410900440c40e101820304c0b507003100c4c284009006182961041d9041c038440e0030130400201e4814003050a0800c0080385d091100400002d220a2158110014403c404002072003000d1170700000307015100c40800790803101800501103529420b104200d0129000e4802c4c82ca0821442c000c9041c0b0440c142d02c45444002c00c4e01904002042080860040500c0b440d080d840e01e42c40e01c180070082c006840894031042e61100e640e409522500c403401d000842c0100d0041a41d0071450a000c00079034119280130b0100440d02c00007450400040c1c0d00b641000407940d1030100022070060881c801038440d2803080500075480740c540410840303881c03804000e10041e0f49460083c01905048c0030b0078180c1d280f182c442111081e600803001049112a16142c1035071191164080c2c5c4c0640c1c00c91115023845018205e43d03807012400102d0340c80a040301c190460f4801c01c510344024a910441c00700420070a00c41d40e10021440300000420200d19280c9412444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 331750926 1250 331749676 331749683
    0x114090d020a02010c15020a031e0501060e01051b030c0a05061005090105130b040905160803120604050613090b070e031c1d0a0306020702010f1103040630060f0f0609090c0903 77
    0x10340d0340d80701d040010020500c0c90034220760901c0480c0316800040cae440c480c00c0c2c10395800d91150f40b08a50a0b900559094100002a6440000403411221000028009000046503040040502012030f25009013442c0d40145007000b0914600700810203940c40c0018941102e03c00e807001c000503500c0101c80d601821200612680060600e45040200071001034042d070750302c000f2000400d1154441c0b41e81e0341c0b00e20541904008900480e4086907551a02d40c0c407242c0c011b01c00800001540140150010640312100c200344c95072003452040000190300311410314030740002100500305107103030203801c0b0804400d1450134004004216001c0074400c0c0c1901c40410650b1401420552415136a1034540042e6000b02c2c3d00320700044001100e00d2456000e09040000e02841c100603505050030b100c0102c4403d21504040c0380d46a96040e54040804c1c200c10400b40f90180341c0c040070a81500304a80303614149029846400c00c1c501c4140c00300b05c3d1940c0402d10b802070b621404408039014981c0781080312518103e40014 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 331752176 1250 331750926 331750931
    0x20307110d0207080105010f0e04120306030c0b0702040f051311192d05030d0e01050f0d0f20070609140601080d080105150f0d0e0f0114090d020a02010c15 68
    0x1c6600300e8000070a94200c4400400034003450703032140320441d1704e00030510443d1051211080403900064030503c040381e001095180006011b0341d242c8580101c1d6a0940c031030503440000003046020f50500e805100e46001c5408800c0c8010305110b4881340081c800040007a00380c800f1000f6a03040b81d5150744480e220014081c110b070340746035124940440410b04182032201040180c1f0101840c3c0b40f9400420005c0740c1d4001c0240071440d401c008203440280b10200d0681c10400c2c10481040502e001e00c01806055030042c00c00101100c21203002812503440505103081084903c00506a005a1000720303031013103038000c4d0045140308261502403030841404401c90498080c0c0c000224002c1c1c000100d048074402c499681489a903a5a010300060326101e928868445c2070070012000429080001001c219000c0f070310008542662424250030000440c00f902c4469440c4ca40c0c20456481212070030741c01c800148080d124403030070020042c0d40c40c80d5a000c000d040c068030168442c02d0100d00c00d800d50324103613000c0c400d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 331753426 1250 331752176 331752193
    0x100305060f28050d020904141204060507020102100501030b130c050301020a02031312020307030605060105070507241137050105041205070c0e0c09040603110a080303090303010902030711 82
    0x280304501c911003070740015402d42180009840d10341400300c5828590041c0c000a0580c9031030300c4000c00030b4a00d0541080b64851940480c41040e06900100300411056036103a44070211403000a092080800000c00081d04200062020800030ba00b4160009084882e00250700c1c02c0d4609110040c8aa82c8000d40c554400703c3c4e00351003250044001d0041c10381412540080c280c40e0740303058400002944000e501580000300078000102070b03034800754101c0300505156082200c65510030b0f14000e01a04480b000c40c0d00390143e042c503521070001d445c0d4814818144590600500c1d02019540d00510050b44240303212030314000511340b02c9060070004486c0402085c02e401e450707820854040c04055404642410514619403510340c466419038889a40c4420300c240520f01c2d1204c074040d440c102038002d81d44520100700d00c04a07a84c03075100d0540154464002090101940000c00140480503803204443d81c20400411040741000300c00c81c0e064071707402500141c881d101d200c02110074041844420145104981c42c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 331754676 1250 331753426 331753459
    0x90c02120d06090b0d03020d03020a0c0b070f030501050607080702060f040f0803030906060609131a1002150112080d0c050702060d1a01030c0215040524010305100b100305060f 77
    0x842c0641e03100c154140300200c0c1000c284540030550b6034020f001078001c44024604148660010044401d951400c0c0d0300d1401c1c2c584030851120300540e50000803a03841c5500d0416190180905801058116481401d00c501d540781c02199104011000317118400c002800d6800c045d0107401d80e00030301842c20840030295101d001c82a0340e80d00c107880d007803201d01c100c000083c414500340c001c0b50385810002e020b0142074480c10b020f9902502e1190401c0e003041c000126011083d846840c085154060541d004054034107070402010300009040e0001c00d07908084481d030301d010610b40300c1103c4041504920000d0907041c01c90040741d95004940000790301c407900041c004d00e03030fa54503000348030f4090b100800c5111002500b0015000c451041e0071300c0015030072450f040700050403110880c0d980640100107403408580485015401070502d544148180b185000050040c88810000c02d0a0141d00350780070004440440b0005548001080001c410503840c4d600081003500d0b0018020403810300940b9a09020780030340c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 331755926 1250 331754676 331754681
    0x1e02070c061106011833091a012708030f09010f08060319150204060917060903160614090c01030e1f02030c1306020a0c0602030a0207090c02120d 64
    0x401c8100181030810000300070380700070442a040701c80e09080c503450303c412040c900010302003121005070003d40b406040314001030284910100c04010061004406041600d014100e035500c0d03070211102922030b104041c050740c0016852034400407020001d01e007035101500c2c03103804840300d40000c9420700000c10126041640318000e0030602c130090729004400c00c103c4608403040e5100301d8450703505920541b031049100e452200c1d150191800368100c0000104800560f00503a441a400000003418580c020840c03e0006d001c1405072800010140005080c0f6920f00e564034000c803099031341e440c13080c0c6140d1000c02040790304c05c1c04c6025001c0803181c15480c1030829684c490710310780d190502290800c80d040c8101000400d030003c402d0750328070400808240d0544000007c0d00000e00d4640307180020006003940307041d126081030003803585500800b0741e01b2a51800010480040c1d005c1010b41d03000b400b98030061500850400c0070b9401c104030002da070309036801080b440e12030803000488440000080003038504c84180c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 331757176 1250 331755926 331755929
    0xb0f07021c050a1403070c031e02041103060406050102030a020a1212090c060206060a0303020304030f11120703170c0c0f01031d0c040c08010605121504020a0201020c070e06010c061e02070c 83
    0x2070f0342d4420300c80c80c1350050300d44a202e00d500090006d08405410300000b08128140100d65415046a28007e09694080f40403140000c040200c12030000c81045a2880c080c0503d50103440d003840035505044280c58040e54404d50920028142200c51064084c5144504000c0e00801d01000b024000ca00c424181041c0102c40c501407000140240000580b4500b072500540c41120341c0355004616062031500c451107902c5910000300c1d501c8078001c210070026550080401e1070700e40d400026011141c9503152941c0404450284400031a00600c04c00c0700712203020804078550403040d1000254007007070b500101c0c000c100032190200040031400d0513505e803100c00030b002c05c50b180083c0c4040000b03445049050f91b41440034030a01001a00070881808419000e1008a410000441e2066800d80d00d100005e030070b80c1c22016103000140c0d40880c9844002c04100034210003414102c2c41800c1c0b90815000007805000c4180c40030b4403507521218000d0380301c0105400300c0042450341101715141d94941c5010703000300505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 331758426 1250 331757176 331757183
    0x80702041d07060e1806030304080307030f020d08160e030f030415020c030a120c03030b04090b04020103150f0b220602030a11010b1011010902040f06051201060b0f07021c050a 77
    0x1405004114580261110a1310800c01848841c0d24501d114002d01404001020107416000a10000410307100800140c81a18402c1d20f45c66030401104800900e009013034080c1170304000f0003200740880701c09045510f03031014403103160030007120104d4000301e840c10a01e2852050320b071100080003e000c405644041e0079080b62507096408101800c0b04142c0d03103200a00029203040c04c00381441a030b5074020315041040d113100e82008224280070300d002500711002c080d0b0503140d140714402000115030345031290280250700024a005001d00b003c0703404000310514020b69007c80e90000741592000780e07450b44c050300b0280f000c51080806032030301c500030744a400008564000c43c4094601100e81101801000c50012019001400101c071100089580c6480d500d10214555a9002e807200503841c2e6020342c003d1284101e802040e5039140105100003400d08507520b0300540d03d01030b01404205010b0003218030102d081014140c440c0c419000060620303e01143c5000581018031840c000c0000100f0400c1c1c1c40da01 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 331759676 1250 331758426 331758433
    0xa090e2221030209090105271603060501031b050310030209181e06190f0e011b170105150f1c0c030b010c0210050919050f010905060d0504080702041d 66
    0x20818002c1d410790281204d101e5102034007100502c120300300310000d4640d6040c0030740c03982491030094a0001c1c014170251603541820242094296059402d4011744e0000e01082c80c0400c80424840c0586003110f82140414003044030000200d071585001d05004405540c0080c0900ba107410701c084613260040a42c44015014001c41700c0002c507041c1d140e03141c40070428400002d0205991b5028031a0700407250700145069982d0b683c02d050103081c0c024403502100024110001400403141484844110f50480310141000311114519000c210003090a40c110b0700d064518800610704a07501006034083e43c071304003441c00c501241c84e0800701ea0156000e401004c540204002170501640c04a060705c00f95094940807030502c000600060401100e9641841110301d0407070b040403505000501480d15140580d5100420350034140605c0ca0102340c51045c80c6002d0078400445454900410614000c011400301910780c0c4000140501c0201012114202c0d8002d00404c1072449a1040c0c1014191088140000780b1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 331760926 1250 331759676 331759733
    0xc0204050c030c040b031f1403060906070f030f0f090302030d0608070608010e070c06051003030207240f170a05010801180b0a0f060b03010620030a090e22 68
    0x1007074012a40100c2400c0c0790b103480c00341095100840c40e030001d042c4101c0208407042030522042c0320100070018181d0600c080c801040150105480d040000e410008503030040800e000a564008140500c580e81e24107010655100c2c0202c28801071a8904411040038103201444c010142d0120041400307103109041000b1480d250308400f079030f454042c0102004100071100600c100c010703420209610044624002848d016569601c00c180e8600707582c0791121360a110424010160188050405490790328405007400201c01c032152400c02c035440d120f41c01c3c13220400941246620801d4076100442094900c18a5400c1405240004150900c5414030310b529006450000700d41152241e01800d420086104007506e40c00f03960802009890b940616141c2c0d03505000030f03500f6103600618001c00035910303010203081142c060340070a06801d580c0c05d0b82c107400820085101981004100c1d098030f0108240c10a140e0780c2849030882a80440d1428808900c202045020040368071003909080c1b409001e21015078 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 331762176 1250 331760926 331760941
    0x20307030b15040806060f060d09081801031401210503040f0611060415050a021e030601021e0d1805040f0c09080706080402040506010c1401020403030801050901030b0412031b0c020405 81
    0x43c059401110519005000810f84920f042c203458800308000800c81e914003241062a8022500c5600040700c403000041842000d1100410207103812150a0a05110001444040c007000032014002c07a040c40c0d080820703807031002ea40b0010310620300340e000e001c5039503640e201c010310061980e41e03100307140006443d9000d100c5411004500c15004a078026101c40560030421510b9002e8400113140d001d883d03509010028040b1284020b400710824000099235690802c4c00009040070302e02440383d084d561002030000c1c0c1000c00099034040030b0340c841c50080039180513402e411040603060382c0042d912500708001d07101c64205981c0164100041a2288005555103100c08d40d00d80b1303014403c1e8408030f16a08005000b40c00e254005552080d41450496250030b003a03500d1080750140d5540c014203c0e90301060900c105500304040b1409400100d075204410741c550303942c0c00a51400108001d0029075a0b00e580d00700c29000b03421030b007508925140d1012001c1c11802c0010b1801580d41d40583c403482c2801d0105000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 331763426 1250 331762176 331762219
    0x3050603100c0807110c04090609020a0e22020a0905070806041a030c011808060709030507060e09130201090513140c070809010f051c091103011b0f020709020307030b 73
    0x2102454490b42c005503100c813001e9820b481c6141020304e190042ca00042407642c2d4501c1414507a0388510b074005808600d50042c01980a115003152896403004418443c1010844181400c0300035041c10f00b02c0d6a10091002c038070041c4071580070032006402d000a00200a030003001c283e1044c6410358040004012a060510241668100c041d806030428140300000d5445100c190306008404413404040075030304d1110f10b140007000c4420f400042c4002034280100070090086400074503046c1b92641a40c651a4002442400c01500404412109144401c01c59018458100080100424504040e4071101d201e401034000280f80580c0341074a8070010300c0018400050ba400550007620f075a091842e00783c01510403582c4244000284041402084800b511125009403070822081000c80c801c0800c0c0382622001c0000f0140b244240d05040303000d500314802c6a903a26120440780742c44006006c032410142d00f03044a6400c05800c50380000104030b1044c2e05600440c00c5000d003924207080d8560b008001102 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 331764676 1250 331763426 331763441
    0x8060603070f050118080709020408070e04030503060f03190506070e120309061e03101a071a060103060b0f030105030606090705030406020a11031210050a050d0204020d0b100305060310 81
    0x20402c000700c081c00254032440360501c10684040450850035110031105140c514160b018070215600010244800c3c02d0a0081c0340082c071441f1103903551400e0560b00a04030380801800d40d401446001d0703a1554541d0208071140400c0c070040d1001c0c20340c5205040c01c0e5210300f0704036101404240440e10040d00c40c107203120035004004018000c1c46c1426000420440310794001180c0406036459000c00082c00c1411000641c014000210208141d6141401da00ca02803c0d000054070a40e005102034004502d500903512460f075500100b402003076a030100140c005050782e4114004402c1d002c030f041032040380840000c60680f103007241100c1481d075401d410071a140400303d603082e000801c2800070400040e01034011740400140c3e410803074074600903040b0262031900082d07103000758000c02500b4003001c03200c035000c4032018203029241c035591a424807001c1a07550400d200d00074082c9030f0001ea40c0d03022800d107900010134500c00901d140c0c030903044990028042d00c07080d10302521a006102c2c90a0070030f2514818241c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 331765926 1250 331764676 331764689
    0x130e010b040f1703190f18050d03140c07031a010504020c0a031824031d030714012004060f03180f0c32030d0e09130605040c0806060307 60
    0xb600c40d4102a02465007000000c800c0c07410303110034480541121440095048a00f0300c0d0380d034401017903d081d007004101440d00f04503004090300d0010184000c0d1903031021300201640604080307003030744840300050616108850f0054450300a1210200810180304920101015440316440303c0e40d8a40b82004102d1003229080000c80c2d00c0302d51200d00103802840d01c0aa010002021790403084e54420f01c80400c80ba43c001030111401425059548154040c81030364007410384681c41c2514078100111f02c6c0e950748200e803c01350501c0b00c0c6080110308a9000d400c50070880305251140300811000140d01000780e04140188004559100a1010668401d224040c4a15540030002440e541d19846034021130b0712110003964810020310001c100381001940c990f81e0b4070f40443c8001f961014544158050f132810410251181d0020711b03c0c2c404c10b651004c1401c4409408580c02c4155480300300090038078807801c3c04000c0685040030108020b100b920484030701151400f03816950541d07101010151520542d00461 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 331767176 1250 331765926 331765949
    0x403110609061c020d0203070302031909080f1b0f0c0306151503070c0506040507080f0c030616020304090608030304060b061908061504140f0d121202040902130e010b04 74
    0x510702c03401d882501600040c3c2c00d1006140542c5040610140d9104a94030350200c2c0d000014012070f254402c8140c8982003e612040040d1199a61004194410f10074002c64083e004241e441035145090400a4603140290440d91504411645152110215900184280a81000190440c0c0c4004804103404001880f0301a180e03202c0340380042c00d40002c0c0c411030403c4501d200c0700e40043c00401516019a01500007050071511380068140f03400c0300300d03140c100e040d0041040e440940c0c0700000ca49030030900714175403000000b0350900d00705d180d4001c950015400c581800303400a49400080000d5004a0081a041c0f04042e140018050584103e4480d848241c4555481551492040c0e0003580c01800061500701d89000300084040a030300190030011003030940c00d442e29001c4c58240501400030701d081e110f42800c0b03c2c4948580b02445c8100000c4024006c20100703050441142c0d90444016140d01d000440d21024001c0e2541140c8505000315140d500d00c4c00d001050321070304002a03400302c400d141d0380d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 331768426 1250 331767176 331767187
    0x7030c02032b0b030102070c090608070513050612030f070302120301061d03031611090a11070b04210810050a0f1a0408150403170f0f04050709060b040311060906 71
    0x800c44a40911040c2c040110742d030b10410a4950703028001007892600400c0401891410208200f0031151154041c0740d030b40e0300251041200e80c4484143c090f05d040c003518000744a6079006c000c00c0705411003424941d031034000051240c01003580c100140214038041c2d42102d8ac20b219009692103640310070700903417010a8030010868110044a801800700d401c001d0306407410070348a611001907410301c001c8110350124203200340030114101a13240b50390041103c801804110441111060b00d03100f0031501800054401d00010103200003030090b211000b0029890318082108000002c1c240c0c5425256501d180840c040c00091518080c00704078161241d040e0301c008054a040410103002481d030383d00314080481440000749000c5d01740b118441411041e07003106000c0ca41b41c6070091410110301c1486804032500c4060000c0e05580c00403260f40325903200f030342440320344a500b852842c0161981c0402c01e041d0a10380c0204515160740d002d4000c40340f280f045801a0149039003000b08601030402c00c00d420910070300c003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 331769676 1250 331768426 331768477
    0xf16080612010b06030a020c060a020f1c0b0303120105040506030f10020c07120809010f1106040f0302010b101d120c041104030501022d0703020c060d0f050f07030c0203 74
    0x9040410000000080d85043e80d80120f00d003500203c031102143e0303a0201b84842c1c0710300c0a0111941c04030769003804500d0101e04c6842031000c2c0c00350503030603d1000a9041200700d4070300c1550020203c040003d049070b898142c07200c0c122021003c240600d90103181801e011030403608001640c0c0c0c00c0c05400d01d025000d0a8480402003000b90880050100b0a100e8441c001651821440211444a014400e00e60351014994009007052544040c1c000400c4207000000c00031000204400390059442540405018200e040813405008141c50341c43c0c0c0701c00041e9800c803200b03130410079000c81d4540201612200075555800c10000400c000c481101c03030f4200d40809401450164000c01d03403510701403086402d042d02d0740c40e41402c98104603801d00111400c28404001d00500c4d46150305081c024142d0140f41c500503941c000d44840d15002540e019a4001c42c040070801119008041ea40301c00c2c0d002000180b0317003407403014404601a203184000c40d281c80c00321000c0c28800f00803500307058071071010600f44240690 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 331770926 1250 331769676 331769689
    0x915150e0f0f06030901061e0815130b0a0c020f0a05030301051017070e1318060902010e041802130b0a1a0d05090a02010905010e130506060c06010e0f160806 69
    0x11000e42e02000400240032280e0781c50303000e54092910040000380940c00c20710700f594100c40c2c001c0e01d04a09420705804000032200014010010300d140e11912400d600c801040440c81440010004c00600011007080700a0040f90f001d0110300e503155003240e1a044460180365252140b0840260140d0020001071002d030404c200700d40100001c521303090603128155030100900a1007030700c01e10005403024400d60960318044540c07808501101c9001c110140e0300c2817010040c49556400200b10540381c08024080d68004c1004400008001d0400e0248450760f5118030041000c0362800c9102d89040403007281e207210648142503003844080c00040900b4181035500c062404508031603410b524007008444150344450103401d02640c0c1440c02045091100c1c0b00141c040c141300e81041c0e041154258540c042c0342c0d5440103c0c211070742c41c94000101900d0f10740116000744103070061f102a600c180382c000150003202001461080b48560341182031612140211022109242d50210016200c0800314469245c0341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 331772176 1250 331770926 331770949
    0x3240b0f07110315090610051305090a060c12230c07060e01020a35070c080d060b0702011202070209040308130b011502010e070503060711070f0915150e 67
    0x3000b0741841d0070a1800041d260081c5903c001c07400c0c00c0c42000f4030600841c10006690800302c4440040840c1c0c1c10000400c1348001550540f4034140d0f01c44c0d0126000e0034060020007a140e400003801d020300350400b08060884150440a03003051407500041b241800802c95900c0301602d0365210914558550b14444045900108402e4450607661950001403031001d10084c44185803d4440d055030000f1400c5004241c856100c0345a40300804031000301d007030040b1a085a07844401e81c00c014007210301c2400c15800900500030300240e058a0100c3c04101070740240c0190104c1d510036610014078000c01419001680070b0000025084603047c00801c0000c2e000e030041603408004641c00ca0400700050b01c3e01d0320604002c0c1d10010811034040ca071400d04a5080c0039261160704108010080c481c5031070082a540e250080150040080c0c04810340b03400b08040c040d03172000f800c04844841189850341035840c024020450b80c6110f21005007000901100e04030b168110820f03050722405200881c80b0248400d61300300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 331773426 1250 331772176 331772183
    0xc010206130f05150f060405060906010f0f0203040b040b1206031605090403142107020307050a170c0303010807091506120504110a121a220614010603240b0f07 70
    0x801c4e1380d080040f130f50300401503c42e81e8550320318842400c0040c180400c0326000741080e07006200010420a169821a441c1506d45c01246060045510880d404038154010b40e04034100c86000010000740c0c0d9101c4501400c802800d0221306402515034004155486042114401000e540200e0030400703454034070040380d03006009040c8a81000e491403030000340c80d8807100041c01c94112140c0507140c04080c0040b040d81c0020710380000d52610f41c003a00c4066903001c0740b910040220070030b860b01c3e600c0c200e42a41540d59400c05c450440307031a5610352018640b83c039054003034260014605469100440b50100c1950120703107803038a91149406036603141c44c000e40f400a0003600c00500413040e003a50b54441f200349100902c00214201c3c5507000500e000303c050f250058005815a040310144141c1e00312044407508040301d054500380c1114442c5c0303414000b4003500d80705040004650000082c03416003540048844051043d010404822480703180c50340f10010380034025004105022002038094144020801a4007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 331774676 1250 331773426 331773433
    0xc0f0d0f0f1404030f0c0603200f0903010c0c1a01030c0e1f08033705070c05030109140105090708030306041a0a0f03120903150f0b210c010206130f05 66
    0x42e1000c1461466015074030441e80c1c24003a0f00b0350b40c180300310a5440406003c443c0360920400d5403000041046582101084216940018110900360110412103841820140c0240000103103840084c004210035034003a6490815000c0e01340c813442100b001303503069a5010079100303d880d0801c6032018900c40000c2c00001c0c40d00c400f103d031708036803011644c1c03000040070703103400039540c65001e400810002074003030020301031a2002d00b020180c85100c510b110742d010881d41c42c01d280c449540f81000411101581d02040c0c06510b807030a45014003100410010803504154028082c030f403a841c54180c0e68061900c541e5100c3c0e081400410079a19094111086400b04aa0f001c1d0078208071200048111402e5401100da43c610001c04000704400c140d242042d4230154103003010014035607241c10b06080b08200c070307109229036281b94511500303029500881c001c01001d0802c4490078030100e980c1c000b25080302c5450a09208020320140c540d8800507c05d4466a00320306252411502507840d0003d152101804035130f10301 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 331775926 1250 331774676 331774697
    0x5060102063d051002070f050d1b03081206010f1e12021201090e15150604080312040507230d0305270907080f0402130b1003020c0f0d0f0f 61
    0x800d00c4032586a5080b8441e0318881c107072500d01000003a50703003440b0040c199000101d041120720010072801d0122041941c00340c0c803042c3c06190044841452001c009440d12501f60702005008517000608000f00c21003550032515282c00780152007020040e08020005013034101c01c40c500c003030740700d003005140507a40c1080200920b00c12988000d03600110746100350140106c00402c031140003800303144c0c1c21480d4507000e4501003515001c40340011000070b108242c48044842d0046882c1c0312441210010b03c03584041d2519240c034606c005510b0030060320142c4581c0f0030180042100c3d0109210020106108400169018810342c240456441c1c40d18060341840740500800b01149074180c1002c10074000701c1c0d8048600001c403c20002403e5024200e0020030103800100000888042081a001601100c41e0081608149000006030070b054100780e400c02415480810aa50540c002d00030140b111025988500c484040a90343c502074076614400046050107070f10952401500103000d100780d103142000c00c4a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 331777176 1250 331775926 331776001
    0x510031b030c030f021615090b1b04030611070215040506091207050414180304050603041112121324260103080c010b01080106050d02300412030506010206 68
    0x903000741860341010800518800204031002110824801007d00c040040000a0300e9131100944001c2080000c403401c990b4010a83c3d8084095030004d6501c214248030308030040f0040340c20b54101c103008a0061610400c0b1020314151041581c040d120702415030350074186440204114048a581c0c0b20040d4003030140c010589031210b006014998615408490040c103080000c4c400c0045800380708190b40c3c1042c03000340242d54034a400c4130303042030700007054034602182c440000b040b03102d5003c9030304028440c180c20540d0b00c1803118040d10a4100101c80088038554542d515120048003214144194000c8080b40501078000c4240103410720001d401c80440780d1041c45244202102030b00309a800c6400801d03c200d040c0800d0040380c0c0600e10a10744030386076501d0020054417030b000d9280012001134004c900c00b83c442d4040380080f40300c0700402a0081c07403410a012101c072003c90070f480075502c2c0104803942e00141030007400303080e01404042c1e0013064640d0300c03c485000b0040b4a411440421040994011043c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 331778426 1250 331777176 331777181
    0x4020d110306120118121206080c0a060216030605131502070606052e11010204031101030501060c030503010302061303021e01030608070e041205091203040510031b030c030f 76
    0x104529400e00c540c0ca04000007001603000502c9034101c820381c18082c0108065110078405000e0a60005500c6400b140100f000ea40d511090301d15a080b042c5030100006038100e00150b030b561146420344032aa030903034452004a072205d0803507660001c90940c41900300300007a846d90006502141410303215290b40307040d07603882c017a12080200841c0e5243d00414041c0070b00c81e1911507000189002c842c00f5902074503021106001002da8403546018440c420a07030a110750003180c078514401344080c000c56581303407070b0319141800240d006041d0740004c0c40c080003c103205000d55004c2550f80c1d0543c8076242143e1841e0f080180c16030024400c0c1c58080f0341000d0010050711100203000195003103501140c0100b12000006040b83d0040c0d20020325940701e01810400c0c003080c1101c1c03e80042e00528848000300e800601501d8621410001a411240652440618600110203481a1082111031100e1018000421001e40710340054090340c4503050b02030f41c0c600900980c8205071325240742c00d0100700c00050800c203408 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 331779676 1250 331778426 331778441
    0x32304020607022706060304020108041209081204090608070f03080c030f040b030a0b09010612020d1b09030b06030c060d1802190614070515040f02090c090108090a02090a0b04020d 79
    0x25142c2e0002c00070b80074944d03c1002d89038060780584500c2e0551a090f00001c000010103800905640c00726009810050310440c00400079042c80c40031500000c0c86607403081616482842a15422880e0500105a040003c40c1c0e41d0115650724441c0d02c452030550301c0c0e030515070713020011154451104009050200d04000e01610042005c02c0c1c0c01b41c0c0300d180200144003502c0d6807071b8045206031000c20060200c1500034141c2882c07071101030001078842d0b94007000301e4000c11080c03281c0100440000c0e5a98140c3d60b01003501415071b8420341c408415500c8070400d05956440940300580e000e82c060011b084070300556845040041704090303002605030410380128006400c0e814080078010305030f0f503041c0210781e005400050740d445580f0043d45441c00c0c42e02c409499010722001050f03100041c1c0080713010b001d104212500096001400c40341c1c40c0c28600901680c0d54802004580400e90b0b0000040e4101c401050350396500d03030064241c01e003607074810442e40d0082000d450002d50080d400c0c0480d039802c88061040c0e00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 331780926 1250 331779676 331779709
    0x30504050d030905120d090803090634050a021603050106090b010203030402091602070b0a05030106271e1d0108070e0c07020904080d020c07050a0603230402060702 72
    0x15590406082041c102200e0040d04010b050038288008000740c03002401d01402041c80c03005507101e80d41042441c000c1c2041400152101d4400b2041c48040b5901082040c00344a401c00d88120054000507280010542c6204026440d40b181612181e0a4040c03801070010400c0340c0306840c204c8644140900c0507a0458005070f8181c0c5d502c0e041445000f005106a2641900034001103041d494503030300147d82c05100406d10010f50101004c00c8017000c0c002c0110303002601e407000900342c54107584030700217029401c00d10502c000a80a240407010001e841d03129042400001400702c40d00500f00121107441d01c0302c0d0030000e01d04120707100000565248250b84094410701d002c094000651400c1041840c0c02901d13003011580480f034030b06000d0100400400c03290107683c1520580c5a958942c1000703070842c014903e18181c410b000082d0360080d8800880c124040c3da81c02c0301c4413031943d9291002202195550190710b03508078541c01c00c180640964404690307120344000c0406142890b16800b281c80c4215158500d0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 331782176 1250 331780926 331780931
    0xc1a070e030f0f0a2a031a0703020703053a0501030b150325050904050c03070b0f0706150f0806010602060a09021518040203010b070b2208030c1903 65
    0x8200c91070700b8032040346507402050041202e02115401c598031080301500040c02c040e40d801d0012150304000340d507105007444c1090044003140d900d04202454182a8068240c00d0000000080015019200361b49083d609a91340b141400c080c0121001c190703403c0c0c0d82200e601454015904081c00700c05a42030884a003402e40840c807545075247c01e04031404064040b841495506e003540c0d0b49a140000c4006904100340b41d4100240d85a03040710000e0304036500000e070401034900c2000b050020010791440802c005030201d0b0001a5a029546802c5c042c010321800c1c16442004071102240c2c198005c11a181c183c0020401d04540d6841d441d100160b49a200e0075041d0080d00040141d10340610465510040441091201d5802d07a40005c0c1c00da2104032451000392800704411356480c8c40e8001440e1031701e402074402c56032035840e1111f0041c90b80245c038084429110b0800096a040303401075030f442400418681c80c403c809115504c80140e5000104020307200300c8203005100d00c01c0503400861405c00c0090301e00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 331783426 1250 331782176 331782197
    0x1090f0501030b01051201091203090b0915270a06090b090c150702030709020307030c020d0503040f120e0406090e01060f08070506070215041508011508010b03060409020d0501050a0b0901150c1a07 86
    0x310500c0d4070051080c1d01c030303400028116000500c018ec2090b40320070600c1d82120f0100d9800480d10300e071454040c0003806441581007001c00c01c4003c2c0d000d10301c2079010b040480c490341d644200c0725a03074001c1824010340201d59044640c290040320f102406c40e02d0300c0202510103158480b030000040741c00407200c0100227038442d21102c004640511000c1c00110113840c10340d20b14076103900c03078020b1948840c20043c00082c080003100c540510680c018081c130340b07000b001840980d54909441c00500705881c00074410354600000040c210120b01e0310380301101c4e0410040c0031034034601010002903030040c1c00141d8101e11010011980f00740084010400703009100c0341c0d101c08000490000707000c400f0580050750740c1b109000c1800b8007141c110001d54119002822030691701e5513040302080244c000c1e0f210094100002246c04000c108040d0011441041c00410401280580b1410401065028403410b950a80c0900040884c54802c0540c3d440e001d02030106001c110005801c26030750b0305000c075102400200d15144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 331784676 1250 331783426 331783433
    0x60810090611210403030902030d02010903030e21221502151909022d0f06070b04030302070c030b0711010f0b03071806090c0801090f0501030b0105120109120309 71
    0x40402d28a07440c5802410280300c2050801c0380c881d46010000e8611407075000a040500c20307048254045c2d8003a055a4611f00a000c0103400782001d0768048010030b081c0050251840400640d8000b560b80c40c00e2440c01c01d42030440810203c0d406003150760540b00c4030040e008015240c1d80c00400051a08890f0400d10002d02c0d000282081c01e00c040c0501c1042c41a401d0115080c1c47d03c0901c505000d4140000954260318400100007020180c8460005680200d2541000c8801c4140078000001a41e290a800c0c5000c0c08004180c030a0749c2005007841c0101e00403c000c039209034054580c161080c1400c000b41901c83e2500003407004212000c1d00090700420801c50141020b0044900300b000841e42880030701c00e000006620390070240500c040c070f1a140c0b0803019004a01e40c2003440100442403003000441100c55008210a070240210f4078054100a1021081d40403445054120394004280310060b900304001c1002c1e0521404007a0400c0d0f48401c0410b0104450000303001b81d11203162070000700302d2a50719 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 331785926 1250 331784676 331784681
    0x30b01060f1707020c150702120f030301061d1306141503010614071209050306100e06090c09090906190513020105030601050c0a1a25120608100906 65
    0x800050030080c0750034140190541101c1ea0a54108030980e04104a507a03030b0b00e0482c079200d0300406980c0e010380c03024004114401010001c0000f20700956141440c080400d08466503604c440c03d44041c158410801085820302c18800358860301c00300d68041c50020074840000d030000f0a105000c54005944500030041c501100c3c0510201520955001801101d58541151540014411801845202c00314039680c2060341003240c4175194401020200040a000010300300c41d110702815001e48600d00c00b085503c2002a5042c6c11030755076403060350040d5200360511410b0200600070684254092242c00309607600c80d51020303c1003041d4070092109140a91045004070542c1034544075032860a41449540390031150f0001c001502820040e5076529124012500341c8100041140300e03003d084c00c001708000d050850802c000c803088184500395154440194809203000c43c01c3c04a40403600088040c56001d100039000c08046144001082e0365240095424901078000008800c0d030f0b1102d13060104103461 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 331787176 1250 331785926 331785929
    0x7020310090335062d011701030c0303021203090607031505031e010c030b01080f1305030d05070e04021908072c1521090c0a0801020702011101180204020705010b030d09030b01 77
    0x2101c5611009895010310104c10360b1180104445c51005175050510780d000381c5512035a01c1a681d610381d860340c2e41b42007003000d42070a030104400602a41880d40c40440905007501e005070b0710f00015100030380f01c0c03840075002440b804118542076407114000181d03554041c01900c46c441280280407250711202010142100c0030b040c10350007032616007050701c500350b40d02a203440e50010404101c0d01a5844111040300da1150b40d036401891840000342086400090340c0200307001d85403039101c50004100710b104000507402950400005c1c60344141c0800c0e407107403042c1045034000c249820480701124440420203941c4400300b1121540c99030540d4084021705003034189901c1e04028011160900854107051200c4410840803044c20300511004a00f50000c2444220403482004080d000c51a40c1c0302d01282c042e4002d9401a0f0108070383c06070002d4290310600891161512085050035072800c50b0b1f0802c0004d4014040c03c1d46c2075903031100d8103850380c0c40c1003114006d65107541d260341c03034160f1540c90322100c0c5e01d005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 331788426 1250 331787176 331787179
    0x1060b03040605163906061220060d020304210c11060406050313050f3403020609040e03090d0503120114010c12050d0c1110020702031009033506 64
    0x4134040003109010080501040032080b407100c072200034031700c0c106184560010324042d01c5580b40443c0042d20301510b40c04028950700c18013404a80c0e080b642c1c80101920511200640c10100070401d601514143d54002c1d984284a14400b81902000c4404094054000506040407502c040c1c8558144001c00e891101038040c1190490b03c3c16040840080280c0800741c060803805a2885200d0100541400310400c0441018201c8050300d09007080745100c1940040c900074449115a1010300981041c0154025641c018040ca071401c64188148002020190110745040c0000c0c840700c1f40c42e0f42c5400600100502400045450b10b0b0b0307038280760b12400010791081c5100c51204681c0b9030301b070740c0050140380b040e40c01819581e40101c190a06946600c2101c00007010603142c480784202440d0480d00324a500d0801e40d040f02e8150705c0d104982030480c03155500107035142d40040642e005e40d030400d420254015101385056404015121801ca103034000030403031101c0d004400711030005555007425405510860 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 331789676 1250 331788426 331788437
    0x519060b09103005060112090c030b060f040f0e0618060402010e0409080a0206040507050105040317030603031606020c06060d0f1b0b07060618050c1b01060b0304060516 74
    0x4020005500d480400302e210061040c105862050f01e141e00300c401032038003c0f800c001543c010f001c102800041c00115509404142c000000c05030300704061050119032503010400c04005411a00c604a034020000c1801390b0007119086c0700301c4651035074021526407019450000c211000310183d06030800200424070f0004030781300c481d0304030452400034016402a80a0030810010b0070240045005400005809000d00310000b90340284c0503800120075100318010010744182c05d4131000112510720031844050001c9010b18108046200c6483c003c0d600b00500604580c501000e80c60742181d90201e2003025280c071a40458003000c3d082c414400d0552015007151815815841642c60600400d901003000e03040d198070222140390164804c5180d00988844480552204480d1800b080508001d005444602402c107190300b009030740794083c0718040c4012549603824000c0304620000c0c05000084890015901c8100010702c0780c000300300950080303008520105940c41c0001d48410104040041c0381304016 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 331790926 1250 331789676 331789687
    0x170d1e06060512070e01170f07080703150603051e0916050a0b0d020c0c09090d120507051b0c0934021002130f151e0903030c02040f0519060b 62
    0x941e0043c569000c291424040c04100f5a0f60048400c440341c03104e00d0a61349100c0083c450250080b0018910415075170f690003c0c0c0e50b607420740807425101c008480074450f00400e2402d010b16030081d0440d59114441460090745143e0103200f4412615087c1e03000b580f2034100b402c1004000300340711042c401601e019103003c190545000b045040e5480340e03141d04040c0700c1c0d000c42d514425400500545502050040c110a19401c10001da80c3e1981610040c071000304004050500082c0d07802e026142c440c99590320b4960030700d1440d5088038207403904919011418068a41805101d44d103000da00c500400c00d0815001491a2a01070740702d903411070661214004106560f07010a1650014452a80003c000d101584803030140901d5411084035400000325841c42090114400200f840250600141581c1e1100d82880590f41902d18110040c00b10000400b080d00c144042400348800601152001e440007401d41492617088040300d10640b103000002d69540c1d0b4009085034a03001d1000030700b904008085c50b11 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 331792176 1250 331790926 331790947
    0xf180c090902030411040c050c0d0305040b010506130308120402040608030304020d0206090f150903010b0d0c0902070c0e15040b0307060c0f080417030304030327170d1e060605 77
    0xea000c0e1040001007600040043d0030001d04410340203007941c0162061200c0340c2c01e102c01400b542c003c3d1101640b036110701d8950441d0b50b4401d0240501550300103010301a207900f00000d00c02d059014001500d54460250340000005e0005801411030341c1c250300f80324005003024030410040e920141d02c00c0849a1081c4280000744e80c030703101b4142180f5411280281e603840144040f0301303494000d0f00c1d8254041d050101c03440100003075400502d9140e004400800001034414104048208000c40141001c0900d080a02400c50aa402040791a02448004500d00c0c0d035480ba442c000d60044940b0040c1d0145007101c0c506034105801150b981490403809000c505007003080061002c1c06024001d40100300610302c9101384500d2804a23400f9000c00f20012901c0046000d00540d642d0003a0b400300d001924001692004200d0340d8204029496044100d52003e43e990b19818456031031031004210000c02001021030b1114184142203e103420550202c401c0726401c0b0240341259042c1e40101e06000c0204800c2491 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 331793426 1250 331792176 331792187
    0x307030608330a0b1504050f041b031e0615080f070e0105160506010e010311090705070b250309050606040b011e05071e0b282003010f180c 61
    0x542140d2929400c40d90740f1002504082c02907a00441d4001840140b104601500c413002441038032010340e1200944c151080511044034603031443c83e50350a05c010707107851603280309801c41c1d00c021025603d45500c200b410501c800455071207074010541d402004550510072a00490020b134000c02240c4525110300d00300340040c0c07100c42c1d03201e4031030b0404c140012000d500b8200c11071140001038001003115a1907864441140d100d0501380070030b84418070908030403400e628260b40b07801d102d15580c3c0daa0605103045a519558016405002000607403141045001c1c1340a881041e403007862800d0744c010407441d4683c03d02c6406c00703101800c410b0181d410442411a907036000351400c00e101c031517070300c2c01c080c84840d031441142c45000707410f4000c01c4280700040c1000102e48000310302c07840d07034061062071100b0f840360080307015441c3c041c0191b600003400000486400c020190f21403010316441c2c0004072042c840c0c141c0b18110b694026084a0000c144c807440c1030083c4900c087c0030101d00d602c045410400c81e00ea445000d4038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 331794676 1250 331793426 331793503
    0x70b010f1502060108062205032b0209011b021c03020102090f09040c05061b03040305030703080604141503030412050a03030c0f0822050307030819091e030e03030307030608 76
    0x302c8110506481f505043c0311411800705540000c00e0b40e03214040102640d4582e25070b03013048401085802c1381c41034031000601c22541813003416110a0079841080c003540e8007080506005030382c891100e0030074040c0148140040e50911b4425400141d4801d00b28003081104403007400c01c9030180c020b0707404020003d40d40d0150001a06d004aa18070784a151000d4145005004c203900c1c0881da0101040c00000c102e0000081c01c0d9152080d01c03500b00303540d20401400301300c401a880c804402003444021030280c0c4903400c005054004e0140c00d0f06d10340f0707848110102c0c0e150a070b440200c071190b0088040e2414540c2c503110b2120400e14500c0c1110150019000041182d480a440042c61901500d05403082c151200300304034081d9032010940c0d855000c141000317850014126080103070008d00050320042041144184441c150b800428010860707103081102103490001c18044040c032490700000c40e5990350030000b4500c14903160f43d002c2081800d03e031805003455241c50a0000c0348007440c1c0000718003078a44240c3c0704c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 331795926 1250 331794676 331794691
    0x180f1a1c0c0e0a1d0604020a0603050903090409060e1204081b101b0b070302120a0204080703110f19080c030a02010801150909020f04050102010501080f12030408070b010f150206010806 81
    0x30460f01c400072a00010110880c00342e030000146a07104a0454022801504c298001c41e2a038404540c4c0c2d0034182d0a54000311a50003250b00100a110f43c4ea1401e41d001e50044e50152400240022900307401c070b80303042c18586003003810302d40100d010171034000304100400e0b419a50045400480840001041080c941400b0090600041d8020100600a0b110040300502c2d00505130501500b8179600180003036201014031100304440d1400110740d0703401d6000300e408079091903000b00002461a2140d03990305041c4003406600000c4141e103e4400c0e900c100300701da100592410030386400c0340341c02c0c006441c05d140c0484560198104a0034513000d40e130402c0d00541140c4c0508031068240c00e18010440e61002150010341040d1304c0030501e08141900480504142d0b80d083e0001c110341d980b1601c045035141803001c0600d207079600421135160010100f4014580141c1700d05111030074040300303589440034400e00b40c1100000808018040200c40d0340300795020400740d2140098041075062495281d1100d50080029 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 331797176 1250 331795926 331795949
    0x201050a0c0512030703021b1516030b040911030f010501050d080d02091f021212220c15081302090a05130b040c0302010207060207060207180f1a1c0c 66
    0x10070034007406001c5445400480704401e0f60300d113031105000d402500078002c0c40c07480316040c2040074094900080c104650821140d4a40c180d503413640c00800405050349660010192180c0e802d80c090b40b103500503814000c0c81014580d841c1c049101c241803512041d0715003284c10368106001080300343c48000d41655060380124280e940c030440708078800c000c0d10038501126040310411546884940401440e410b004045600b65050010403d00314038140c001d90900600c00d9800700b000c5000201c20b00d9440c1e011407200c0f00c444864414944071102041c3c5c0c01d078081001802250707400c00b0350540c400c0215501c4049410006015180e98002c02c07062334004000c040603039910400b01e0b42c0c0210994003090310581c0501c803548070f86403600c0c00d111588414801280540b10349007020481c1800401c541d800d90f14260300400b4403a1a0080c00710840e03800304d440b008003a0380d414124100701400d00038244501035404009240101e04410b0040c14280c0e1010b1070b214841d809440400180d464401e0012924000403030b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 331798426 1250 331797176 331797197
    0x506280b0d0b040609060507020c0f0f0118060216090e1b0a170a020906030c130504020d082d0c030a0c08090a18111305121c050d06080a0201050a 64
    0x1141c00220032031005840191464104010044c080e0003000e10280f00341c40078031854541c800141da84076003a0f001c4a074086030048000340c1505201c070944078082014035000800301740c1d900003281030010079084500180c000c1d200510890000505100040012203010403440e20707139400f00f6803100c0c9410024001001d8400c00742c8135503503848008502030202d804030092640510f489950341c1c9d042e8000d0403030066442000241581c0740c045001c0724603c40107040c61202c0002c501080c0000c060041049074007140c41681c002c0801c06050203050048110810017a8500d00b04101c01440b41e05111810389050003040401039500001c003d6500c500d0482c01d0810a08505d840c0c004140d0107414595908640c5c0034000080501c62400301000800049804001c9503800b103680780050f11400126030b0013005030030320400440c108020403401d0000104240c0342e418909010178590564407012117000130300d005c603615100214071311810000f809000001c081050321f95001802c1400780001c0f98081c4203a1918 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 331799676 1250 331798426 331798429
    0xb0a03060f0602010b090610080c0304050307170c1b0112022503032408120c100603121b05120307090305010f020403060608060928060501120506280b 66
    0x40001d04001c1c004104041d40740c82e030003802002d554074014400c3c1d401e01c002c120b00b13007400000c1c544034604654a84400d60f94103032030b411881d807010b401102c40b0f00c070400442004c142954200c45070705819605890343c0c0ca4004040610342410242d91728280301c5a4010030301c10360f81010f103039440da83c0703203000c09070300d907400780c0004040034491140c5a25468107100c0c48900301a4035074008003125440c110b9207642d21141041c0d090f8901c40034080d2485580c002d6141460480f0601c0190210700c10800403102c1101e001119641070303417590f40c0100c403014001c008101ca80d90300501c24000030610a403603038800c5503144d03ea0999604901051800385403002000c1402c5070b1040c0c20081c040d42c0c1000c001c0c004201c0841d00030000f94404e11054801034036003c408500c164000c1000d600515201c0000c11030130340d000441e03904640c400410003003006003144001c07000804a004090080201a001503544403640c1000f50600c0d0004021800b184040302601c05001c4da004155559900c040b10001400d584030340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 331800926 1250 331799676 331799681
    0xb01021b0f0109081e01060f0b070605280e060c0a020a020f030c03030a08010e13021e0111070e061009150c2f1e01021f0f2309160b0a03 60
    0x1001180c03039003d5104810010101140c100c00c5e140703e020000c009041c0c0c0c0d40c1c100f00e44d180042c0250040709804004120101784142c1100740c014039000d5200b1103280c1e50081c08641041c500307412090141d02d50300c00141e002000d220b030a0380300707003004501407800b904036500030740b52619040024480d400400a2034483d0b142008000d16403c4061304a90303540d1598003014049110902c503030040e150070600014004449480b0002c9129405008420801c2800480152190701d00030500d0402ca14220014601b40c800c000c468000c00b040c401d4183d840c10b1100c14008020002880354080c0940b11070200014503a00c070241d40c41c00041d14000f108201e1901c5d00c8203005030241c0e0b151000300300e25007240344840d02c1401c00c0a40f031801192200d032031b0700c241c080f050346404040401c90302507004650f40210091a100c0c0b03820010421190000e043ca6503c1d1003502210004c01b0078001e0301564058140e03d030224654400d800c10f4644001f00104014015403d8005585019400081c0c0d0080365410805000c2d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 331802176 1250 331800926 331800929
    0x901020405060304050a11060f27190e0f060d290a1b0f05040909170c1e01060503060105040c020313080f01151203030b01090b1c0b01021b0f0109 64
    0x1c1082d66203003007a09046594a088480075a00c00c040c0304201c61f81c500d070032030442d0f42c1c04081c4011181464400101920f1030f0f44051040d4005c044a82003081c1c2581d5030300c42c041800d1485a05041d5102c0c00c081d00e160501000a05000441403500305121403560340d41c3d0f807500c1d000c0c0e001c0c441d00c005074a01005607101030200e08090030141e110400380007100d030a98008007080788649103140720924402d8003c4030042044a098800b2034001c00041c00003180c1d540110174014042c0000358100b1919000148069000813815685604080403d001c0d1402842c240d04280f511000248041401c01001076200c0c0818401d8901c150341e15003115811a00900a45034030031556000030604c190b480d82150b841c5d000307403200344100754600203040a10540c0ca03810781040d01c401030450050f01c151960141e00401c0c64000860510403a42c0002034510031002c010503820780354080c6001300283d60f030101c04c291070f40c4081250554100300d00d030884025800f401d00c04140300071104c03462616503180050380c010340c04d07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 331803426 1250 331802176 331802179
    0x2060a0e2d0a0803010e0f060f01080708060d050601170c10050a030b0a0510030515100206010b1e0a050d0f0c020613061811030d1403010b07060b130f0c050406170901020405 76
    0x40700000f0b1b0341040920007071283c2d1030304c1042000d60b0f07140400c0118441400481c90301261040c40800c41141c4609180c43d0311601c05001c211a102103500d1716850310030240d0019880090600b80a28008418410060500c03c151698000f90300c110401030500d00a81c0000c80400d95220030061141d0354001c40000105005481d203044240c1c2c070b01c0024040c110403149503400c545070007208201d40c104080c1c0754062040d16809094582d00744003800b40654080e80440d5120304c1c03002d0300700780d003c1d00800052150091540f90315546240f401001026650143c4245541c9490082d0102800c3d0300844c00542c001c0c5d1101316003a43c856240b5054008100a1548444910344442884100055019241580e010440403602c0004003081700711131280c04440003101c1114248010050142c40b00b0107810540d00c101d0f800b00700245e1b04404141240308648102000030785401c0b003016100c00300d108000328200940b422600d80780c141007010f040f109002011044805030080010300c140c00a40c16203016180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 331804676 1250 331803426 331803443
    0x70518031e0c0f0f0d15020903011d0d05030103030509010e011707020a1109070c140109050115031505010b0301050d0c0f0e16020d08060402161202060a0e2d0a 70
    0x141c68411959849100401405000e441c041000f691070b01110441d8040c02c0144000c1410000c1c3d6200175a00d56000c0e40075030242c1d0203003e0a2525038081c0960345d40a00d1000c41c071094040240a003500e0110165683e200b8002c0400041c00405c0d8001c007103602c0c2c1c06081c2000d824010407100102c4d02c2c2602d41000b42c0d40582040280000f403680402c4611406010358a1051101c0782d20040040c00107095038020003041c111000303400012115034200d103203c41e041c80005240b10301d503202c0e1402c1d212841404100c900c0d110405004106040303600d0328a40c10510f20802c5a5810140412018841030041500c103103446060b1200308210f26030101e000c1c1c50005d2003a08000d95851010901f480260380c0e5140c00045660713428000340c4000307000019001c05544500f5030b51558000e000007035003e0003075030728542d00b90188e84010561035240484c1540540e0f0040c20b1604d0300d15280c0e0b01702c4d20300c6481e80c111a040701c661550020080400d020164228100041d1501d8a40c1c1816140c88080390f002494020f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 331805926 1250 331804676 331804723
    0xf0c0c0708010f0f02190f17040302030714010207121206030507180b0d0b13060204150c03021c080a05090727060515070f08090310061a0307051803 65
    0x81c19040000010460781c402d000300d404040ea039000740d028814529044401e00000c000c40b403480360002d40403041090601900b00740400d81d040186010892301600076034000504101008082d5112104003074150008504100301e0341e0320b2012101c039000f17507581008540031030070805a039150702c0100119400811901090ba0f58480680348105d210904400c041c07a200e80d448071800c0c400c0c030010500d07a0045c400700d5695a12550302e4070340b0564920940b28180e00340800b0039145a4003101c1040004a51580854441c645c038000385040e164602c0d901c0c0321650016500fa80b150016801c5400c5032888601040550700d01000e2460100305a20170031408061110340c48100c1d0101d146c1c60003900c40601d0500c040d507114014000130325029031200741c161404204403800301e14401c40e07a040240c89081e1140c90118000f0001c0e2a00340c07c20203580100344d454404004090350080702505041441c803140d41189800d040241860144031b0f200488070041e48000607071907600f8004801c403c0e540714400706251 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 331807176 1250 331805926 331805939
    0xf030f051c140c030c2d040308030402040e010e070e0c070b0408071203110d020c010e031305031903080601050703030b030a030503160305040c060c02031009060c09060509090f0c0c07 80
    0x40c10260b400c500c00c01c5480e00441c40c51141641220300c50070b54003030700c0b910307040009040941c003010101c40c0c0443d003442040d0400000095000030002140141d88030f540b2420240108821503c10030303000d82c0582c0c900904d05d40006808101c2760115008a0507014055440007800760681c030840800920300300c00703c4208000c0102c6080500521030007140c4801c1c0480c3c1c102c0044d012201003d5201c00392440910103446030301c9445d0020840e05411038004116036200c0b54603180745400020010b0303400750100c8403c3c40f90742800c000b00700e16401002c0d07010421242684024282315406040e040c10040300103003010515010707030483e8003c2d0340d010b0708455004480b4103000348650001c0d21004000c1490050044400d8860b020b014003840c1c01068031800380307207009c0c0292840300b003d140c103d0305806001c0e01e075084808940300344213a4038058040804c0d8110300c4080141980c07140c4d080803041c40000e00104440b5103800d011668000300002003044d86850307a07010100c07180507044c0b51008601c900040440c40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 331808426 1250 331807176 331807181
    0x7060e030c030c120301061d2d12010b0d0308040c0b030c09090601031b12060e011403060c03010f1503020c0f0d1d0d061113030f0201090504090f030f051c 68
    0x40450300300c00e65a90f50034004c0030003024030080c03042400091407200811410340008910b10381d4604014010f0104903401174030f00d02204a9804540441c0550000a500c1400c01c15011900346c0d035a071000b0800c20f842000050034540303030307030320007404101303044000800300486042040040d090349c0280e16180d00e4981100f07003aaa01000c6200d02500300180814215406801826102210001d0104580f900c044c0100d51503529024002c03120380c1c890000003128260507031281e0182904100701031181e1200c4091514140010b0044494104104010082407001c103900106490780b201440d0b40b03608490b40110080d0140441e4401c0900921100322035040c40000c012564120706d48420784162002e95040020352040007200f03420482c08101800080c14582c0590255152800058244a1100318040050001da00b00b00c540c50040c0c122141550380040142004001c02c4405200e00015983c9410440010041c001c090212212203078222500582c1910403001c1d0070041e0100200622184401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 331809676 1250 331808426 331808437
    0xf04170309100b040504150c05040f06020309030706050903070b070312050705120702011814010612080a0908010504030f0e04060b1314061908090a02040906060602010b0d0b01060507060e030c03 85
    0x42491802d4000f42070b0b818103020740da11450300214158500074078945070001030720450140f801040810040403901403030100d8840060141035000313603154292602030615200e10742d0410804e105040c452210340742d50024290080c1e400204100d9180c40f91880c0039140380303c412100c031044506100030841c0d00ca9001014200d80c0d0600c00403010103403110b540907030880300c0d07200e42c94071031042813420031010400b0444401301c6030504c1800018445c1d922244a02d00038085101124811400030f0104d100310392015880f00a01750750381c02002241800e5a028040f80c09580c41042803280c040c400e02141da45550002004007010f030002a03994254a00da0014242035014605c8407200800310340c59907051490a40346840c000104507410a00200f00a498011005001c8000e40c41041e0950005031141d009403181103100748404110941490720290a50300303100c16241c0034080d50002d03500481d03000d683c940d04480d0a42006540e1307040605102d40600314171413012041e44000144401a40b900100814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 331810926 1250 331809676 331809703
    0xf0f06020c07060323040b0a1515030c0807030506090106080408091906121103150307080a030c0308010816030602090102010609090b01050307051e090a090b07030608071a030f04170309 81
    0x494031001c0303021410700084c2600d018050313051f80130000d000b2410a80c8041100f94044650000d00c07940c4210b4040d40203001c6401500098444047c110156000400d86400030410b041c20b00261031b0107004510007500c14451001040800c4000c5810310014100312901c110700644603c070012851324a48a03040090301c142400608d181c00d840e81001024843c3c07a80c0c6072410300f111031454440545484201107a28004c80c0d2600800600041c450300420041e24600e1098032080d8140d09a81005486c15005a0104842e90001b080d895055a502c244100940764130000050b101c0b5002030040303006001c19000140242e24150100c0d0030300440d500c0450407204100c007103078a06501e45040c003000030441e40c1c441900c50b0301d007010070783c1c00d1520013a000c0c0d00c40a1010005030300790841c0c4407040360703050648402010994500040c00120400e000135409000e55141c58082c60808001e015450320000707042420001542e4041820080302546030034292100040040e02c90030480f011301c1e1210403421128 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 331812176 1250 331810926 331810961
    0x20c010207080106181a09070c21120c020f03070c030b01050301090c0b070609020a0e0f01090b180c09030102190f09050d0602030612100209041104030f0f06020c070603 74
    0x10071440500030310007650044c8000050450489402030003a2100010400d45005682510a0b980e260f070140c0d1032041c0f00310343d40c84080c0012030904090005515040411030820683c0140c901602f0000c41c90142030b0034403000035500805130049040900b28070040107140400a401d4003444500b203441c80c00c3d24040d281400150b680c2da02018201c5030642c0e001401d8139040401000502c1020380505241c2c0c3c012480452480b06940c001840d14040e9000305061402520601070b030081c10800041c05001c81e001d007007152140c5100000c0e8402058035044015804540020326044483d40540c0e5205902900940d110f240c50180d10302c21010705841800080d040b0700d04086900c0c4203141e4001100c1014160b00044c0040c1d442d8000030b540014551500118003030740a050101c4100950300620b0b404a400503142c0d44018104002d4544120b04480414030902007031011640d401c42e88000f1591104540440420502d400000b9016242a207001c41c0035280300007501c0b0f90141c00c280c0000d000301222 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 331813426 1250 331812176 331812179
    0xd1b0203130e040203121c02161a0606030606070204090b0a0501030210260a02070c030b09010f020405060904022b0c12140105060a050702091e060d050606010e0a05030a03020c010207 80
    0x1c081c10003c0341c01950640c400100404030906920040045c800101d08010040314543c0b555001d0740d004440e041030400d0840b051400348040c82c00041d40395050161408a43e0600c907001900340c0c00f01600e600c1c03050100098440465845521050320140d000409429078036041c0c0592004010034030040c3e020311850ba0034491442d12418010440300c0c0c0b5441203505003810541ea540700a4402080503500c1542001080d0100f03e100c449440154400c0092040303503d44607030807900303455003c044410346c580144000d001e1942d448041d150500015903005807105920019912032200419001c504054049540d050461040d0050b04051000da12007041d004410004d02e8102c914400d084503c05414500610407480d100004028450251402d24100591900002c1280c1e4050f00c0240c50748a006100e09005200c10b2f50003035005604440b0039511400503118a038031048000c040394100072140715520b00f170799514052000641009070440320300740c03e2460701035610040c0007403090251144250 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 331814676 1250 331813426 331813439
    0x90b03190305030a05130f0b1602030f042c0405210a08070e0f190f0504113c07030e0a080a03080402041d160501090b0a050d1b020313 59
    0x41000596a06582e194595594100039000601c030103400d072012200040044004907460300c882540050088414071810304025280070748600b04c1b00c4603501036402c00d06c90b44100c2c500080c1079400315906501c15150000b52a20a20503604918220b80303c400c00c64803e1106000c00081d812980c040c00800301d00881d84104211030716409010a13000020715044000341907240b16403c868440c040c040e01802e1548054000190001982d013441241a181c0c01420820f4140c0904140c0040000380c03401c100f04040400e114100744a500860440720b01044101c4240f01c40c2c0c01d65071180e0103038854501c229060005110301079584403210070390004d00c01c01d050134240d00c1d25840380001c9407000c0001f03007001410380d40c0564071001e00510584e0310a5071303050148060001101f8640d41c1103240c1c0003030000b42c81041074100d0b60b440c441e00b090b410462050410320500014008440903c2c4440c18019141c50940e52120b000e418000042074034000c0c041441c0d1041c0385c0000c06007028042c1224140c1520384c9908 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 331815926 1250 331814676 331814713
    0x5160806090f1302031e0c09060a0305072304020f0d1505030601060e010e0a0f05090a0c02030a14070501110a0905060702030c0f01091203120501140109090f0213090b03 74
    0x692900700901400c0200c2d10070f02860307009144440c405400c0d983e8407180e41840ca000755624041584244d0001000c0c0405490300b10f44060740300000b150150281e40c1903450704d50351000e03a40038050f06000d02e0a000036003901809090582e106001740250b41d41c140b4841c03c01105c0c0c0144400e443c406040a030380c10801c5141d868180190384001d402020282c0ca400710807641042c00a1155040c452002d4403071042da15000300391800342c40ca10754101c113100d140106121600750024a10300c00a0700c1c08010300c28240d4003108440b80e0b20061315003011a18001b0110328054410050b00600640c41d14a01c5404245014041c10882c4900d888000005a8131020b000062040b00d100950540000c21482181c1c580b01d00407540c10b04040c03400347c092a0700d42a00e03c100da54110004e87c082160800e01e0141c0b048a03010301ea01501c034003414a9a0101c41c0c000180c540c107040d005500c0e030191685052540c2c40c081d0f40c10354101f107004c191400321060383c030018000148100115103019019030091000c11000d00f4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 331817176 1250 331815926 331815931
    0x80106031e0515060a03060203090d0f0c120e0a09051f080111040308030a060b070c1806080c22060f090e03030112060e0a0606090209010e0f031e100516080609 70
    0x11000e01a1908510042400b80c60004d2100d41c0c803918401e404000b04140e413000d10320600007000103040050f0410005000510403040c0041040a40c0ca41c80c000100c00c00540d440040d028182041358100520018201400d66040000c5d4580741c4010481c1d20100400b0003c401c0003050a0301c5000c94a80e08240d090720102c42c080400448100010400158003600855103d080f95000007400707501c9600c9511180d00c42e100541e80c0000301d490500c400034180c50410507050401d2001c11485141089068940f030310f800080e48030389155104003500003014058640da0110054040007460f071120200742c44045a801035006443c0b4040358600d202100100b200c0c141d448900c00d540a50000e5a40c80c0c000c0c1448e00c012980d54003030002054006409406031002502c0306940250700c1e80a44c0f400100b041240010281c0305061041032642c4a480210355012040303c1c0130039001032845480c1c035a602d010810014202018030f032008111140c80001c0c01c0700010115075594038a291108801c103c100c0324103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 331818426 1250 331817176 331817183
    0x1603030b0f21030d0914060609010f090902030c0301150e06090907170c040903170f150409020301092108011a0301153605010908030306090619080106031e 68
    0x288540d0054000342d40380b154103002c503000d0480f07141c442c2c4070344014107544110808445000c40c1300d005030020301c018058a94007a5007540c20030310a40c5803808440c40c1110501c903c11a035903940201405544040c8075071030541d14058000c0c00351208400341100400c0c0c040c8107100310f010301000894520f1400300314aa0098402030020495242032540c003180c2c09520300c205c0c1206224141c1d070000251070354040c81e20258041e84503d1850b103508505024840401000c0802c00d10f408010407a02d010031905003000c2290a540010b211040c900c0403d0040500c5c440140041c414004407149142000100c5da500c2201a50751b000980d0761074119503d03080c0d4075240030540070800c0c8014001ca44107840703000000c0c8107a00d0f040c118000d100d5501584055140741c903000e0450b085424620441c1074540120040c0020701c1e05000300c0d0f2616180c1c90300c0e400086c091611600001e404034409544044003081c040c8000152a615940d0320040f05000302160722040340c401c00341c01c114000300c00d1545480c900e02e541 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 331819676 1250 331818426 331818439
    0xd02130e0307051f1a09010603110c01020706020d0c0912170f0a02010f0b03030c03041806080f0f0d0f0509040f2004050315060a0b03070201111603030b0f 68
    0x142410401030a180e0100e40c0d0148800d01141021803020481d69000840b2500380540041d200d02e600d6060318440744204444400b540e07010095900c3d9000c2041c1168445d150000740003080540c071406070700c5203030707880c120543c00481c0c00300a103c4194002c0c0040d0021190401440b440b03000242c461180500c03486032034004048604011949003161080001d0203207070680c1c6000c0d40d140240c030703090304036216034401070303544074100541e00000c0e10038140c03145400c600550500904120329039807031180707014500c8080c0184018500328400d0360404806448408151003500071110000c039942c05c40301d071700c0394503910030313200c2c0c8082c080d00852812001d00c0b00c95540138501401001404042d10703150810b010310641c4d4903003500f141021048400382e089001d041300c6664a142c1010075151100e40e84004440030a86410f0000300e6a8094542c8121100e00c407005d5240c0d44c0303103601a0700500c1d020b00a1340320080300003104940a8413004001031140e100c0d403410800154031105002c8004800c5c0b105641019 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 331820926 1250 331819676 331819699
    0x307120807030e060f0307180b030c0d0b041404052a06040618091b090b0a091503140c0705011505091906080f15071b0b090316050c0109050d02 63
    0x74443d5200c108505009000946004502c8001581d40d070300499000c2e0000750304007a15820f107854090710a00030440710700181c0c2141400358560b4010700c00c0070b08558060751340740880000d035152034210840b810340075801c4280520b0642405a103035002d6000b082d081041844045c540e030030090b0800c411180001d0b01c1e640c2080d0401d102505c6d8202c44101e8102c000d0180c01c000202e0300c1240c0101195a0800d60b103100c1320102003400a00b8800f016000740004580c240004111940c2c81030320641110740380210701904020400301900140100550010402d030b0b09402c100401400300020141203100e50000c208420b4148d214444542c00c44c007034141d0213080e0b030021411480550010441c444481480020300503640d140940c9085a07094200c415030300b0400c54001001000c203031882e401045400c2c08003141158118209601104610061200b0110713804901c040200308140c070340d80e003081c1c00501000440750078080d0382c809003101d480c3d00140070001c010480c3d0402c00e0002c6919603010704080040f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 331822176 1250 331820926 331820933
    0x6010807031707060b12010e0d020c031518010c0306031406040b0106081503030c0a030813320a050f0f120904020309010209091f050f01020d031119020105060307120807 74
    0x540c4a00760a80713803e41c456000c3c0d8101d0b0344074004401804501d000019a02c07044001c02420140b43c0844107096412140c0c080015490100d03001905080d50340c2c24a40c0750b07644600d07036001c851b04449039200c1c56280900c0124810340503030156054070300031403469032000741244085aa0f0081118014840c4113000d0040007a00e0203030003025005900003021002850788080881e2031034000408500b042d601c041e0140302410307000701016030849040c0d400c0d29050042e0303131105a10012000e030318010032541c001c405800c061289a041d0034440d460307020340b160380c059804e2499907003030300012801c601d014503c0710000309400090300f1460303c4002e007091030416070058100002500300510308086e40d502003020034804d43c0c803045a24851300c0d5001c091140390300f001d041011002e946800050141d0100c030400d505581e000a28800025154900071030110084000030004c0d018141c030900c0142d01c1407060643c8a9019081544101002e0702140c000c03a56031001c1500c400e114180c05006043e0810401c40417 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 331823426 1250 331822176 331822223
    0x603070e0f030f030d090606120203190302100e0f100501140d080f03070c0c05041a0405060a030206041205060c0f04030f032105011503090507050d02030c0301140601020601080703 79
    0x21950080507565503c0010a1081c11a132106103004081a41c0e00c2144041040c1407243c400900401c1e85001d89800040e0302281d500e440c4009005040c11005d03000c80109403007003103042e444003102c42d1b052100f41c202d4003699640740078541c104280c0740581e90300d00c0c25500d686d01c21700e8100c40c0c4490114403905e07828400d0080b809801325080d6000c0404004540703140c1602d0009500400d0345580c0e0080020080c24104908480c41e00304034800c0382480c0300c007801500c1d294400000c3c80811100040c8548030000000d000c46007542c0000e4000d900443d002030280000320003642e946000304255010b960b40c4076800398103481142040220600140010b10105801101420700c1612a080003809960f00c2d90300141c030790315540341100d200341d00c400040c4015014005448401c94240c10144140308255842c41c0d02c0380054000c42e400b40621080450a40d5400c000b0008000c8001c0c00801400612105092511030111150f07409445001e0001429080001d040401c490304481000d07100154010340184 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 331824676 1250 331823426 331823449
    0x7030504050319030e27250903020915040e010903050c070512060f0c130902090112020307080c160204020706050402090601080405072106021201030201180f0e041b1d060603070e 78
    0x2445034000102404003031a0005842c000d251f00080000c8804540c1d440304100105240c111080242800c000c10050310f404100e9500001019030840d413604403080807a0042c0007904d10710b402c640c00e0001d0441459049001007604100d004c003a101c2c015120700a0050801c52141e0b00f6005074000800600c071a42e00230306007078109042544441c074110301f101c41019200c210b500322102c0b8079800101c0c02d03410340c2c21002c0820b0317080004400798110b00e4418005081d5480c02045894109000107400ba07211135924400010168004c10443d102d10082c2800001424119005c03400396004a0200380d035580200b11861040340d100d00200030740c034182942c5a21414205485210045c5090360082c0003d48500162019462803000003020350314500006220707400c411060801030440041c1800079011401c900000d441d0305040c07000840d10f4500e0a0b407051001034035002d5141c83c80401c0459020012440a881c0484404440d203003a02c401080208511055a141c008501c04e01000ca00f641011051603a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 331825926 1250 331824676 331824709
    0xb1602180f0c09060f0d09050d050a02010f06050f0d0816150b06041809051204030b0708010f0b0d020c0a240b01031802010305130b07030c02010e030408070e0c070807030504050319030e 81
    0x41da46060356548c2e20301510a074195010801c04a0b03150186039091240c0c2034105451881800a01c0ca4800410a0384804c50001d90180520300c00036410312003207804481c4c02c1c82403403085400404160070140d040200d001003480d1810b0030300e81d00b00aa0301d000d400b5901030b5000b14040303240000f40081042c0007001080e01c22100340c056124880f401d01c521a000d00000d50040d0030ba50390f10310b0098401040400160040c0c10b02002420040c800b000307558041d03407095180e44000581d180c0d512841c141c0b504101180061038118500007041c1c1c0304980502c003040c1d40c0300003042030040c5c00c06c42c030055007903580d660960303d412451040b501b00950312a81040f0f0300020421020f5525101c40d0f00d52450320a402c803503882c046038890944c13180e1140d09224000180140002460406082c41426922099180304804080388280301003544c2500318400c07109410750044d005a515a083d18028229130064820684207008616035503064243c440302c0050560340c035654075001d004036602040b140c07014103030005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 331827176 1250 331825926 331825931
    0x1061a03011e09180201030e010c020613050705040905011e05041518021906090f030b01090b0102120c1501170c0603071b061b090e010b1602180f0c09060f0d 69
    0xe498142c3e80304000403031850303201c00107144103c2c0c000074084e1019030404161a03850680c0700a40b456012915070303004040080303a072920100c0c41c28040d00c0c00c3c1d02500310561192030b100c00f40041181c1588401412804540380e1082d075003241c18001c0071904201e6001d414142100c3e50700800f6402684030450034086207070036024850680d00130a0030285d542d50505041d01d0707e80d0090000c00d4000c43d880c0001c0c4250300744420300605640e103001c3c030401c040c807485215544a0441d00103c0c0c1c0280840d070042500d000d046c503242c2d0820707030719a0358488036044504c0401c9000d20001c148c950660407001034000b0940010281000c0c0581030280aa10040400041103003a010707402c00f140f03040c042d100351640a0302000c900601001c0c1000524115205058280a140401002641c2048240604541c0241d91640c0c840c00241c0c000e450700704400b20001e501c18211002020030501c0d00386614041c4003c603e4003c05595403840f211710b10321603c031002d42e0001c000d02481d040c040e071210003440a1f07503420001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 331828426 1250 331827176 331827179
    0x14010302091c0c0806130503090f1f0206040c15020a0b04020f15071502120106260106050c0607030b2b0203030a020d020c0a06080609100315020c01061a03011e 70
    0x806480180302e400840341000c80303810420034140100182c030307000380c10800c0301d076501c6006964007070780c901c242425140151800301c07104103541d484c000e811310b03100b44200006600d004a800000d4940f10300b1102200c070888620310103c3c68102c420b884a82c0c82c0700716001031150003221744030b0743c0d610131005000b04e9000611034009582c0b07031034040b60003100c1900051a036496405a1504154090000e450781d84914410311110500e107444440f01411103855003069208040f00780318900340340c00c041105954400b00c00700002011540003009102c21100c5206485154803001401c07025500c0e0b415400b540f0000e08c03122411912101e410f44428002d40c5c500c1601c1c0d00b0180c3d400719095410640454000d038200c20072540c01d060301800b89412101046510000c010f040410180c030322907000d0404d03070042040c1000610102c82e80d0b19003001030f5401002000f43c1301d028882e040065800150fa0b42c0760b5508102002443d1030f0024110807540d1b01c1041401d0460307003007007046c0303064010017017600c011803400301d00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 331829676 1250 331828426 331828459
    0xb01060f090e04050c0613090605060a0806120304030b04080406300b060c01060807030b012c130f06050105121b0f13060e010314160614040504180303151401030209 72
    0x3010840547c000804100d407810003002c0450b10180e1002c2d01424007041350010096005d0000d661104d011070f00c0c80d01c0d084004403424510702990f000200340b12581d60600041c084d4190150045540c0b50b95101c4c4020145900d200d0221601c550f85c3c801041000605544842c0c66081214040001b81615040c050540b0115007900c00a5000d110780303410018060040c41060342484d0701400b070011070b00352007132001c90b40706e0103c40d01501600007215061000c42c9d072002d1280b01983d229038010907003100d682d640d070921030014070003803260034421445020b103162160b03004a0010302140c4032108074103180c0c0b260014826903545481045501c440d0b0380a440c02407001d140f081601a1600c03444946847d0705518101c05041018410001240c0c005240402c6c6400468084410f452041c513200d208208060b2a592550007240c103c69071007420040c0c00410740291034125140c090003a94140680c4074061400009032255000311070b602807240e01405100e50103a0000c0040c42005411100070358542c07031 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 331830926 1250 331829676 331829689
    0x1c02130b090c030709230402070309030f050d0912020105120402060912010f050106090302061c1b03020309010513120c051c0302091203040f03060b030a0602030106020a0b01060f090e04050c 83
    0x2115112282000f00500131102d40c041c08900240038100144240300e490550302280710609040a80c0c4076580024051040520032803040000390b80c400130340e02038800940390568444102c40400000142400d00025046000c45c12680482d40c040e1151860484030445910341000e008009076001441017010340c0d556250403507156190031214000142c1d01a6903640d42c0240d90069009404000080f1402d0016943e0034013203480a555844448507070112120f03151010305010888403114030b0700c0642d210300c11764141e00110f2141070341000800c01c654403104200a2024084006000d6110246510f21081c0c05070500d94201030040301190b03001307c0760345160346040182c41d64030310020f500855041d00c41e050070081c480362800b0040103107007450306100300d1a202d10700520000c0e120356224032030100e09440600a2100003904031030199602c1d80c5a5201941c0e960502804903890010440005905407240c1d03d040860b01c0b00d9580c1000481c5454032604461074050700070344490090b005610072994804 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 331832176 1250 331830926 331830931
    0x40519050910081507090b0c0c120a030e0604030807020114250201020c1e0d03140d0209130204050a030b071e080601020f15070f0909110304111c02130b09 68
    0xb400014001403d005410342004000707082d080c043c0c2d6032202800b500315000b042d02070941c0d44002c1d0443c0c03541c00090b01c2c40c0c03900d6034401c40541c1114a81126840032a0f02164803140c1e06c0c040d485d6086d12668410134040c0e40d200303501c4068102441401440b00540c4905a50300d00302c0b91016103607003044290440100e40007909030709214800e111040140071940c040c40160484407080700c00c0740c0500b9010b100400c0c400411450f541c0b16220701a440f0b410540140c405040c000c0300c4c0301c4110345030700e161800c0720025441328601e02e106e003901c00c50100501080f4021101a0f881c05400346e00380a1640d170395002c504001900071024845802c58190b10410380101c010300c1c04038955503050482c2080800a41444a00901d01e90300350407000c61314401a006107140b40d0401c81e60325100b914000016000c0b680c007040e580102c9499400c105040940c1c410f20300103035018078015407400100c40002800c008101e43d503440c400244103101c448527405440c00d103080d2178258101500c08180b488401300003646181d000c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 331833426 1250 331832176 331832191
    0xf08010b22170a0204140907030618080408060a1d15100e0709062a0b0403111002130f03030e04050a0213031a0906060d120207090608010c02010e120405190509 70
    0x200003400150325081c0910a5000e031b6800f078940c5a407d042c0c2e951500c034281400043e1441c6e4a441c0104460501460142d802d5900400c0355601d40f40c40d5a0707001d49528094580412050400703585500007204241103003100c14441001300000701c074001d6503200084000302541d5503517000020016610b480c003401a8410b10340c641d20041810b05142c4c020307100001c0440040c0d02404e4000e0442da1200304203100751120b58001000040580e51f034517040302c11425851505019000f060781c165500c01290300070381307040c4040c0d40701480819144d8003550120007007071001034000b030782d41c2040c6501c40c00c040e0b00c0300c0c0e0030059820b400351070302007114402c007a0010b840e13104851403668081c5100c042d000b00c50549030001103060103055a030604800107803840c0483c2c1c001409010b190100103c95074020010400101600314041c0000303a5030780c0006000702050b03026071000d5400d0080e04001c0c40e2022908010001d00607a05038145400c00c2d0511203407003140d414040e1110000e000101300c9aa50007011842041e4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 331834532 1106 331833426 331833433
    0x181b050310050f0f061207090b0f0a180f08030703091d04031103070b0c0306091612020705010e10022203110409060b090c04060f08010b2217 62
    0x882c4840c0e6170311040000e08034481260145000d8480d02280d03c1da08101d580d1a05800920b1191004c1264480420054080e09034090410110402540b010b42d000c0542c8980d0070b9507500c40f460300507040c41d0b4400f14002c420590302c40c02c0407016206941f101b10342e0303030b03100a811088000042e1004060200c4c09402151a0b00308006807415076422140104031030600c152041c0d4182e2094508602035201c040000e20040c14080703440c5840742c210740e103035000398010700204e0000350042c2074100d0b0103548070300c0c02c90301401c010046601d90407070700391300141d1341c000d003001100348605204a01e1084200e1205c0030000306172803040502502c102a10040b87c01084c0d85803078001002c1c02e041c190341c050708800600c40000b04c10030160041c0d03903007901ca41d00300b0803a103081a165a0070901c02d43c04c24110030003c680c8500c0c44030f85082c03805210703c0303280d1a0154540341e038104115003810540d4443e81c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 331654676 331834532 := by
  have h0 := BRFrame.cov_init 331654676
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 331654676 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 331654676 ≤ n) (h2 : n < 331834532) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
