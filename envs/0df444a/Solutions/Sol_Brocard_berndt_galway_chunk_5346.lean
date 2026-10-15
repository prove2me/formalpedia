-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5346
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:58.636215+00:00
-- url     : https://prove2.me/submissions/0ae95ae1-e5a6-486b-87bf-3085821b69e3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 961330935 ≤ n < 961510791 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 961332185 1250 961330935 961330961
    0x70c080c06130618241407020610080a0302070e07030e0d0e0f0105120106050901110d0905010e311805060406050c030408030103230a0c1502030a09140301 68
    0x301003000360002c607400030075900c1c50060b4410321640c0c9000421190603030140d20060304070b000d680c201d1040700f88080300020707a003003c1810020b0404180c1d030203000d842100707031032650043e0841414803440c56002444a0080e0001801906101c0802e5801a6594080d032003034001c104817407000520308a00076804400b40c3d40407481600e00e12843e44000070001c1d10004100b030710030300701e050102d1006c0d4892020364488040e2400d20f2002e80e401d15205940c29001300b02c90b1030401c82d510350381011070001480100540308c2c040c2c40b0b40c00f8071401d060001d0444644024114080d101411903141c5120364201030106446944c0d032081b414030b0784042c40c44042c001410a1144c10501d45440074200b2800080c803c1c400e81c02400b0401140d1038030700c640b50091005807006084800c0c18401840868a0701c07645003201c4031018500361340740504c019001d04018400800ba00d0a01c81c0070020001a24941c0101c0c500c820302d48051440d043c60841c000d00140c065004842c0c0517881c2d6098880c003510254040c211031490 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 961333435 1250 961332185 961332193
    0x305131203060806090d120b0406170c1e010206040b0c0904090302060613020f0315041d030c100204081b040905060c180d0213050a060f120b10030b070c080c 69
    0x1059010700a0a00c0e0302c5404190310074440050310008001c100003d03a4400d035590150700f07510100792940680240c1c0d004682c02a640d02c4002607640c000c01e1011460030f5154080c00041d402002000760141c1c6195030051011500c3c82c40780e6550303a01040c00c40c2d100e4ad01c15250000340e22140d404550f18010007918540241c5400043d0061580008030281305140031250a038020700180103c505902445074a8100d150003480440c0b2001e40100e0a10035034280030f0f10001f130103090404410311044064688880319040014801141013050100c2a4014a210b0055151514081007a03030740d440d2071050111070b101c221004440c1d55441e60070400c81c45400c0300c12a404d50510103c103142c0b5500964038402c21741107800120032141491010110b03030079001012150030103281421036010f008018101d19445aa82c9004514509a240c1401c05003d400251810f4004c1c0ca180c940e400e080e0262241e514040702120810025000c80d40701640300083e8907048800b041e1900c0c11155500511100140c0c03402 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 961334685 1250 961333435 961333463
    0x160c090f0e070f06090608070e1c030e01080105031c1709060601090f1d061201150515070c0b07140703080d05150d0303020f040b0409020705120c03030403030513 71
    0x265041190281d401c5000e907a103450f0380300b601002102180c0300b000c000c83c0d512882009440d002e10000b03580001d241c00c20300e5080c000c1c10005150101401a124000a0b00201d110300345540518403000a05080c00c1080403541000b0003e07584401040f0850341c0300c54503001e00e4003643d104440f0700718801580801c0b1051818498081c0b07444000c21280140010b4030a032000401d48080f005c568201c50404c1c082a00c039141c080b05818007840020065030300b012044503070100e0b4200920481d4010309050100c4184075041101f046101c3c0a503c150030a10303003042c8501000308128030403a5080742c03c10100746960b140d46152850003024840c81140590050381000070500c103454009003c20f0fa620079080115589007030816409003000c207085d0350040314060021000901a50060010200283c2c00340d0070310f07a4030582c290280e44180c1210100c160081a4407040003000c1202070340d50300c1d031034003e01d08065007440c40d00da403800000c002501309515880822507d4100e5500e18016a40087c80103107215 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 961335935 1250 961334685 961334711
    0xc080c030703110d050304032010060905060a0f0b18030f0f0c0414070e01030f02180a060c08031f030204020403081809060d0311070b13031115160c09 66
    0x90031009003500030480505030703585007032000b05480c2004d07946903c3d418116251510304682861580241075490b42c112401c41c00d000307804002c00c000d40f200b241c81c08540e071400c1041040c1a280c0c06004140100c05046092205070422100d0000b81d401c4000b0640d203800641480340c0694556040c0785425000d2000401c408940c08501d144c03a1b10349100403a030b09207803d171042c001118510b55003007242c03c000b4800305210612a20343c1c00514001454082051a015940c1700102d0348014109540b00701070011504207810f101c01c4200c0141200d0a140c3d100798140c1e01c0c0c0c1090351000a00b00c0c00501e024070000303641c00c0325019002e4051a0098400c40d16641c581c03506d403959034003100358410b00c00440900b018051501e0141244585c40150072850301000b60355055415408880925405005403040480d00c00c1e0803001810309448000c15040f881491820302410381c030700d6100e8490089109140420324003500c4022a00710aa090703a482230b01840504003d508a41c00780c20030025181059a050412 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 961337185 1250 961335935 961335937
    0x12110a020d0f17011503141501110d080f10031e0605060f03101a030a1a0115050403020d1e030806030c2710030c06030f1b021c0c080c03 60
    0x41c65507101c51070070203182e52042d038501c06554842490303074800303100500c00390365880704090050350b160a0228200030446e486085031803013140d60b11107507446d907444102690323480710952403100d0f080c80140001d070244101c020200310004040000f04c40745440429030f400c910050180082da007000c40d800400103804804514540f506105852207414203001c191320340f4000c2d810740004c2000800074040d50404000550280c2142e0842c2e4404e80d203511030707030f03841918288007009000d8803c8255a80c61200700d50f12110316041038200400050a61803001180703900f0074211815241c040340d2020801d5201c0c9483d03545001500030041550b40a402c0d55000c00d904904001d000700130441c00d807a20b000b40041405401c2548880d05a050390081500c210310310751705490190030485a026100030030346c480c0c80e07241d8803940c20341c02640026545d042460758040c0c40e2080c0c1d1014001800c00c41401c400b0301c4d40003540e907000c1c0e000c0c914800401c0e1804010301d40c003400c045628154042052511007038100c80782500e07 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 961338435 1250 961337185 961337203
    0xf0e0d1e110f0a0501320103020f0d020607060207170a091202120312060f19050f0301022106040f1803031a0319050607082502031e0304050f0606030a0312110a02 71
    0x10301b051580b000260700034040303010b04003180c1c800038011180e02c1c58081151884200d180c1c5500700e00342510b4003000d42c030b8110050490707c0c01340002503556800c514044004605402e02c030703c62030506100d580c0244d80e02100950403601d22650f4102e03c1200c5000069450103144402c2020341700011780200402045410301d0321908048074070f040b2810717401060004420506184031900700142d20240190324001c002450056005070005050070306004085c0c1030704000d07407103c1c00008100020800b451415000e1a080e01c54040d40501050400041e03101c2925066400103041c0b540b90a040d4030340200b508200714071044000c045940800781b1080f03981c50510f54101c01e5070b42e4011207000030142801500c1880c010514180032001d40c200106442c481e81102e804024110702080150101081c500c00005080300c0c2d198400b1603890800c0e2808034542200341090000c107802140402c01c540c3d801013803000d038198041c20000710000c101c0080100078000000a650364800200d200c0c19215400280001c3c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 961339685 1250 961338435 961338461
    0x6060111030f040e04060f060e1005030d0804020405192f0c030a0c030e040f060e07022a0102010b090a141b04090218040f0e0d1e110f0a0501 62
    0x140e24190a10312948074440e8044028607070200f00420403a20000c0205070b5442409180300141060000c420041074807881d501003140c0d01c00352400d01255140300204140105812801490700790031742040a0007824000f00f01030321a5a860b0700040b4a80070200500cac808200712402003001000403a850034500c3d5200c0b040029081c2800300c8408107004000451b1030740440c8400460524402c0c410807113081c4c40d04482201040008002c1d2a0340341c0b180c0c0200d021260400707201117407081c00d2120888841900a040d0300456000c410040c00031507a40204080f00b8800100c030710003100039200140d0140424016007508079034150308003c0c40e8100d0350b200b5002200341e01381c2c400b1076460f02e0907946280c1c0f45000342400c030407000b00000c00214000c0e0740200400e824031580780400c9070382c040009040701d5200907020000c5841d040b490100754000c1c400310700c06134900c2c2448841c00610170392901e0801a00a080c10a0140f9800c186000102c1002524040da281101301d036050030180c80c09a000c2c18908100e48 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 961340935 1250 961339685 961339697
    0x19200d020a080d031503050a2901180c0309020a06080618010306020c0d020d05030c1305060d0b0916090509090304030807050d1407030f211404020a0603060506030f04110909060601 79
    0x40c201080c0c0005d120110b80d040300003400e60401e02d8a459010807072900d03200c011701084141900c0541514048103009050f4441c803564140c000000103401d844844801c0c02c20589000c04400050380c541e049502981c0440c1b500c1c080644c2d405001c0740ba1030302090100c0002000c400000002c011841c0c0040030508619820744460715985001640d0b14040009540d012910070f000044054688034060a2068000000b03030014581d500040b0f20523a0021508140c89929802a58200e04000b07403103039000214104141c0385055040002001086140500c612031080c400100f9265007080042e6400303940c100c0d0040b80d03035103001d10b042683c0324400d00c040c80108141500e20003c0405a909542c9001e8041e254514440b0200c04104c0f4021030b6130302c0b8410001c0001101410b020302034818803040c0711486455581d641401d0041188200c2c0c0f9600100030141403403802d10860325a042034136005440e8000681007900c49140078201103c020400c2c5400a1620781007210043c00058528002d00b402c4c0c841c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 961342185 1250 961340935 961340951
    0x312091306050312030702010216050c010801060f0e1903080a050409050106020a17031807090c0801052722080405010305090c1f0e030706030c0219200d020a080d03 72
    0x4803054031400e1280a0303040d04552000660728480c1001036074419442d00c0018903046030302c0e068401e0510700140503602a440740311ba00e4429608058aa0302500c80c1c0d0828120304118910001d021a180c86207041c000e0303143d040100c07036407110b0807100405140d20203101d585a442e41400280240c2103845009016400e0a00000b903150010a54003640750f000f40c5112204241045000c500360300140ca400b88a404529591440d0142409120041d10418101080c0e00070054002841e42006802442c030a451a45046148042803e4609040e80e445250fa400607640d0240da001e8509072080040b90480d0621180010440828000c00c01e4034000d8800b0880c944a105803030342c0c0d90b400c07044115044540401e00d00100291a0750303601d4580c0380703440c0401070400c8101c0441e003846003a5025802003038889842405e000d03014400101044030015041700c86c0780c441d440701440b2681c802c10101d05c00e1407100c81c42203240c8880403484612500130b003050444c140e03079088455458020305413100001e450310000b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 961343435 1250 961342185 961342219
    0x13180c1b020303160f1401050a060501020625090f18060b07020d0b15040218101b030e0105041d01080106050109080a0b0a140a0603050d0305010e071d031209 69
    0x200309a03054000d001181080304040d120b01c036210380c4200548503011102c0c149400540c00c581d441c2d20400076100041101c0c100f00c09060151401c0e42c0002d419074116504101805580d19400d0321300300c40340301001131004401d8a041c0c50074201070300000b0310400126404252154810007940b94480000800c0106c00c1c0e0390f080300b461600130a0802540000703460f2100c004180d1603028180c01510001c1c446c0c503003403061340000e8126881966490a04030064155114924018101103d90420742c2824000c2000c500c614400e0a2000000201489950002c50321564440c10640d0060443d00150051030480c211914007a901c092264100d5076092003000700705540b140c1c0285044450360002000c0c940c0e000d640f0601902d9006141c101c5107951020500700160007101d0781030180c40980d078001105811424014102101d40511506250403d0010800840310102c21075000d816803500e03082440c5030946110ba610f00381a0340d01c3d411f105403100d901c44094654000c0001d46021a1040c0f0110702601c1f03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 961344685 1250 961343435 961343477
    0x9090c0f101824050a02250f090b040b0604061220040308120108010b0112050604020d0510060221040510140a02101805030f07080705031c0f090b0c13180c 68
    0x181d05401178100002c7d000d082c0d0700d111a0748450301c541081160606440e0000d1040c90011a84440100c940396409110300b0705152080841c922070540da1149450308000016244000407401e01001c02d507280982c991448101c0c01c0d0404810382d0543c103503031352640da04200c10590080700c85400340c01048000051400c80c148a40e00800d40180c40b1002c05822185d81c40004110050a02e5001034080000610503807440c0b013a01c1c82000060100048a414003100a19104103401c0c02d04542c040f1408081120342d28109481c211103084420281851000d20100c0e03056000c0440c00103100e1000c1429544079801044c044543e40c5201030400440312b00b0842c41c10004081d40b03000d0000e0304100410300c0c09145510060130300600075245645000c2d260741e10640b45501202801d010b1038907122a4900c0c5a070b880c0201c042c1600c00740300c184085461919102ca01c000e01030720090304160005030118280d0b80440c1404c2c010024640b000c24440385140515001d0610016400000382800083c8105240000c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 961345935 1250 961344685 961344697
    0x180b071506090525022d12040609080f1f2a03060914041a0709120b1e1017191a011e0e0717100509090c0f10182405 51
    0x2c04890041004480746d19a00c0c2c9443d100c3c2ca0b540c0140c241d009000400440200010a05583e828207132a14024559050440d43d00c800341440e0045000c0381c445803001c0d544d10b500488010b4000810355610500b6031050140c142d0030080f207499040402000c95003542c891401c6401c580d03c24082940b100e000002454011038000304001c100c0a44405090a010078180d0f00000504001910540b110302007600414100012203080011408001705803648031b800c7d01c0074481e030407090042810070101d640100901401f03184003600901100b410140c1003049000144419001000c3c219012400c00e40000c03105034449001c05e004150000170006102d800950f040350814082130049420520501c043c42005880d500c1003209021490580d0152007260714004e442050340040340c1403411060201e8000002e200009039000844414429107512190540381c140494401c0d0304031008400550760020030540c0034904404005021840842c0c0d5070140011a20030b00166407125001c00703045805107c2d031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 961347185 1250 961345935 961345963
    0xf0f0c0c120a0c02221503020f04050705090a0305071d04030f11030409020c030a02010b0a1406030a150821030112020d03030905010e010c180b07150609052502 70
    0x103a084200800301c880080c0a011490f80343c02a041c2c40603030000340c40b498680c001001c2000c00300e2488016128144600c550320360301114242052071464002070460b504101480f801541c42e0000122818411012120241c0c001000c81036405e40320704219582d40b0203030044500718800820550108804000e0603841142d141e500c1200d540342114080301c141040380c008401a02c018880844c5088940c0007502c44d5020f00c0380250340ba41c402c1c0030b000342550203040c000d6024101066041c8101811568000e078481d10541d0f01c25901d0f00c442d01c03203e00a100300203030034070354040c040300103d145031010074a07865401d0b281003200c0c10300440c078620300d41c0c51100b881255124902c2c00c0c030110041c10300180c0564064042c0c203000600d8100c2d910349600355000400140c00f10303551230303815480094004c08036030400544010b00c070310b1881c14005032800601c5400805454456681050b1f415001c090300140054144904140104e0501c2c010400c2101000140b4201c400343c14000622000d10004440c2504041 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 961348435 1250 961347185 961347193
    0x70e040e070e0408070609021302090316030c091a0406080102272202070c030b061005070c05121f090308010801050f07081302090906061008070203070206090103060e0f0f0c0c 77
    0x641c1d80c0d02c040175070098000312141c03915283c1c41c0001d03030354107000c80080c2880e80e1405a554801e041c10035043c020340c150100750403d4170107400c0c0081070040c800c41c0b05603040340c080010b281040400c44e808c2c542c0300c2680766074014109400421800d034113401030b240032648402d4035181c4510411050340c2400d61600c8840e004003e0008486140b01030300064420802200b400600d88400c58441610403080c60b041134503010318000622009090842c140c0e43d460314949021400c040440e5590300b80181e092007100d12884000e48602540c190030301c025000c0b0780f0802035100030140b0284030440504284003055011034003040000500040601030540b00e5440d1001a1915580391700c8140d80d02c59026290f03440000d00056517100684030810b90500419043c0b00030001403074064104203040a0b402138030301c00c000720a000d100d14aa0000245c0c0c40c1c03213504459030f907111800d0200403070051480e68042d0f00205100d6081c0012203c40c4042c0900030b04060908004903540c0c4890350b140c621521020400300c0d40 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 961349685 1250 961348435 961348441
    0x706030b03190b040f06023415051f0906060e040608032223030d0201020702090705031308030c190207080d0305090708120c060618131a070e040e070e 66
    0xc010188581c41841481c17004007504030383d02c0707500803a00b00300c0000f0f03502d204a0001017142d410414407581802da1016100104041030303903034140f0014440c203044066903100d40100380381c8010a400e80c00c1c1c410402080c6591240c0e52640c501c007820403881902d000c60440c0c00001c3c0300d410680074260556401e040110f02d002c0b840003140080c0415428a040e41407401000810343e11400c2c2c41c3d10b00e811140f121090003240040c01010f08101c0c07200c0d100000d40e1b05c10400d01d80180c0302c0d240000e510070490306103d034a9540c1c1d030000f402c0100d00c0340802080e1550000070082e0201000000d031044644a4242c0c05000100e07080583e514040c502a10400703502101c02844640e10070340103940d2007400003040c1d91115554064031494011290341d400911500403440315600380003000017542c030400468600040f10b006486408a003180500090040c00461903c0410300c04064035401c0202244995102c903071401c400d00600d1002d521403071500c02c078204901c500082c038001803060140c6648100e03406484d1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 961350935 1250 961349685 961349693
    0xf0f06010c12140a030b03060f100b07030c0501061d060a060e040f0209090907231c050a02030a050304081e062208030411040c080405060402060d06170706030b0319 72
    0x1d090800344100300c080880186191544805421307250b9485c2c80105540340b10310200b604041009000c0d9108400c10000c02501e220841105070032500a50146a82d50b0907a04040359840d6007803002412960030035030300244444600d0202c03a80802c252640040c96242c139820851150500d106400000b400103a05240c5403900303a0040c888400082001440c004440021480b2030340115505181a040440d04104000d14141d81d00446004040400e01503c80388000074006500300c407885007450500703451801000070402c0038580c030540003411114040300a103000c40d903079801030080140303c0c054171404c030709803103c5003400d0010411580d000e44410780e141e062494082c808400b041c81b185c942c2040120119682c81d00860042d07020b000c9482548948100340419101100b60000c1000b2120f8204404540003090258100b80d0440d6481d5440c91954070f80006848241c010b0714600f4540d0400002c4600002403400845c2d00c0c50f1028007802c07030b4010425450303602e1549500b050a80e240301280000d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 961352185 1250 961350935 961350953
    0x70b0310030228060e121b03120f0d0c03180606031b030b041b150f140903031815160506101503050c041a07020f09072001020c0609060f0f06010c 64
    0x229025100104040071034490307604c0c000308040b1005030058901f111007660704092000c1401c109282500c54640030342c6210080c0d441c42800480b55280e81e54408000c00341e4440d8020402d1280c4d00603810480d07214908090000344424030040f10f139070309842581540c500d501c04001084035042140f104c46941c0b55212040b2580300c400803020456148100800c040164041d0002584842da42d4291030306084480600b4401101c54001d40300da10921018010fa50000100d60521407400fa80c0081d411a81c40170885046000c1003074001c0b00c2e00403030322000301a04058444002400f80c02114a40d80700c1101c80130a64200d400780d0a4240400e190f0040300c20700a800658102d012000c0103071402d0395502d821000c215150f49100d03c032540005804065180161800c20010022a02d1410905002c600076002c0e0b80301c510440020441c034800c0d20301c03002d0300f0750542d0500500c29080c0ea07514940f18581e203880c2c880c04c581a105804055011407082030a80000900c40c1d80181c607810301c01c2d00d00c0d48800081c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 961353435 1250 961352185 961352207
    0x302090d020303030108070314011527110a0306090e03090d0c081204090509010c120e03160f150e0d110c150a09080309061605070b031003022806 64
    0x488030300300c1032500584040000b1340c000e01440b0007910045086103403130b10182006418401c2a681081c00b041100300c40d80d10683c00312810b05507280c14030400d5400c0031f14510080c40000112614201c004025000035000821401c000c030390b0200103541c0c0391110801103901c1014010f86aa00c01e0001c0c00083c01c009a03d086400d0143c48003820780d56540c40c43e5480d104000c481071800c2c0a0100d4108480e0046010b840d4015120304028001980036650091040c2d00c1885100c0180e61030307034640e44a20000707208444008031201e00c1c20303c40c01132605000c00d18060300002246e40403146414850b404640384030700906038101c0000380254490700c510403a880d0240c0a130011140c00798130030100c2030b5500c0171920034006880040d6661154504880034025021542c091104ca40040190401c01d50311030702203070200740392649034040403410b178200300c1d181c60216006598207510020601803000403031881e10040b24400c542c0c02d145211507c84040054884a080344240510080280b2889020740c0c84c402c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 961354685 1250 961353435 961353439
    0x7081b16060e0111010e12030c1c02181c0b0a020d11031602031e03060f03060a09021c08072915041a09241809010c2c030120120f16030209 61
    0x4c00c00442480d207909038071001c11480f03491540052800c50380050540400b078940c3ccd08a070605080c04044440650001d460760300101020254000070b560109103a054502e101c001120400c0301c1200031130403a0895105440c044681d0801403611094148000219182882c0080c1c207140c120f6004602d03440c1540014003a994030a000b01503000302c0f0781b820060284142d4080e900414040940e005200c1150414051080420004400340000c00d100c103003140c08860f0b00c0301001c001c1c41c00301e00940d10b40c035400590107016065048140891000b820000280d00003045404211020b1001c0007400702c4046040800c0d0490385900004018030b8031044c00c0342200320300b1152440d0324040c01c1c0024884089150440703030201d0709078091102c4144248200ca6040c1070704e05044510b080748114004070380d52190f00d43c61020300c0802e003005054400307420180c8001c43c41c030081c00418640110b607003071541006d56003060030022200041c1880f401207038a180100307200b100d01c07440400803100860107548560110f075 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 961355935 1250 961354685 961354687
    0xd0903020c04020c06041709030a0206160b010e0f0123060c0a020a0b1c05070212071a0a0507030507020a1101120204030f0b040506010b07081b16060e0111010e12030c 73
    0x480c1c552200c0c001803240d050070070041c01e13032460945440d6040a90320f110740c100203001404002525100000c0140304190120361103501d5210101070014100760494000f41402d607681c000180300b50010201c280a40c2c1180a82c10786030ba02d43d2503013810031010601d25000d01c0300609800081d81044001013040c3d9400c8015641014100e8010962140c160f81c802da140d0b440c001046000d02204074411786042c0302e0800240850b05103810002d5840310401c030700ca1503600000403804200040d440854441c402001c9100032a0324180d4012001000c0442d511004039051200182c6110710119100441c981c1c8408641d00800d088001190360040841844440903030800c800f0010031901450404000d00c0750a40c1740741032910b45401d5040001c1a4460354111038140121000a154101030b100d103040640418411114825112403038403050240400c4800903040c40400e0440d40108820b030884400c0c0c071400cbc2c4005400160714200e07400c018000e00250400720588600ca0302960046400022010080d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 961357185 1250 961355935 961355953
    0x71101140c010509030307030606030b0f151201060c03090806040c03060e0c04091b0b120f060409120e1f170c0405030f150a140a09060f02161e05030d090302 69
    0x71400c42e002544c1302c1c0f699910110400c103403a40c0c1070149101401407803a080c050b5030b210074003245411300680c19140c8130f115800000c0700d070240e48005840901c4600100b441c242d5a5602e405042440324010030340015003100307000302d00d030980001d031940070307070760006031076015038910344600008200100500085005003604280690744074041c200850740200e58603a2440e60307c0c10001005680c42c1d001951245091040184034904580013a612081030750b04402e007507448100040040c1802d280c0200014403401c080040b00d030340300c045400400c2041d100720b0665071400d4441000c00c0d6a00702d0900002d031011419401680341611340c1c0d90040c2e40c6d4100340b403c241e02e640c0000d05001c80c11540500c65402260141300307841c10b888015400000310401001611040070700001040b0740200144502c1d91590311003000c001c060340c007642d60b000303001c802103442c0c1100c0700040c99141d104140940e000d4800405107480e041000e203c9400741d950140086180c4102c0b00080b0380a00181401501580030740590 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 961358435 1250 961357185 961357207
    0x10608010c020610061403241c0c061b02060706060b07030221090a0b070f021f110d0804020907180f051f05040603090c030615170307110114 62
    0x141c0c0c4254140c6401810640c5001541000440c0d0941d20081c01c10020301c51110f0085108800c494101307500050210444240800c007140e80030307002d0031243e0425240d8034900c003031328951840d000c0b04500c22040000d100d076072103008441840f001e0121031032042035a0302403001031130140004c200d4030307108000214080d41c0c0c1e405e090450b50041c2c00140c0260704550140700401d12441c0305424944840a280360a000d18540401d48402c00c46c0980302d44400d00060200602051030003c012150340101412070422003200002e1a40a031010f600001c280820702000800001094807070003e01603941d03100380f070b56980d0204815008050290401c2c85881c900030320902c40d00003080000390215894214001c3d240405104d1140300384424070702c281203140078441e03805610800b1901201e1507880d001c10009c4407410300011001c100d0348010aa00d2500c130303000c0d50000140e0403040403248145e103000301e00740d24080c03000e03242d10501d0001055503100c112a04a10b40c01442900d50700102c141c0550f04000400750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 961359685 1250 961358435 961358441
    0xc0c090a05042f0d05010b150901020f0601180902011b030c38060411070b0405060f1308031810060512030408100e0319051e0403050d0e010201060801 66
    0x4140301401d894000300018410412980e0b0043c690f450740c0042001054039040100b020324800c0c19102d14403661007031003808030035000131549850003410a1080b140c1798004020b00da019141a9001d0300031001840c0f01c400001c0f0300c460488641e1171501c030b40440213140e1a4020302c07514000303c0c18420045c102e9002000c0d08441c80c10503d1294803506481001c42c00c010195040c0700c2410480450303071400074010102e080d04400720003401c0481941d05515020006005084007401d007055081020500d4801e200c00308418a00507070055064075820f440b40030f914121008100d4100c1b82e002e2104003080000b42a00707000315801214001c03420f8107072140742c21280c2400707442016045035944038201484107141085094002c1e070b14105c0150b24152904151544070718415a1b107194040c0d4645603c80d650106108030350b01160011100b0002040c0448050004d400c400b18603212100320b424030040c0346865100700d5040e641c106005041045041d40c0c2142c0440903290014110754890100066002c0240 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 961360935 1250 961359685 961359691
    0x90317070903061401080309040e01180b1006180b070312110a0e0103021c15030b090f0d091a13081c0e040213290406030f0b04050603030a050c0c09 65
    0x55a51040a890b5040c040c054442807051074142002c62801001100d40010444961010a80d030120f441812141c01c80e0040c06109568900c042c0f548a03140108001c03203005c0ca100344181c084400700c1d9900d40004075210b4141140d00000b11a105105105404880c0040c2c03a0040c4039151075040b105200c1d0517a020758081511018900300081076450720a44c10a09141d07a0220a02e411414035030041825002841e900c0048801c0540c0c8125201c078001300d201c4810007554016106d0912800d1a407032031a40c0342504c4840380501e008482c010759000d0310408141c4125480d1540000c2030714032a0f007030072aa42d40705aa08454410b659030380000e0b90001400031144c1c241e0380c1103c01c000d001520001070070307555070310f240c2900ca248104218014060010100c01c141c0b815400c10440c980c00700c1c81c414101c0442180010344410010900042007907045e0400a0590034510040c00084001d0080c441550421b403101a455042804100c4225102d00040c2259550000413141020380d9040490704c18070b001c2d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 961362185 1250 961360935 961360937
    0xa021306051009210c0b0d0906150302011704030507110105070f0c050406060e0904030c050307050102031501110a03090b090d06060815090d02030409020702041b121a03070909031707 80
    0x210f0b02045400760050540401040f420440c08090f041c83d13031100a5442c0c0e038002c052081901091003e00c10303210b41d204440c01039121008101e0210341c401c01c444101c1103880120300140b211001c0040c101113085001b03009540c5502e0340d13400d1030b1710359071070300354801a080704141040003d1180311701142907440100344581c000c20f0420b01e4181002e0500041d01c060341c00c0081440b0107805501c0c003a841d4510903a5000380c05140005070ba80c040d1505c54103510803401c0180c074641c00442809030b80c030000307803c001a007a001d032245621402030726400c0f0f880f103c2c0000c0c05804136454400070400740300304200030301d84958020810071010f003159580c03070b00b07c0f13140703070070002141d403040c00416060b81d0a0300c52107401420210040110600c40b010007035503031055001c1e5205247d00030580c20304644880e048590b03400c00031305980d42c0d1140f200703400038002c41c0805006010103040c000104201c502404040e0000c140c080d001e80182030500012001500d5900001c404110905449044064850804074040c10031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 961363435 1250 961362185 961362197
    0x23060a0e07060c11040c020c090118050105040c0c02011d03030a02010e0d020a050a080f0d050f061315050f0a08030a0f02071d01090b030717030a02011a030a0213060510 74
    0x5920546071500700d080c0c1040301801800031081010882c01640d0010141c02220007103a03190321144100c1c2000c2e4105004ca820000c106c00101e0303200d892030311504403e441400c08122030783e602d030100303c16600c0d0264180e02041c0f64488203c09940318400c102400054040101a040805004a40303150720220220005035910724940c811110140720354850058544000c1541e6481626200c0e01c40d080b070b44004100b00700c00100c44031544400002c1d10320310300181c0820040c500c5c110b0300c214901c01040355070034828038151844010591080c440d068a015813500c00c0882e00d03082209100c0740000f801c410560100c0100c1c0700142403282080203044400145d036643c1d01c281580c81010f494800140c0050300001d42508245420048ac40502c60444580200100d07012190501082c10404150031070213984100040b010039201d00000241060205035000f0003104520742c142c8000500c1944c8419410b800c01d644400c050f20f425005030b11002800303100014601d6072403000a5180e10014090f801188c2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 961364685 1250 961363435 961363451
    0x2040602070b04050102033705031e0c0306150705010e0741040b310501030b0403031d0a0b040b010602060603070303030c0c02031f050c0f0723060a 65
    0x15050240714024454a0107540c201402c0c000080e440b80607660360b51002c034903000b121182071884100c480d0805d94501c84000c14070b204c038000c003d1141e80100e988803002100841b41000184c03804002c40d1103501c00c01042030454846004102c5009160305502603110000d11114000c5113003032184804203d0303060002e02403180390031413481c803c440742c4200701440e07240722082c4802e1030412403600200000d95500d0038103440244000030b005000008540782c0004039a15840c8401c41103410742c40d820754442261240041909141c8400d690003404003c041b40542c00200c0c0000340280c101000c5145144030b41d490070640c504400e40303408100762040e244540140e062100303011038400740324050300c01c0c3d2015004610385070000c01d64608240c0f1000341015542d10b171100b42c640c4a1400d506002d580241568010f421501ca201d402604100090304043d103410040390301500c009080b03030801d4141024440c10443c41c0d8030b5503010b0410540e000020107502c0d100c0300400340c01c103208482c802e0504d9040081c0d254 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 961365935 1250 961364685 961364687
    0xd12082a030702010e16050d02060d020d0c09290d06120305030103032d0806130e0a051501030c0603020913090302060703050a0c052a030c0d02010f20030a09080c01020406 75
    0x44080a01c90943e801001a50006c1c2e8004000801510320a950078045100c4a20200710184911844440303594804a402da21312000d0350400c0000303000c5a907846c000359072100101150418410024800d13200e00c0e0b13210f90949003204001c0c0100d035184500008040c5e41d900e2036690000340c3d80c0000c600081d40000148100344e0003084400b500540744403206003c0c5415001070b80668856202c080074450320600280740d99861110f0459004541c40042c480d1310341281c102030b40c80303001000494440c060b11822044030200880d805040b0b9070003680101a0a1801d2400d4009500c4503071130759003045880040201014441c0101e0b0303442480b90340180060710300503000500301c41c8050686c0c4e4009052502212609a00805466a0034910091040d20b1050085500c3d02c083d11446019020f001c04600d0b90400e08000c107014108512a030024408001c20018003411500078000c550220000c007212101080c1a09010b50740c00072402074000b4202e640d40e1a0030700150010001240d007a90000380a00c051 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 961367185 1250 961365935 961365941
    0xd240606050408121306050315101d0d08042903070801061101060602100b0609030109031106070203030709030611071a06131103060f031903031a0d12082a03070201 72
    0x50a0350300300c2142015903030329201030785d00b810340300700401c00401102040f200d40e0069905100030301c1c000d040620442c003202d8094250740702000c3c408014800304104549900340003001e52078066000c5940e618080c203003514001504503507803031801401845486105038600c00c0c0c000b10701680f06071f16100c50940c940080244852400185942d00c0e9060034410445203400265208414040540c00320305100a000850030310f02985a40035419824070210740c041c550010908610907506400b55009996200c805998a104c1901c513040011441c03001000403800e06e500c1005443c9005d109203203440583e46400c2c20701c006603603000310500d07601070a021003032400d183c4c00a07522914040902400c840c00d1500d6100e0300005200d06c0c001c15030004080c407207035410f0002ca0f88504d00a001c248505015080003401041c0c18009103e000c040304001e0099840c0c154200c50815034003400c200c0c2e200c0011403045400c030302c02402c0c1c61849606048500748020121003415a00820300381c0450712441c00141c000d00b9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 961368435 1250 961367185 961367203
    0xf060a05100b1201053601140d11221d19050307140111030901020304110a030203031603032d0605090103020d06090c0302041103041209050d240606050408 68
    0x440020018030f80941c076100c07409811203201b10b610300b41e00b400d003a141e00002406240102405290000c2466240c1c115600b290f050301c544007001e0100900328400d001d07100d10306c19405000a54280010380803031424441a01d00b00d10140581080c0c1e06d490381090080ea40005003d80f0a0680d03580604404242042030761100001d08100072031608880e200c3c00d46a126044026100c10b070160294400084250415200c140042c040703260703070746004d28026000b900150360032109400700c0c403411a454500303c42e41900b500d400502451400012100d00401d04c012610102d0a043d00c03601e40c40d001d200305d50a40d42d04104261000391004403211040012601d4a811191140380c840c0018005070302d4480b100b01205034040d000050100d000e017055801140644e2000b5401070030440010241140c100180d8051846007001100c0b0400103041616507904501901c4e4108180b10400d2011845408040002441a060100220f202c201040c010340d000303038000030003180300090108500c07070007009002c2c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 961369685 1250 961368435 961368449
    0x20406061707090f14030f070f03060f05041e050715050d112d13170f01050408031306060f0305010905120309070509060105090a030501060513020f0415020f060a0510 73
    0x6504003504420010705a0203000d84c082c045803405c2a554604120681800703090b01c04039207843c1c0e0f4a0080114280f01030004075001410008542c140174054064540100d03440310800d0621400009500c80340298100144c07203d100301d5400280b441001e00413410040c01c155180c0340d45000c1c15a0880503100340001800d4540c000300209500c0f004100e4440746d121740c403d003c001000040c0f400c0b1002c580112011010050301610002902e06c142c030360a02c0d00751000805840540c01e00014003400c844044801801c0c00404000141c581c10740007020000080c480c002c0050259180c0415032285030251700b084485030754a04808090000810454405201109d166844c1d49401500707282c03201c03014824240102180c601043d44d03070b0b02a0b020b95602c08009000300f085c1d2030352411b00d1800780506119450050340021030b1030328200703402d0003111001c00405a843e46060b25140c0300703079003546074440110114002c01030508800e06060058031702076000550041200d0034802c860036018503040c2e11040b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 961370935 1250 961369685 961369697
    0x1e0f0311150103050c060a02030f04090f0b0906010206040611040807090c090e10030b071116090e1b0d02040b09070804060b06040501020a030f050d14010e0c34020406061707 76
    0x3c00601c0004001c500d4480c00d41d141078491040c5e950170fa10f075001e000840c242c030fa8408540031603a24403903801003403041d0703450308180400e08890041c400680001d0320140d0041e040140011b02080340d640204900e4071121414500c4d20b41d640d012039090400507001101000d840b5680b01e0031041c1c0c07060481014004c2400810707843d0411450040701a031203484010141401c24000031542400b84c104880c00e4400501502d480c0105402e01060300a568008d80940f5440c290f2240c0822a0000302160380ca09003000003ca601954020015245050101268025100e5046407020b44400388810300072441511001801d0909240c03820503a5402c00c0000d008150a100030001d9a80c0050410070098140c24009404d0520020840d80c1d4401d1090020300c00e820854101110303211512000d048400801c4001c2654a40171204c4826105010071142c8580b1402c00024403010100400301c0d00798880303070110340c0d4800254041400d40c0d60b03c0c1d0101c0c010039880550301c0380602004103c2d5034030000c00e103006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 961372185 1250 961370935 961370939
    0xc090a050702030a0c060902090c1908090c0f04090203070608100510140a030605030f030c100912051809010b1c0c0f11031c050106090f06020304031e0f03111501 71
    0xf0f64a0103400042420440707032100c032005102d050f50000c480542c021700062602c1c40c102c0000d404c0c0e64484000090701c0500b1000c0c031540744c2c0c0300d40784030342c010280503001c0c01605100c00d04000480074281310003584665030b1140440160b408119000003002940c0b5004040c4c600a048000c0d444042d80c8202c0c00b680100d0f070081e84a56002210b24040044101c0d01625898a96822001002690403164061145104421000000101406215400e10101d0390700c2c190341c0390042c0a403840c000000b0861700c5120324404609001c0c001030300754100300201d01c5680d801900002408080280c0c400d03401a440054002d0854205620f040d146404d0b55600344170140b0345035002800e00c205c4054140c100030014007402104001482207407030b40f4424000200032401110b80840c0100028420b940124042030400036502c004004803000f100d0054002c0c42c00c1c903243d5140d411941d03a80400f1808421002c82480e80083c07004259100e0142c041e81d900303503802181081d00c070b103468000c6008401140001c401 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 961373435 1250 961372185 961372187
    0x30f010c0801090504051c03050a15030c0317130303050901080a02070b0406020f041d1f0b070321020c010c1b051b04090c33080f040c170c090a0507 65
    0x862411500c2e66140000c4c299241d003081405d103021020020341e11440c52429139101941078100902030488020f04004050103110080d40082c01444005d0050461920402c00309e200a086000742c5050301c0c5040d4070b041041750081149907541e40003100810b2002c900f1003020b590010030b8691003480c81d101185000390640702d00050050040c802400a500090780440c51884c0b0400d84009091780ca400e00800c41400b1000c0c40400c0c02111064401641c0502443c400280e01083c84205c49110384442e01c3d02c00161012104000701e5003c1840c80b03044001040e401c1522072009082c01a0260000600580310301ca000707088141003c841c00c0402918903103e4046207000c00c9075140c0312003000d6407507400d15065021401a00714514040d0914007640000503101346502c1c8090310b460300c1104152036100540000f6a0860590341200000614200008140544008149800c14010401030f0700c441e40c0c13917007815813142088440040640048a030900a81030138180c054101e500107a060000b0310346610 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 961374685 1250 961373435 961373447
    0x1f02090913030504090c030f0e070b0a0e030c0d06090c05010305010605040b03060406033005190e010909110405010801140d020607060222080f0d0815060d0c030b030f010c 75
    0x1c0322616014a4421020405005a0880d0001c0c440d240080c0300b85440c019019006000c2543c031120322a0410070349541502010805e901034072681000d0714100a40c0c202d04440c18594811000e8143c0700740c1c000c4e007041359204492019a1441400080741e0840d1070701d4840481052503100783d06141c00c01d80107000c0c1c190000c2c00e840a031080814501d440741d640a001030040d12580c0e101030030900f11100401ca00c003821120520048040381d010110b600c0d03200004803050b110304501800c01480140e03c07000c0c030314480c1d000c00c14170540524140300704035158031030001105c400300400c402000f400102003001b960443d40c4540142800b14012500d0020100400c908000780d540092060100003404002c00460364180e54140000d016104062040d04103400c995021900a0b0892445580c01100e6917003070000f050460441d00b0364503a01e8a44902a00480d005904010a0340c001824400d545030001c8030301c18040644a42c1e41c011416503450002c1c14104440081a9603003030341020705009080343c000c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 961375935 1250 961374685 961374691
    0x21e0702190f05041a0a03050d1805012109150b0a05090912090d050313050429011d060310060e01020a0308070813061a0f040b010e1c0210021f020909 66
    0x40c401056468034040175000150402d2105507025880981c04001e0120020b0101000f04540d1039140c80c98006446101c5240120311489001031403140e140000821b2403100101c2a404a240c04141c0044650301da004803003180c24400d4201e592a455007045207000340003c00101015900c014450800d507034500e840e248800c0704900b100d200011800156200c50480310060f42c2c0001c150307500d40f011402160003425840c4206403046041120f1800a0740b05a20301c43c415107603507044e6141c9110820015140d0028000e5000410740784001c00943c1e544550000303510441d080c5020600042c20b10001425501000c116181158024580440080e4108507600d8010366241070206c216650883e100081c04012040100240c0c00d04105412148204070161543c0e00708560340110269004c05200c2100c2803030403128000b494a1003860410b06041c01a405803011041c41d20040841580101d096240d1080204006a200d4402395a01c840090030681c0910b507a075409600e844c0710300c1c0000303c0041010f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 961377185 1250 961375935 961375939
    0x9060501050d03120e1203040b191a04150f0b0309060708101a070f08090906060913151d07020d0e0109060e041d0321010302061b01021e0702190f05 65
    0x21310b0041e400306200b005610342c1b504000440a540c1d00d807903e0038850b040300c25039151283c5a9913102c0c0d001011040d00030460740c500c65060700e2410044050810000c0d00302c450840b0b000c4030344a540481d08509444201c00034244044240d13640c1e040c0212070905d48400144038104004450b000e0103031490300031078110125400c0e841000101e181700c0c950180301d449030543c010110b80b2100c85001c00c105000c00501307a010000c441100183c5d4860081c041c4d03501c1440220f0fa0f02841c480329494105405074041e00d4070030310759081e1040301c1d911582034101102e0000c005114043c600741c10000b545504116105030780240b803034217540b0003401d02c001074402015805840d0038800305484400294845078401d0003425040141d1801580d5900303c019100e43c441001020018003480742c010b90441e45034038040c1200e40c09029145494405042d03d40500e01202d00a007855400308000c2d1f039221614241d00701c00e00e0007040d4140c0c3c0c7d0309c11441008581d0196012024a106400e817080000e00c0b400c0007814200c44003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 961378435 1250 961377185 961377191
    0x8010312090518070e010f09091e020d062102060d0203060334050105031012080f070b010f290a0c0b010b030402040c05160321050a09060501050d0312 66
    0x4440c009540785540d41e04180d400c1070301c61031004042020341018501400540e1205400d5074144001141c0104007480c2000104401030400c100b402c4803a40700342a048c40c21040e2040e00584a10020140c3c1c0c04003481204440d120b410901140d0b054541d90b40428900c0f0700c01d904052090307804a4035038003c9a084128955010001440b541c4047c0301f03890f89441e4148415214541c1039245101d0080c0d407403071380c3c55081051071021134254090001c0780d010f91800507500e13a665142200756040c0c540a214101c1d00c070345040c0040c0301c070000c90402810301316101c1c1c0d841140f558100080000c172510300b1350003d0100b11040320a544114111108140c0052a0004007a502c000100081d181042c900e0740007401c0d26410000002c036080901c010390300540c4202d070107010b900703e910801c803114001e0f5a074001e0307044041c1e502000043d0140451503050155881c4d107502c491980c01e109022158100c234413404558981030450100003891140d1405020101c0c2c6545040c2c08949008004560921405241c555 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 961379685 1250 961378435 961378463
    0x108130f170304050f07050d0218071403011401120603120804171c0e06010602060c030a090618060e0319050d0e0a0f0311010501030f0803150909070e060d0201080103 73
    0x2050703550203103400030190105580e824107243c0f0950b190014003208281e0300951601180b503241516000c04400e400400d0300e00443da420704103642c1031901412000501054040080900b8154400395008001e040301841070104201d0000d00f00d4100007545180c0c0d9450000d00740009a0f210310024841001c0d4904002c0f80e030340b2441c04840c6a006250400c1c0f0101b00031a1001480d0340880c110b1101e01041c007401c0c0151200fa030764107036541100303024410158000c0300000b00d1004c60f0801566010501100211746c040b03807629101c1c225034101c003040d50404107504605061020b18002c014602c6038050082d0300d131007100c1007604e003400604020603040010000d101b64040d022500034803600c200780400d81d070040c0d501d86009000d80d5a072000c220049502ea4418180141040c46205c0c126a044506a08406890b13561145140c0c0010100380400540d440c200446444541140d072052444000400e035141c04c0081207215500b008010901c10461800300c0c100603640888501e0440381c1c007c01201042c8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 961380935 1250 961379685 961379693
    0x606010c030906081803042d08062a03101e0308042304180c150c0222060e01061103190c080f07060b04060605071101110a14070f050108130f 62
    0x4100030b41045144000f04001c0740d232401106d61001c002a10743d001c6c0321580c171800740068610710144201035a982000300005d00c0702e600313020780b10141440d145018070039101440c554070042e0015100c0c1e9491030320030740c42408031803072910310002100000051546414919540e00016115a00981e1405001040c007101501940c015088115000400a025102c1184a003812046085c801900c0e0781c50703d5100003c04030040350344205080e81a903148030350305900740c007489040e50f5503040c9140c01c00940c00190031042c1a9125100151000e00001502e651601d2402849801d02941241944c2c0080003031201c1140102041c1b800c100c0039080c008000c1c3d5290030000c10a010b48507200210060009015080107541d80c032607414640102d804002d4140c42e028119068058503c009203503403140c44040026600520356042183e80c00b80031549188420b50340c0d01c4584221412990680d4440c0b0070600501d4800310201c00030701400e191414141c40c0c0000391226845450708060040c40000007440d0600c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 961382185 1250 961380935 961380961
    0x7030c09050310050f07092d03120914010e031b03011d031306050315010309151e0f0507020a08070305090d300e12030c1207050606010c03090608 64
    0x10000107080e00c82e00342c1c0080f603000181104640b0030117114680c4000860141c010742d845c0094564130900e83d80900e420940418824412048000f600140c8240010020b107015480001c0c10b62a0760311034104038502088450340500208107035060101100246105440003c0c0140c460325100130440800020b07900440d00405004124041c1500500400410000c00000a001c0003640c0701e0040c3c003140d0b0b0344108a489001c141c40d034403542c00280d40059903544c441d8001108050041444900410301c0502c480e0440306294410300c00312860504074a5104002d1050f105011440c00c0c06000c00e2074030040c020349502c42d281c0001d0032210080380c00001d05100b40c0c25a40200b90140c0040c001400d5030501c2d504826180c104e40b204200d13007030b1041d44400b000000140340e0101c0b5485905926603c00c0c00c0199206e003148001d01e4901c0107000a80e0501003c0007080310b035001c1040420360790503e90511030f0500900500031410700c62440c8580c00001d5002541070100c61903450a0003103900e50805030242 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 961383435 1250 961382185 961382189
    0x1c06051b0901120e030a0c0c080105010e0604020901140a09050f06070b04020d050109051209130b0307183c0207020619030b0315180a08090402130906080715030b0907030c09 76
    0x1e5480085400e02e46d40d50040c810000603402803610307d03100d555030a00c65090710824050203500080d01c80206165061540142488140504110b4202c968900000540d604428009400502d04403020013660920303d078011290f240c01d42c0c40d02d18221150321341c9002048054402030003100042e4820050100c00e41c4030402c0c0f150700c401990031504110b0408811900003030f4000f03105054880049a400500b0300c43e020721010040c0142405520b041d92030130300d2901080c120500c198a07800c9050071030850380308015040444031004e00c0c01d00c0703540700200303090010520a446560b10411111000d80c0d00e41044e02e203400d15003a04079501003d0000100c019100b20001310341c26120b20043c0c05441524010300e2031080c525a20428401d202000b112595600b00b940090403a4204120002c91400c1a40092580341054902c00100c99a150001800c031003d6030b20690103600000828013000850595440d208011441d0505c07600e0341080008000580160200050565510bd04031949015910040c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 961384685 1250 961383435 961383461
    0x150c140c1302341e02012c01050903030417100c0206010f0311060909240f01200c19060807030203190c200c040c05070b01031704051c06051b090112 65
    0xd20102c413a110a42940080304124041001000248440c0c03a1412600d40380c00100604d1201c0d0003290300065030b441d401565940e030580400c120104402c2551440b070000040b038000100401d0172840140000ca5000700700420454110000401c01414048100015250455010611310045400242c46403044207640f0343c00000560810040c00d211707040d180820085441e90800003444081004503001c030314400117011034200c1c0d0400141c00070810780882c88a207000c0c01c40325000ca44000244035207040f0390000950840400302406040d90100140380c20107400e090950840c01c3c64610b8184404928800700c04039555190000f07060707481840e0444010210002841c10a00072b0b4a01d02c1c0c56a11200368070303000c0e50070030340003004082c4148126051160001e5101d91181d08641c2c852080e003050000c0740b11100c41c1404046815552074858000700b961a0018803030704039940c505041610002400000f40002d100044500d00302540f04840030304000f4a403d00c0d507a1042142c58005114440c2e50203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 961385935 1250 961384685 961384703
    0x3090c06030203131416351006080d0906030605010e060a020127050601050a0e0f040c08030d060e0f010f1203120f0c14030c04150c140c130234 63
    0x52107041020400f042c045050303480f0306d0440f9840d51600b0300e54100111920040c078207040c1e00c2d03e4021810880203c0d4a00344c503030580c0c144614081d880420f9600c0ca4000196980017440415110341e08007031007000406040c103060010902c0c00c0006000c20441080b203900410700000c0c4009031030700c00c3d4004072840c081031040140b4030310017024004550708001e104507141d1003044004a01c2d40b4010f400d1008072101880c48600a680c0c481410000042c00380040380e540c40c039080042117415090024060311710001300c0004040b0f140c8a480c4188003800b501845008405800500034400001c0844081e03c1c00c3c446a5149401c0901c2c041b903203003074144031100d4614501409000b500b803050700141a024115501e90031108a500d170324180c288415180c81c51102c2c01044200103104100c09540851012414a41c00c4036a140d1190601202c807030a103c00c0942107080d20364018600000c03000c03480c0043d10011070034854211034840000c18503840d030004403025481001a1070640040d941101580010b2030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 961387185 1250 961385935 961385963
    0x171503060703050411011b061b0210021206190801241715070908011e051b030a0f020903010e0d0914030703150b03030409050402040b091e191d070603090c0603020313 73
    0x201c0c4440984c554101c1c0180146a4a25052f18a88c0259404d08412100890582e11124100016090a81c400304001e008a03000041d005a003071080c0304d16040c0440c401518590660320400c81c080294122610f00380c4d05940d801c0e00c034080002c0707820340c800d10480c0d90100e94503041c0c820703280f8008641c4902c006609201900d000003039a0300452064462494040c811619003c010100b00c072418a241e051201c420f10000d0340301511600260354540c0c68010061070b124140004c642585d03060ac8082c002075001078401000c1c0d541c013601840c0180741e03015145c0074108040c1c0007e5207030941d9110140c076500da01c0504c0a030a040d0740e8080060140028126035840b9941d02904e0013414040310281d108601c0d00708000164288083c94078801c001c40300c8485044108510700354402400038120002c900103808800c2a80c0065108590b401700c01009607849980425951038a40f110580102040605052100002031001e4175000b0940b451810056100c2c3d80b1009240075420350250b000c0c1026001c1d03210 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 961388435 1250 961387185 961387211
    0x150b030f06030337031416030b0a06050309070501050c0d030203150307030f03030605030a020a060309051e01020403060b04090b010e04081905090f01030e1903171503060703050411011b06 82
    0x42d0b04d221012a503840d40458010407003a011195500c81140e89491700742d00180419800070303002c0c00ba804403410006884c0f54070740c2c046000c505517500824080380e400020b08c03174000810403d0720020002483c1c174a00d4084064000e039114500306400740207154010001c900e0b00003030201e0b00c0507416405011225441e59a04140c1c078031550381c40c4242c0209240260200302e0b4200490b01744403664002c4d000c02d4400303190110460003468101015120341c01110ba0070381001d45a2110071000c05030304030000d0f072104d04509100c821100c5513000359202c0ca03e80340c804000154031541d140c0c11074102e1100c5030059a40c07400c3c00d0300305115801e603200c80d88002d1541d03007e5058102c000703440b4005050f60f62514016041005408030307000c403141c40356a0303806603941c0001d055402c02040c41403842860500029841c02c8250882002d0a89040030011948646017225080401c041f66101051b40303020b001c2801c15840d58203000c03001b440781ea81045004169142c03c5080791000d654026407080c4204420150400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 961389685 1250 961388435 961388497
    0x240427060b030a1110030c0e010f0201021204150605010302091f0c0b1603063302030405030f0f0d2c010e060307080103020108101404021602090901090204150b030f060303 75
    0x1182e20311840148240d00c1c02241301e4441c0e4a031801f0b031910b0b0a0528640700c1d00640300d40000f80300c9a01150740030000d070820040c417100b2541c0030b54410b0312141c4e543d001000a03001a0b031290f170806810544107109084460b5240c000c02c1c0300a0503141c0346c40740929840c4404403050003e03c00081c044843c800c09101c0e1641c80a070101301d01001c155000c06c00390740c0312040ca00310b814078407a1024012002d09000740c054024040e074802d05414074011640307860382d103801190400c2408200603400b500490b04400c45440288680004020545881e08240c1c031103580c000c2142035540c1400d06181021240c800703050340500e0280c400840b000705295107900e40148005c010a40c01d0204900145c40741c0c011611003491040b18000740c03510810080400b8181006010007900300d2402022072981c260040790140c2c90742c02809000d02d86020000c1036524082c014001681c02c0080f400201c480043c000300100450501540d4110720702c924414016201d11000a01c3c42c040c006282052806aa20121401c0c0b0310103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 961390935 1250 961389685 961389713
    0x5031617070932010e031608010509161d0703150b0315010e0102031605070f03150b0f010801150e060d0c02060f040302070b0a090305010203240427060b030a 69
    0x282282c086040020f03110f4281008444404541240c401410980c0f580282120003075020702034106c3d2903e107500c601455005525501041159542d6418040104001e20201154110041d992044946400d05030381d40000c600390340b0f004003901e01000c502902d1081d00032080d503e95a1000540b40f81c2c442840301d901d584248e50306005000492211041d55002d035001424105058006d18144640343c4440b862030103000404031401e0284403804600021504600006540180b499403003010f81c240203082283e000200c1d26104168048800c241c50380e00c80c038214151150b01410100ca0104008c1c10380300b8004d80e26403640d00400120b20046140030b240d1210a00403101e5086910540310004504001001902c018006800c120b4082c003100300103c0061008420310314003e01c0a50390b07a12a02d013260400c3d15031008522000515900e0040c0840c910000704500707d030104510b000c0038440140c00300c480941e40c841e40c180042c1d440e0501c409a440020f20800103820f44060a005180060407081e0207 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 961392185 1250 961390935 961390949
    0x3807060605102a1a07020703030f021f0c0315030602030a110c0706032c0606270a0b010e0a09150f030809191d06010915050316170709 59
    0x1942c02004692040c90943d0307020340c14021284900514409218600b8003500040c3e4801d260001c214101c650744001440c45603107564041c041d01c2d030451500070909041e8a0f01c20085600c0150850b526000000d4100e01a061640000958510814003a00505090200c0c40e0704c44d8503602c0000188030854008500c201c04030a02000a4402d52440c1401d90060020b511a140d1118030203102e8140658407484d040651000d6802400c8160001c440600e03060741c1030031480350042014422641084103500d001070030740050300d124402c0c0340700c0c11180300030004081c40d001ca49c0754245a582c42e4054000c1301c152980103030501c00c50684603046130703014049990118400d041a65000034024a400312940c041d20340c48241e192170000e05108001c80ca06c2002c4d40519080841c0c6000101c004481800410104172a5400b02e01442d10400140642d0095880420404045181e5001c0298000110395202421801d98800742a0402c800c58007103240242d2062000e5074601489030f210f13041082c6004491003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 961393435 1250 961392185 961392199
    0xf060609061f18120807110f0909160e0411040c122306060a0f050702130501080d031506140705030d0e07081207080d0914250801063807060605 63
    0x50340040c3c0b034102c2a5084c014005035814440c803400200c0010701c0026035003001f01000d020607003d800144c8100c0b4280c07994180c5503c0715a0000c103c40380440004006c3c51280c40c0703500a49426180c80c1440320150b18a18890f50b0340c2d0b1108220540a015101001070001c0e000300800f2220441c0c09840d500285c2c03140c1901000000000d18a1402408450304810581d0356440583d440d03144c20f0f5240d40060740100c3c0d2021031031a0142020310544641c60003011060008c2034041e143c00c10140440301d051600c59038a00400b2428072180c1e8004200b098480d0510901c180e84419030705005041d0b00480d0b50031001e8500b003201042c0e602800048510654200c07206458004541c80c501854921815400420a8805202c004044040f66001001c00e600035144c0c080080c0410410b503080440007075110200d58040d0507001c81811914410001801c1564002c1017034504005081580c10038402001e5141800504801032500100c0c604841244088524a8541c0d0f103910340f60002d4801070017a04d000c2c0c50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 961394685 1250 961393435 961393439
    0x10909021c0e0706050a200a0b24061e16030801180e0705040b04140a1a0d020303070206030612071413020a0909021819080d020f060609061f18 63
    0x240850b40320700304c90312a10350510f840b80c500015101900300107401e00c46a40c0b180b01120441c00d0510039410764520682080026140c030065003140c2020021081001c10310320842c0c000d0719210320040b22a4850064403d1503520b010303683c41041c40c810056a9500402a1003500d810150805142810b0700c005900b03c0041c205540c4240b01120010305c1080c2d125881503904001ea420958003090b00080040c2020400c01c1348440c402025440035501f141010b0b5442d000e0852103c28605010a9840221904071201c03286800184e42c902a41002900c240b1000010500b1966400340c49040140d05d00140c8010f503a840001c0c134208180103204d1806005075688031029a40c1034801c44504500301d8951440b050b0500c0311080003900403080c4c0001c19048504490031b6035503a03401e84c08900c00040924200e1a042c00b82c5a800c11031011066800e42d030004002c0c2c01aa20b000ca07426520010039035243c00c0d144d035004002a42680c2011142c041c00c60031950b0320b2051940116603038544c2c03504918080c4065 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 961395935 1250 961394685 961394711
    0xd0f0b031f110705010219031d0601030602030a0617060f072c12030d06051008060112050604111b01050906370617120406090b09010909021c 62
    0x2a8079500880c103520711914000660010541c40446090703001c080907814584140e68160880e844803151000742180720004140c40d640c50702441e00f8072a48003681c6503103d07032040207103551034806000060440303401000041004c1503552250008004481c0c0317680000707510742c01c0d068882905035030013030403070000c5000294464024828103200c1012200c8403880080c03580303200042c0f20b002e90f0400d540f1001c0105c11000c4003c04001510120f10302c940001600d911f40740400c00f41c1254805038609204841040003041c0c0e0300108a516000d4007200d01244980d50310707000400a0003511200d0032603004c0451008003900441ca5251700a2010400802c0251203440b1019a202c208441800c018480605c81301500c42c450f001d05203402c0403403ea142c60200e0203800d0340042d40c5298002c0e4a0744074690701001c0b4814001c2080c58082031441da2013a1030142051001441d245050007444840b03000081c07400281d07403045034218001c2103482811074035410802e050040076101114103015043c1170000541082e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 961397185 1250 961395935 961395943
    0x1d1212040e0a1b0e01030f051503101a0d0303060b031026070603020c010207050a0b04030816020c0f0315040b1005030303191d0d0203120108011a0f150d0f0b03 70
    0x1c03c001e41654030054581c000444461090720215810591a1211415204d2507070054a0258115115840798a808401410310b080f4080014106042c108180c404660464162a000d03908090b0f0304241230642ca800c007035000d051980c0c0078844a9000204100c85140e0810458094072002c0354404501c66150103042400c1030800072048494000c14020404e07540640d00604000070824000342c10303c8200c1d114a4104066807109031951030200b810803081551101803240d0128031060740c4028403200240c025500d10000605500419103500300203050380e010440141d090301c01c49400d40c10740c601458500c4105a09580804111080e03010110340f600d07010040d07920a401c104400c441c0c030380c10036104801030a41d200e402940c019104801c0141c81c8002d010070101220150015a03071640204010000c03c07030140d04c51600c0d40d00d001c0c0240700200c501044027039000d20880301d0340b01c4403600000003041580729060920101400081803000d84e22203400c02c0980001c0c0e02c00070840002440281616 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 961398435 1250 961397185 961397201
    0x16030314061e0907030603150b0315010806071b1b03030e06040627030c0303020a02011b08070204150801020c011401090b01091203020c04020f09030c060a1d1212040e0a 74
    0x3030a5081c503902c2c0c00c50500220460340720340a8580403400d40d917252644001c0140304120082c450ba2117030341200c0f45080800c200d1303d005c155006078a00035032410310006e454850160400c0d00b0007400102d0f0fa85400071510400001c10740040f180010745860340061203082c15103201c11408103401c8601521039207010025a0215074032516000055000b2810a007004016842c052107980500c62010010500c1c1c1400b02000c2d500c260010302c3d2482c0c10780005403071800302840c2c841080184801190000301b048007550849035040c3c8000c6400c01d1451000008904590812080c540c07000c608850f240e84150000c1e000b52503000c81c0c0074190390300c0f6502d0030195019111143d002c620058010050a00071010a0107601c1c060701c1603a0780052014000b0b826a48440b0203481001004101d0041902d803e00080d82c030b009045440340d00d01417811102400b480300b9000444e0088541c5425498203403502c8115007182d031412420b4400c460303190801c6031016042400703424000e40c850000030350003450511552139 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 961399685 1250 961398435 961398469
    0x20a050909040f050f0a0b0609010f050904050a1b05010801080606150a051309091520130305030307030501180501030f0206210a1a0607020f010e01051603031406 71
    0x11800c24a40280300d10208042c208407010844050ba9002240f01440442d01044400c0b006e0510b01c441800d1032a040300c0080c2100b03114a48001c01003201070356012002048400c1918070002030354640c10450704100d00f020001d02400f81c85c080982d0300403a05a03240003558401d0303c0d0f40107140d80b9030b07900300d9941c0b80840302d041d001004007400790844042000600812852807400b20f01d400c25040e503901c54540c05ea404050302c01d45808442040110200c08251380000ca080d003001001d146005d400e035044c14112940c1075a200018100d01004201c0d0b2806003d59000360481e9a05d0508820050040200340f26212070010210381c07072181c80c00540201c60499802c10700250030110503808000555206403a0404031010001c0c90703041e510b0710710712428420854064002030f00241041c4a108006494001c0d5204200070400704005070349004900c41c5090081ca0710342500c070003090041c1c50f24490b81300081e0280c0001c40401040660642208108001e001d0651285803a60b005200988424540c418 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 961400935 1250 961399685 961399687
    0x2090a0b07020604080f030d060b09090c09120a050a02030105070c08030a050c04091b0e060f040e09010e0a0803040c0e0c0d052e030215132705010602060403080a020a05 74
    0x19460321000303031528500083c0303114139056640098520b004011041a80141c0010400d001d0388102c0744181c0c0014200b1506984c0ba00c008900010f80d151001001e12848030030229000056894544020300e0302c1c0140400c803107011940d070910350755560400000b02d00c03941c201400200c05034419107424000c44c0e404403a103800c54403400f81c14006010014074407150b030b0a060000240c580d00038020840740b12040c2d20200484041d80300c0c0109001442120b040c003d0004004c84403104520208403411910b204018810383e8903085403e03405842100d0400607248259002041400750200096000390700c5001460801d6aa840c07042400a0003155205150740b07091242c01007824540d0071203039010790500e074840d0107101406500145481e401c10700c4403401d0065101801141055550030401c240e10311125418001405030740505059140591071041c4a603030741010713816a4074607040902c1d03403070b28006010a68440700020360ba5101164140c000540c080003050f8411114422074545c0803956440c5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 961402185 1250 961400935 961400939
    0x30201150b1603053603120a27030507060810050a0b0d021305030706030e06060306040507230604090f0b1206071803140f160e04020121050f06031002090a 68
    0xb6181500b1170416090303e004241e03481c0310904080e40500c0004110015140b01000c1103806240c03500e403d43c0e0308903510b01300c10059071602d1b5410250300311101da201e012080368240c640e11405500300d5180c0c00203159120740500882c82a0b0030130580362192151100042c10303541d803101080440d024030301c2200386034001002590312500981d001803682e9101c464060410560310b4000c41e07c5e025084d440000000d0340c412090764044400d1003844d400143c202c00901d880e05060f00c0399520b440c0c030341c1b04038214400c141f101850200c5040c0740302d402106c00245116110b40d503607a209405006107040312640075207448010740c914503145c40c01210709000c2d20001e086aa80c1d99900b80c0f80704900c8108800303a944107140000001d078a4112007000ca4820704040d110aa10700b07800e292401d40d9032400c14030760050801e4140714004041c100c0ba03500036024179103d9a50502c800c00a14091070704460746000340e0501e000c204098901800943c080c040a44c1103613000940c3c10895400c9001c1c14020b95401030680d801 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 961403435 1250 961402185 961402187
    0x3080d020702030a140d030606020c03030a0305070215070909050603240907080604050c0a06020706140f0c2b03020c07122d0519050d0c060e0109030201150b1603 71
    0x3070488584007a00302c0b100080143c8494140e0049032088442030382c000c1c08440340141c0d0600502008016a0000784030141540c00021340700c1c09a5040081015501d000141c26070307200300607040e00309128020300090f034101000d0082c401a22402143c1085083c0000b01e0003034140001d1840351500c14403808003c1175035003010000682c90241140707520b0300c11140c0c00725940f0024000540194032920080c400301d24420f09009405880f41d002509640154034200240d41d0440c001aaa104507116020307940c40d0402c0105040340200d4028810610400c02c8850b01040c841d046031700322980414200c5a0b01c100028110164818060303441a6a0000341e002c014102d1081500092140700d00090580410034091020010751500c50000280d0450300f01c61051090600c00103400c0040c403800249102041e03105c50355268896010f5404020071002d84d6028051268010000f14130010000d20205d4860700f0024084c240382a03000c0c9148007080307000200e02012204841e65401c2a41007041c40051540f8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 961404685 1250 961403435 961403437
    0x40204020a05041d01410604050a0e06090a09030807111e010c030e01050115120b090c30040209180303090c031218011b0b010308190801081908040e0c09100903080d02 73
    0x150687c7c0060003440082040e566032440c4c070000d46092604001545031010412204070005003c3c0c0320150310344000c50300441c0d0702c0a8400c0d4400d8460822021a0270240b089601d802410010791010700c0e80c100c4441d032092019000400700040ea540d05100964030405501d003290b0082c0b080c0c021809000600d10032442c0a44800c10364aa10104005101012080030660034141142c085d45081d0340020183d02c080b00b001140340d0180c44001e401d20b4113007443c0d07014111284000e030019115282c12000694111480f44000b821250060241e175200d003010ac03e015942c03014510b51621a0060100b81c09150320240141c5445820f40040304003252801710040d10030301442c2d00c82080c1c00900400d5070011841c031a070840d008500c01c10344142d80e00c8100303111400d000d0403400800108441080100000500000c3c40f07914900880320386042c0781018035159500d8420b03903100d0190b4902000410000400e9100948128801540e15005000810724116408201c2d800300814404091201c8030005000d44c4c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 961405935 1250 961404685 961404809
    0xf011d010c0309170304031b0302090406050903090409060b180f040602090307080d0905090f0907030b190614012d050702061b0c011d0306040204020a05041d01 70
    0x100f01124450b4585020110200140903030301d03181d40c0005010000c020101d004000c04051400141e00c516040d5030000740d11080142000c4c00380d0741c46101240b6010002c1c0304540c2c10300b038018010450307a1602e29240b0050401d482c031142c800d9000aa04104075080c0452040c40b602404118009540c0c8aa450a0080d0030040c210780c0c1510803008042070f0520308000c6018918020749905408a10f840b04210b6019001480100c02c800c4070030501c01810000184881602e52084809100395140000102007001c40b4410415030307424440c002031021090300301944101400e07680d10007074040404c0e1100940305180b0304041002ca1038034461682e1407148000c0d02404d88000c0880b442d048420402403038a9030072172810f2003560408441000c1d1580c000303080c20181c00c501607000800034181e0340000d0f102d500061010340100d0300014510300301803046080f1000b44c01a01d01c140414920302c1c000e048068024010183c202c01c80c05c3c000e800ea6410151264598082d200100b56404514060300c024a6040d07 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 961407185 1250 961405935 961405937
    0x2010c06090c0e0a061806140d020f04060905040c080a0213051b0a110105100503030403150605100f03051f1202040603050616021b01020601030b220305090f011d010c03 74
    0x9500100718000041c5010780641c0040c131003c5401400c10324812041c0d0100591860428a041000c10010001c401e0405074402d04a07484080b0031454004544040000c074041a03200d0b18080d00405d4882d4183e010a008038042c1405041082d00c071946656240701c03101020354483d0000760f0b00c864038a103a400241e4401701c80301d030b00709140300d80070f20090701c6400c0341c9003507800300300080c0e000e03252400f007403140c50383c00380480c510b18088078509000703c0d40745c2c4100c1c00090003003410100500e4210542c2d03003048006040c05041010541d40c03a0b00000c180d0030428448100103424003010a4003104003401d1805004c900b0700c00150100e240c505c1c42c00c011010b43c1012a08161501000008603000344400c40c4505410901460800340145000b81021201e01640012a0382c615041c1e0300799030700007541030541e540b2840803030080e100c3c604e11500500c0c078898103504892109203c0c0b0109a40312000e0100e00f0400c1d26a5580804e0103001564001d25408035405482c14580402980358403502c8071144850103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 961408435 1250 961407185 961407203
    0xa050709060605191e05030f150105040b09030a02030d0e192102120f1f1118030f0601090f050112030e13062301020d0801150309170307120b0d02010c0609 68
    0x420805685e44c01c00111403417011030f401204020702004541130b19070340180802503800001c105100042d00500071400307801001a000320700c1501d1901c0400082215a4008045a4000c00e80e0000208980e007450388e60742c01403e00c540120b0b50908a02c000c4c0f001d41e1000880c249071030503800101a202240703405c00f80d90003540c0366040072003000180701100310f40d03150201502102605011000303441030900d1409888515108032082404c03003040580340054200070004030080c84e01b8000a14200d095484d500c100d02900d0f00000d0840a81c1c3c2c420790110404002c10310060713984105105000d00160380c0580420402420030035075103054148001560001400007850796180c0900505010812460203804003200341c04030825a0100101030260000f45000c042c1d0358100aa89810304001e200b21000b03043d10b800c08142088080480c031312204150815080e264900034500403c0f07009503402c01c0100d9031030540f02d000369040180503210100e4068403151240d41c07240c0d031480000d140d40032068a61141c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 961409685 1250 961408435 961408457
    0x4090908090d11030d050702180417031806010b0c191e0507031b0302100e01140d1a04050c0702091815040b07080402010e04051b0c0a05070906060519 66
    0x551a85100c002c0350085440100c010014400c0c540b52000020110090240c1031043c1e80c010380e05d07508003281c220650701034600f06071203519241e03e80103001141030706602004010840c40700c0f07404003184d07559001c0310100c8000b643c1e0384044200c60700c5850310012041d04010b1980c11100180703000403455502c1341254a074081f00070804901d04100358801225150011601001400381040d0800c800c1c2400219214029265070300041100300c101841c1420302c1283c85140c1000d0703004003040c0895030302c0341c030a0555401d03d420684000300840800c030142003001058001c010b082620440d0300c915100f0280030b00d411101e400700321f026403006000c442150703d01502c002501c80c1c184007007848210103080c0380b4170740e0500c0c2c42c1208441c04000c01001c100941c810810000d40e0380030f030022480c590243c41c009426102c0300c0041c595010010380207003040d5400680f110b80c0200c00103082001d203000c2c00542c2c158588500500e810b5925a110350f900060080c0444d007542c000380300d48200c004000e810f024400340c0e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 961410935 1250 961409685 961409689
    0xd0e1f0f021c020c033a2a030f02060f060114130905042f210a030203190302040506180a210209010510140d0e060112060c02060c0409090809 62
    0xb0005241d9040180c01242014190b8141000412162045140141c1c03203198112600440074411b210243c95841d40102c080300094020f08000c045070801e02d11a0001510700d00d1200407140d04000210001010320245c03001407031011a016004105404800d0b409407140c6004480c1c01035822498181905e0030404840046488a9007000902c19030381d004c10360349401d00b414044030141441c02c9481120911628a0309110607001078041d1104480d44a1841c140310078031851a0f1841452400601c100d10b0a04203064000015004a02030311414044081441c1000c40c00d0380a070f8451f55403c40404c0c41601a4102c008030044d0510102400076060207542e80b8940040a0a160488000c2d03000c00d5003d1096040c400d11840c0035110646e600c03e111060310320300800100d03c0030494000303480c0c041b800000403009600000310514245080320b5695031600c03450700a2176110441112078500e410122200140085502e6200f8410060840c3c2014a0300c40c5d90009004a29000c0303882500400c904c2800b6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 961412185 1250 961410935 961410973
    0x3070f26090105060a080712020103230702010603050d0908060612031201061e05030f040f081314100e1c03181d0a0b061606060e07020d0e1f0f02 64
    0x40e040c0703200124803401c0c201d003441540c0b28030f41c100090a03044403c041c4402e4802c031461659143d030a10700001e28000c00c01c480f16a02441b04148180759003141c00384030070395905404c102c00f030b2070281c0c2c00d40326a000d1440c0d05541072a814440c41103290800c9000403d03500e4113051100d03080c201d040a80f0728061502104c8191071100760440004620380c0540c6c0c6440124404c40f6400e034150500b0407900d5418150360388524220300610051040307004d00415001c210f10314054520000f072807400740c03500549550041c1860111070b66814007035044001420340d03151140d201e110a03c100501100c41700c0b0a0002130348500ca8684009400303004070000b84804200380c90b03085600505801c0c0b610401c0c4683300c1c00e0198491000380000f0085424120300803d1951668115158600c22854001c0241c90928065000d0300c050760100c0c5003800d01c1800c00160315004030b6009a2403010751380c3c2991601c000400c00564641120a8441c4035001c46a60140b40d401501d50640c11551070046030001c42c45000c220800b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 961413435 1250 961412185 961412191
    0x2c0a0b01030f0308010806040c090c0e04150303080a051b0a050c06011d091501060f120609090213020a0c0f02011b050f010f270224120c03070f26 64
    0x540b031500380c6103006050b0301c0381c03555015041d1440034104600340780d160b036030400080e40100b941c0141d981e074801c0151405119800c2c0c4a1001030014052a040c03503076003100e0980188000da02180f00c188c0041c9070b40445c0d1007810b105281030780701112104034840031100309800191045050000c1080700703c0c01c410f820403040340204a04c803d41d110303210f002034128042d008003500c50038650b440358102d0844442c030007958074192a0b1614100310004100001100e031072002c0c08100c141d103843c210000c152900a500615080d030b00945241024002601000040b0302c5182024400541809555000110300d18080b04400b8014036000c2420250030112845d102201c8000701e901c1d82c0221460000340e4802c6c0560003080c00240404c02480c0c20100540a402e551300c0e403031100201400c4018021035444c20043c00b0052000121180c090f03c8034500d0900c1e5610143c019100009c0d180c0009114242002c03c03248584016034811150402d8900141c450554003a14444011710104404042c11403030070308548 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 961414685 1250 961413435 961413443
    0x3050105040b0103120314010b131a0d0c0807020a0213060320010e010207050306010306020c250f05060301210302031909091508120a0e040204030510050a2c0a0b0103 73
    0x2d1549186403410aa40340c84d0058014141002a00342c8100305034070600341180c24201c0d009a5650340e403007606d94010311641040521030310305060310790f41003450005054004003103c002c00007000d5084003916440700c01c031030f03050046c0d20200d907500c0103061100e0074005641a4520105100c1c0d180da131110155201820340206241c940c443d030f116250392160700303082e50040070300242c1082420103000c251510014080075040b6074000810b208854010440504441c0b08036059150350b100800c1d4070034030301e162403223034a420315010300006c202031034880b0131a41280c0e10001e001c1781c0801c1c0c940741d03c00d03d00c000d50400e8040d40010700c000310410186c603030203459100180d03540ca010a402c1400c108204c800d403501d105800a41c403038091001800000d5040441c8030505013458941026403c200d410700c81a500072078001c0e0010800004010000a940207410705c01070f001c1c0066600e01070240121121103200480210500e60031203c105441c03042d50803040711903402e841840540c2d49518130080420b9004031 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 961415935 1250 961414685 961414703
    0x1a0c07120f23070603051510050703032714070f060c1b12030507240207050606121b06070b040c15021902100c05060903090f030c0a140a0305010504 65
    0x8402c01064030038881c0d0010b003070502039451510400015689600b6070191006060355000400c005140f0030301c091a038008000d041c00e9000313140750001406500208011004a0f040170210a10902c3e01510707000704500c51170281078202115150140c92020044400c084c81c00780f400701090401c00c801801001d0000e940719102c03000c9492502e0701c05801e005c00222200d0161a0017408200901e5120007241c541602d0000e459002d1030504020860712101a03462144a04184460501040c6c015003002030040f4241e5109a68030801d10640c1c550172560ac42c159040300c0a001c039600c0074100b03400710400014107103505010180d0780b03208968105840c00d98030015040800c200705c1e51600c48000c40013503540301602c0e4088113224500d2851001050007881048445c81151081d40314140b00711002d030b0030108071411400c014a0769500c1741d00a454181c025000c4410441c128200000d040160003405024402098034100c000c010605a248040b548865800c4000010800c24016940901e000716924 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 961417185 1250 961415935 961415963
    0x170c0607090503120f0f0f160f140a0b010501030518010501123c0602090402031501020105060105040807090c05070c0303030f0506090c031612090311070603061a0c0712 74
    0x5841e0004c0fa04d12020400001c001c20741c078080d8044162803c2c022075807001911008035002c124054000c1003100e0030062180000c10050000300c1c02024070450082c405800c01a8042e21116216100744c0340180c11000c2a03001046654426032240347e21103065209007900c907914801d0035094540a074098541104e082c5003d800380b141000328a4104551459a00d89012a07034007002107440c4004824011094140100818403a640c2c04403103103088001d108550307030b24244041c0809404c00d420202d0044d80b8080001b030786540110700300c501b40c40240c4000c0400c00e18044c02d200c0944414040803080090501120002071a00d1651802642c481e441c0420400c040481c120202c900c010034440c89418035a09209000c58200b00716504280f082c591b0707115641c049982901e6620003402d00c41c029916015400044c1980694a100004251030548150075031310301045045d01c649015007542c664a0401800c0c50b03089500c02032001103042002e4403c143d03901d1200082d0042c014000380c0c4c2c8205440c1c0f007 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 961418435 1250 961417185 961417189
    0xf0605010f0e130f0c091b0504140402031b0c100c05031603020c15090304051c0506060d030e040f0614030f060106030b181501021b0d170c06070905 65
    0x15540c0580960000c50301d00ca454031151000d00e16002d0080c003803030600040c0d150240628052004400e076040401042c226590f004114000c0801050a000c0f0b2003605e00e24103455440b0300202c1d4100c0e0058522041c000200c0c0040000944c0301410310f0020741005000d5084243c51880905440352495000e003240c1000140c0b44425951303558502801c024003007040041050041c1010422440366140c0142c8032040661843c0c48c018101c41c0600a008203201041010200040248103884c0240c8402c032600756a40e031115071a6a40c160700803d2034000300d002603920704148804c08607c83c085d03d401c1d0015508000494211480c108a42c0015038440d881030051204012452146000c280d00400003500d100000d41d03150030060103844101034076000240c00c15590041d071184034000d000d0701e54603d1f081c040001c058151040010601600075921140031000f51f400714a4081d240103022890b101c4599565103411617000300e0041c942190500038107040c86d00030041c4512541060b11362040040c1800c003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 961419685 1250 961418435 961418441
    0xc07030303021b0604050a0f1b150e0303090a270c09030309080a1203020c070f0e100e0903030c0a03020d020c010608120406120f02040302060c0105010e0c090904030c021201090f06 79
    0x24200f5070035406001407000064000070400d10703d43d0807510041c2c0b81c42031443c2c410980c86a07981c049104044842c00400c2c103a4004c0c1d40706c80805040c0d16440e203040c40702000d058890140001d41c83c0d2003e41c8070820400c0180c082d10000f110401202e164040080c4043c1203c02c88481c40786140000b60040b5060003096005480c65028100740c000a0411700300301c0d13903484001840c403003c1604140c5c000c62140141e1804028560203480c00080e81c80003d0303110707001501450812210841182c03403140000600460b2243c189020300346c0d20780517519543e501d48002d0501d6110f00303242e13400c142d0700b001048503400d4240302901500c80d49c82c0002c94050b00d01104580750002c0d01e070a021820400f00010024a038220714a010480c003c4500802c15a086580d141c0c024000c1d030340041d42021000454411686045d80102d058a0320903294560300d0301c0b060300d07480316401020003140d048803503640450040707800bc03201d1400d0346200810030840121400900d609503070082008540e181030300d500c100100003442c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 961420935 1250 961419685 961419727
    0x50402100e0f0d33060e0106050a03050c0906040e060a08010209030c1504080a03080702250902130503031306141e070f0501110715050c041404020c0703030302 70
    0x1c50464074a00c00c9100040d9a02d10b040d220511480301810041d041050303046900c0c41c1e04c0c82003003030a00d2040b07405882c106401a140da07040038152410b440440c59024000003a4140c1d240d66440d68107007070342c502d0306400904018101c007103401d01c2408034048566032000108003908807100c0307820702401e00d40c0602500305401e4108a140364010300c0312a0b0103480009250f0110182252032180d1072460302920000d612964010782030500611903102d00340340d005001680075400c585d00300c0e05403441d00181140504140900c0e0301000480e05820000682c1a40123021401c850040704000303240d03100002440c46e48136a80c940781e12103160303c00300308003030b00045402c2210224000603868602c3c0e007021a5200703085400c1d00d0003580d90120751003041c00107030402c075072045500900030440c800c441e40e16905180c100e8a4100c40094a035503480c04c5141c030074040c285c0500342c2900c40908003400c20900764200c40800703c425030001c0d1300740f18180c0f03141c00400210300211700035100165901d070f40741e100840b031602d11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 961422185 1250 961420935 961420937
    0xc06020f0703050d0c14160212100507081303230d09110a0905090303010510050708040311090a020c1509010f0f09030e03030a090618030203060f0108100b090118061805040210 77
    0x48000c096000305400407107280b0042e0412460241c4840d02c00150349d1041c180d18426180301d9001000744803889584014003501c2075445866665503000b6002e101001d41520040009d101c04c250b000180640c0d0b047d10880400701c01c2c0890a00320402101c0c8216010058180d49107181e010b0f55040d242401c5c080030028022419042c4280d2514588540d0b50384418401c0c5801200070100320240715101e0380c20b071034100d80e102c021301d90340c1e66490070700d81051000c114901d44941e00c218081002c0b0a00d038401c030340c10717061028060041c107007040c0b204420a110041c1048929501c07032180c00354845452141a181d0104054005131584d12401e0041618002100003402a4010026403941d02d8203c09840100c40152a101c020344040d07800d5a011105030b544025018418401841a14070810302c1d0f0718180d1b40b40904488850341d04517410760a0303980f0170b04d80e9a009130300d0304018000e00c0c80300802002510362a02c0c0104403a641d610807409001c440041181540e946c41d0203120441c17802000c003085034011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 961423435 1250 961422185 961422197
    0x50d0e040204030c0e0405011d06010e070f0804020f011b0605011502010e0601030803250c060c03151406040b2a120406050d0908031e0f010b03070c06020f0703050d0c 73
    0x441c1e8644004110305c0c0682c8600d40c550300002000c0142c00d4101d2010b001c000d07000d100107525107100c03290b5192804c0c081d140f5403116071030004200174450640354403511241d6482400e580c6aa4003448144034a021002d410000c080464452a02d00c510ba45094a0f01c94000000c1e15890001d01d00c00500f2124460401c40e41401c0c1d681b03c100000055450540341c004c00300d140c5d030746c0304e00340c0040780c44030b0502305a4452015551402034280e0003402c94000f15000741c4043c800c41814210850484041d940416049640140d0520000d0008410140c008901a000a00d440d81b07604000c82c49400148803ea81c584001000c60030481402481540f049220301c010062038501910005141c0a580200c0c020000003084140181c40f1f1900b241a210317421540d40350b62410500f42184030f801203079006409910000010404075501008054100e80c0000c2005081d500d8000c801c40340d0f0b071030715907068624540a12000e2640003e000080951501c241c40b9541e442c203030f0280c41d20990365090485024020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 961424685 1250 961423435 961423439
    0x2a05070516080a241b020d0e09070c050c1c0c0e010b030f04020102010902180601110a05070308090d062301061803030e0112050c03062e2a050d0e040204 67
    0x500041d07550311079a0001204548407101010f0032a81c0d0213040d01d00210340d08001c0311503124500700d0600004214180e00f070707403040c07000d03117100b40c070340200014800c0e822440110000308094800c0100c040050311070b105540e20300a4020000301081041107820301c110310b01c03008070000c014001160000615110500070b09075894030182c0800c47c00000c0c03c91000c8243e1000040440e8401c0d8003490390b081d030040c141000c07281c0b48038483d007454000300c03010b502080103407801707980071032000a0211445500100405c000c03420b50b13447c030a60380c01044135190894040c0c0000380000b01c1c03c0c0900d08400d1581c400351454002000901e0614840681c051400c0c0300040000e40718800449040000366505410417040d1000141c004032100480760303244507440b601c0c00c81884010522000154042d2004503070b0210b40c011114203002c00c061a44030381d08032003d00400310320481c6004010b094406aa0760b04801075a00002d9070b04c50160710641d2049501e42c10410904840c0e07900600444c00380344042d941141428 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 961425935 1250 961424685 961424699
    0x5070c0510112704060909021f0903120e0907030203070c020f06130609050f030c060307110a0602031e01080d05070201031e061203031b08010302042a05070516 70
    0xd4014424860010b884110b928a1840d1540032580190034a0a00b014030380403012480500ea094202e0141c4607070300304800024804614090401030580040c040402e101144c180c040d5011401d076800070602180110010109c1c40e486070b425400f0341e8a0301d070000d41c1000c00382004141c0c0c000501d0b04082c94810320a10682d140d0100c0c0041d81c6d90360503507103100c40c01149400206140207000c848030f000340c10a0800700305540c5c40aa09411101c05840714440d456410301015103481c94004603581015050000407002c620a81c02c1c202130b90100030940e4610400d070344854090740d00c00c440c01c1140e510841482c1118110b0401e003280100382c1807010300b000d13005c5150000e08601c00c8180107410103480300400d8030110800384400d0000f01c009801000310342d94070700e045150380038031010550102e45803031342c50700c0c2210300000080015012588e42c0302080c1e00303550802009121001c0b440f0903003c031030104600c800c140342e1840307014180c00d0703140d4079261401440c00074580608640b800b408443c2c4000304106034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 961427185 1250 961425935 961425943
    0x6090f030b220803010807050112051e1b0d060e060405010f060e0f100c020306150d03032301060305010f050303180405060d0c0b07030906261b120a05070c05 69
    0x1c01076824111200050b56140403500440701040a840c049000000240364100050068101e900a0b2210050010204403420440700e003210400b111010341c600c1c02c01c034040740420455001142c51410131103040856002003461700300481b01c160981d0348202c04d00003050b105000507400030f4101ca05100b290305188511107020190701c101010702c012034249009503954599101070342e00d4050141690703000c1205c1c000300001900700c3c003640a40030f5000403030b54540354055644000000034004604041c05035400700c0052012075142c204040d5030a080c000030040c6540400c1c001e0449507408615941040c2d00658944481d1b80054404d82c020000c509030403400440b4001c2c105030484000400390756510211311052a070420062140550f00c1e404206c0340700c2000500f83d028040d030381d581d1a00c0d031110303000d444034030304581e05d6160007503403903200c081043ca602c2d0081d6000d08015580c54600350a40c0018140e0780103240080304510611041200b031030741d0384c440e00f6400700481c500500a102561181030321 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 961428435 1250 961427185 961427191
    0x20f060405011512110f0d05010e0303220b0f070903061401030c06020a0510020708120406090606090b011b080c16150206100308030901270b0612100e070906060906090f030b 76
    0x1451b40003907000b0260748034522590100c3e08a4002c0c40080030025007182c480d4400c4070f1602c400c800014542c1841c2c0b60740001450314603400341c5900e0090b00c0d641103100e1102c000404400070005411400b10000c4c1050040404820000025001950461414480d01c40c1e45410030070071075000d90a0000030030740004100303101a00000f00140d9580c01424484a41d00c00c3c0d4030400340f00c883d502e0911040050540c0140c01e03c42c014142006081d40342ca50070800d490014009500003401e895860030640880c20010710620f1041d00d5161030988111441d5040240c203000b120b1404544040c20040c410016074615012406c5102500c0c0c01c0c5001c402d02c072000040341c0030190600e0000700c00164a00801d52020a564040800c07400300420007074641400941c0080c400ca0300c41d140035000c0b940600f440b22420041e01c125101425109807813200c403000030001c0110626140c41001800541c44d041403203590040c1a080d81d4542026007402805001860750340e1155800070b00d0120108003140c8545c400d00e030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 961429685 1250 961428435 961428439
    0xf030e0a062c0f1810050a0501090308030702011410090e0309090403180b070605150307051315181b0c031704032715021504020d03020f06040501151211 67
    0x2c0680416408034810810803207016410182c8240148642c2c00e443c21614854843c010f03600e1801c0b03031100144484612240308444c08038100d0402031000501400186500481ea4800050035030a91240a0008003094517032540d49000b00d4020300000c082070050446004c1c00e000150b00d080b015001240c00980002e0001c1c080158404020010380d405c00103840040030320001003500e43c05c7d5414070100828055032122007581c0e03130801c0030403c0d08012540d1012100010811440703c50f0001151004c0c1c00311b0300743e01c0c401c0510401c0c049242081e20801a14802140d440050a010b00c05070720401100c0c03114a20f0180300079080e02c0b40000c0c0d4404480503840450035070502140d15140380590340f400c00300050158094000929820000100705000c0c2195022a1040b00c42102050240d0b1101c083c103030042800120000058054145001c4000c0c106102e441210b040c02070510250342041c1040d14100e8203039443c0d07800c402c180d11014040384080c0c41d1145407085001440d580b1000200c420055083c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 961430935 1250 961429685 961429757
    0xb1315030206030705041502010605120f0a031b0804031a1b040513060819060605010c03050d0209032a01030c08091e0c130b031006080d0806030a0f030e0a06 69
    0x1e420f045c4500155001400c40981800e10b08844210103800b030117090103114012040b55105480d11a03001540f805100d62070380103414201d6403902c00f10350101c0344108450345440e20441c4031001030300410041c030042d40912000c42000c103607120724072201040906814034650003825081503a107100022281200d10442d00f5241c04036641051030081c28081c2e2250302c06d030058070800000080440100d414662140782c0800070a500d610043d42c00032611030740070307001034014402c051003902503034000c142044004048900d2861180c001100c800e9250010803050407145540780910350b01030048101a0b1028200000c0c5480e00c0740d241d60340c030a004000007074011415031421003030400a02040140c00300c090808030704845003403492405012081480d80c002c1c1700e11000000c00115070f1007114203650094020704000d07442e402003151860700250003e40e25010b01001940012810440400c0c00c034840d44409000d0810001089034880701e6078450b60511181c601d144860307025081c001070070410384030723006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 961432185 1250 961430935 961430941
    0xa0e03010605040615090602030c0304141203040b0409060b09090f040f12050406120605180c0f2701020c090a180c0e060a06020a03020d080406020d0504060b131503020603 75
    0x2902501a0b644200e801c5031800d403002c03498051603040b40e40c07502c0203926101c0907142c0d02d00007281d03a48038000c4606450340081c4810310250301425201302d85c02c800140610100114600c000c0e0650740154015503216400280421001030203020350002404881e94841c108000030000c90381c0e00400618801c201d2079036000203000c000109481c0c1240070341100410b151000c8414010f4503591050080f08046030b221000c500550109009400640360060403c10249411000b088141680075045c02c507e01828440d2240c00c2a0307802c0501509055014000601e010030354801c134003841c1c0a4034442c115000106551096103a880541e50800302c2d4002c00200c640c8150341c0d00e0a4a1010714001700540010350000802003a03443c02c0500901048694241c01980c45c8804d80e03036500d1141c002000340c0c0140c440b40c14414040c8468075409030050201502c0e0084444403d4101c50045908460181e0f54035500702c12400c00c91903130304210011050800200304030b000c09031501d8406200081c4285400000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 961433435 1250 961432185 961432189
    0x1b030322150f090c141801080703291003110402090f19090e01060608010b0a02070e06041b0309060c0c0c030f0204110d0929070309051e10060506040b0a0e 68
    0x824443e1680211598906640311030780807220080f4052060f225894044490400084c5146400d04841c0184000e2036010f1031a81c1d0000f2400f0f02045400040fa041900c082d083c030b050740d0103e481a030011701c1e200951411850846122001004400d001e2407050121860755110a40104160003046030320100039002d8407100f50081a85400000c4040e06104506081980c1504414199100c07500c54500c140e1322540d000b030960180310894070050380407010030450b8540c29054241c00450142c00401c80360741340325050701034800c000602030010365285042c10500c00148180810050140f8280804e22402e032201e10300204540005095084286961070444d9034541c807500103500059025a2519101002c0d000140002030056918144140042c20f0032100024213010300320541002500d5901da03800200c0c000d01c940d81c8125101e01c03544040c0c1002d2040c0d02c00c0e20b9200c4501c100181702c11001000c04600382d400caa807195000306410701c818061444d0b481d0654411076007034949a0060200000 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 961434685 1250 961433435 961433441
    0x703120e07060305010503010e060c0d020c070b030403020303180309030d030b040209120a150209010507030c0f0501110429190c060603030f030c08010608010b0f1b030322150f 77
    0x40c030052030300c24501d00141c0150580c01c100e0417078200310020440d401c140b94040e80c9030030080b94683c000034410040c032040a10350341e000e460344c2900c0f5400ca40c49503072603900d4074501d41c0c0309a40940c050303440801006074249098071001d8001c40400003850401c00d401c00841d40e100301d40b00d042004d25841306490725858403990b040d030b103007803e00801c1c00a00b6600114500d844001a4030140c07803c1904d5016079600e074420b40219551a2010b94a061401405841c01c81e6100b200090031a149018003040f540411024042c00e451681d050850595031460701c20400d261071034000708030140020700c207418400c1e1284031080d205c1c420300441c42c84c3c1d00c0303503818402142d580a4103100100018035040c0c002c420f166201100800800c07060324104290041c0441c140c500c120244a450001400e01006001d80f80c50100a800140421600306080006200c01040c0880866102c2da042e03600220800240020910b080204a901004561001c01d059110486200305002c1540f26803500c0b4040321200d400302d54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 961435935 1250 961434685 961434701
    0x1104020705010e0d05040302010215060d0210030f05100f080f10020a02030708040e010f050111060103061a0603090a030e1203030601080601090b0a17010f0b040e0402010509121006060e06070312 85
    0x3006413a00403240b140007820a400c40d0005a00510a0212100e032a40000d14124000c490080c000703e2024200c0e13007000241444040e20104050305c40e010b003c00c0382c456000742802840d0b400c44d100100c90030b0030307003e00113220503030b0007190303036500c07000000640f00400306080d00d9800c502080580e4a20a10500ba461481030010042c64118005000250941d400702803605031078800c401c07410080d555400440714640c0a541c5503241e03411100040001a500b40c2c130054510314201c4060583c0c1006100140c0c0d10b4008a0701c0300345a4000c548800201903000125410803c0f04482002d40220600342c1517070b4031300009003518180860303107010480680c01509804020680c03607403156600c0741d00307003070051140e2054010510038043c140000700d104001061a00180e0712040398042c2800e1070500200d003134640181080c2d0602c00700300119030b400d860707a00407480010b089000074083c2540501070f482c00c03030383e40d58441e108111681600050a6a0380c1c01110b078029058900201002d40c044510001400300c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 961437185 1250 961435935 961435961
    0x8130b040801020c16060e0f01091d0105030c031906091e08090907140f03040804050d14060703022703010f050108010903090b130b0f09040207060219020109110402070501 75
    0x31400181500c8150001c1c00b00921410035a5420318408403000324005082c021280820b54a0141198a007810035000420100504d0400940e5039540030302c2e038040025110002400340c0200c014030260a04202c03104400c0001e600500d025004004a4a036107016600300401c0d82c0d8075041c550303040c854040c6101624508245000800492078603080010798040c55100c0d0150080305c0024460754042e080c0c400000c4100410b8a2030004407900821042e840108110f0740c4100500012420380c58128054440ca4414201c028440c19110503951502c90028403040425004101d81558400500e8800c0d00040096030404104520440040d01500e03d800749004560720b0a800000c6102c015000601d07841e010b600e4000606880c0d10484880f44207a02c6500041215404104541c7c100c000041040e450710703150441c10500384400050a82c1d0041d10181d80054001c210035415108400340b040e100301490000f000400003503900c03180c41c514000039181c49546d010401e102841000e400014a840745 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 961438435 1250 961437185 961437187
    0x1150314070c20010801060e0103020d09060203011a040b07201f0e091b0a020a0f052b0c121115090708060f0606132102031b0d08130b 59
    0x320004158000da0300c2e050714058041900e040c00311444040381009807006964191850303082440503a4050b40300101d0504040e0308001c3e242031001184111560f00744140800b50f0759501d080002c01c5990003100c00c03014507403420002002144007140444a14030307803000d600d90f2040341c40c100722441040340c2c21129800003403079180140c0540d22403029480f012078503140d81c2e07403000071601403242d45c0204644100c08488000e0010070030355108000b90102c80001d20444500e004199540d000d40c40900c03204640356444050180d5040c401d41c0c035007543c0880f0010001072035a0001d90010204e41d010701001d00800000c00140328090f10070410f60031110296000c459007051400124070b944142111660760340d0081c042c011404900103c6c0d000e006040012030081c59440d45420814550b001d2001c03c4000808160001024041482045421003c00c4e54601405002c0e006042c00d1060f8802d18850b1001200568034440ea60000d8000700c0e81d0304580515120340d4900d02c81100e840e0150000400030030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 961439685 1250 961438435 961438441
    0x90f120f020607060f18030203120c070c060e010207061115100b0c1b0406080a08090d0c06230427140c03090c040b0f12070504050106020a030e0a060801150314 70
    0xa105d4010380307041682c0c41d41c01c110003a05805480d8001224550040040e0010400b400b2207003c41140076070445a80c503411031410440741d032801102c04003603000c480401c445041c45507580d07030140003c82c010a0039003010700f10720000c0050755840301c02504003541e24010046c080340303000c5c1415060310098800d0307a80055858521780d800c0d56548401e4900c403448802002d00028242c02c10303016950445c0c407481d0003410f83c00f645560300005500b01c032008603003103110030f00d9039804618000d4880e0b008105548070044101403488500702c0240044d6101242c40c9000c00c000c00c1070400c4407900105c11005807c1551903000e410701d038080a40316000001407054420024018030620700c000030342c003590101e0210340456004030705200c156a080440305500403102d0400061318106400a042c1414002c000e86041584a400040850700d00b0317000364005a000e00304000406411102e207030100c03041240c8a20000e40f03815002031103800f050091640c10b00e10b9850b0528468061b4100d0741c0004002d604d210b44174a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 961440935 1250 961439685 961439693
    0x305010b0a0c1b0504060801022505060f0c0702040903031b11030301050f15071a0a0b030c04050402030109120e040c0504050d020123030c2a0a230a06020a0807090f120f020607 77
    0x1420214180f00c2c4e4000390644040b0302c3cae500c00016408654004044d1815031750b0011f9501c07400070010400707020140c1c10094100142d49a125104245100383c0780003078114041e8080c88400642c60303502c0000d01111100f03107071098400000b940d0465204499180c03460281c0001b29041103000c140440641001080c0d00041003001207443d905218020040780442d41c0b1600707024203480f108040e0300e070560002c075845081411700f03400c010350290001d000030840944a03921005103854408034003002070950581c054991416000710101d04001e89440303030509082c2800181030061a05000741804030100054034154194046141d228000183d60352300e900c0c00f802400c156912160616050128400206880e454195100c42000d10060010001d9814682e60307000b00c00c803000070594401c001800d01000c5184100200c0304214494080541ca59032210070182c42c82c0310141100e41405800241409000e45094480c021241605d200f0000000107050088828481035000303900b20400003801d0080c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 961442185 1250 961440935 961440937
    0x9030d05150325030b0601030615090503010b040903021903180f08070f080a0f061503110307060c03120504060f2d05011d10081504030305010b0a0c1b050406080102 72
    0x40d0100360251100ca20860b80f826075018880e0000d01035158502c0c106002003041030f0503c580c807880604001408549070040940b011840c0320314840055840c1f0400d10683c1028000d00748041016501444045000c0d03502030744034200414101d5051385095284001e15116012401c01c4885003009202c506845107111541c44201d07001c1c4007114460204009071010a00e5500300c1126141d03009840b03850300980d2010303c2d0b0f007074000080c6c44680d101c030341400090141c2c0c135500b0300540c4950349548d401b0410000b8542008025480002803106546e8940d0119401100c0581c0c01641c88500041550310703407620a0040c4101d610b600041d9241100d5400c0c0202038284510341c011a0307a60203200a60b128001c4000e95000340074400d0201080000c445005448000303207900000313906540a1030b01e8403800b40c076142c0342d200c80001d0302c110000343c148414550184280740c05828110700301d03450311440410117010302c2c10650b0000c00000c078901e419182014040307048005004020014003e49039103944a60107 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 961443435 1250 961442185 961442221
    0x7090605040f052b0b040507080307110d020f0411210105060a1119030909050f09030a051605011a330c01140f010815011401030c140f040905060108090703060509030d05 74
    0x40f44623814003c156950000282c580641d8080740c3c84000392103610901c088000c85000403a007080117240c0c0a0031990780ca0081c000400d900030781c0107032540c400d0f00e04007841d010b05000300580c0401c440c005116644495080b900d14402c0c0c0e0400c2c00507148410f0f969490b00081802c0c00d010112a00b12030b50805a204503044100d4840100078003258643c0000d00319540c00a0354440000c1e8403c00c80c41d501c55006d0005408a1241300c4a403051107100d42c0c40c0c00c1d082d80c003040311910060395001284001850708041b5000c0c94003d40c2c40c1c4035101d106c1040428050300c00c101d80301c0e81502c0b01044004084c1025080708052054403440e80f0b034181895080c4800c1620280100340050045d4401145051a195403441c102c0e41450418030b0587d50b680015401404140b5080b400c100f0306908094102c0c00c0e10f0010300c030400c044407403a40e545140c00200c004131100a01928100540d58042c0000c0c200001001d0068a40000e000621516890074282c03540c4140b41003010942d040000700f11483c0b0b0065000d80c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 961444685 1250 961443435 961443443
    0x3031d0703030e040e06101523070623070503040f020d050a03020c01022d0102040f1401021005010e0a110903011a04140c180102100905010507090605040f052b0b04 72
    0x681c070f6045c0b55901d4000c200c81501103400580410401d1208646290040300a24201280d042202020110300384c4405000b15228181c00a00390f41048000d200340045401d030300030742207200da5401c0b5003000d0407000581000100440400440d00741328410070301d03a4074a60300414003250402c030391406c1c907160203440c0c409030098091508401c64650000c00c011a83d03d0600c060360b054000b440e0082203080c03109400b101020340d82804080780e050402906200581130003080704419903070001c002450851064402c0c1c2016080000412581902c2d08185800c152a401c0101d20244458030a0a5078014107038619451f40c00d0190403440080c1c0e07070340b8084e02d24400340c1d01400200103054102d0702014045d504214244020040320314000150070503040340c080148190f4070944500d82030030040e65890041030310700d40d5592050210040d00082960003c000604009080901c8d150540b002030640f84036050040c0c9035a64055101d60105240c01500e42c040b8190b0f0182c24440d0038040188134049608403 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 961445935 1250 961444685 961444691
    0x6120f03030b04051501052a03120919140f0706200a0215030717011d1f0b0f0409020c061e0402030c0d03051308100f090c0303031d0703030e04 63
    0x541d036041c0303130040c00e1085082c009a10b6804c1c00002c011101035120155075006070114281c01401008821000641e03808448002c58030b40c50210400f180400c0c001e411016142c9c0403801000d844d0301c0c40d16060403c2900002942c44501507000d0150901d0b0f51284034039000d010384c1c0b030301007041c540080c080900003000540680c42820314550165480340c002c20069804245424107942c5504508000c5034452a84d190642003d170002a0400b0040d82c207801c0b8224003031582c000440c6510b502c0ca0801d034004e4000400c3d1a2104200004000e12045402231040110000901e0f1490f0300d0400203c03001800311060440d900e103200343c0031a071691010385940d040d4990b000143c03910340c42e02007034007401a60000c001e4260b01e1850401c0019000b441c2e0012418000c0900070300500301650042c0000414441d405028680552102e810807100300020310707407040746485a1400400d511810303642c1640d5150800007180c2d1840b6440742c00f5141030b04103500043c450100702008041d07100c040c0c5c0140d008191014 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 961447185 1250 961445935 961445951
    0x221a0c07050f010f061202090411031905030304020f04140f0a0e0a150c050708120a0e06130303112a01021c060303080705070209041106251101020d021f06120f0303 72
    0x3941e0900381b4600a948224600301040104100d01405860403200504481404a0b0018000c10001c0d0404050707940341c10102c10042917003070403490351010b090202c2e0300308200264010035405103180507141854200026000071518207490f403042000c2c030486e00443c1d8201000e441d10520080710408104807081c2840050201107024109444040d64441502401cac040c500e1152040394200404521042c2e44a6040c030005540510565001d88140e220000001120b8200603081c0c3e604182d10f401d07003a0080068200541003c0366003400e001040140c565015800000180a4050300100c0b402542c0c415003510700c02d900c1d551040040301e03c0fa440300b00c4195a5088142c48034020030384003a400c21341c0c10380020005050480383d810303400c00083c41c1c107060500c405044014071400c10b4102075024800010711051041c030303204510b040b03103091008024204d4181d82c020b446103803036030148605021042c0c0c4288056807580081028001c0f90401c052041058101200c100840710010740210340751440f0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 961448435 1250 961447185 961447199
    0xe0f090a0b0628051509130b010c02150c0616052502030f1b0f0d06090f140313050301020c03070311030c0d030b01110106060801050d0311030d05221a0c07050f010f06 73
    0x140d40190900400c58110080c07070600b103c2c023400c500d10381c103410403103d140e1a034010303945d1011203072030301c81c42211054603003112026003842d102021700b0111034401380c9030860f19074131350080444031140e00702c1034115000103071480c0d02214ad80d10b2079030003941405040c0c01400320b49400145114080040b44800705a400c07602c050060075031b4001031041e00950540c1d1103801040316500482c04280c41840c422a5400054503001d08188120424424640001424046003402d03c017a41e40a17050840003103290080f030f4102e0fa0340d00d1240c1d02d4002c2c00d00c00400d00030585202c00307000b5501211951001d4034111012540001d000f0105a90740c280401c1c005a010101c00e00140308010580c0c0894803140f403264200003c2151039412000100c1c104140403443c200580f2040c0050301c1003550001c0d000c00d050806203480700b042c81054a0100300404c42820f01d20108802d045400c80744420100c00c0340c040e480d113a0700754003d480392560207043c070320840120941d84001588200c01c0e008200c002000031686980d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 961449685 1250 961448435 961448437
    0x60f0a0b060304060903020c03011b300b0a0b1606051602150c0f0d060f1706040201120e010227030f120307050c06100e0f090a0b06280515 61
    0x90311900600c05000040009685601039002c2c1c0303002e4011a2041718000000909680b42c80d41451400130552844181c042d40151400c0c0c01407500303590090407000700c907442616030310400c0e001c41e601c40d8540d00460762503141e2140c100702501002c0318081d9120040e5404600c420145e078030454482c6d10300400140401c1c1c0700727130005c8280d1b2078683c050403007020891405162404042d01d25042000d040050016000c200002020003403000400412000d2405181c445071244030383c000308a1518200a90303a005001058981e406507090030059440c1c0c0700120030000510040304600d0b4158130004141e03400030030441c489d0110208001c4143e6144a80b1414542c0381c0803000012265584000262a44d15100e072001d998442d049203442418043c0c2081c816107050026540303030107090b00c0494140001110310240550110190120b81c07428107001c44070079600c1130001e43c05010984014003185441d55a0b02801d4508841e2800f400e49005001e12825981c5039503205582c4140c480a003440d4036121604 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 961450935 1250 961449685 961449701
    0xd020604030f0209011a07112709010614030a3c06050a110421060603030801140d15200c0708160e0c070c1a030403030f0509060a1e020c060f0a 63
    0x10b583d1f0300700f14050743c60000081d01424102d902040800305050700e0354034026072000c114100c1c01c04046609060310301c0780c212031140c0c212001190603081610500e850004600d864594010300840000e9202d600c8040f03103110700d03204090b85032003410a207a910300c0042c0c41900000e0046ca0200714a8071769044c0c501c02c4520f11108c0344e5441c034ec00e1004000b90403950002200300e8800a13022141c511050303640f0f40071940e4981085000c100168014400144200e4600d0740b4103105640450f4400003070b071105244181c0c0c1403114200350b9250503000e142c03108618a100320079080c155150351684801440300d40c6030040d60080d05c00f107114104004c3c0002400524900c1150242c51010721140c41e03c48008000d544004825078005501c480002080102c009034005d003900c1c030905c950348a040134a001020f44021982d01218142480184560008007052641c0c001c14104000100505907283c5074441c8000311200d50f0010f40b001c58592450b040c045040d80c42032450000e10442980e400350014101e94402c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 961452185 1250 961450935 961450979
    0xe0607020727180b09070806070503010314160602030913020310030f020303120a1407230d060f0905220c140604150e0102061b180d020604030f020901 66
    0x7010300e8602e20000c0740101c0064034041d03900800d54040340007107008880060301c800c90b010b001010030080004814801000540003131805080c0078180321200414500040c00003500c4003100301c079002a800d41c10800d110034608500b6065901e01d43e030f10030203520394000402c03132401684251940002c00c02580300700da21844c510020101d800c0d0075900c1d0100b504080210807038061100f00002104656500c07201ea1140c0103081022031100001c1d1100c0ca8080401707407019044c400c01c0e500c000418140e0141c2a030507890107440c82521703881014606009002c1583c8441e0190070300260101e00e59041e600000e01c00e451640d00d000700680e10116003d20032842600250a101c01103105002d21442039801088104004100508080d1503042514928900840700d201140c2420489040c41d40c06002c0682d1000f50740c00011100506611282194403669900c1064600a900213000d20390b00e40000080c441d801415180d00d498580c617100f001c03501044400c1e4030a10031036000144007441c4201801040b1702d0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 961453435 1250 961452185 961452209
    0x61d1501020c031e16090c02011103040515040302070909060204081204180c03060e0c190513060c020a030c060818162102040f020d0e1216140601090e06070207 70
    0x3140012903082e814130541c120a40105545180081d00114100f801303482080c1000409240c038840117800c42c0d885500c1c58408607014010080440c0020414610804034103050003220343e12854201d0521242d40c1002080c45e142c80307072070b00a00495a018000b40c422240440344054135070b458500040c099481903800340008050035030841304007900080d441c05020b05012405a45480701d003480c1c02c000b03c442c503030000000305100c408091609071307152000c0d1203030070554603005064000190000441c042e1800b40880400010110349400e040c41d0021a0421103d0a40d41c2c2c494030000e09225040e40d421140903691300c0014224800440e10300c8441001e04031035000d036071034410550000312546003201c004449031362805002d40c079140201c0c050100c084d0401a5159580d440d030901300c540d090001522a400203103400380480e035410464000d000e48000c0047c2154030741ca011301c2d143c074001100c83d5450003480000a11207500c0e07003103000040c180e901610031958510804036503940c0c892081001d0303a48 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 961454685 1250 961453435 961453453
    0x13020c0c12071224021204050d140a0e060f1306020d0926100501060206100b09062a0d080406110307080106030f1419180b060f04061d1501020c03 64
    0x40300080b400c0c1049007031181003105513520102c0402c1ba0000100441c45c140c029080108000c400d00c001c0352030010a0805481800d04110320804500611010100340b0981c1440446190785140c103498403071803a904c84c280d854920740144c802d107a00c548a1480540b0034024110203407402080d01c0740684000e0620303c8480c0740140310700498441d1740d941901440c02907650001602ca52806030a02804c080e800030002400c01d80308000310030f403c55001d0302105c039081c8001c0d001d03951110100c8483e548041446d5103101c908580101d000c4043c2c0c60981d100e842981c10411805411035070f1a0311841c05107904200800b508009071000744070488400d000941c0c07100060050740d01a034008607051401080008801c07103942050a4181c000303444244a900701c140f030041050086011b21001030904406820189903690740d001d00c10603001d81248c2c440c1c0101c502118650302d441c1d00000003000c03102c505201c03580c5500200c0c00402d209450800200c0d40d0410016881d50000a0b81024508058010141d0312 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 961455935 1250 961454685 961454693
    0x20108010515220e07090e01140d020904060b03062a120f0408130603060503070501180905132102011b050702010c06060b03010308041415040b030613020c0c120712 72
    0x12000f841d944010407400c20011584107080f2206610444076074035409a8941080e07808001c4150581c004088405107140a0b103458480a810b4083c241d03064419803a40d403504d25000c0c000d03092b00440d0340d816109031320401442400280d000701d001c14000c005610103801001c0c0b410002d20400090b200c522119002152101c03000c6501c140e80a8082c100440c141140303681001201d10ba2648040002030312900288814070b400e0040348000c14007400c100d14114841c544044440c00c0e03a00c43c1800d01695500040c14619066400703c40d03c030ba1026051a101c9600d031182d1100d0800c2c51030001c0158609901c100500442e4044034001c80480d444043c1401c20903401100d025103a6401103501d00d8031101c0001b4103401e0b020241d40030394810079000e074645080130520602030758031041080c4180c41c00541286d6052124080302c041d80e080f441020340d266100408903a06213400c82000b080f05100280300a40c3c000003042000d107205048902e0594204040d00e80340d510310490182030004412030b801c150001d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 961457185 1250 961455935 961455967
    0x250f030b150a050315131a09070e060d060812030a0b12060115052a10140601050c010e100f06050117070e1f0f0e010518010f0e06040909020108010515 66
    0x110b201e5214068817007100003240c40c5204440c1680d0f4038603116000003507904105030340c1c03244a0760142e030300107420716103003800030105182c0b84d0019001c4c090000e01c00d02d0412a030740092010f80700001c22616811040440fa010541c002c84074543c03001e14205420071145403680400102c7c464005c0105030300d90801805081c0ca85254825100303001c81040044402007031042503510340b1407204100071f400c8241c2c8418504081c13690340e4415000b450901d480d00c018000c2d040160300a5000e180c4503495000c2c2041c1c490040025400c1040240700305000586800c0080d00b2560900d1102d280a00c0340542d9400155110460701c210f81802000c180009600b591064100d40c00001d40208018107001146813203003d0003a0841200c0300040c03408414050154111034a0f4149030001c2c6092403503e00d200d85009427110310341e01c3e41c42c100144000d07424080391080c14040140d8000a02683d910365403101200000c0c1587c40c822408104224000651031070f045220122225030403842520300765000c4c54140d44 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 961458435 1250 961457185 961457191
    0x4020f010504080a0c0611060106140702060c0609010509010609150b03090a150c18120b181f060e04152c1608060106090b03250f030b150a0503 63
    0x10032500b8040090481ea04010020940d40141603040b100b905040004040d00104c040c055910750141d0010460b1640c449441c8140300011141280c0f50049072000a10b1849440d00031070403031107204148407000c40d040d844580101c000500070084030f039540c001903054861120f0a4906201c480070b042003d010420000c40d40310310f4031015110b500c5c1c002e40da1040340d030744a101d0003030b1803554035820000d40540082000741c03650000758401070150b18018000c0040448104010030403000140460151070402e070016000540b01026501000015000d00c810601d6980650944074204100050704081c1d800065003d2500308205030600361148540704081d084030001d120500040410504507800d0343d411182c840c69800001d80102c513454110b074030b4150300d290092041038121900400c003c5810503102404c0f101056134650316580c2c2d800c0307440350603c1c082c0c00c5a00d004008003c13240200e03920074114401940325440c200b1510300050305104802c00710b0f818481303d11000b044044405401100a154 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 961459685 1250 961458435 961458437
    0xa0e1c020705041805060f1515040302011d100e01030518061605130605030103112b05070515042d0b030411041e0f0902030a060513081207030c020a03020604020f01 72
    0x6201d41c520745d10107280c5202161200000245030782805100d105000c05030001001c00c561200c400d600c55029600d5034400e80c40700a05106040021684000a4042032034020400a02e41e04042101e00000b406140c14042c0541c002454140000c0c81d84003195000758031142c80303200821403503551650920000b022200080c00f440303014885c06544903004900d050142c00700390390b0951254554540350300c0100e025900c0c0d0380304c2d422828504600507000050000e6545011600701150a4117080440c02c1c2102074100319001a00d502d07404280310012001070040fa20103a103000341008103816188000d140b50000c80c03104030754090041283c0d855801c041c40d0014010250700041000800019089500811a01300720300f641010308850300c11a40314004440135409414007400c8540e41c000390b111017403031341c2c01400503588001041c038548200c800d14004640c000c0c806541c0f52640b40105d4510711045426400080c01d10020801d098400f0074001d44043e415001009130751915420080280e001a80c0e0358 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 961460935 1250 961459685 961459721
    0x30604051207050f07060203091017070503060d0c0b032d0118020d050a0606030b03031218030702100309051902060d0b150706061802030f0c0c12030a0e1c02070504 72
    0x40001136003409082c005001d01d80085035110107260500540e45442e20303643c414441080d100341040c00000d92a207034448240d10b455907481c0e40d42d90014284a10404014100080040003c039006403014000c500806008042c8074042c4020140482c5070030007420030300e0051040c0b8004020322203001074000507110100e400941003078010a0b02c40200d0300b0444105543d03a03225041049055010300c1014410034096001e03500d0841c61942545c1241e0001d406448c20b040d8039000c2500c81c11042c4159006d41d03900a0807540070403c4140001d000d02004030065900d4002c00d808030024403100e00100303071420ba01070a140e042640b48000310b8000c0080c0c90b070382d03500007816001c140c2130400c0d108014211075125440009003541896040160500c1b00c9807120b55032403042007401291185542d295a000c00c0600d0400c4c1c0c0d0341c211948450802c994544012a080004414009800d0294001f205a00c2003041207500700c8400008154017124075001000158120b206e051040b420030350008409900880156 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 961462185 1250 961460935 961460953
    0x50106141221091804021002011a0111010e010c170703050f04030e010c17040810020a0905060a050d093e0120071410020c060d1d071403010b03060405120705 69
    0x12440c0720f00080c4a5802104e000f10400c02145000d00140501b01c1061001b000300d174943d481c20210640c03201f0710741414408090442142d2403001d401489462402d03000901032441c0b003ca000d428000d225680d81032201841002903c100e00c01e2082512030022103890505070b803282c0d00c040c0ca402c1041c281e840e04000c604030401d17012841044070342d00d000020700c00d2542e680c4e2521030038900b080c0c0180d2102c070110303004000b41e0300700d55400300540c0b060725000c07904150740d191401c0050b101740c800d0001d022916030038504060b003440300b10004a6451303030201c130032030804120000084540549004c003604c1402000f0480b440954442c00c001c464580d0504007201807543c524541358507241803588454191625443e80450300d00300910b0900007000580024200030b0300040016040e0b00880c8400703200e05660320401400141620010b50522010b801511000b0752541d03000100b41e80d100c50755500940c200b4040342c180342800214180f00c2d6401c01d001d4041001e0100307215280350f11940040d203282c80b400201c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 961463435 1250 961462185 961462189
    0x9060e0604090e1e06240303041a0d150302100f120e10020304060501050102160e1b0f071a10350d02061b0c030306010818010905010614122109 63
    0x90904007403015130090030345151581402c04684400c070360309211200c0f010a042800e84000007070f07400391442000d0101201c0c0c074004c2c0c240c0c5140900340030f100d20719080201018003c1c1c81c40308240103032070003911011503407000d40c2010794140c4499030b40500000c40c441480076428080350302000d1030104000544011100806145050380c20030782d401d450142d07403100100603540c0c04000c00300115000c0c211510500349840055400c82000801d6440200c890100804000300000102e541545005004a458a40d0ba04050404d11040d1400100e00c6a403600411054820222818115806101c1c2c1c8040b0381c50408001042240c00c004009002150180c0355040c0481400b0440c0d210301d8940c0240020b103407240d0064000b03041542000c415600400184842000100881754402c1e02800c1041090301c4030020400c3e20440510300304a9035207811004402c11006401480842d08442040f040d02c0c1c2c946010003005106903000094941d01058024a0a40e1210f2240d0b000c180c0140041c3c3c1086041e40c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 961464685 1250 961463435 961463473
    0x60d02040b0d060509010f0603020102030f03040c0317030a0e010b060f090a030c081005010b03061309050703020306161d300105070f120b1e03031b010c09060e0604090e 74
    0x30b003140e5441e250300c20803070101d00034840e1035034052650005012051454001031344a1045c40c0316440c83d040c00200040510031400810702c015588204503440744107108440d000b031900240d410307048160030400d030218036100500584038090001014680b038000c114826680c1c4d81c1c051044140c01910204000021502d020030000c000c10801010b4410b4403400103408040319030580040020b80c0060040c0b15035501da04440103000f00d4a01d42c0010800c00e2418883d103003580030303400298948501010804400c0074904034840c252015207401e00f050340d09a0600700019990030701c447e0010b84c0e0075424141d107003540c894140480d00000703491550f5004180c3d26401e4501c111440d0020600c010100c0310425070043c0000307485031040d01b0801410840c10009041203214040750380034110f09803145001c903a0240115102c0720341c3c910352000d0604207960305601820f4400c0c5a01c01040e540e0100040b403a0007070400021403403006220900e00b40c10681d048004001d480740c41121485401c2d600c45041c1160b80d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 961465935 1250 961464685 961464709
    0x181a07030e130b0907030c210216120207120807170412030e0f09040b01050f0411030a0e0c1503070309140d3603200312070303050c0a08060d02040b 65
    0x280300801c00c200c44000b444190113002d00032001700f510b042038804410b5030007417004080c02d941d00011340c01071142010031300190059410200141d102007680c00108040305410f082a84080d80a6501c40e550326501400300010b0410050304000040180500194500380e42c0c51a4404411265003000e440b10b524003040c0e48410002c0b40440d400d0090000c0d5442c03c55450200004200c2d10441d4170320b41540d500b01c01090600c0744038003c40e0601c40101c5255101e4101440c07661030902520348900d8000d9212000c1c1c983c2c041c2000042c020716600078807608001681c42220748452240600e90b8803200d000f2030003422041029100c40010610000c50520244030b100b42450013942d80c1440d004c0000800c9001003c000d0100e014008522031314444903c050790f003d070803690841c03189480140c090120480c010145200741da4140a498001d0400c0c0084401501c6458001d60382040740d40e888501c41085071040c071072a1004a51041c00203a16031410301d04200c0c42c40d101610100b6a1603455006c07402080c4c0c11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 961467185 1250 961465935 961465969
    0xf0702090a0617150f130b04061d0a0c060507080301150e0a06110111040f05040f15031505090a02010e090910151406040e0402011808070e040201181a07030e 69
    0x350810513041e2025440b080d8110030030742881012401e0107103041c26035005280000740305100410000b400d001103607000001c070880100041403400301c5103100715115800c1c0002140c0070b1042c004c0c0812a980b007038040e40c05056001582501d164208002201890381c0c016000080242081c0c0c0424591030386101c180c02403a081d10381d41c85601d810f00640382504c802050700c0300c9210083c04100142c03a0810214411288180c4e40090b8194810800c00081c102c00d2455403188030b6614400000c02a0401c5010000180e1150401c40f54032149031203615450740841c013a0024903004400501c0c1d2902140280e017010100d42100c441e0f0744050750000999a0003254807081980202e030401541c0080f8809006600046a1091600d8145184500003d0025102a040208600b0710b0176040b0000d1071208080c05d400c4d81242c00301540d514a41c001c940341110224000740420410b0038015001e1424070054414884d01d040c08030040614100007908070b01c2d010740411409045c040b4803911003002c1000e0348100 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 961468435 1250 961467185 961467193
    0x60f0209010206090d05031f0909030804020102160b0904050901330803040b1e070c080709060902030601020a031d12160b0c1f0e031b0105010b0f0702090a0617 70
    0xe40029040010061086809412001e42192200d5000703003183d074068420701c49080c1d489074119002d0304072201500070601c400e113000e4182040c035410551441c4114400d130308403041c1000804a012410b152449000364080c2c091004210780c2c138041d0000c1c0d600c000c1c0b1000011b030388090392002550a1400b0f0880091010f000f016041e50301403003140702e0015000d12002940303094a8040c0800c5c05103d0b0f00c03580c45400701002d0381e10440b2440c0508880707440e07070007400107074000e5181c4910316100d500354412110300b986048000180d04401e4020b603842083c0c16000340c800c0e90081d440940d040504100e510f21a611144450300255461300049041519824000c02c0e81309113589103004071781c166401c030000c0300406010f64141c8010000b20030300740a1400c1a0780e0b50709680c0d480302101502865408d50b401c0d00000c210307105030043d080c03d08160380c202c4c0c2c2c000b4401c80c2d036180d4400000d8811314000031070007002080381e50301508084120603001002004005510742d40c0c1e00e010034030320062083c90140d40d00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 961469685 1250 961468435 961468447
    0xb010323040312090c0302040b0d021003140703090b07030b0a0506071112010209150c10050a020304230a20030703050a0605070315050907031b05041e0506121003060f02 74
    0x40c0c000903850000015030402c02004504e602d4070714030750207188030080c4a1515103184442c1ca0b1500410296901e5020702a652285010340002d0301a200c540320012002c02e40c0400920224802e0082400d056081182201103442c1c4c000d045024114484500d500180440400101915030000501d01103019450100c01070710b2030400c00c024800032080101d203aa006010040c20340e03545003042c4546000d84480c250b51b40c50743d00e039105e0a007884003090400140c940380401c00c1c10a0340b0b4000794448c1c0d2007071200708951100d1b41f64035403e41034458010070942e440078441d040041d01c1a0744444001c802281100000000707940000e2070004541c000f200c0035084210800304110060003070035000b4602c0c0c1024000440003803c0581180c2182c806c4a2003480321401007600e40380207520508048540c198803100210a84001800982c400d12414a01c11914150b920600c554001a0810303208000c11203440c111603100d054809a101608281c5212000d020010001e5524071a0800309540e0300d0015032240 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 961470935 1250 961469685 961469687
    0xf030507300525050705010906060f051008160e150d090b0f04030215070c050d200c150708040f0f091d0c270a0f1512060b0103230403 59
    0x11809860500f2481c11010160480b03000041d000c00c040d001498a0b0f03481c0c02142c182180035202403100500b07501d240c020041044c0944503a400b0035542c05070740d8903943e0841e101d070454030380104070781e807142140c18619a0101c0500c54143c2400d020401402c8035860060308800709131b16801038400e00865551010800300f00a440d50120303600c4000c0040c5031019252a442c06511036132501007401440142c4400030740440d000303000210303890341c0000c1100e12140c6030030b0014000d022032141501d246242000790340020f46d070009a03010f0849014208543d51540f800410425802c4401c2c21140c0410920011401c820f480442c0340007003d03050302c06103074503103000c01c1c2e901255501201c00300080d2003a414420710090008600d4000e4006407511850303400544a180e030b840c001c01814042294001003400f40340e109a070813188000700c5420341005a002c1c100c4122b040005280300b48074998050081d02c03000308540368001ca00841c81030601180c6951403643d5040c6102034400b41505604503082400181 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 961472185 1250 961470935 961470941
    0xb061c0507081b1c090b0702010b0f0409170f0f0d150509090d080408090406030b0402090f0609240901030602130801050622020408030f071101080103030f03050730 72
    0x804031000d00c030460441400d072280503110b000203643c0080039202c529010a0344c16440b003044181c104c8042c1d000340c208004c00a001e801156000c0c4c2c45180544151041460b0034801e282856501c804001d1859094000444003600603564030400020240681c070004810031009051401910b200012484142e0b03260003099650347c2c0129001d11064410014203440000304042c00032540e041144080d0760304e14140d1450302c200c1080c503422a0520704000200480c000d0042d002d00d1084800e21500d80d40ca000b448d440450403a40254042c0381c8001046200401300300403124403100702e0095101020b00e1011840c003400a0b0320446601e58002800c1240b16000d031001d0026003096002448281030443c0091407500010040c6000500042900000b030b1049a0454005001e04000c0d00d40b14865903440800035005410151000d0039140081c5040758480c2c4000c0f0706881d40341d180d810002c0c000240450041200515210600c10810b43c4101e151032090350714401c0181c0b4030080c0d0205828280720f4015 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 961473435 1250 961472185 961472191
    0x310020a0f0f110c092d010f0b12010605090301110a030c0813050312090703020301060b09270601140d060b0337020a0c05060103060c09060c050d030222140405130203060601030b061c050708 83
    0xa80300502c01c12b000300c00041c0a40703044030801d00e40242c4030704401000a00401c540310341102c1110000402d44100d81d015004024105001c1e00ca120b00b03585c0740403a5903802c07005405e004145410130001185542c80d0485601c1e0400c6101e130481e1102c91312540030908442c400d812690307440001040320151490034070350100d00244400c0d100418220600040396031041c0c0071b460181805405212107028055010a58618004513001488083d5403140c0c4603605501c281c44440345e08401c2011906162441d00752046152903000341018200e000d050701400941200b900c0100f0840c601c3d00702004140c0800249001c1c5000b400001040740402101901d0700c812903010909105080c5884000714001044415501c1e0007810b01503940c1150a01c1c000007400480300340a1031070340901c800318040003201010061003005031402c00c0203444100000d44c3c004941000258550b109400058655201c1d800034404040060041800c00030460481d040002c065038100e5042c1e55580701b04020285c2c07050707400350 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 961474685 1250 961473435 961473449
    0xc1e0307020325051b01022503120206040809041d0f100501080c030a060e0304180902010e1c0609020310180203060c0304020114090310020a0f0f110c092d010f 70
    0x141e52585544d03019158240340c4815000e01e89080050a40c590092102c9a1605c4070303a1b4a04241222060041d80500d640c2c0c00142d441c0c8030f141c50003c80003400081d01a01540e0044510303802c2c20800307801c02014000b10068600601c0303a007803000742640701c20802040d03032080311000341080c1c0880c580100b080310816440f100443d0b0164200c0c0c3c1c11906c005c030705d42d2a5035030000c9002c914003880269a501d507100d00c0d0f0000440013020a1143c150a660b81d0003151800e03c02d9a0b0000210008010844d826143c40d03401c451072b00003108600001501c075402511864030140580e08d044030b80807402c00c12142c1c0f150f21701e4000c0320080d583c0401c525003480200d6000210610aa041d0700301900000c0001040181d0f0714030341c0400141c04001903904200640c1045010311041d0360f98031558000400210014040c1f10209031551000c403071f1940911805901c261b094401000c50507003072001c22140e4400500400b508948500c02079141d180510705107c41d01900d18075200340d03075250042c1c200c1c400c01c0d644d000e65 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 961475935 1250 961474685 961474747
    0x70321060b04031104020408240f060906010e040f02031314070812160503131805061c1a0c120115020a1416030c09060504140c1e03070203 61
    0x7010101110342550203807a044044082081e10040c0881d000348501d42014100388100551003c00c0300c080811001908903121003124030740c4840c040501803c0c030030780d61141c0c49100d202c0010001d51040030380b807422071790082c408184040514454022a41709aa000c1c00075200381f0382900c207003c0000e035004007200c1204004e0440300d180056060b01d03110000441402c07036100040054900303100d903007040c90083d0000b00341e070303944c0100050b400812100d81c400c948112611408070112141a44a031500ca40405403c01110550621601c9a070350f511113011100c00c2000b818802c0c524008006141c41913620b940040e071703640300c0a0b032282e20b8240141d100380709a500d4040398401c0c6076400b00c0c0310740d042a440400c0c202049051070f80d80e42808881e408200c0300503040c1c080041403251000088080782e2000c24200035998071007003400b0940c1c2c2c1d401c0320314403842d0441c0c3c003180e51484400002d04010488241400d2500969a071500c2650b10950303801c401030340089420189040304403c0c004d00b0160449440c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 961477185 1250 961475935 961475939
    0x2041406090a090905031908070e0d031e11100b01110303071b140607080a051501090e060a1e080705040b3f010e0606041509020306040b0607032106 65
    0x24030400d907203004016145441d131a480003008400c2040e5000c4880d4040d0320183c000070842d008100c014219821000212070540440072410080c607a01c405540540c0c1e941240c09031904000c1a407250088078500b082640304070410354460620200690b00e0300742c0000b1a82030f0b90f0384001480f802c00c1d0a04a6029002001801421030b0030a142001c60a110b00703410041b4206410110704540c0c00f00307031f2120301d8081c007010030030025404010700f071281203c10303402c0245407103140303ea144060609580601143c840c1c541401101e042c20700290703029a0043c00c08504a4131080c7c1900e0141060401b04004030221406004150b410311016020b00015142003110510500000d41e00d2106103401000b007a18094000540700c40b04020000c828042c1c150901d0341c503e2a110207402064100c01c1c40100d8000e02020070600d20380350041c02110304ca030b00360b584485801e08030040000c1d0f20141031540e202da0703a00c0c01c031709890300c3d42d1011740002c42c000c1d100c03444116a40303903520000d036480705002c1100034034298003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 961478435 1250 961477185 961477189
    0x605090c03030316030603020a0603020d1a030312040c0302030313090e0c0f220e0c0a0527090703052d01090c0b1e12060114041d0901021c0204140609 66
    0x90b01e07440b140c0c0d50380e0b129943c1c44d841c406800906194101a4010b08000400308a041c0c140d0000c01400c3c02c0003404103d071400848101000d80c10314841c19905801c20041c0307449541c80141a00c0e00b160060310700c604403d560354000780c9141d001e0007042420451a89080006400d14850700c5507940000d00138111180010002905c4010004116445800c4100203440c0d00ba50000c0c41d50140700002c00300700180200a000140d0742d5000030003c9200f007040050220701801c16a011842000305404d41401012652076011922a030080203981940700303000c030001c0822802c02c4403140b5006050308481440c9030806e0803503482400e52510051136070420606000284d480f42200e4222603410868580302c400c1c207542c01e0b01080f50304bd00a0319500f800705074001e9075088005054010303035098a410034101c514134007648284c00b0750311035103081040c0543e5190700b4001105090ba44501135074001450090100300340c0c400340ea0354602d6140c2091380800d090000c010b10080d2660526800c59015042c031100b940 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 961479685 1250 961478435 961478437
    0x6060a05010807030b0a03031d0a030b0402061b12030a0c020609060c0c12180a0501080903090402090d12180b120c0a03021e090a0b190e030304170a0605090c0303 71
    0x411207040154202c00070318003c2c400d610110850f680104880300555403410300509c446941048100e407104c9261803505207103403240800013203036445000c14906581d250200081500041802140c6403615006010b005d0b10501c007540001900051b840d84034140890b99804035078101038604255031000017405860300c0c0001c1c1050b80100e449001c690f48038181829a400c200507420a50801c540115040814903a000d0032890314400940c0d800022030f40d508011218030000780d5149041da00204190001c5060a030020705010070b0140442020071200e554119014080c900f00d13000007610681c9680d800c0a00da51100024021800300302e05054400324586500c0300b01410707481c0c40c6103001031141c18103402074058504001084490842551b030061b0840340da54070078204c1d03c0c070541c80d103840802c8800d9100291504800c5050307403102c0442503a00c044d5840100b001c0c205074107110902c40007682c0c1e43c00b0001c49800700d054101070f0544400d1403078101c0130386d03c0180c000c15580d00180c1201c01251030002c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 961480935 1250 961479685 961479689
    0x2203051018110f0a081c020624061303050c1f0527030f03032e0509150a0801020702130203130f0611031302011803030203040b0c07150e0102070806060a 67
    0x202da114042c2040300040007041031810311074202e05042c100140e05140868100c1180d50f401e0244120004440030403611a0001c41d64214080e44102101080c40e20310b04001d01c030518060300c02440c0102c81daa0103500040c480c0e2040354107038040d416404841c1407102c09402c281e071039000b00c2d2210410b51b880250950150311521025424990f15641c2040700904944520050280070344c0c0c1c8010105c04000c1d113a600440c0c2e807002c0c030743d8a04a49030000e41000103040d0000c46d540703c050102c5050108224050f500a030100880c5041a20398001581ea81080c0c080200200000107a5681162040c8040b195072251031881c502d106108000108902028519600f41d001c01d884500310018035100005151246000744502404002c00c1000884540103022030360003622030240030001c40f041c0704031000e03040c00000e0060300280410040345240d44040c0840310300c04020f9920f165103803075500000100c620a0540014011281c02c00d555070140841c0003d080854042c100500d0f054001c901000018 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 961482185 1250 961480935 961480943
    0x904020705010221010f061106072d020318010e0604030b060612070c1103010213050f01030902060d061a0310060518030d0e03120c0a172203051018 65
    0x1030100c003042030a504444c1000700084903e080010308200a1001ca4801d01503105400301640700420904d010780308401c00d0191000c014103142e5202e03141150080012020101d2007d100f2414208001842c00b2401051026900031034032409100e841300381c44205200d059043c01200c0d40a000c15485500071602502c3d000070440344183c44032400304d40244a280d54107005079100f141445040d0754880042c200d128080d11101507000005000c1500302e10a615821040c402c03000810410350501800c010100d100504001400d080701d50041505a03011310202d40d042d542c0c0d030b130381070020510000f25010308540c42070f0018210720b003005200120440c240240c100740a4045011101702c0703502c02c98110410809401d81726100e035120006040c1c0c42241100920174000e4554292400903480103840280100c4c000402160141d40c451540201c00d450000d54015001c100410300354120640984800d501040d603103000c40e245d81821401c21000000c01205203080c120041c4000001002205243e504 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 961483435 1250 961482185 961482187
    0x3053106020a02160e16030506030604030f09090e010b190e040f0816030201021b0d0c02010c0c030b011e080303010b0d1e0e0a140705210106120c080f12090402 70
    0x3800b00300380d29194403c01c001c10030420003507000c0f4000c0558103a260180b10175507000c00c0e0a1126680030b0b003e48004495568055111000040120744101504100250365040c0b0040c44c54982541d441a14840b800f00480350307445907070951260504040702d55002c032030140d040000c0c07130600c411004401406072000d4242e058041d4404140041c05c2c0032500e4180040b061244411403914020f4040e40040c4600c40031600d8007000300002d200c010a52480c5c251480d5288850000d203035005460a4074502c1702622140140300b000700015002e032500390301030809440a40e609030355110b02000e4000780c44e00064015001400104942602803040c0c2d000ba84003540f0101702c0c445c010351143c40c845040711411480d903081115002d030810b40415100d14190203410100c04180440401c2550b400381c0c0c0c03180c2d42e0403030309001001d1201d0070f0000e4003030180d100010022070490755904506581d69001081610110350f40c18081000381c00800c031071144806160003401681d90b003800d4046060040c040c0c203d0003190 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 961484685 1250 961483435 961483447
    0x8030c0d0605130c08071d010f030e010f050402190f090b0409020a03030513050303040e071b05010e07150809101109040f0e12040e06010e1f0305310602 67
    0x14660007020203840040d150005510094104001038a80c000004001c44e882001042c007244c451401e0030306104024101c182d400580f20011140701c0707404009001015600d01c01c0d00503d400c28045c15504e00c40726100440c0318201030040000080c07069080b4003501d034000c2000c00a010315000d424003141c0417410002607041e030000124014040340c0100035440041e0a601008060300840908018030503001d45440d401d4942c41419070724402e40c02004e02c00800100018a060321a02c100c250003600080309c07241c0b0070720035560182034a00481040c1c811b41c1101c00c06200501c0201000070403607a2624003100f641c140410490b40740d518240705101c0140e140d054003000414010120340b00c0c180050030410162460000c5d0300c0090412818100c20303809014903111a40c0d850780192015034101c1980318000da200c002c01900c44041c0c0300341c119041401c00342c6a030160070041398050142d03055901c000c6414504104c17180c12420340c80c410040800070769000c81001d040b804001030991580501c0c01030f0342d45 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 961485935 1250 961484685 961484707
    0x4030f0810123008060604030201080f0c0c0f0c130c27080d180b030f01090519050f090f010608070b0f0c061f1505030c07032a030905090408030c 64
    0x40f0550744542803000c0c18403203050b50b1110a40c0c1440c28096954011035101c50041020901c01c1303100c041c2c000741014000c41c0042036081c035840c0e0098041c011181c60040025945070410403106160f41c03213500300440c0000d541c209401d42048000b48480700b00b104551042014054103008405080c82140d00000000e902e0300208020000d0109841120052521008005d140107c82e2840d203100d1030009500043c00c928002c1624001e4682846074003da030b0810f601c500c0280030060038022080b41455000307824800601c50503000703283c00c00b5036001130b203408507150f031420303070302c1c100e13450351a0b2602001304a440800b20f04802540e00c028a5030369150303070300c1a4080d00341c007540910f03500c54010704050282c10407a10054513000e58000200607032035941c2d0398919034041100010000411010800200c40c0d0301d402e00101040c0d0310030301740715001941c014007002c420b640c0ca18640d072902040204031010f06401020300b000401045520b200613140c180e07240d290500000d0480f142801001c03c2d074200700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 961487185 1250 961485935 961485953
    0xc0516030c0215271f080a0219090e061f050d0905121e0306062512260103020f01110a1a040b06190b0a0c08070b04030f081012 56
    0x210000202a0b1900f503414400c0c00280c0d010300d0442c0c522007401c51000c0b60703070074100e0525440880d91499490764140c100360031b850500004000200f02d0764208104042c001c2007200450b901030540d5214402c49043c400c0d0321080240240283c1d204d070341e00d148400d49050403111900c0307000a081c0782180c0c80340c0704802c030301024100064000744180039401e64560520b803000060595658000c03840da80c0801c102c1005003203440143e52a6070000d2080280303901038400c1055a40c01189104201c0d810b004007511148100815032842c040080d4154500000c80309020f40e0410002061000030140c95266500140702e54503540c880d141404010710020822078428070803e004982c0280c1d43c845c003070940800450401e81c0407a401c46074a504000801c2107030030140545402c000d043c0540d0061a410100106120307041402c04008000140405200040794017001e04a070620030010031446050a240281c01070000341c070848100004c84040080140d2600035040c119401010344c5446039085090603c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 961488435 1250 961487185 961487209
    0xc0a1e020a080a020102120c0c19030614060316060c0b04020a0e070309120f0f080901020f0c01020c010b03011112071b050309150c120f0c0d0507060c0516030c02 71
    0x4440d004801c0081c1da00c0700881e1100185100743d0030b85403c448900258140ea0064950703480040e403007412940003d00303100f606211200240c280102050380d80c3d40d102819120160b44007060b524880f01404058101000001074180f002100c0718121410031000515041e20b07140c0c0603000740810004241035444800c0500e001c1c1801d403070070134281d180540000e0060003140c4c2d82191040c00c2241d02003882489150010600400c1b60b0350a10031021207441107603084e8000e0704804d80780d5400c0040c8041000810010080c0010b43c070b00240e00c803100b00003030f50b003119a00e418290290341841c2621056410940440700c0b003900c030032101d8445859a40c400c845005d01080380407c000d2280036481e00f0310070008050f0000440482d076164036041000c210441600032020f0400b4990320014200031840c0e42c28000e01001c14608803498182141c020200749001054101c1c0b80c08124005028418842603010381e1008400506140740341074807081007150011082d810140410107403105000456542c6843d90705 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 961489685 1250 961488435 961488439
    0xf060e150d02070803070e03160e100f0807080105010801061514070209130b091c0f0e03062a0412060b0f09160e0d08041518090c0909020c0a1e02 64
    0x900c812091070a03484c9a84190b545502080c891340280c03065280010b51000700100317185040301070030310b040041e60b20713460003800d01500703110756040100e0b00040025102005205040c02041d81600d0b081040c0d00715a03045e000203030240d041c484207118134000c4584e8440c2c1c440c01481c0406400040c00724001c0c040c064103000a50007440001441a12a0803a6004001a018056802054403410750160769520b80074182d40d500d59420000d01d88580c0a40c952088003152070518921801e60100064103210040301c4d4000c2e2011140c1e0380614010840004501461000382000e11341410100e8030360307100e6405c48000b000c558a4408022082d21221031000426401920380c01e40c5007072010b4140801320044a8580c0014960344c424800c038909156480012030f0410035181c0382c40d0805001401840c1e48441190500102000fa400b160042e014510001c00910b01300113080c13503800700000c11804059006119460043c41840300301c42001c81c5081070540e01c100c100c41140c07c0084980c0780b900644601135 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 961490935 1250 961489685 961489687
    0x7031401032022091406090705010e030102090405010e0412020f03070206030a020c03030901090b0901060302130b06090316081915050601090b0f03101a07080706110313020a0f060e150d02 82
    0x9070503c1442c0c0100d00198440c1d5120b414507851410f000303a40300d1044680c3c00c1035038042001000194050a01c1850a00c5d0140025281c4610400840d050f140b0070791060000c199144200710901c80c0401e2481c2400c1c10601c0540b40c1000f04000b4075589000e01072020b44502c0f0700001040030000c80d541120552800d2609030780e140d152122401d4004c1c12901d501b990f1241184002980d1504107115020681e0341c0280145504480c01c25814014008102e01c00d8201e0010001800280d90400910a6045080560111032801c101da00703400e0940110078050001180d00d404000140407081850303003115041c00018499803000300480740984a540300746d004000014006211002074070085125846070414000025650203c0c6125884132544015100b9020300203140080d00d0f450044c002c95010ba540441d070689075070f9101c1456401035446070401141c0980b500304608160b100030008203404610030024600d001c07005800c1c41c8411104c1c0b40310b0b107042d41048280307030440025107a05000c0b8a90031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 961492185 1250 961490935 961490989
    0xf25061107020405010b1e070204141015080601080a02090a261902010207060807030b1302040509061207060c081306050c0709021c091118070314010320 67
    0x12012030740241e400b40d004030304200010401c0b41024088481080613204906048444140c2100f0349030440607007240e11603102d22003a41c00181c06c50040d40182c01410b0901d11091400388109542c00e0001104000d100b40300d0200411030703170042481c0307520070000b400250f901d81d071400010720095001d400000515824080d400d143c0c420484201d201411960100c1e003601c000d4400203084075614003002030069004020074003040e0300c1200c2140d004805414003240c2c0040d1800003801d000e54000c2e003010200c0d4003203003c2210745803143d100c903044034040e1091140c1c0c07125942e03a0f94481c0e0081c010102404580603102c0304000d0114115901c907507903050320703564241d00c80c0340007003086d40003c82d030140c0c41c880c60704081880e081c00d200721103003081404002c0c0c031041d92a001407000340c42c5450303003a2095040301c00000c265449144c1c000604c049440c43c0741980d407130103504c0581100c140481000700820382d000140001b400b04170070244201c2d0310040c02418401c02c200010b4423100240000841c802103001c0c9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 961493435 1250 961492185 961492211
    0x807140109031101060509040b06040c18060507020a0902090901090509071d0a060b161502040506070c03150e030708070f0203030c0106081504080d0c091a120c0f2506 73
    0x303d5084415560002e200c036a03906c0c410031503900c0c002e03140545117196190225106d4501a80010308560b51400c150701c10640c461410f41080145503c6003003c80c00028005007140b0300002d070f00d0040d01581500310300f0b048828012a9104405000304a41255104003040041104005490003414070707024010f03200701604c64442d49840180c441c408164205038010461400f40c400741e4621b000a90701c10f00120344c848d2541c8540c01907121499540581c200070201c0c103500c07440010035105000c0d0315080e042c1461890140a0000e404c1d07641d600080c607044041c042031401008407580315800581283c1c41d0800f500300710301260301c40d04c0c00139890f204c00110300d08a510190815030440341900295640b0114903124624140c1c0211001094204100891000c007242584034100c0c81086d0318000040a85901e510309481c201440c0364500581c0200e03d64a0411416040759031115600302e01c03504140708000100b40900815441002d1a03444070342c0c0400080c031f0035448495194200780f00b889182882c0314 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 961494685 1250 961493435 961493447
    0x2160f05010507030615180f060c14011a0d05070e01030b180a081b07030b07090f090b06090603190c080405010c0309030e150408010501080c2803080714010903 70
    0x1900312015401e00000403182c034003e108440484d0700c1d2203030080203d0b07145001192240c070414000d003014940c0d91804030300c108149035210041c11090311030400510302c5051075003452104c100c5965031a03040000b0382500d220083c0010000d03c02c152140c0c40301d05458980141045120b0b00320824201800000000340846501498054051210b0940d1103840d4080780c90303215002c591015081040401c0604480c0f501e0a150302201540e00c0142d5403a191aa45ca0300002d25041c6d84180001c3d504a0302842401e00c0d0540c2c2c8801000d03001e104204903404580450340d1805000941446000084009014802c019103030a400041c040020404002d0188010f0700711801541c0c20340f00c9610b005c0f00040c0d05802482000341040ccc2644a1144c0d15075088100701d18201146040f40d80c8820601001900360303400d00845020700400c6010708008581242400840010b0540401c40c0400000f201141d581e01c8440030400e59030400d03541d50f07851101c1c1c1021402e003900042e0302181036281c40410341c28183d00c54 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 961495935 1250 961494685 961494713
    0xe0a140d111f1418090405011b020715020601080d08071116060f0503270a210806031c0e06040512060739110a0303080421081602010216 60
    0x10301c4a8040a0010754501c0c5607014040700030301e5152841c50b43c42c032030380b401040d203541c4141f0840c004070f8002180390741020401d10030030b03491000d41e02034801031000224030300e9140000001d0f4801020780d50700d40f03245e140d91210b82102410a0180000c0442c41c5c144c4900e50306920030300a5070032120403040134541d40d40c1c040c8a5209400015801101010035075224200301c90050243d5041240c4841c42c0c8656903220403550050b40502c1c2c803d591310039000591140b40150244e030242c44040e50541c0c0100040d01555005140341c0c4641c002a18010140d0010000c040000181c0e180821000b1101c0011680364865904480e40c042418440383e0f444050019a00e84540e000c0d9496018218080c8807600107a451201200305000368032030200140c0d40200724015000380980c044a03290626040403c4540d402e0707410680001e1003810401080c0300380c5080380795028480702544180c50480f180002d0040304007a1240e40740081100403100b0b402d10035010368140c8405a07a95030003c640038503000111441032 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 961497185 1250 961495935 961495937
    0x20613030e032b0309020d03081f08160801021c0b13140a060501020d050d050415060308070516030b07080703060b1c06080304080c0d1a0c0a0e0a140d111f 68
    0x10700500a03004e210307025107920310383d014050440b40303241e035601543c544500900407284841d048004812580315440034100503e6408040d20344c142e0100e00329901381030103400c8600241c2c01001900030b88103c2d0245110301d1410b2a000050340202400024015161214003404603420000c94000b032950005d80240503003a1080200103459032100107a840c1c0c40740b6445a804a402482518407064094201c546c1c0580b18464100000d510728140c5800c54145070000da543e0700f004141e0b9030401008001c045a2035114030f840c8181c0c0c0b4916aa10050281c0007040c02e000c20140c40046641a0702070b410490187c00c0302c0c207182e62100f41501201c47c0114411210f50380c024140000046d40402c0481101c05582c3c5d60300241c2820803040091140000e83c4d41c100300c905a41c110401c141d002d07d80e880407401001000d20300e9a8800040c1c200500900b04030b2102d610810000781c01304030030301d40c1010f0309010280681310401c501209003070202c1021455007403183c20403015007010450305102d141d641150005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 961498435 1250 961497185 961497253
    0x7050303150324010b0a0c0203150708070c05060403050715140714040b160c1d0f0a02090d060b0414041b080d0503061504050414060301110703020613030e03 69
    0xd4020540d04440142200d2041050721500500c4040d480d03000915034401c2c2030802c47d0072001183d01080c50b0640b40d1015144600050052000c00c690269407a50000401d2509034580d03185600c1d0a034603100c01503c02000d100b030020743c0000304040055845943c1d40484410000701c12000c103240c0d00140c0442d050000034100c01240d00d0b40080c100c060b10150b5452031100350a0900f9904c000710345403e0f80f407003955400181d100004450720162240481543c1051600d505401c00c50305030130f030303040011b0603c004490050100210316202c15031041a0345800c903902103014036045020900414041c2542141c02ca0700904110621145246104134505c0401800c0c0d00f40d60b9854905071582082c000f0034000400c1000490034601d010010600d001c003085521030300e000d65500000d006c540b5421808100d404405080001074030b800e20403884010340b40ca40700c514040541e9402911090014806545181804125428103100b0b0181c18441c41025003103035112040208852805901140030a842c0340c0c0d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 961499685 1250 961498435 961498453
    0x12060b0d0e060703020c06181f140109020c0a02010305070302130f15080105030a0b0604021b0f1b0f041812110105071d06030403120533180705070503031503 69
    0x80301e4801c48203d000240041c103031f2a00e60780706079002035104425041c0c191141416030f180b0761a8582d40f04030b02441481c4002545440a141c2c41d84408050b03001c481050b00c10f110b1010359100125203410f40c1031742482c00081503a10600245d009004000145030140742c0c601c404104a912000410282c42400b618504210070038042124210404d02507d505504180002800901e482c0103040d0400001880036080412011611064240255100180350f1140e1040445c1c40014401c145050f00340700d140c230076500760000210b08000086520703a809540c0c2e44080c10b43c3c41d81080c004070080f6601c0b03007481c48031248851b0000d1940320070495908155180c4008a00c2080c0130701030311f044061001c0310348076848100008001c0c003500020030a45c1801042c00d5541500101407090718890f91180344c000c0b140b0b4a14802c1603400c8000d22082600281452140861540c0c48210b61201000d048a41381080d6461420440b1a4051144000c041d0710020040c800301e00c01d20301000840807000c1e0201c0b64209 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 961500935 1250 961499685 961499687
    0xb0a0e12070f0e01140d12030f02071a0f09060105010c02010c080301060309020918120a0c140304080f0106080303011205070f030809040f020306150309010e12071704060f12060b0d0e0607 82
    0x150950758160388890b042c2903031b00000b410044100d59030101d40c203000409a000256a1086ea4030114049500111403045d09041450041c18981c0140f0702030716651980c500b04248039603441041c0241414808001603900440e8803c278107109890341c0c4041801c2e201d5035507070b901078090691070b40d080f4447c3d410381e400a0000074205114141d200500c800901500c008146003c0c40740d40604030b008200304905440c007000c50703c50700514007290700071001113594a161003010741c1050003020040740c86904000040100031070010540c1d0660b82c011340c041c1444d40711880c04c41d180c02c0c0540c4c8258411542c5080020030302000101804c0102380641c0c0a000d0a03841001070b50491004990040c0d1044030f100481c0d00103914034024580c004469800001c0c04100011501d1504d6030b00c8070a1070381c024000655104005208090301d506024403d005402c1c24100440076040d1980b00780031000b00305040740042c0342400143c11103402040240000740d6034441041c8203030701074440041120361500c5900e001c04c02c2c072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 961502185 1250 961500935 961500959
    0xc061201140118030818100801172a03250303020c01090312140c12090f0109060909050a02130603020904050705090a0b0f07050316030206060102070b0a0e12070f0e01 73
    0x14120a0501c82c003d425507079505004d0b0441c4590501450b5010004107060b1110032066200d80815210b0745650343c5410f04242e125091400c1c031012030b80000b0b444101c00340503500d08405104500064000034031000000c60314004445240040b02c10782c0d68500d01d40d00d21000f200c641500d000c0d6007503600400341d0400564100c0c0c030b02c0c4801042842c0c807580390761055100e01c00e50110b000e1450599440d01200c0744800d8030302490089c4c4805589000031304d070506c1d0324014015960070380e000c3c00c1c501802440d0480203440a0b00303071310606040b40e49410004040000c5a8100e070008400d01014424458990200070700a4200c014554080e6103001d0109000300e010b00b0940d400700e00c005007220540ca080c40c2110300c080d081800d172370440120a020410025100b031001d04a010544491039401c4d4007181002450800040c1c002030554000c50310074441200d010301110143c091170300b0804100f4480a000c110801c20b0041e00c80400d015502000c145074007800004402c440c1d00118500d49039885405030841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 961503435 1250 961502185 961502207
    0x1501020a080f0a14030109020d05010801050c0301030b04050c15040303020115050f040c1809091b060503070c0f020a090501090608010b030307060b03100912120510090e0c0612011401 80
    0x15034941409000815030b04100100161140d515011031042c82c8600d0391540c54000ba040444000e8020030b003414810b401d0f00c240b9004001d03200007031100341002220150244810700000d440c07094410002018804104061040140d000d0490461509030b402c404000717401c1400110015401c12050b80c0c10103913400454010381c1d0b8010040c403c1c250f0800100710003008000608003e0004064003451100040360241000707045581c00800c61507600d01c1e00141012481040c03004800d903040d424485294041c003a207900c90141d05040300050424201030717070f40700b41c031180080d4804018207011895108503041207040b9881d1034800e0044c5520b0f45090780c00d864813580c1c0d03550590b20500002000c5130320354020f00c10030200035094071580b051800c9458107540032424203940c11455804060002d541c003441002c04002220400c000d281010f9445e89081101485044101619505407200081003031158461030440181503917940d000c41031195640d641c0074030980c1d28507440035409074a0713035000f4410b80358 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 961504685 1250 961503435 961503443
    0xa08070c020109061b0602130815190207060e0a1a01080f0c1e0306010b0711060f070204091110110c010e03030f160c03030e03371b0e1501020a 63
    0x2416824500e00311a20001035442d0440301c0c1c00740003807a0201b46c480c4000c0015460341c40c0718014442c2172103d41403800840384466002900c0020401c001c2d0001300b0b803031155020040c080584c0d140c4841c02c00d80040c0441c10b02c468224040d03c1111410480c0484146c41a1030462000c8409613a903408001d40b070f07100100e90042103401800c07060300c20f4a441440c080206d21141c0c11045003c00010100c0d02e005001d03001080070000c009490020300c03a070840c403040030650032100d29151890030505041d640c0640300000740507a45402000c403c02424010000844402800000f10314000c0c3c4d000070000e030001010241c5c980242d1005030019403060300a00c854610290007146089100300da03031260f90303002c419a80c1941c1d0900030850b00180c40e0702c5051000354000c0e60386024400d00c007803c01d8100b0030841c0e00a000911a020140ca8041c2110802d4140360b10b100030011104400f402d00201e0551060b80d05014090142408074450346100b8095025510010b80d0b24000b10120f00103a0740d030484400054 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 961505935 1250 961504685 961504697
    0x60801050106021009021201240b090d06020c120a120e06060d02060304060912051908090d1404030c0902030403020609060c030103060e0312091b0418060b0114030702030a08070c0201 80
    0x240085640d8100705803686c4003138400344207100c1e5802d14030700b1916040030650ba0000c0c1c8000445010581a80e500d010f8007020300d045262599940c0001c814034050301004008540210320003c40d000f090002240c203480510307080360349510303c80c4018000032080030007401c05e5190510428150b43c00055092054402800c8a81c07040c01c40e4080001c0d681004004542c41500c1700038800c00501c091581641464103912040d413190b000900c20492400034202140410502c0c1c0c081211000b000250b0308107000d043d062503010390324200c07480b000c1440b89400c0070300600d16114000030b40d0f0b26a540194486c0c0e0195007a40c0c4a9190903001070380350300003641c00040400c0140010f0001c21200c0c0d11001c401301e034100840f8541307a40340d5824010a00c0c2154500900d4000b03500b2002c80c00d00a403900b1000b40c4080b6403c10501c2c2c0e80c96284040c2468a000c060030031682e8281045050b4007c2c1c0050b60134100201d02182c4920b0b00c800025a04e80c0000c490200095582001c16072250044241034042d540c142c40302 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 961507185 1250 961505935 961505953
    0x10b030a021c1103060f0102061528120b0603070b031501090e070c02030606030a2114132c152101091a070504090b180c070606080105010602 62
    0x314000c1d4004208503400c1c010001c02d0040000868810143c60700e65002000340c90345451010070110800303a10a40d41550480400c000791000d014000c07512001e02155240d840068905161982501d100181c401c8a180f15901007480141d070000420035034811003550a140ea0340100381901c40a041c407a1400440c0d040c408110384225101602c1000c00040c174142c1c1c02d40d65144409070f0f0341d010544922000c1070742048181c0540c202440516444030060340146030005803543c5150809019200b40c4000544c1d5240d86041e6503c0362110b401c559003000c2a01c0d49030b083d9120041e030b26182d58410201840846003045101e0940c1c5100714090207000c580d02c0007a59144000300d0343c20642a402d480e80020b01d060303903941001e00c4030014090151070b4000050030064034a480001c094541852450703800718441009080b075030003070850b0207a45400001081c100e03003400100d19680c0e001f002000380640050200003442d003070080a01030781802494180200f0f030b524119030b400c0321028094540182c0080c851 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 961508435 1250 961507185 961507201
    0x501090b130c03090807080c160b0d020d0e0a150c0306031707170d0b030709050f070c050f060103150b04112703010e0d1409010206010510030e070602030408070905010b03 75
    0x11050800c800707414041030f10100c3c3e6070b1700781141d44911070481d81c1380030201d4005116007080000440c0540141e00c18591a0308186503410107003d070440d03210790150005a020788400041c1c001c0301c00c41c0603110460f4208a400c0c80e00c01002c6586581d030079826403030910345445040c8280602800c49402c1300712140148044244280303d644010f2050f00c40700410040c0300da6540c0d01100420b05840b2010b00010400340b09010141081c034142e001040103410503090156a00182002542001250602034032507400d91500da0300b0301c01c940c1031011281c065800000103100701c4e03c001c0141044103d00420001c0d410008201c00c543c446c0d41d2101103403506000c00502c6003c0c241c0d212401c1e40d14007010076514042d40d000282518010460100c264004c900d0b50301e91584c001042c100025512005d260403e98401c0000f50390f0841481034030b1003404030600c6840110300940c05121420500c4058460903503d600d0046c1d540d03071162252664a200c0c3c2000000c210340749201e994140c0344030341c01c040d1450700e4a41c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 961509685 1250 961508435 961508441
    0x8070804080307031d2e091a04150e010c09051002100c0507021c0308010f0e0a0218040905011d0a0c050f01090e070e010e09091009060615050309010501090b13 70
    0x15960035170001010300350828034401c21214a1860f0043e081d00b61415007081c0c10600e084018640100c4075051242860008150022075040e2410480104c1c0d1195518200702a03200f070f0000280c020075103006180011030006412065085210751112194035540303a007800121240c046800c401078100701801a0303485130075006051801160f1a240c2e080c0700c80c5400081c8000e80d40c1500714950004608204205034001c000240181400d03401f155080b842d000710000100e10080151810b1540080c4151303822076000e425142c1080007a04c200140e49036454524020006e00d03600e600e5114510700041d0007003400286106c60958051884281e0600d05428003000b8415004c515040c0484048041a80180925001d00c5448280c2c2d407110042c03604400541070341760000307007240610050010000b68500000c1c000c07041802c03170301002070051060b0030b0600c000c040721b40180f1180301c40040b10f0b03090135510401450261605100803c10345c0d0f40c80070707504102d6440300c140c6034114441e19030b140104001d0f58 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 961510791 1106 961509685 961509701
    0x41b081f051e040c030803130c080c0f040b0604091b0305070509060a0c02010e04020a030c02060f04020a0314030705010f06030516061b050a0f03020a030807080408030703 75
    0x810803221034600300b40d0156403045520b02080822458084070001035801c043c1d40c40d00c0342030149030540d032540007020603203074209081d50100314120301285d0b0028501c0010007034099285030b00140400b41801070782182d80810188000104071450740181d42d010300c5042e25201d8402d080d0000901110700c00340186080220500c08080c03646c89040440c4c4c12a0941d0070b19038034122461004803a400c2002c8038140d04140080342d4824540d070550070601c802c004070b40035921141d0300e40007903400cc100101c2e0003a40c0015003610410101390441c0c00c0c40c600c40340080907240741c070785191103250940d8606840d43c3c1d03c0c5070b6290010000d20009100040100e200c011080f0340840c036103800100702c0c0c00e254041c039950100d00c0c0e503200100a01000a54181d540c080002800000241000f94880d21042001d502044101001950861060300f6052150303601c100c0d80303825911010340c110f00900d20300d = true := by decide +kernel

theorem cover : BRFrame.Cov 961330935 961510791 := by
  have h0 := BRFrame.cov_init 961330935
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 961330935 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 961330935 ≤ n) (h2 : n < 961510791) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
