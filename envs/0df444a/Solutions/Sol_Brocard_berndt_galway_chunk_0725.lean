-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0725
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:25:23.379515+00:00
-- url     : https://prove2.me/submissions/76a94869-9030-40cf-a298-946036b6d406

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130215827 ≤ n < 130395683 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130217077 1250 130215827 130215847
    0x9010f180e0115050309150604021902010b0f1909090c0801090b06011709061611070308220b0d0b0604050405070f02010c0203090607060507050c07060c120801050d060f02 75
    0x40c10006000350110700c46865060101c41045803400300c0b00c450a11408005001410b0300c000b81c4403030741d100d00040b41c20300341d510680454003a004210300310008580b4543d180c2051501900311981d2007506440c020280b1031403504110038000030380410150260452828043c0c04910b4005e0160680144c4600c904680d44501c0300e030842e0352400d02074607940220418000517603801502e20300c5040300d88505000d1400c2002c04140c5841c1c0c0503150b00c2010300e0080f0201501400348113802103d07982d910a0b20b002030758904001e0002c0d400582c0a4800e00d15004003111103608464181095803070303c0302207900702000e00200500804c8908003c603880a404d100000b015a1203000341d600c100d00596540085402c01c460207401c0d552800301d5442950800d03c852a119292501580c00080d00600046019240d110082e201d40c4141c0c500e00845009103200440e625800c1410314a010b407240c4480301030480e03404012030b4600028002c041e40b0441b02c0f4a401c002c9a091740019115001c0440014036202c0c40300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130218327 1250 130217077 130217117
    0x610021e0601030b01150203090f0102010f0c120e070807032409060e01110301181805030a0504030b060303030709030b0907052110020a020304170a02090c0d2009010f 73
    0x20031a0105a840040180100401c910321180104070344103c038203840c0030500340a0348901642050b10302556034000d6030040b40c9e101f500544e510300d011020812141b04000f000400c1d01c10b190010366100350408911001c3e8207800030301a811181108050400c842c2591340b00b03980c071008002c01840580c141445003440c02c0d13842c401c0e440000d10503040020303400c0c40c10700e02d40d0075984026a00c40004c00300340010007800c110380c6041c24400412000c002103003041180c0b10081c8441246002e0000d102c08502002202d4002c001482683d0041160100342c0d0703a102c08059030ba1200311030040004500042c1000003845412803950000c00600980700019202d0020a0b11000041e0108600c4490382900201200c01884044000040d0030400e500e440d1441030085c5d941d20540c81400400d0750790003002c1e0101e00003030000c49659a40142164075a003000c0380180f08580068407a403081c0c6190003401400500d001d040300030504140708a00d0b0a1504201c01501c044030b00000340d0050100a1030b400c044220a1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130219577 1250 130218327 130218373
    0x10050d06150e040c08130501060b0403050f070e1b0d1d01230c040311150c03030f07050703020a12030b03160603061e09021e12090f07060503061002 65
    0xd040e641403114510a0040801d0425401d2502483c9084007a58044e0392202c9000d600030001807200e08a030140c0d180007401001d183d03100c500d03034081c0882c02108101c2d02161100c02441c5c60011621703001d490348903101d14414142c4882c60000b035840b1001101003181c901800d165800e28400140d44901001e4500207100c0100f0618442e035035800d03095407103903880d19501c1380c91680e20120361540e14011075010b456200710b010282c894030350310703032541d0312030b5508489610300003841c1c2d5a054403034081d14116641c940081e103032480e80001c80c4000404003446003050b50107094140d401800f9580c4103440b19114240e0940c030160400d901d44402031460f880400c01c005010400c00d0451030424582640141200d0940e000014941103000c50141030002c42241102514902c440050343d500c4c000245001284240d004c0c60101c0300007194200603282000e20b202c1c850404c1105407080d02080c413903c4d58540c0728900032075001c80ca007800482d1481c00c11035810b02c02d4919a0048030411202d45008000390244 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130220827 1250 130219577 130219589
    0x30090d0e0409060902100e011d0f0607050f03041e05011b200d0503041409040c09020a02070f030b180d0c0b0c09030a12030c09150c020f0603010b040302120706090510050d06 76
    0x182040c0d00556507817180e0102c101d8070000300144100309c0307500001110760351015011482040301080c44400d00c80140860391020030001d084a0380d40c2c0d5141500195a080b50b051752034403d410800008065001d2913035001d540040c40403906040603250b0350a034052a5002c141d040060049500328015200c2040448996000b44021a1650b2a2101d90141c0c0d40a140b0385034001d001902c10302001642c204403003000d40e15009030268030744104540480c944085544100c00300302d03103240d00205014a0f020058042c5402d240301d0006a201004d07141d41d140b01c0e882c512800502e105090b500400d4081e048580c00085142c90349241014000000e07142840142d4151126141c8601d4618101d030180701d15204006103040c6845040e1030600405105404840940d0a01ca280da0f488411541c5d81c5020540c000d200600603910b03543c41d00862541038000e030208034060071081c061500030b03100018803c801c5808564800074968104000d00400894204043d030522006010780f68403100c0794002c403406411 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130222077 1250 130220827 130220837
    0x50705070606050409020303070803191505010e010f0e0d0311010f0203011707050d0b060102010207020312030a0b0f030a062003130c0b21060630090d0e040906090210 73
    0x52424070104403441507108510841c80c2c02c40313020068601000b91400590401180c607100d5031100a40e410000712707018040601b9180650480c8c008490000410507200c0a9a0b031a1400c0070100041d2020b032038520780c2c90042051000c0c00c6006182c0440780e11110f5119241228040f03058010081c03e41c0c82c594119141e00d42c01000510000a0b5a004514802200c40003480703030301d140001041d4840390784140a04100904000208103900075012503e6481d4058200e50f012002025003c001d0b40082c0c3d40f61a14a0400d10441001d150501034000065002000342c10142c1182ea54075000b4125001c104100700f80d80c024054001c184807001d144240e40e0480355001e882d40d1454081421010b6800c11107080005000c8000c420011180c201c0004e010340301c05d890181c584000003481d9001c2c0c0d0003020210307415000c440c2c903650100d284840030400c050a05104940b40c0d0442c0c0e9844001c0c00c01c0c4100040e1100802c00d072503240030703000030003c980154800035415180350080340080b001c88000d000421 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130223327 1250 130222077 130222087
    0xb0d090210020a030c0615030b040303060806150f12010b060f0301030b0c0c0a060504030207150504050312090904110109090f050609060a0501020c150409021c061212050c10050705 79
    0x418680d80a9801c05128800381c0903520144e500981031266400019007030725503c030700301d02c0c0c040741d141030481c040c41c1c20030100c00e0b03d440c04c1e180060151003240521a058080d81c13011694051001101180b010b0340141008540b186c2c800a210311409050704505e80c540d206d508842640c2c075508000d1018691400c3d00e2170341c942c11800d0448001d01d010307240416821040005640080c00810b800d040d84c0c1e0702000c049066162810224039003640d68000c1c103040418011521000c030703044001070003107030800d4007a1031074441d14881c01000c42c0154000d10390070040d0100007034002204002451504a0305050000782152102c0c01c0c00101d841c1c1c030306200f0600e070f91002406400d141054003160b01c018201e44035403a850402000035102c18051600c4e6020300500760103411040140003c0d140640160901151030782c142480c0292600c1c0d840030550415803401d80089400703080a403440010b5600500c0d141220403004034122800e41c4550500c045600410f031b0244000309140c01000d014800d04c4d84c4503a212 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130224577 1250 130223327 130223329
    0x130218220b060a0504030609031e090501090f0506041518060309060b191a0c06040506010e0906040c0b031f03121b0b010b0c03070c15140a14090303040b0d0902 70
    0x5030210341e0311030302c50b03102404904281a80301080b101500d0740108080740c120314070300c1c090b0340c99413908141c01181e10590700043e01803944200c2c40800c0340ea00341c1e00d804c1c800b03585641082604403d801000d820002c10407043c054440307040118001c100c0d80b860085105000b1000040c1c104070076030400700c000307a1500624000d001c00341c021350b080020708980c2c20304c0c40301e69034040c000c2054540c400d00310800d40d0320034442400c541e50030a40380200803130802e0740d9a524042c40c02c161140800d0085156000742c000205194500016039103100c1c55110591188d0241001002c20254000070040005080c000301c2480006200c0607003980103501c19580c0d4443d65030310904c0980380304030000104e2920f61080001002242144500a0441e00c20102c003075600c0011800a90540c4036011020303102c00e00800c0000760484900150b4150301d016540d4080c1c2c5502910401d83c43c9104029161000404580c0c185000c407100c40c0c0281410040201100e1419540c2e03881314042d070304a649215009540c1e12621815 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130225827 1250 130224577 130224581
    0x121f030f030f020d0906030f09080f0c12181903020301021201051203090108060f0f030d0903030e041a121c080a060807030812091002040305010b1e13021822 69
    0x5403101600240c0b41103414800700a01e030a42070f121b40002c158036400d16400c050045e41c4065000c030380000c440e41da2000c4003441c0e6817180d230002100c1042803103460401005d500c1587d041d20720340c8034110f0088446083d84020080811203080407180d0103004e10750004010386e802d200031715110b44203d820014943c503000411220309030301e4940050344d800400c84685c82d41e074420302480d44100c04485d8412482d044101150030400070340302ea0b641612914411305202a0071481110440e44642c0d5000c4910031184140400c0d50401401903e201c0004410240b00d031800300c3c55211620100fa0441d02d6034040720000c603c80c89961131010300840e8000d0705011071034410303000b2440035200b001d0080400d1455540c40c0c5109120341c900102e02c00500c2000b083d1401024042c114480340580010f5440b551a4144540203103d010825403260304140303904110091108000c03100c01800031b21080c80070700e84c1c2e220030000e0751140c030902282c03a8502c20102c1103981c071050340002110362001503002c1c3e40350721848641 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130227077 1250 130225827 130225847
    0xc320a030e0f100332040b0601170601050c010e19110a080c060c0106091a13050702061303031407090f0b0c06060105180301050c0c0d03020708121f030f03 68
    0x801401c1c40106140c503030b261140443e00c068218030380000c800000b0100d00000c410303042d07810108035a4400c52104c2c420742001629020b03502512203101140c03901c10043d5854002e2220801d505840040050b01d15801007016182d107590480002c910241042d43d01780c2410f40d0301b03409241e8612405240f00601c50b840401c5240341d0b00541d0380050041c100b00c2025036513405400c0c40e038030a02001a2400084200b0742011000b0013591400784405011402d00e51a006c0058440500905045c5e0700c100f44110180127450040840c3d0700a41400d4031203085440503208890720035400c1c5a03e84107840c0ca01d00c000841d5520480a0f582c5038103002d400c120b0400d4041106070f1040051040a00101c0003451010840c43e4001c0d8007400d1103583c1e060b100c0055001b0a1032054007950552822040007880900000200b02e12145401600c14058505c0c806908034000e052003c0d10410b0f043c09900c60810510f0441504010b00b48001604440041aa103071140c8090f0402c844a1080c005030808064204074681 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130228327 1250 130227077 130227079
    0xc021918050c0711011404090501090f0c0c02060306060f0706050a0c050408120d0e010f06030203121e0309010b03070909031824050405060403032007060c320a030e 72
    0x70105007000c4014200c1406a180d0141800e0180c01c0528103136030144980702c410941556401d901c0702c0d0b41d51114002410244541e0880c03900340000204021020f01c1402c008100030f456a4408480c9602800019000140b4903604014100301560004900c00b0140000c0e42c890390000c43e03585000d14441d0240d031240780140090000500091041c4c0c070f00428100481c030b100600b4161103a28410401700648807040c05412154030701590010802c10641001d002c4da4020f404031420b81100600300302241c07044c503151001c07111b070130386115940b144000300854101001c0300002c140e43c80c41200007420004280d0004004c03a60342c0351b11303404060b00b021080e4804080b00381403010340c03481c203c0702414004204108804280c0f524201c0c0001c40e00a00654002c2c08016051ba40c844e91a07107800740000a00c00b010045001040d103400140490001e00c440a0300d02c03e90341d0320303000c0800d580c8180c40140c040b00d201511f03220b02e0700c00d055051f03a481418000010503030020004a04207050250075070718544011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130229577 1250 130228327 130228331
    0x10b0a0308031b0c03030a05070e04020c0604170f0f030405010e01021207030515010806010e0d0b0907230607120504080d1d010905010206130507030b0c0c0601060207051509010c021918 81
    0x19030f413410030200599a000c1c1e070030900468655034040301100c04490743d0001d15070243c070201d101c580000000a246100c2c1d407141c0003401d500181c40780101d60b540503509001c100d4000421a8000000281c0095038202c0e120310004100c2611030008030313099800210f025800702c2c004500700100242d150141e180c21442ca06120384102c420391000030200507004024a05002005e0011161504d42c0341d084405507400890649060520f01811525181144100001300f2450820300c048240361a54000c0310700e0004002c5850301c04d103590b40c155020106410788050207001d00001800a4040c00855110400d582e521591841030f40b1000c20300c0980d82c0d02890400c0000f0500380200c1e6000a072454005911807000c2a541e4003a24049160240607000100030824010501c0070a4a454000c1c220807404801945d44a030b80300c800480e514a200d01c5065405980401443e44c600d0303000001301b02001062504080007403840c0c011030702d60114254150740c54145030004200f608441103402882001c40942 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130230827 1250 130229577 130229587
    0xc020a1d100b04330e030136050a060c09051002010b13020f0d060902121807060810050d030c11010f0e04050705120a0c03180803070f02010b0a0308031b 67
    0x10342d034683c001c40c058181e424000400d0107210155084040c2c807205495095080d4455a46200800b10310600890ba8002c0d070138803030180003600c0c5c66000c100200020402010324052280100c4c0181c0380251001d503924005c06c2085c20100d07110b0b018094042071140c0307030451028500030500c00801c0c050030b030040459140102e40c40d61580d84100c4440074440201340540c035500d44d545200c0e0188155902c11005c00c0c07a140700040c00c1042600a86002040e0510b400032a503104000f02c005600c8149901c3c1840c0c00c1006d06000700c0c0d0182c0c4203a41c2010b4600d850300c10454441c80450b8000c5100b01003980440d02c601002e1041080c1030041e0b030800d10081c03a040782c40c80402200a041c1c20034039000a0312454075030340001c3e200761150058410003898480b03101c050741005035031030004286002c1d42400007420325501040300d4194854203100349901c100602d18540e03807002c048403d220b04032150390440d501c5140e40603888d9120140030300554014540a81d413800c114203d681d4510406440c01115074040c04 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130232077 1250 130230827 130230839
    0x4111b0a0c12050c0409030302300108010b0a06030e15150907030b010f05090607050106030b1006031b0807020f030307020d090f270b040204090c08060d02060412030c020a1d10 77
    0x1584c003000c80001d0303802055080fa40e1034150080e0146068900004c404002014441c2010fa0038194080c140540c0c0760700140d8842804900740d0f94450941500054811001c0200038840da01c582000100c90042c1c6212031038811400400e80c2c02510541c000600800103541180340c41103c00c1c0d08054070f4141013154400317075800032301420038008050b020302402054902540d185c11048502c25a40400201705444d140d03e00041c1c0c24009407414402c009941c200883c1460103442015802c070701a050150b19510b03290001c80b00c01c1d0008109200b10300500b0969000b9001c10409180581c00c150041c3c140217059030b00007045090598404c003100ca20b1308008010020705003080b121200550040170003c1031441d01c0c01c002600341c000c03140750031920005000451401c5940200704e107540503074464140c0e483d41010030005214003440030358000301c2000204090014000d03c100010710900b002450f1501b0f68000840e501076550100c15422210301202801440304040380380d0044000c060842c07040d0400d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130233327 1250 130232077 130232083
    0x3030a030507180f1827120503010b0d0b1207080c03010b09060a15050408120d060501050306011403090a05031305010806010f0c030e012d02011104050f04111b0a0c1205 74
    0x100c592245c2401c40112001000aa5001141a640c81601031010309003c0711544840e0460018141d421407410300d14100f400e44076204a034100c950140c0d0040c10840c900d8a0f4100a1090218190340500100c0000d00b9051043c07102d6001007110344040c0103111605400c0c10709492110818620802520040007125602d502503007040e20f01d0001801103402070ba02089ea000d12451304120214400c01d209040b01001400081c206002c0c502d2003880195500e070019902804103884890100c0c1880754130034514030229000c4e55210128504483d00034041e511120308660184180703421603501d0b414203109658001003800d40000d0280713800301c0f80110300c01c1c00034500402020000d003000342a0307507060300507846403001c0c80c0fa11038800b413403020008460110960b40c0e0304803040703a0090350801d612400754101d4001501c0490703c000e00b0780811003440c501044010500d0420700304100f402400804458580303148040100030441004110092050a00e02c4010300f45e03521036071604444000e03a070000b070004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130234577 1250 130233327 130233329
    0x90103060b010203071a040201200a02010c0318090501031a070512101d09010b041503030806030102040b03010807081b100305090a0b0703022505070510030b03030a030507180f 77
    0x405000900c000001c40103d08612030354502404203058000005508006411803038017951007601c451114000103000400c58140c1c60340400a03582100140d8809540101400c1d83c1c0940310386880c140d5011240c0c0a004102519001811856902d0703005004100e20700c40152040c0069000e410440c0c9440340c030082c05480360201f440c2d41c210310303200410a10401e80c403c540c045c000c640c0300026203825040c1e404801c100e00700d4101c9225824030441d903981d41003d100d80c2c00e5a41104204507480741c151b480960348050054002a050740d42008005504d4410a026502030200310010b05000c900c0c103504680351a10030610104106010a400034166a652519101e00c118a04011480340c0d02c0c1e000311410700320740070310180900072001c003088000790b410b070300414180150321065400003008250740486c6038103000c0f0041c00d42c4e008030720501481c5042680415000280d00e40802c5ca580b2800c0842d007950030100ca8100800d4484040c131034913039004441603610700801c80f114290300340340c0028143c1c0340c546 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130235827 1250 130234577 130234583
    0x70f0e01180902040207080d0b0f03030d1d1002091008010609090f1b020d0f0215010b0c070902041206140402030706030f0212040f020108011215020a0507050604110a050f090103 78
    0x184520691082042d048801c42c40d4008000f10b407204218285607150b6070001c200c01c040c89107810403466803464a111032242020010303002b5030400f60303040c05080080603110900c5880c43c9613082da5135466a41081031068103032402c100541c507070b00048140722114200c0c0580c4801d01c0f40d51401404001da0000a07007049a8101030081980c0440f94803d00051500643d030800c49071518010f022426000940078001d1421965044a082e00c5d001081381c4a910b0800c1585a03080f003c401000003000030340140c142c2c5a0003808ae03e081595842c441c400300e03807099000035140c5000c90414000c0c03014511800140c00380520314170010380740560000b600c94545000d440141591800b003035003140401d905a0300492015000d619540c00d060502030401944c3c450100c0c0000d60407400818a150f052500c040c5581d840820b8030711000042c00d05030041d402030402d01040040c180700e00b1012a000b04034441c010707030044294043d101e525100b0311501c0999600520700030080c11500011940314030744124110782d0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130237077 1250 130235827 130235849
    0x302070204060b030f010f150206060d030306050303071406060109031a100b0d0623090f07050708031501091401120f02090405010b03071704031b020d080318070f0e01 73
    0x24040c800240140041d4001c1181c0420103c10085020740403043c89068038410884103445a0340c52804541942410351260010b800c9940490700d039040c54400b100305a8030a040c00702c0c1312a1030340d021a1942e00710620685a13440c041c54000242c1c50301b8011150004403c0ca08140f10500355202c02c800d2080b02c05e441a48502a40c002030700380c001540340d05028008401c1d100c0c7e5140120325808000d010700340600e900081c0802c9500d1500c0d118981d01072400c0c00050080a05030350303400c0754981e41004c002c1c0a8014081e0803c030a0300015141d400440c07061104141c068400f94600e0001043e002458004c0038000c08090a001426a04007107003100005407035174041065400004035401030b000d120011780c0c11600b00000880d002034054065449001d499896184030000c40100658003401924007070302040e2200409016504070040e0f505102c0c0c000b8140000100d25075980300826401128039800f01d01c082d11741d140c3c1100b01449040700408503409480541d50600000309450034040c03041ca42504 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130238327 1250 130237077 130237087
    0xb0a0e1617011d0a140709030303050901020a0e09130807060e06060909100b030c100206010302030d050f0f070f0c0f1e0b03010b1308060a09030e0337051b240306010302 74
    0x5041d9170041000c00303503010060f2060b4140240c0181c1244018007040380800e080200084211205200350b90790b0030041d5580d140f50711034020a00c002000c0260905442400241030100420703041002450f09511070040001e03064401200b060910102900f030520031407815040c00031544c0d0000301d20900e0020117a0000300058808006843d08203016034264100c00041c160012907600801c10a040380e000350f05851805405040c00c4a01d0710550b0080081006c09102101000c5600303000b40405502c5540d00e4066061a0b4503002034030700050303001020200915a090101c44500c0100e226010000c03013201c4070307890400140007080c1c00b0501950010b18000320380c11145655005542e0700a081203409e0707070b4150070182850000f506180100390007082d80c410010b055070a000507040c10042c43c12004880d0442d076000c00f04a01030340d010007261080900d50346100803a0050020081c1441011220b43c15101c0d144240700003903000c1d20240d56018030b001d20180f032014002e01200c1c0e100209190041c0e0b20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130239577 1250 130238327 130238341
    0x11b030b0a0e0c03150d080a0c1106070507060f03090b060409020f090a0b0906010f0c12112e0c020d0f0201061a0d2007060b0a0e1617011d 61
    0x300703099000d01e85400d420414490445040c80046000c1e86040103850190307007401060140780c03440b0400007003d8030700410000e0380081c81076200351407040c8104060b40c00b0000310302c0001c84941180c0020b030b0b80c0e42c0003101d0800c40250044a4400c5001442c181070082010b0ba850381c8181041c000c0040b4080e50300c5541c62803c55441c0b180107000e2504c024007140003814040b09000084c009141e00743e003c1c02d141408600a5802040ca4140f103140d1640d600c1c0e10780d07400e683c8030b040d91200240b8401c140204508840314020301800b01040c41d05065001c9001c42c19078501c00048004000310801203a80380042034004981e0101c8c07044a19003441c20208030f000102041203004100c1a03100310340109080029428150020f4000c000201c0200e20500c0408024040e0146402000d0011030442108004501c00104c640d00301d007034101402006d0907000c42d540c01075900050030495291488400b805550101a5040aa01e03079031082e0084150203690304080c000c806a1003120b5080400c0070308800010b03a9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130240827 1250 130239577 130239589
    0xd02070e220507032306010b12180f010f02090102060f010e0103030503041e0308040b0a050708151201020327010212061c0210080601030c0201020c0a02010f05040b03041a09011b030b 80
    0x6692028440c514542ea071030305c0c42186462004082034034000d40b00001040c8803000151030100c1400074012400e52641000480c40c050f91b006050202d01618500d0000032100388640380d90350280c103402580d00c44102000a080081c024916210200a20300601a010004203080d041d40ea1500b001c81c4d07251a00d04189020152a41d0019015031414010303a00b00f640c040e05060145c0e108180e0b4419940b00e030f000003001d48000300c58400004a100300001c0488195204180c1d0b008409400d449010356091031481c260f030700890b031032815101c040d0400c44013400500b03507103403420224000131070038422070103451015070030017404262050701c201001c4180c555110340c00340d01c1c5a80c0182a00017000c650140038296403400c5038000e01080c43c0c03242c800d18060060082302d9401c40d10310040d0100604943c01941d41520303003140001006003d000203c4e0340c1900c134005500841c003851f80c005010280c4001400d0f050002044034000380d050403040d14500c5424103406403034100d541004900f180201e008030300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130242077 1250 130240827 130240829
    0x3040b070c171e0606011706010c140d0e03070b030708041104020c0a030e012a080426010f0605060315030c151c0b060d0c120c020d02070e220507 64
    0x54615007082e4440b03144800540d120380461404800301e240c10b440d22925494030003c5a085000c220a8003c024480c040302e00d420ba440101410510000c006a486071781042072021100c41180d40080403c0400f20f400500c004401c83c4200c000300301e0503091800604d200e0201030110000d1040603800b04081200e01241245010009041191a015a91a0166542800c910507008109690000c401551003801d20038145140c103c815803603030094119503c56110740040a8941140c21f001c08120b007991907040d545d500503080c050382a403010210780f46086038040c50341c00b0a91480c0040801042c4c031002e09a03540b1461180000e40740040440200f4104500c0d4141240c1c41a00e080c00d64059007070400150542c0292038080d024000000058181110a540342a90380081c05101c2210480500c2c2c1010700034966500e06003002010440802059610701b031058005600301c0801018041d40c100211801000c1da1f4025407554105106036520341c003541591410300d9009003500c4400e21008128001c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130243327 1250 130242077 130242089
    0xb0a121a040e0109020906010318020607021503090706080c0a0e0d020102010b041814010908120702280203100b060f0c03190915020f0607050a0e0a09060801060f030503040b070c 78
    0x120006828594443c002c10308007200302e10800c03200d800300da801d51081c4100707e9180c01c0d00e00001013103862502007148075003002d141282d224201c10780d0138004200e0603000d1030189030050001d09026007044805070030744000030400d40c1c01d440244810503520b070340103031080c000030340c180c4220200c07110030700040780507200385030555421500f0200c0c900ca07540c41d0404181c18160041c040d000c00b174520200f1203800d8500b2128003400100040c042c52041d400d95552558210501d40110340e2400c0c5483e107620400c003c0441c0c5e0085030783c43d089015003541424481c07170281a8140d042001018010000103040d80510781d0354141028010071010f01c042000c008031030358003000c4000043c583e8090803009280003464019101010302c7c00c201c180d4014000038804020300d140070042c0c80c240d40c50010484140e0043d005400800030100111441d0b520781005030405030081440106076142000d04036801c0d100258892014542d03070f59420004590f010050f50709a800c4441d505690b0441c0d420010b03039022944c4c000d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130244577 1250 130243327 130243331
    0xb07051201170c01020111030406051e0109050f130f080a020717010c030c02060702060106081b030412110d0c080f043f02010e090c160506060a0b0a121a04 68
    0x4140c01c22181102c01c00d0002500403a840c5201d00001242070b20001110200341c0002400030030006001034006560010280c80f541441c0c00d08a8082410410f0a0740845c078403a5803201482030350201c43d02507a51281112075103c4084d801c0303a41d2003001c411204c0c0c0241030100080742c00c4100d64802e020580042022445540046400e060041d009103169949080480d01d0410140710b2240081403240c8a0071503900546116843c105042e00c412000402e140e41000340da5036208481071018010f18000da00403c48410b0040542d1409410b40c6001e004626190340031000d55200d003903218109000255014100a44074000b03250f00b030b0102e00481d0030450346c0d41c281002200204903c6440d442e18100c02c10f00001d100301d0101c1c410070a41e103c0c0c82019000a0440c1d9004066040c40c60405800140c494400c9180c8040110b14240c1c070f07885072100f111547c101c5c0083c0115032600705100c0010740400940186841c401960103040e0314400e03c030628440788c0760305454001000340007110b070446e80e0140003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130245827 1250 130244577 130244579
    0x30f020a031a04060b0a030509070b0a0203130e060f130912020d032009040207140d120b090c09010c0c0305070e010303031506120e07120812010b0a0c0b07051201 71
    0x40a80038002c020021030145014036502d00451415005881c100c60b420070381141307842c2d00486e0850150100801005c590f204502001400131007030401001404d6040d070256072501d40c151a103406112996001e2034640b04050103000080d96440c00000d5190301c2200e10b00b80b410151402d40002d408072100142c00490b00c0ca400c42c8c034264000c2a90080200183e5040028003454241000700300051080c49010803424083c040542c14154010b000803402440c4501c1c4003000c5404e501c1c40c084010710108002039080d90b00440d58040d90242c0400200100e4111411b031074006ca83c14003e02500750240d0401070300d42600814000a408040b015680003801e1700c4400d610780c5040003160314203200450011b0700d07042e010980c00c1c5490301c08905540c455507072040c1d0203030074181c00c5026251002c1c226000c2c0c001c643c00002c490110003100c2c02c41c1e038441c0403036035107074007504080404a000580c03100703500781c1c810482d96200070303404511031800a0703010045144544541c2800c950324001d10f4400d8407510726884c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130247077 1250 130245827 130245847
    0x21608030106092c15030a0605012d0506090d0f080a051206040b0901031410021305030d090315110d050a060503010b0105040e04080309010207050a0c03111519030f02 73
    0x114031011340300700f40e0000c4125002c001e800480c205080030a1483d9074025408201e40e40310240b04600515030007400c0300c0c0c107040503803111b6040320003c0c0e00c000ca400003500c44081d8509400406502200c1e512250703078403220714140200740c0c00d20641150901c51000e00c813142c0104404821480b490b01c2c0c00030343c420b844200020005c3c000781d000c08015400600c400c0b0000e40246007a000701100c804010304200c14030791850707851151746040c441c8003031064000c181485200802610240ca041d01c4800c40b1144114540401e1504141218000c0003c200c010001400810703214203110191000c110310005000500d28004060307801007002e02441241010148021401690010015524118000c000c840d07459001940c96114038800c90603217091450018000c140141e002c2d40e17114848200140c50300352295a518140750341d00d102240d85400c058004c2c07062010343c5001d9020788005890f001580c00c809000302c6150f004442e80d0b845c0c25030f1295100d5612a20a0f00a00d1888040e07003000c0d034aa84c9152 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130248327 1250 130247077 130247087
    0xf041203020309010e0406051f050c19020a08010b01020303040816080a122d021605030f0a020f0106050a0509090a240b0306040f0215071718040e030d021608030106 72
    0x70b040304c0c00201581004a424949403003401c2c116440240041d407241300a071412840808640302c1d40701484400d03c01141c03002c6081c010060045001d04920b140c04095104120398501030341c122507030341d81c540501400541d0700001101d8101c1c4d0032a040daa22135012001c0f01804440e4545c0040410340d012441410854002d0281001804404000d02c00c5422403400d5000b42038030903041c682001d02c0e91600d9501e000d030302d500510720149150b40310f140c00c074a00d8560500d940c4c04000020310744400014074124059050101121007002ca4009201192405001034103011090188034802c201c800040b40e02210200500c1012a5002d07a6540380b604690440321a101e1031020307024906401d000940c2002d01c3c000c10150301c201c0d0f10000b07140001c0c1858080c0552000750032059049800100145004035844c03403024648800c101c20481d503684009030b96460302c400d03840c94aa0050703040c103041140200c4080180c0c0c6484a5600005882d1000e031021180080700da004040d0045100200100700e81d0780c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130249577 1250 130248327 130248337
    0x2090d03050c0f0706031b021f0207020a0b12070207140a03060515130c02011503021e0d080c03030a061e1505040504060b0301050405060604030b0402010c020609040f0c110d0203040b0f0412030203 86
    0x304100480d420004416038031103c09d0070220351010200c50307140e940195140d0140c0080c0b4000b80070420710648800c02c9054503031114030440b8203403100d002044000f82d41000740001030860741e0084044030149a0103d0200005400001c1801d82c0f82c0340000c2074021b02d440e002c048400003d040141805584400400138078109903188015400c082611a008620190401c02c8a60143c50000302c0740c0810208040d011907011120780c001e03500e81000020a040e030300039000c250120340c05103940b8203180410004607200755000542201d0181341400342203100e00024000c5034809175258203031109980c4100c440348181e4205540c410f01c0c0c20804100040d60784003560603603100b600c0401107619450300f00200c41c051844020132109035200064019403081c104000f1301440500715504100503100014240d51404d40026007007035455400c14900c1740e0083c0b0703000d0303c0940d60000d80f0b996008008000d46a00c12750003954404000010030350300004901c401c075402094660401c0251b00d68520b0029203c0c1c2c04 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130250827 1250 130249577 130249601
    0x120c050d080a0c051e0c0c030d05030a05010603062739020a050d030b040902041811041802010c05100e06010f0b090a05090a06050a260102090d03050c0f070603 70
    0x141c82d9103d503106020310115a00c0714841c3c0c03001800822a0382808120750711210080381580035642d500142c41e2410041020b0001b0300d6150a0748034076112280c070003110340c164080340c10982460410440402c03400030180340945038160114131400c0f2154400064492805520441c5022980d40b40016020464010ba1460303961040d05200c8130001c000c036900e05e2074030300252050300080c60404a9500a60040e48000400741000c14258203640000d401c690841c440c01452070801000d98042040c0b40c0508007195004880401ca10b0348071074400701c080c5040c18402818040b01483c1d42d001e00404002106024111300c1c414000042d0782c4020710f885400030300c51303042a803010440208020b00641c0665091043c080d001d0030031b052600c801c02c031440340058140c240d001d03520b20000c607058841503580e1003d0700d610f400a100f04c3c280b00e0400c500d00340039a1580049a4414840079031203540e4004501c0e5940d816113441c503200e40f104412a81050351007680c9627401d1103210320018085425030055410303156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130252077 1250 130250827 130250831
    0x70c08071203030f050403050a05030a060902030a020901110d1d0406080f070e090c060a0813060e0c03071e05090402120106030c05120109050c01120b030a0812180604120c050d080a 79
    0x25802004c415208103440090104e0410710410004034440d8000c4d40e404156600003103a0255503004100c22a4026141140182d800144034507155821030106c41e5080c11040003480f0b541441c020080043c03112001c009264402071050301400c0e82d42c1d030042005403c01c3c030255a802000200190b81c1c0b0402845420300c001e11a400051405101003600000500d014244900d4015600401c171840c02c001403028886403180e044880100c1c2c8140300f1035201000d2000188440c40321181094904020ce03400421014804030320803002c50640d09052081764030903030700c205058495200203203441500c40e0080c10250310b080c00000a1003165000502255003c0d81c9220400d42c184140c0d0342030b103c1200010b03109a00007000300c00c03954860382045c0c000c030411106c001000110030700040d040040c040c42c02d491221021078580d20100307510580035004a8000701c13038040305840b0303c0056125a0000c101906031200e0044d1922983d0107904800c4520b5400001d440d8030240c04000030740001c00584444d101c1034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130253327 1250 130252077 130252091
    0xe0705060f19030603080703020f0601050f03030405060d1404080901030f02070812040809040905060a0b0109030c090b0d0602030a2009010903110604090219170c03010b070c0807120303 81
    0x1060010855551560701071045241c400c52031500e000750351188280108140e590b020000100d2100c1000e400f0341c2d440707940540700420400300d403203143c0740068024900c00d500c054400710071030b9000412902111419200309484001180407840104000030001d8150301d454030403c01007188035001071610314801d823400c12460841c440e0030b80890081c001c0040c243c0384100011403103004012000da901c070f8810003916281001c007801107030070303140450001c40f1075030b000c00d0078001002d8040c014800085828030b4218120741c550745034024100740c05d03c01e20942c0c0d43d450a600700c0325150036000d03109481d0842c0c0c080d035880c14030141c49801000315008001418a0060030824800680f40c21907100603416503561010300e0a5496040041401d100700c158070803410070000070a0b4640f800540000801c035420580d020038030034000b4000020600e01040d080c8100020070040c1ca4007401500e0544003610300040c0c40c0c620902d00301c08100e4003a0041d10b001d1081e4100005e202040c1c44640441c2442950180545 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130254577 1250 130253327 130253329
    0x1c0b09030301050d080304150e070602070e1608070903060c0e03150103051b0409020301050f011a03010b0d3207030b030601050303160c03060e060f0114030c0f04020702040f0e0705 79
    0x640070030302449038070001112a40780456a45006550070900034820f5542025120400408440e480350050030507410004040244c141c052050100400c0d01c580144002d00e81503101e1210015860b5801c0c041c0500f000100c1c1b542807082c1c551030091035010404010b2224a0b010161201200318010f5100c0d12500d015903164680d0054680c0c101c940c404020500d0100d00900310021406000c1b100307030000e40d2507090401595007401780c1c034055405901a01c01c01d50402c07817601c8901c10042115180604200010044012040111500d28170300200001d100e85400b0310103440072081e1454403c60260041049589001c031300c214a000d10010380b400c0185032038507014552549824802e5562680003800300844101d80d8640956080c0e104045100c99070341c82e1303601e4904a850f00100c40030103902c0401044074803074507091101d02428664404020505103c0c2c0020303599404c0c201018061148855610342c01d45981c1c0540300c7d1940d004009002d01c0b4251000040140351162442ca03da1040940005071 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130255827 1250 130254577 130254583
    0x503071e03020a060221130302010b030d020613080405131407090302090a0b150d0204030209060d0b040212101109040b1017060f0603070305060907030510231c0b09 72
    0xe103650603000741c050320381030303407240300003500b0a902e04a40000042650314000c0310076982588a01742079000c42048145c0c03410020700f1504400c2c0711602030f07030205d14403614241e00052050b90220707582082c500514180e02d00820380c0d00859000c944c10060012004049001c6ca800c0707401c881c074901000891554545004607031768800c41c44040d40045104011528080c0300790086070214501400241802c40000c5100105070710000c3c684070324607408182801103251520f441038006000b2505184a00c605448140c00b0f260003410091081c000c0e007401490b203600c144079210b07800035550000c0207018a8901042090350295520a20035498a41c05400324a49510003540d0355809694049100a090101d0894020090328850340000000c40d00c1803182d0390480118420a0103503000f01c1d140c106641031000a40c400f810341e030180340c00c00c010011544a480700000884070b660800b4005400301521084198a4080d81660403044c2d01b02c0007903c0c020b018180145a505c99240040c1e2641d48030030b0303151 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130257077 1250 130255827 130255883
    0xe15010810050a0b0309070b0a0915050909010e060d02310e06010b0c0102120a020a080615160c0e040b180706090302040e010e06040c080c03061918050703050307 71
    0xb50003c19031806114007800d00c0003466124000c401280c0304c4c01c0e119003403c00c01d41c0012501d54005540002e0520403059101c50300c86180c031b51400c009081560030b500240318030405000d001d8000030711100161a60341c03409031030390b0b03084d030058603903880c1a0507030459070038205045d04850503600a803a1250340c50400ba01c501c0c0d2030008076402070308241e401d004104200341c2c00a010603c41d507400307208040504000314070f103500038001e503c8016903c1c4900c6102603c0c628004080710b205d03091950b43e0520030800c460403102008500c80c41a0149102850400411811900031020401845041200f04107010500c1800b80030900043c14141041903115039841d4514060040010340c415420801418550800c3c40d5014051002246080005034031074a00754040b2001d44564603070850420040000b840400101d620079000390400d860900c0416101d104259800d50b81260303903c4c4030f105000031380902d50a4142d807000a840e64541e480c100560740790442c1d54207940000380448041d40e00d94406400c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130258327 1250 130257077 130257079
    0x270606011d092a0307030f0c0f090e060a0e0414011503050d140403241a030a0807141c030506010c02010e01110106090609060911270a0e1501081005 65
    0x6100350342c0c903000c003607102ea604007940080040361200c007420f00c1c0411000e584101525540016203c900043c042c099600b0001040e041c040c249101000280c0e02405050540302c0c402c0c1c6407d40c6446060101d0661401a0b02110078a400f40b000d01040103011b1440321a02c48180c0001d000135041e5003100c841c0c0f8001448014041d602c80b011500c00603015046800c10110311034146410a940d0380c5039076241d4090700310424409a120b0070401186005c9101c0c0300044100b00c40a80c2d200c004030b502103035803080a8400549410f0000ca0b4510401501108241d01e449040061700c62010100f04040740044d001ca10b05400320703081c880052110352060110f062669016500d40d0281c0340d400d001501c0c241c08004901c0b00719501c0380d00118901c400c0e801100018a4a040001a80e0b803425001d00121420031800b0b0030501c100708220382601030718552a03520007050a501440000c1c50354001091003000d036120000081d03086080040005004660ba59040020780f901d40c0c080d5141020600600458004d44e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130259577 1250 130258327 130258339
    0x9020a1d01150e0d03020d020d020102030c09010c08040503010c090617070c02010c0606051e0312040501020c13021201030609140d080703090f020a0f180506031005270606011d 77
    0x40040c0304182c42070180441c403600700030f1107030001d03000400c00416a80328160050ba000c080c0381c0020b00c0c1c0c10030019414039a00d2000714107500304403000f005184510b105150421905807408410300140358121401400000c0081040083c03041c070203090303c03400384228408500c0740312682c91000d0309440303c10703c248030035510b46030a04103a5005560159003401f05607026036541030003040980780c04040305412580c0040c5000310b41802000c00d490100c8000f02c9108089061000700603698002817980c814150480b03e40d180301080350301c614000e0040c0400d180ca0314124000010900400d0741c00b040301f4600034070300c11020b1031880c0d00640e6113051081107400000c03c5240003c56483c80303030b440b25142a2080754080d842905580000d840780095411007100141d00b40c00401c20120152170030b015105440d0400d0000b4609400082c1d10380910100c40f040d5507031540c001880d202c200c1d03000c020220310850164041c52000e10345d03282d500d0001b02d48076404070b4032803041c25280c00c2103550407030040c04000b492 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130260827 1250 130259577 130259579
    0x6010603021c110c0a05070503100e0d0c030c0501060f05041d06040b0c162907020601030303020d06090903030e0705151e04050d03020102030403570609020a1d01 71
    0x14024a000343c0d41d12601d03c000e0003842c2c803640017803016001860140c0b0080403004d00b05800c050525004030b007a4803d03e403030842c0d0718541c190082401841c14160717040c407141481c040c1c02c0c251044400018010b1a55181130408126140032158200c1074400c2640c0400c0484050711007100c0000d591400210303a540318400090002d52420f00c2203910960103c42c0504011000c0d01c5401d0b8041c4e0302c2d0049400030f10b20910a481c10340491950042a5032401c1c45507a00e003003104000c1c0d110001800040e04040c0c000942600d03919039900600000c01694604001309121420018010b04078904030b5111801000301c00a41c900d4008080858014540c8080d0310308250446104200c100329682c10340c0040041c8000100caa60750b5424048050180c0c0000d0f82e2490039240042c845180340d0540741010001c0094101441c1030303401110140984000010507030390400700201101d0005596090a071030102d05040200000c540180722064426109a04c0c86511032060258011f8104092080c43c106540 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130262077 1250 130260827 130260877
    0x70503130302030d11031803040b070b0601020c180414030405011d040b0d08040f0b070803070302070f0212100b030706050a050307030f150510030509030a031104080106080d020601060302 82
    0x40d1031100c00d031003401120310340390000600d1016580e00745150b940c07550001c01048031007071a8a4240c0700301c0b0003040140d458a400c0c141200c0080c080c00703001074001452480068140e900030401c2412a000c010302610380940e11200440003002c048600301c0f2400003940c0e2004455000005a03000d48105031511081e115014519803003095840c0321803548240c0300d0100d1080d60f26024400050580190301060b074540c28045a44070100c01035000ca083e0b40c804100e03800104401e5000d51303070040c1c0309140140e40d8003840d040003081c0034001c0b880658000c000240e2045075500c0004e100307864034500c000c1403100c40301c1407003015200c060501c510008601d0400c281d5000c144100002c580c0083d1501380000c1000000802c48101c8061081e0706001c0d0203039000c10300c218a445034291076980c04514060026241a4180343d489004444203541415220160800b0844030070098a020b010f800c2c0003045440c0d43c82008c1c81d41d8441c2d01815202501a50b400031500c90310078021140da1100708092501d003104801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130263327 1250 130262077 130262101
    0x6070914030102071b0302150306010e010311070606080d020c0108040807020103050910450206031302090a090b0105061e0d1e05070e010e130509150a06030b0a05070503 74
    0x1440107906560030001c910000741d01c200e1000307504c040801440c00b014150301c144a144041c01c8a0300b41c010381c1c14003c0020340daa100d80488051102032030301190701104a0719036034a6015003600240300c542003010200317404000150800b884140360b4225018041c040b001918001e0041da0302521503101048400c001d035000c0e4102d5500414204121000240c00728803480485404201c003000003052075003a448180c001c00f002040400d8a41c0d00b0040c4102c502d81407120094200000034003440c0088001001100110b910003100e030b0f0094000ca42514045048000a0805101c00c403004030906001091a0914800341c0d94120000d0301000c0c80010001c0324241c10f5000315001201ea07581300d43d50340520400700061442640c245c20404a614140303058050004020078000d58104a0800c0d01845a03548100d0100350100d504100041c1e6500d0369039603141089044103200ea002000c1400303006074101143e1110041384d000e1220100c1076101e101c1c440095400646640c00004e0060000c00c40c684149 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130264577 1250 130263327 130263359
    0x10804020f0a03051c080a050601020a030c0302070801110301031506180f1104030f060e0f12090402070807050703030306060201020a17090f060a02041a04050102030a080403030b03060103110f0102060709 89
    0x805003110b25680303984482ca8248134000e441d0200f08482e501000c0580c0000e030403078102d81042c40600c42d901e01800001c0d6a020171110103010440102d08003000e140c002d2001001908080e0000d001b10440b10f62440b5041d80203120407904a242141c5407103d2890302d01c508000e80b4201c9804c203040108041c0014080e02940f03007500c009541d220108000bd850b00030050005500c240c2a443d00000c05e070401004032444a0b4604800d6002044805148000401d665071580d0b1a41d42040e15040c402c0c01260082c060030000070901c0070005841e00c2800300016014040b40c1c425a030500490351115000c074240c2c0903e0b14254046514040d0801c100c041124480354000d602c10115890924411803d520f0280181d03407a882450b1300240510061401e2100c240009107031400302803400c0c0c94030b00000c0d541d00c035181c0d40d0010451260042410948680c002d042003000c0101259115610390030308800f400c01c2c03211602e00c107009103907000c4213039400031851500c03e0a0030f85541072440d250000300c1800200c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130265827 1250 130264577 130264579
    0x6050d020c01020a1d09100b071a010803300c0d0b090c09010e0303090a1412010c02011a042a0507050708061501050708160f06021206150702010804020f 67
    0x1d201280180e40d0900c003401e000282075965074075111144608402c92008007034224002d91b1030004000710030030000c0c7c081d800c40c0d080141480d650151414a001c014440003450324619189000000300540700001400c410784082c1c3d1480041910803101181350014504002600101840000d44420148000d131110140c1101c0105600302490002005200d044805400318100440c811100307503800455405000ea080d0300441c5020703241030001d0503d52003842591a802e405002000b4507071660500c0a13181306114009109044c15128040d01810b40003110b007000d40c000060381400d03480c250140700902c01644045d503090a4250420070002c12001c810380b8180308082040c0400184200101c070005e00021018114605007100700321040d83c101810395040007070500c41600800c076503c0440b9440880c800b804a08603216150800410380d031703140040c10180c404160b8180c0c05140c03900b818802c0008503089603482c8003480300009103000d880c002034002121070002030b0050400034103070004440 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130267077 1250 130265827 130265831
    0xe0112080d0f0f150f0602060a0b01020c0d080406121a010804050102091504050a120812040f060c0206090c0a3f12030b01020318060a090e090f070e090706050d 70
    0x84902c62800035100d4044140c070090b907451154040302c4410001c601c000d401d5800c0e0544100740341905c000d540350b6000d00520310040d51946004480e81c02041040c0403042d0103090201d45c126a4284038a01d80c015114240218005d148035031351140081c8502c2e0f410307030003a0902c4c0c14400c01042c0110f980d580003c004650542d0308010401c1c05584481601c0f008044071400ba60b5105d0400c820f100001c42c503640241c0314980140d040c01d000800c0b440542e24021900102104980e03110b04240e00e800751000c2e03019000c9850000b495580030740c00720300c407131003281500e04540d11400e2000a001c070424144c800d641c400c250000c2032107040c0c01d13051109540804458125030801159140602c501410031130200ca80e511000c07000c200240d01405000c41101003400036600303050b450360200d4084406404254030a80c000211a01441e0040307100d000908040e12041c1120710b844540c041e0348000311281a10341d0711884200180c0781420f05001362080105002a066003890302c40190b070541c202002d826002a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130268327 1250 130267077 130267091
    0xb0a1a100c1b0b09010e06030106080610030605090f0109180209011401050d0e013213020303071b2610090321050411190b0a26040b010e0112080d 64
    0x2c0d1449045a024266107000300313941d500240005450003290b00d40060180c0814401004019040710902d5400003051780c0b07a048290b40010110010601508403590041c00341c03043c03021407011085050305803204408100a035440300070b0030186100503144000e5000e81c1c1c0e80c0041c828001d0744070001600d544103041450138881c400c100401170783c002200034a200d0f907541905088241c1184d0a0710002c01c0e441c0040c454200010900062480c03008088000450181e000c88045460030021246d540303411010280c46030700220002020303c0c071b052068000807400300360a2028100310030201105414980c00515442c2d488000e010090440d000007030741400041d021044841d24003143d0f14001400c028030000e0b040c60589002020400c010a03464041d51415495803da500035081c02000d94440106160300c595143c00100c1c0e031f642c156030000481e5801c10000e11010001238140314000d501c902c000d442c3d181e8031000050382d0709009102d44502d010000c1c4030f20700030403d50001080341c40b448085c045040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130269577 1250 130268327 130268363
    0x30c21070801050702060f04080708180402120405010c030c0c020f0109080d02031315020c0906040e070602030304050c0f090408032a0307030b22050a020c0a0b0a1a100c 74
    0x30003900c0d4040c0056035110b90400130b0042d41803142941c01056000031080904040c0c80703000160160b81c000070440c810001d600040c2c22285101100b05410040055684a080c018180c0c589041500c01711a0ba41c2402c0c2c603a40c841d0301030300a40c1c9a095082c0e440106082d505d07001c01c01021b0501110505001d0b035440d0206007100d061080940c100e00c0c540003941e44010104482820842a030b02010380b0690b601820303541c0365408120607488800841e4005a141c035103800040003454445408a43e034440c0d5000051001e8020026500c224011029102c0151a03a4240541c61f030300000e00d25072000c2d9a80014001030381d090051a048507680040e00b41c0031001c0071020340c014492600b00507021001004201940c1e605018244510b50296198011405420100c0b01a0803112a032040c1c6d1b83e407900b0000382045101d078151041c210210048400304c00e250304009013038a40c159000098141032080d20922196244080f0b04c1c500070140c0f02d00f50030709040c0c40442d1500007255046410715120300340c800031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130270827 1250 130269577 130269583
    0x3070c050f120d050c0706050f010f08070308071211190507050603010510050c0a02040c030603050f0d050d0c1b0c0302091b0702090c070506040b0a0c1e0e03070308070f0b0901020702030c21 83
    0x4910800149c901655040081c0c0c0c0380c039012582e00c0400c4aa03c0803405000050020081d1040642c0c844c02c000500700c01c0d40b6007694850303e07112841907281704584255604240859002501901410683d4065038a800c1401800d102c240111030f003103400035242020b07ca1040c03005141070321010313040e5002c5411650008081e20321510320b49001030f864801c24001d0000070b00410700e141410800a0402d02041180038065000d1a014810820364964241800601503407011841c0f86103a17042c2240414140790401e01c0d20454082a0f01800e00d038000911a074101e541407162258043c4003190400846500308549030030014040030038243c0500c01c400c001601048814062031103140205032030320780a40b4110440d980390011400700024580d0340c140070914014042c7e903250440c40d08080c0c414044010070b18041095000503e4008005918800d0003000410380340071502c501d038071540644840b03817810700340e00074180041d505801c00c88050b0002c0c50114400c44500f403218002d90f000c14400b900d5281 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130272077 1250 130270827 130270831
    0x15050402180d05070e0f061309030e010e0a0503010212070306060203040b091504030b16020f01090b011e031202030702040605010c0b070309020a0b070f050c0a0803030112110603070c050f120d050c070605 89
    0x11b140c0c026001406010310304586c003100b520108150811840060b610000c0490f445440c0041c10302c61850381c0416a80ca030007040c0005800084e0082d9600c06401e0442a804101100c0f10f00000346007183c01b141c69440842110211502d15000d01d003010044020400c20400300040b080719000200f1000000811080c00d0505c115803111504402e00d412036000b81c00c041100914040d44e0340740220349400103c0c0f0545c0c141c12b5400791000c41d80c04000b580c1d030701c442c416400d800180c62000d130b88006d1600103600100a14803213100742e41c24400b040d46c4400660310712500f01c0c2c0040580c01502c0c00070f500d8a11a84c402a4000e0004104e00811942c589005000d0341c41450b0a035480020848550280300b03040000000c0e0940955461008900d13100c40d0585900041c011200300603040003141051110000d4642130081004001c16600d0500c10b1001d030020048060840380b034001c001100c0d2030585c003c00c08811414050200c10f01d40924682e0450003428014100c00401c041840840045200c9208a038 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130273327 1250 130272077 130272091
    0x52203140303042a0603020309010e03030906041109100501050d1d0312100614070c0302040c080105010f02060106080705070215030705030f0a0203070c080a0e120115050402180d05070e 81
    0x15540b4103060a040b405420a020210810540070300070103100101020000e003128207920780180c907612851580303030143c408bc0c100301e440e0303120100c20b002e441c190104d442030040b803041d001d0782164200c0605000741100200c8141d00002680c8408101d00e5014800810840d18101030028115440b40905020601100f1203000c2503803005c2091004411010800341d009400c0381041d0034140c0c0b42001c02860080d9103102e4140003800410508100403828031940c0180d680100140705a200c40c810040450380244113684c0021645900782001c28000300380641a1125903582c51a95951b81e90252110350202c2c400320b803c400783c503101602c0c80c0000301c0954011a019500d00341d50b81001c1c003528190a6026100011182c07042040c40b1130a80c101c43d40310960b0390701552094803070440050aa850059110795035410104985e81d80420070b0065018904a280c2c1c85c940c84060303034407038040c40101e01841c05080d52422103014030f0640d6240003000d1160f000d21070303c2107c42d4991100d00c18000e02e075041d83e8403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130274577 1250 130273327 130273333
    0x303090f0b010f09061208041202130606051206090411090915090102091203190e040b04050403020604020a08010b0109050603100b07060e0c01030c1d030c03010e0f010c05040605220314 81
    0x18400c00145003c5c1c03000a00e419001008506800e40f0342e0741083c4200d203d1891003010540d81902152075902c004020860112803c100c06580c0b9103010302030f9480907000042c060000e100240f01031410401c0d0501a80c0c020803610b40301d199020a020390f5607000780c1030041500c1441680e00540031140b080e50300c50007024001603100c4080c13005200e18183d41a84c80ca1081d0400c5c00b0740e4004104038013400070a0031007442c08810600310040446e0040031140b10254006082c0700401060503000154540180c3c4241c810409990395140e41c80c1c02ca40c034207060b1038005410f541c403c00603490020f011316000807004214038180b03903a640300503040c0d81c0102401c0f6000c40e22400c01000d408003d2083c6000c1090a00f0103101d090801813000f0315081040b007071680010a50080b404941d1400c00c0340b00b001d1b0078003800030005856252007043e83d43c00b43c94085002c660030804000b207424810400d0700e08950182e2141c5040001a00c13001c0d00302d00007a6040c010003c080d540010202d1660038084000028400c09 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130275827 1250 130274577 130274579
    0xc0d091103010f320a0917070f11330d0501080604030f0e0904080a0e0603010617060604060f0c060b03030d0e010b0102060108070501120908040914011a070303090f0b010f 75
    0x2001000c80840004c0318550742e04880211500158441e0b1060312120001001641c40c41c0401c400a00640a800c440e807001c25a082080aa141418003036400307583e000c050140840200940601c155610741c100000407042d002c89554445000c080c49000e0a010340d05080000321150101c60099100c00062741c4654180414160007a158001106243c501000c83c0c4400038042400c0c0100035100624604001403102c4400f41305039140303008000300615003130b500e51392502c8c0140610b18450000009c0400400455030614041040750112031540c1c50b040d4102914800c107581d813401801d02980c21584400036141d4554050001341280c61404d0000202c0d0070252440700d00716080d040030681907501031f60041c086075070006134503401c036003003441c05548002c401300004020301142079004101c000c2c04240850440901c0e000544800304280d40c0041c0e0b40e90319010b4103001e481c03401120000031400c10840f40800d12130380000004e075010b9141a40700e450306a8402250f20401d0b8401c503440c120b0540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130277077 1250 130275827 130275851
    0xc0210020d08100623070b01140a060509030c0f03070f06080f0702011503230303040606030b0c0a0c060c0c02120706020118030206190b06040801051e0c0d091103010f 73
    0x100701c2d604125a141a40d25060a00b1009013203450810f40042480030034101e100001c4d0000c1c0120313074840ba4040c030000711b5542e403001c41404400856071501e1140b00d120300049002da204d1030942d032000d81c1c010010021602c0c180e050000c4040141c0b1400c1d05070194003004a400303994201c61400030070350b0380d0341e020551801e281040a0b941000e401c0100310390400a410002c2c103801c400400039a0380110380f5110381d250720915001c9440300140c9500321400701000700402d200b8141c0c01201244d00943c442c01c60303a03070344d51901d10845c07203400b19240100d81d82450040110300c01b41d119103e80d08080c1041010007100340c00081032400136240701c0103031b83d101c100c0911080b0f03428007403030b664181040c40f0a904090300e9500a900d8070300041100d8060b0340c0c41c102c045003011003031300002840c41c400b0702025600d5803540d40769401381c007040b142104020424001c8400d21007111444a00c982c880004013410010b0080c80040980080f0400352405030140c0d40c102c1181e503080c0305000e2200c2240b940002d100b14801 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130278327 1250 130277077 130277087
    0x80601080309180903030708072f0f120304030c020102010207200301060501030507021f060f0609090e03070f030c03031d03070b0f0606091c0501020a270f05010e010c0210020d 77
    0x5605000e0340d2440180113840b2000002c0d40c0d00684d050820020b0f42d61048000c407503d04000d42208505501449044046510344902c0c51f0100042000d458580c034041c0708a40c1c0c2c0c1d0001d0280314401180c20800503000c40d101e410b141c503c6520510000d4a8030044d078803170400440036620568042c0800c40c0e220042e515092052000814003800c050240b03103041c22000c2e4586e645d110301920300f901d010300e501900750001c0c1e0101001c5c1940c16038000f501c0c0d45440d8000c00703640003406000752451a02ea60400c0c2a10b0000690340c105e54001c0080441650384d81c0c08459400058130101d00381522804210f1220715100c0f05008500c04410007540c49510508064055242c0504104060004035051210303070f856000444a40c08800d944480c0300d811102b98400b100341c6080d0000e40a035102040d00e62400d50b01c011000301c41c0081582851441e80d0070342109100d1690307031003801030841d104041041694003d101c011085c07041414601d00300303103098002c1051004861a43c0d40180c000c040c40082140d080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130279577 1250 130278327 130278349
    0x14010e030d0e0402090607060f05090f060114060d15080c1003020708030a0209030a0512040303090608060d060f021c050417180411160b04030e0414010e06010504080601080309 77
    0x1100141440301081c0d0018150003010745590780a0707500007a50480a440300d0301264145036001504210b80d81d000c55030b0300014181501d07111441d02440c8842e039100f6100041e814180c0d0940085c03180c415400c10104085603120750007072240103460301d881d4102096100c0080c001405204090500c0400100800111200134401c00c400d01d031050002501281960f01500d030300814013040141d031401c8000004e494103a0280008203039100311513041100f03031a5400a4001c40388240c49a840c65078455005542d11442240c14540102d0030403130030700c04902d0300d4004881c034a9803d680189450481c0c0c20701c82d545034030310301000d05186d124010301c4100310b004c50403681c000c103c4003255424042c41c0307070101d002088400c0901c2c1c803a42c4c40301640c041010036081114007015446a602c9541c5199107015000502d0447e0290080780409160001a00b01800b0702100c03100c4120314000b1503800e00030f900702c0000e0301501190411000707000c04255417404001d401e0103030892800950700d0301c3d1640100a07040000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 130280827 1250 130279577 130279579
    0x16030f0e0609101811010905101e0503010503370c0e01050609060d0510090509060f0f07300903090f090207030f08040201030b19090e010507020a080309070e0114010e 73
    0x4d0b009500e90449041800a08007035417040b545049090075200480c0c591043d50000350344510740d40f00d068013181e000f07000c80ca00e140860f1841c0400d00e85482c000d4410340801d2246503016013040c1c03940160480750500c1312140034403034190086844410b0403d201c42915a103001c443c2249e0325031050000342d040c114840e004141c204e804501e00344580e40840c41c103005410540740081e8071100402c10303038401c030a00f090240078410010000d80ca0009002a03a070304003540c11000c0e80f0344007400300340c04075680300e4864498900742e00c401030880b8014003034403c1c00403030809891500c9c1114105900300e0050780160f60b1040e00a641c0d0300149814400c400042c880c0e240d0114451920422106000a402680d4030380f840b942030400f82d1003a07441d400140d020b0f02e070350304440358071000d06803600096100104090056036001c010410840c40d4420015007207a205803210009070b401864054005182240115400700c1d001044e04c2d01c0300d9035a03501a091241c2a00301180d2185610200080c55900501040c90194 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 130282077 1250 130280827 130280831
    0xc110307230118120201121113090b0a0614090109050303030702010506030607050307140904150b030a060506090d021012020324011707050903011806050f010f03080316030f0e060910 80
    0x2150140504e001c0003402c100a06000b090f00f8078240305009540148201e601d054001c0d030b980c1d14404c440c040701c14500e020780c08840703140050002e8a03040011852066a100d80c5840c0a80044d220301d4240e039800603950030307040003226030012402e51020705c0654000e8500303400214460811100301401c100c1d0060400d000c000d8188200103159030301102c2070210b030b50f40b91169982c1e0007400000c03902030031001c01c2043c2e40c1440000300040203e03400d00218820940d00307608121841d07c40f000c1002503c40c14600c2a844041c00c0c24003030140c50010182c0b1003450007420480f44406500c0301081c02d90304125040601c203841458926048200306202c1300400030b09207482400e40101101c0403c05003005403400080200c0800d002590b51400d61000c1c40c0e2110028030001100e00d2803510034040c00c1e084600d0f903031101403607000003070300012070301c480b4180c039400344002e42950745070103150310340c2009000940c0403d07840c1c4030798003200c2802c1c0c4240d0440c44c54020207041946041182c45140400c0070420711580c038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 130283327 1250 130282077 130282079
    0x6030f14190b0c0d090803090a0309050103020903150c090d0f02010e010503090303130302030c0109051011040501080415060e0a0c03050705090f01050708040806090303100501030b010c110307230118 87
    0x40d66945140c0e5205032030600e07150700c60300d2121444009000c0010006d00010380007040c0221400f0010380c803801507200341d4400d42c2580c0c0350401102a40540180f454256205080c0030314542030b008104c691043c81002610b04000414000a0503c0104801580c42c04081d1034400e003903581c0703d008040002c0082c01c14601e1818104031060780d9100c0208803030000f0000034401e80030075109000b04c402e04034035031000344001121800e180c0c1d251860807107a554440d00e414000440d015596043da405c4031030507140c41e1a19503440d1100152512461000149280e80c2c80c404034102e84c000b4a914041c1c14151000189604038a001408441024081c50140701c0300b80101c0380702c0c0d902c500c45e10702452428607140d9143d09091504001d28010b9030000c07001402940c00b0807615900c000082c1d0b00c144040020040a141c5c0d03180154104c414800e1500d0004030000e02a2001c40c1c0f81220180020030094200c0e2140c0c0e07600c0800f4280c10f4200102003040b01080e2400310569a80000241c5c0075201d0704000783e00e01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 130284577 1250 130283327 130283333
    0x603140c270403020f010c180f08121612030603060b04090809041116050610060f080105300601330c031b0f02150a14090406030f1419 59
    0x24180c42101c10802140e9200014201031007401a031040100d98002800341141040b00a00081140082d80c0d050104016000800044051055045548903006040060960311080b0140d5100344503040403024905c044500190190300591085046075500042e500d003145030a8056410141030f15114604144d40b1001150145003141c0e100007003201c001a194080c80b0f041c02a0740190f49080c0041000305c122a401d100010030118030505070442c80c203a02c1e40e1141d20955004003c410043c00144680300180414109900e03101c240125010a18110500c40f260b81078444c102c103030403020150410001000f0301d10340e540303894584050b003011040240d54000f20103514005000050740400c02c200340c0714424140618102c1c402c0c00c040c100382550f1801c96003842c407400d1285840c228003c0cbc40400d0400040010300d0141e651020056880303244040f01d840a5944a03000744404c940e110b6540c2100100066806c1c00c10150184250b281c00d5090760100540c0d414014160306403400045225250000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 130285827 1250 130284577 130284619
    0x6040b0106080402131e1503050f0604110f0607020d03021006050a06021009080f03070f020d17070c0212010f060302031002030c0a120f0614030c01021902040f0b040603140c 76
    0x4003030031445e00081509400059014100802501e00c1c1c81c20703e0103001e00a00e840124814042d01d0140d07080b81d10001040000d5942c8030300840e03021303002d894021103422003864429100c410200f4001c200d5814a0f0407030b0005150725a005001f01d01583c4045500d2035400d94500901000b464115841c080300ba21702071029440b201e01e1841c40200a944203031500c100685441628040c034040c00e0210380ba46421305000e0304903d1302120320005440307914001200e05102c0c08603450303c01003000d541220368031740f800151101e020301c9404a034408074801007221202e13802d2084503810048070602140007481c500607d820924018240e200342d6004100b00709422200b00100c4403422880c1c600300c0042001103648a0007000c1c0f1013105912181040000a90f04204040500c02035000324103540d0080c0c07404005907a40d2910248004000c4503c0c0354071009480d240d4042c05110080c00404549500c0000004003102c1d510303042214600c05090b00350030801c2081000001540d01550264900c1d0006070310209 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 130287077 1250 130285827 130285849
    0x3070303050c0f030c101503020d0b13080307031d010501062106050306010608040201110703120f020f060c0307080f011a0c01020d060e18061302060a020a080c06040b0106080402 78
    0x501c000055800c0341c2c0801041149003002c040c030305490311811102c8a450300e41c1d1035070341520781060030302d4a0501c2d0803450400103070031070b0f50041000480ca50b582d0340c0c0d04c204d00307801404e00180d0701c420b42205000c1400e400081d4894120307660000740c1c0e002c9402540e420700d6070f004108440c1da0300d07140c0144407442e00044a4880480705c122a030100a0408404001074030389600701c40d4140c050720780005829500490114000c5200342c82e4052100640c42e070060f03695000b44000703000780c0c405058040e403071405155003a08441151043d207144241b41542246054001c3d90304010007403000040001c0190700c55412604143c8010b108843c13549030280110a40d050100c4c407112814000035a03001d081001d504452000351111800d1020b1943c2e029441e40c00c3d1000c403444010210350021164444401054082c803400402200060000150302400301903042844128154030030400e100c00031412a0024212020221004040c0c9207032074540340d40184070680c0400f0a10452405220050b520b20a03125 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 130288327 1250 130287077 130287083
    0x1801180b011202061306020d0905180109110f040e0702010c1107051504081005060130020904020403140a05010b0109050f010f050421020906010e09040b1e0c0304170306030703 77
    0x11182c140c00020326a2003208a480c1569030107420025200c2d401044600154110361150322185540f02c06000d124000d41340b400c9202ea008400500c0708006c59403127001802e100d142290304011040d40702050030f0f80180c21240d6103807070500401119660901501c802d50a10b03117041703031072440440c450680c0ca04480c013880c1e100e11099040c14501840c40c02c143c1e4001d02c01f40c02111400700202c40b00b14010101601c00c83d0020b421480c6e00b644c1541c10038864041800402103900c1c0801400c06410001c1d00880c80c00d55005800b00800804907000244080032070b1205400780509252510303045007101c0d240581306060081407c41042281d82e030792001422010b081c03c1c240d00d4101d103440d048031644110740014040c0745441d0840e034050301159001110807071003070b60019266101d010054500516085449605c8124440040c00240d40907031043d03088044d174200e00001d808007080c200c207100011920102c10380c0c4080100401e005071040346040c1000c078840154607606240004c20303143c00340b030300000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 130289577 1250 130288327 130288349
    0x209011205030d06060f080105010f020c090606190801090e01050c0d1e0c0504050306011e12080c150603060601030e03160327080d03050106020a030305040510051801180b01 76
    0x506000382801164a100f1002c201008060303110f441c040e020070410000400022149400483d00e54000d048240400459400030728250810400704841000000c0103d074203c48207020b111015074102c02d04000072149900c03a82d81c151304011007141220020b200c3e402aa030b05080a02490f2008002154003000c0e0141e40450001040c080d00e000360304d01400104e0106107462a2101c070340d58400041c20a0703030400c8007910426684d4070f0b040d1007150900101145603081d6240e0800800c0030500c210301c101c91140a0041c03c2ca038554413003a050901c9101c5485400e000c42c020850945014004158041400d080c100202440592040d54900039221580c402448070040c2c9002c0c1030195400b168032140307466007100c08601210072a034660303000d407080300d401d8400c403200f0303802d80c50003070155034160f4100b130b801008200140d0f00c040f0041e2a0250042d14580600c00c0d0701404404180038591190f0030420103064070840c2c1a065070300310740d800700009201031820007403500020551810b05044611500007 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 130290827 1250 130289577 130289609
    0x804030c1b060201022517070c030812010501032a0e0301060302060c0a0302010612050a02060d020d15080f030703080f0a0b060a08010326190509060c0105060f040207020901 76
    0x28415140c000340801080144a01c0026180d40c150010815203150b0900e140250103460704c1540c004c01c80c10802014200492590803031040000d010f4202c09014160480346290380303850709080c03a80981d5001140e40c80807801404256018068180f00c0d90740c00e107800302c4c1e5032090079602c5900d5a407000083c007000603403941c15030b190341c09411102c05148c004201d29662040b0045240c2d492090b160101e001d9401c0110001301c0818643c80740d81501d8206010f060b626400d031382008100d6018482c01840e0075400c4c060407070482070307603c184d400181400182e00e0900c2d0601d0310300d0307140c1a41c0030100741180c3e00070003103280000c0d40043c1854100d46140d8540d00581c4800c10018050a05480c40c96048480491080030072039010816038101c9005004102048010166041055280e2150b4881c0b841c4200031580d845240b00104088000d0a031401c04e0622060200050595100e40c00c6413829a4580302808414503141108104d4240304540443c901421035020801c040300500c40c4840c00d06080310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 130292077 1250 130290827 130290833
    0xf080d030c050f0a020307061a01080a230117010509190201051608071b12030e011b0210050a023705030d090f0b13020303091512070504080d0207060804030c 69
    0x5554a0110201d03500d5104e20302d29030000d5803604a20400d0310034505000350103406d00c4101180e00210310040c3c0d03855540780d46003d03011001d403610b81128060f01c40086a910060810b41d0030560181c201600c440e50b50300b10300c1241509484c0040c00105298000341c0c00000303040d52100c00020003a90a0a2054540c0d071205c440017400246054060100c00780000c1d000200034680b2044144044524200112161602d01d00e0a89419580380100807510b0200c402c911980903012010411482440c40f201e03003015a40407070880c14544141d03030081789021840c1540c80e9018000039190b0b11030310304010540c0d01d1101680707110181d100c06600a942a10880c00c05201060080340c0701c4940c00c07402031001c0411880c054811a00c000801e0b0780940d49800480c1c4801c00400004082540040085007400d01807410440b41d125448141d00c181071080115405c0000d2040c0f640b889549135895081c4c445181080c514103101952241c48115003000f00d080c40015000080300d43c02139018508880f204405103 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 130293327 1250 130292077 130292087
    0x803090d3204080f0a120305010803250525060e09040605090f12041505120103061509110a090b130315090f060504020109090209060301030f020118140306010f080d030c 74
    0x6000032245005207804c483c91100f00003452101039100e4001c045400150134422070840f0360038081c00c111504200324050769040f8214488002c900c500d401c8641694056590382e140400686065103400c045400c4200d11607100403241c40113184600b002d0070801c2000000070f0390100e00400003015550b5420115405000030002c071001c1318007134411111240b0000d1004412a0800c1c403900703118a1648092400103803084c401c2c1c4900d29010944c40d4016400d42ea5014081c01840e80c2d21320122032038600002e0116442c1c01824650f6400003511a542c0f042d2510040c81554260003810144c401000412006144000400c0440b0740010009061481c0d031104071001e40500c0c00060300c9102e200707810000f440b4003580300c0d50203203100342c07181c007119551015607400f0b0707000e60b0b42402d900c41c900744010008110302040c00304045205240811b08000b01407140c0d00907100e243c0100d0040c00c00c0c803503103c1450034208200d5003d072400d4441d01421514080e82c071a5200300d0710600708100754544800303440550060b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 130294577 1250 130293327 130293329
    0x509060a0207081905160503061303020c03160f060e010c0602030604180b0709170705090a060e041a010801050c04030624270204031703150a030803090d3204 69
    0xc2d0241d0301020100c0300d402ca035546070104c041c0c0301c1c2e000f0500c541c0a100c40c2d52815100f11203024002c2c00c060751366401804414123560b0303400d8055016682c50080259828842c40241141144128444508100600b45003034002c0d000380c3c1c03c3c49222450944035070b802c400c5a8040541c092400769596440f070000c40c0242c000c4004641304424103100d02c50400240305200c80c401c045503528540ca103a03551a19840c040340a400c4140c01c0c0e0080c510500250030007601440e800f841c11500031a9560341c0345c001081d0810110740a41d50300084130ba04400e04410480440d004204110007031050741851a1950300c41d02c11844000c003101e6813001d0300d1b800040f070b800a2818007881d2200405086580c0c901c001203940710421a0301358511141c1809002401502c20b803070a0320340044125850292041100380f09a1002d4115a1880c108926941040d9207202c0600003551152181d5905c0381050719030300e80b03012080c0c0484014890741103501511180c3c1c4805040540c2480030072512000e04000c00d84400380300da = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 130295827 1250 130294577 130294589
    0x7020d0c050d1103060901110a14092106090304050108060409050f0a050610120803070503220309050a05180606092b0b07110309090c09040e070e090a030509060a0207 73
    0x141c2c9070600610260040c3d003070340c826054064406a64405120508072001c10254101840c13082c0004041c50740329601030000c080b1180c01d1381e8680103404e00002c40341c0c0c400480d44180c02e0954252500c1c1042d0034440d00390440a900015424030b401c180c0081c0c403401004042a01480c0c0e21504001482020030031a11540e00b03101c1500ea4507003080c1012070700c3d4401114458669140440f001401e041448004a03c058202c0061400c60712100011511a130010341080203400451007011301034000c108000d00d00174841e8554901080c680401c0c8048072196a01140c0b0a800000d003104409806803c501d0340010211104c2c0c1c0d030b035540140052028000072822031401d00c29010306810288101003110355490007104086a00c0d83e034000c0844268800360046641a041400300140c03900300710300101c1c3c104031040c1525040420b402c010408807480c0d6a40340d9200d5104500c00c000c3d159047e802544c20011a4000e0405100c0340c2d24058060b00c034200046018034000600f450100c0e209001040141074 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 130297077 1250 130295827 130295839
    0xc020907080a150b1c2003190b0d0f0501020f1b0106080109032304050d03081008010b0a21020301050403020d14030f1303090f120515090307020d0c05 66
    0x50a81008103080422200601da1500d81001c0907600040d00004400304c820300d400ca245407040f590b641312050b11202580210154440034800d0241482000c070550744805940219102e103043d09901d2508040e0403104d214075441d0107007111040c0c88400c0e5802202d9000810f03a9850916803800b0340c0288200c0d05a000d900c003001ca2186154400071a0805105240c0d9000303000711a00e42146a0880c1c0d906000100800d01c1c0d14078210744c00d40c65904100c44190400003103401d280c0c1c1c13000441c440c0f12010b01c0480000e0400d008020051060050030400b41029100810411150001054181448e80541c00c0030162101c48007500e1092100c80308a800d0f40a0020311160030300b450041d5aa40b26224007030041240d440c0e000a0203104442500e00c910024948024552918401a0f4100c5103d0a0035010400c15807400b003000d40c98100808001c2480d41d035003154500c4181482828114001704018841441e541406803140c000030548200035011034080c0d1080c0580d151107508201c583e0300c6150070407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 130298327 1250 130297077 130297081
    0x307050715020c0f010501050a1d0a0204150c02031603120e0307080a08040302101407020f06090306040c1517010519150203030403140901080a111201080f07080d050d0c0c0209 77
    0x10501003071307840140d80d03100e0003804546d0300da50070415001240e0151110036045e12204403107425050500d80e41003811100010724040d2112003900808000c400d5400120b01141401001c42c2000c00100c030080d03a46100c05c1030200e0031659007040074640030022404000441c6c200f10407507a42840010000e2440300100d585042c200d2424252682103880141d119003c140c035001000349c0200708604020801700c284526102141e400c00c015642c00005407034211a092004040c0380d1401c201a9000703600801020045c0f038500419082e413003c00f8034100b0100080c292891468001d850182c03415113038115400c01c1c0389118505030340070708c0002c6da00494854452000234160b160b0080003d60142c2d0181d0740741c1c140b425042c060100b06100d00d80010f4001902000003c1e04c515032540308040c032045001d04207143c00300d0080d102c0260306c02070700640c56640104d2a1683d00103000c02c1040024079001f4058881d25a03810400751540c003032180d20305051078595101181c01440744004160b0158001c0c1001014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 130299577 1250 130298327 130298347
    0xb030604050a060b010f05090904060f29060906040e2a1e0a0806010c060f0e030c10090b04030807020a06020a18061404090e03070b04080703180b030705071502 70
    0xc02d01d008050303a000b8504694512207502c01d58840c100c000494885600d4162590103000701c00000901c1920182c1c0d80c0c4140c1050b880e85400752221800d0139110340003081d02c036500079070082c00d4803000b0184954410090800383d522810195012600780e11400400303640c803120103011580e40403203516a0b41400403400341403441c1650240c00c8400f04000e14400f900c801c3c0102c14103905c600003800b00440c1c0403c00281443d8401e4200000b21445100d000c90381008400303500382541c503000b2600005400c003040f1a0302c00f8404210b0501403801c141c0050205d005a900c1c0e0305040c00300584044c2c204111400042e541c58020402801001d902440440d035540461038000c05050b0544008164003e9691300010568400c2c075201a45030410a54a883e041ca00086040141205604003626010a000d2180807443c1101d85a1040d80180364480d86c445075454000c10403504410300c0401c0b00301070117003804903030b5424080ea035129809081035075460b0340e20f040c9610074550058813684100c0c00040e08002d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 130300827 1250 130299577 130299583
    0x308070f080a120b1009090513050d05040504150e06011202130311010f0c05060127020409021e030c0a0c02040f05100503070602010b09060105160f080405090109140c0d0b03060405 79
    0x34a0243e10f00700440c0f100c440030440c048410343d00b41c00c00070304000814400c8101c0caa000b00d4120307002c1d48030030704200c2c00c3d0380e10541001a02d640301c0300070841c042020412030406004500d2042005082950220706000d29100700d40000703840b180c1000400c9101010301d400e039a04039580444440c03500358200e946d0317103080209800b0241801d400900710b88a11315440b03028045407541c3c9a40200a083c0c50b03800c1030b003540001100781c0032079008410a0646c150f0030003c41e01c0200082c240402e40540d40e89540d0700281d000c5002c2107182c1c05408070030801c0010f900c0c0c0840681303811851314640084102c695000240c060b04800e500d90481519041c1400030015082c0d142404503082a020303540070944c0c4400581c2250344288956804c80e0365240028010341c410401000c030b44e103041500a81c60100c0c0d440358502c8680c0100c1c00c40b800480041c0504c03541c43e01c6000c060062245140a1100806609000140c1440030b0810300d800840030412b1034000b1819006202c9102016040b52082d2406080a0799 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 130302077 1250 130300827 130300847
    0x4060203071b050705010809031303050319020d020d050a0c08030a0c120603020915060c060a02071e020d111309060f0c0809192102030c0606040203100308070f080a 72
    0x104a02c00001c0e4200354035000201070041d007010160000919040054a1402e8002d000c10301c60b0104100c0700c40c0030b603550f00411026500a100a5403201e03156882c080b95048191588015540581e00840d0388507800621800e4200643c0b400985802100909603000b0a010400410030300c1c0100400807440354582c0b080c03200805940c0c03074010180781006801300f100c44e5800040d400404400010740e030715960280010200c81d0281045181149280040342030400554200c803100380c000485006000c020188142d044a07000482010600f00740d00091407080b4107000141043c83d003e201e9080c56039940038003072004403070b034405201d50803d528180300142680da40c0154514035168102c41c01e11321902040703205980160013800040140040c1035042c6c030940c5000c40d01951103188400c030303c41c000d80c5070001000312a002503803140040b03e0700c10706151008181e240102c0c418000c11010040307810003901141e410210503940c608071814005062044000040e200140000300c2d800b0445c0d111010311 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 130303327 1250 130302077 130302091
    0x40c02010209010914060f0c0a0507030f030905100503070e040f021603120b0d0b1504060308091807020705010302070503070803150a0b030f0403051b07150e0a03081603051204060203 80
    0x4c0d5074643d10407240340303994843e0154102205022480c031b9480b00c100100412a1942c0840304034604903512a0324003403d540040711507590001d603103000c00d50810902c501504007110b8500a05010000003072503400010301a03c200504915982000c0d00c0742c2d402114030700e840000655951001d10302d0420301e01e138060380c1100003803403070004002c461002d446010a803802c01040d6002c4004907886000e0503c50203885100d00d6884121014800d6440384520402184200e10705500d607090b0f001041001c0404c000c0098410f8101003c1100c010307804110f132005c1e0382090030300680b1820766061091a5000340c0030028042500082400015181e204e141810750300125558003000741c139403140030034500041e68080301560510f004074000900410243c60b408925001030404845081412482e2444651003007203003a02929030030500540c8140d5842401c4c006607110210b02e80b45503140c009500c100c0d8801254a04003140e04801c151242c01140d00199a210800349507062906060b8001d51050ba020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 130304577 1250 130303327 130303337
    0x2120f01020306100507050a0f0804090501090c11060618071202040f030204111602010309170315010807020d050d02071416080d080403080622020f1b07030b07030f0b040c0201020901 80
    0x45404d44c1300300100c40243d84e010002d000d0486040e0b43d2800c0402207442d0803a000041400080ba404115104850082c90300100c04910001e91007c09080ba10302c80d10b00c140d468004400b0040d280c3c42d030200b00d90020b1800c3c0071401150755201c0e01101c0c200c00c200301d0003041c0c40c00090001f65451a1405640c1900d008507410002b031624001100450b206031102200e02100f240c1c0e800d13003d90b00941c0042d10240c0985d40c2401e040f0600080e040e505c0d4000c41704041d107a800341d55240d1155074008140359000301640000d042c00150b503a00035105014480da01648140c001800340c0c03c12101601d41070551030a6800c4410300c841c0049a8869040c1c0c038003420065100c1c1c1412001f6007841155130b0703070007103815880d5151151a1107007441100c0303003805100c10340807090032a0400415442d20060038401e802c00040d07911040780305000c000e030480b0011210792a5001000c10f0001c10140b00900d9049070041c200055041d440301c03c4a00039044075811568032600d46a541000c0b641c0640081c0704100e400d80e15 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 130305827 1250 130304577 130304599
    0x140601051e03070203070209090d08060609030c04020306040209090c03010305121603030209030109050610080c0906030c100e090406060305160305210f0301080312090d05031302120f01020306 84
    0x111428020910040d0701a200480d04214000c0341400841d00100c0340e00c10f5a1402c203580d0007203002035000303a030140d0590344005062003c1da94412803030360b00310504591041c0b0384417115001a42d119074a413029485940c1c0000482c40c02e40c0c49604403017001c500541030340c1c2c04c3d1034401c01e0b0001c5900309100c1590f107400b03404402c0040f490b125007142c044010035910702d4481c4503162400c030002e402440142d80c15658607081107000ca042005168410800d60394076490742420002c945041001c0e00f551513011350700c006d00780086030358045035040307050701e06491070088090b81d4030040342c900c0e1404180d80d400c00d001c0028003041c03100a80101040c1c0b805002118100225414588410840d13171001805e1a008104600c800310a655007440f104100364420394140a030184248440b54400c0e4042c0b41c86510001d0b800e181081b10310b514aa204074541e010301080900c220700a4461704c0000c02c1100c201e42d076030740410215501c03100003007001d120030011200c10000142020f4000d520071b854003840303610a440 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 130307077 1250 130305827 130305829
    0x80a0305070228030b060d05060a1b020105060307092004081c1704170f13292208060702010504060b1210020a0509060a030605040f1a10180303031406 66
    0x42d00f00050921994030074916245440784075100030003400d1103074003081188030311001c40c804000040c042d001016001a0185074807142034203111b03201800030196414071081004541d0007042c0f80d41151070b2446c022808484c040008040d84410240320040311001003004a0500d0b4006910281c040d81d10328030b103061060801082d0740c4141c13818000c060480d850b0000400295822000c030100c480084425400c6c80e1104030b9980301c130340001e400c0c1d404044da5528204180120000800c071516924818000794507001c41c00301c4501d00c2001c250f1240c0a84d440b008a10000348038420030700038001c0c4d006840e01800c00b008028041c041c250340c1a10898140707440f4101e1071074542c08400711001d00c600104480d10201450350003030341240300100144502449103d2094079a0f80040201c402c0c00c0d900020500c0c10b0000300700858001d42e07505504103260003810b50055040144d030848144089607107034160000c811040710451010b22581014800211000082540540003c107054141d00e0f1041d82c0356071000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 130308327 1250 130307077 130307119
    0x503030a05420f15030a060f211505010608090106090b012f030a18080703080a110a061b030b0d0809010f090305010518010e0703020f0f0604080a03050702 68
    0x7644a6150000302840d0b00e40034078012002d0904504050451140d0300c500000003080302c400c000058a003101c00204100d080c403070b11312a02d0040c200c84540c0114450a1600d03890030049207061448001c11b0080c000740611484400c500702d40a86041c09110320340c0c5034800105400010703100824258203010000c910400240600140068180d40700ea060342c50942000606904600504400c202e800504080d0085c00b400140340720708590301c561030034000981c0c8a40b0542c2c801d6000884641103410140001800c040895a402c5441d1030802200c0041d01441801d01007000c0d00204050f145c41c003c0303418209000040403136092035460070460120141300b84400000d0308100208128010001017007198000e070409201078499281c040407050320b954456085035003e8a60402140801d070403044940801d01403a07a00c4403484c8040d011551541c0c1c08211004141c0e112684640f07407541101d01c0e251151001e030380003442103408413070540103141405803031a40801d409a00491040d864048100454 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 130309577 1250 130308327 130308391
    0x302032103190b03030d15060c030903080f090a060e010e040b06030c1c090b01030b01050d02030714040e0102040e060102061e0c090103090204020724140612010204030503030a05 78
    0x35002924558030380300741990504184103421103080c2d4511050203d43c070104040c00c0c4500340c4a0000480310300507034020040c0482c55100340104002c9040000c00640e022002c401101e50010f070154940c4000c0d20551040c1c01889101034202040400020310b0300c3d4008807841a0810a032685103131030814400703000a4a801280e9150400342c02c00120340c14140c40801002b25400503040c0a01d05032000c1e81c01c4050b64203059040e188140c03018014814850003006080c0148801c8485e0f11420000e41c0c00b00380c0360070062143c00b94010140e00000c03000d8803207400808000308031000856a464403074045115841060b92380c203005102c0c4a0006403100ea0030383c004801040c0c0080c40c021503a9802c0341185003030340072240c0c09041503140c20360780d00182c8860010301051442142202c0d6141c0314a007180e54400f00c000c881a0301181044042140300c00041c41c0c090300400203540c0c0c404a10700ca100590f0281c480c5a1000702148000010004d11099a5005501a135000200001e120146100b070f0019a100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 130310827 1250 130309577 130309633
    0xc03050610171b1201180c090621030c150f0f0506090402040c0201061a0c0705030303010807030f050a080c0606040b0102010507321b070501050403030914120706020307140303010f05010809030d15030203 89
    0x10054600300002c110382c4c4aca0003203100385404041c4024a540303181040f0303a180b541252564a4520300c01510180d402070b841d00301d030000001c009610306040040d5a001303001c3c002a0103180d82d00042500340d8803c1d00290013911082d00c090344064001c2504102650100d19005030780e0042d81030101e460714000c81120f0486412070002e02c0494115140c050403829000e00072a1107101c5c0c0caa1820005841b2000341017100d160b400035082910b00501071000352000f66061030f04691500040251040d002034825030a9500c004046180c0358041100c8440d0b0352041032141014880810118401c400e80306408c3e08a4041030180c408199507480150f45c54050b0b40002404a030f80b2602c140609041d4480c0108600340060544240c95a40d40d102c1d41411900d0f00f005006810001c0d42d00f05000d001840004140c1e1502c0045d4078543c5411001c86c140500390190303604010300350740480c4c1d180c0f208100307680b0301620901007004400c95427000d100c261000c9100803070007030150390001c8007070783d2080d043c1050140c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 130312077 1250 130310827 130310849
    0x20304060f090e0106050417010504022803050303040b0603070b090306010b0a050d090503131212030203091507020a03141206011404030c03050610171b1201180c0906 73
    0x41401400d40d100200168454108801054005604003803060a58005c00341a1643c650325402d1941c00c0e01c8042e81010b036040700c1c0c0c1c104800e0000503221150803040c00c062001c0c284071903090101d11500d4910141d440a031081c84003109000c18424403518081c000c203021421a1401c2d507a0715203028540c02800d54455260300410010440605614010300280820b403070f00620f0030380e505902c9811a454003c040d5941d903c04101c605030000f59900c4540a81400341d50300b0380340c00c00e542e41c44010030500304c0210101034012000c64240041042550300841400728020828a0b20500c000c0d520600c00c4070940c0055004501484003400da1004c03541803490008008015a07030b180015117500920303e45c21034400350f0400000020076030b0010341402443c4920054030450900804c049100400c0d90408000f290a034404003c000c00e000503800c0d620440d228001c81c00c1810b0b00f002440350081001c01d03c2803542071090208a012500300c003400c5840c840e80f02400400e0f25444c10100701d500c20301620024071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 130313327 1250 130312077 130312079
    0x14210a06080d02060a0209180f0108010b0406180b01020a02150705060609040f02040519060303091401030b0d06051b0a02010507200d0e0301020f0a0f090519170a020406081b0907020304 81
    0x4a17482d0001d02907031034050b01092401100c40749402008000311040d02c0c0103000d04c0c00512a0000078050200c06100c201c0341403214074144142111880700128441c2083c65480b4041d0402e41d0080c04500d4030140c0080002401c01c41540c00c581e010341c420383c8220b4082c050000051f08034030701300000a000720341202c1c0d00051411380d5070902c030060001502d0702d0489a01b405010003401d0f540e0103090051071003550341d481442c1c9000b03044e055900144500a05140c1001e0886480340c41d00790491140913000703100030aa603200d903102c41c00003072003400048014501c0050500e00254054010714003c48980c0c0d1440b81087d080b40c1c144601c0d10a401e4074004640000f400c04034940c3c4903a00130458820001c0006181c00d00c841440025984410b400d038003c1146540c11981141c0c000841d0700042c0802d41b00e81442c0c07081c0e0003844c0c0210006014104050540009038481490100140f14110303602900401075251644982d139900c0300b1003c40050b0f501c8135500010b09500700841300c54050610303600154105 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 130314577 1250 130313327 130313341
    0x14040f1203150b1614010e06010b1918091506021911040c030b0a080d0f0305010b0a0c05010207020306012315040e2d010303270614210a06080d0206 65
    0x80d4442045820707803182800b13540c00440c10440320300c46035440c62000041c2c5400320509250502205034031034034400209000c0307403406802030050041e14180351304e0700c0b80c0d004020250a00c64494190010010340d850311802040804416000710285c503a29001c5480030210f20b401800b4a8a9a84009040c210381035040d5443c0e083c0380d00314550725401c600300860440c2084000c50020543d80e4031440d2964420420b40c2c541c2c039000704102c0b01810b0380313107020700056050200a01c0b40d07109050b0444100000030300d010b400d000003036058503800350340101640c03420351b51440f540d4640d4800359901d412500001c55000443d00e0600a1200741c90035a608560505180414140b40400000c00102c800071100101031400300c807100d000c1141a2050550074569415814010041500c01c84480c400a01c80041d480300b40141c2d5180004448440c03508960108101440300020300070754075100c148940301d100c45410b510300080311520400320050100007040c0c0c0c64840a50b2440d0070041d0501682000021400c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 130315827 1250 130314577 130314599
    0xf07030215040e0f0406060e04080301060c020d0203010e070905070c030206060603060121050a18020904020f0105040906080102040515030f071416051506010908030d09050114040f120315 82
    0x18418074281280d050555891034180302c00002c9410f980300d81c20300c41c00c2004001c0240718001c05408852412595407038503603101e104501c8180280d006018484080c142107594171421500d031a03a016000b4001c01c004c590140d541c6051a000e440b420360b050170001500603100c0e000d02c2d200701da016401000c4540f103e41c2072212980c03020300300030304021701d1691180c200f0001082c0c4c485d0006a0100019051514801103000c490880491480020074103030030380c0250b602c00c1e42c40c54100750100c030882900d0b00000300598007807149034469040b0307905000002031001c170194003410072a5800d5444808d0802c494110b64040c1c441281d802e1028007100c5e0202c0e00c00c0d0310902d180b40d800e030050755480b8941a0540b034000c2a110b2106000c8a403a840b40490448064807141029000780080c00d1070b0403107a00b0000400d44030702800080020031680c2e541c1e10002c3c4074007504810200120758131b1140702070409080011460035902800d40b81ca500104c084941244039109828890040321000b000b103038100803214030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 130317077 1250 130315827 130315849
    0xa030509070b0c0a0b060d0f0305090d1e02030f0d090e0c0c07030818030601030309091a0a030b0711030a051827091204030503070602130f06020703140f070302 70
    0x82074414504045840c1d56074200400c103280010000305000b03038403480c25120b5203500030142030050a40500100c00a02c03a20444002da40c2c0c54181161507130141400309000b80010321000e801380c81d11031032003440103440541c1e18105600031380544021050100f4255070390f0680c0504000003c0c3c000c0000c2200d40541065140c0003c4003608283c41d004680c504545410300b02d810035501da100004a0400441390905080800038003507001e85510340c5981c81c0644489414425902c4080c0c90f0001001c045200040c3c24504500050401032116100d051250144e0710898075107021175205002c440c0d001c030b00001514200010ba5955030b142c028800c0d800b0a034400300e40030858121083c050306900c0d202d441d00d06850411030801281520b0301d00501080d2070000403014002d00143e04001c18004a00040f044034003054101c0c101503900e0b403120b4145103444009030b05c048601415102d02092143d030104494003142e0040501ca004081140701c840d4555040052010180d845803c01304010304241907049 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 130318327 1250 130317077 130317091
    0x806031504050a0503030109050106030f0903080c0a03090b09030a140412110103110c0c030d0903080906090d050601090f0c08010e070f020c130623090c0c0a0f030c03021b060a0305 79
    0x8100e28015941c0d28174541003030b0003240d5116100d200510510341c1c90302c66546480c0740080c090001c0c80700c54030068070030b000107001d040c403d800000e100c5034074902903003040c003120f544060075840350f1504142c541c3d2030360025050107000540c400c02e00c04443c000e400603102a1807801e03440b40981340003980d0745030b000e41c0c4417581e49040c191901140d210070290030000d04410b0249401801c00140705c07504160401c17400920b030409200541405101040c0039000b5912041401d8138065550704819001a0320b184156a008000744100c400100e540e0106402440011010f0042413246c3c100300e003400c0d01c6080e401d019007410000908001811644141c0c020500c40390f213801034407151121003000c241603807009400e00d281242c40e40790401102c13100300000c010b52500c02851004403100783c0700140700c0200150074810040d602007050388452070305000381d03080940d0021f5400c41d01400d92401511070003045200f98003500401142440c009406d0080f402c0c016001002d452403e0100c1d0001c1d13000300b001030402 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 130319577 1250 130318327 130318333
    0x4051305060d06020d0e0c190e061c03170f01150c1110110f0d200118150510060503161103040303020102130f03150203040f0c0e01060e01080603150405 67
    0x2c8010800b140300034039090084200200b826800700300d0300392801013107040c45401400305040580003100c0c26003880094a00084a4041c180c035620001144c4000b0031040b40004c14900d09044101078101005214140d12085048100e1b581c1e10100540410244170303866405151164010042e48038807c51403549101d8000d2441c00a4640c010458400c0c0410804010031004080080507600401c098140d01d9544002410411030180c0b0080c0303210b02e00141030f00342040b071080301c0480e02d07000e41203440820b00b0050000a52076841c10029410b0340c1d80660341703240f146014040703a1010458446503003030701c1c0c03e030701c0c0d091841e100c060302d9000c0740d10b8120b02c100401060640c034405070702d01400200300540c06a400580c0b00c012180c00420f495000d5840120750b000c0072a01000060402c0140d00c03003415080d0b0300140c40f682c660400c01d40000c404c00c030042000f50403607000704881c42c030b41070554182c50f040c1c0d59282086440b03600548846030107940c00c651503401241c211407108a002880c80e07000b0300c56029 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 130320827 1250 130319577 130319599
    0x9050402011215140f031209280f0b030603070e0a0b0a03060c020c0a0e1303110109030f0e040603080706020c070503120d0b060f0703030f02040f0b070b0c0405130506 73
    0x6180100e4282c01c9189400103c0150104420810318064460100307080742d02050541c00000003aa9403600c4a15090703101c1c0b00800c01403800da540c40c0e49502825100da40b05003e10a041240a000c000140195443c00c0032600303010460320501b000f50303441040090000c082c868203080700d25064401c000c15520031030741c45250410041d210142c989008600c41c00010130345c03110b02c400c041d080c414646202400750100c08020004100840d401d540c004036000140802807445040450f900d8502008014096081011800803d540548011b20b44031282c0c3e212491086010f0410003038440318807018040d64801c0c091040417441d1903006158620700700c0c0c00c55002596442c04607060203004c00501600a1010401e840c9841c2c540c0504468400101d45003454621000640400c0307001d030078401341c2096034a42c0780b041d081c401d5a0498019124111603100501d0307803211800e440c0e510107181201c003c0058000b1580a8901d0001d03107040d6a001400ea0400000c141100070080400a040c15404040145 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 130322077 1250 130320827 130320857
    0x3110d06060903060e06070c0305030705041a09041a010e01110a0c06200c010c14070317040303090f050d0308070e0a0b0c0c030f101d240a0212010905040201 69
    0x880c50000340708507207400c29041d14509000040701c042d5070125085030098001c0058065000840d40101075260804075201c0d240c150342140c1c54003507508068440054910b15040c0c280080c1c0182014241c21070b000c2c00f624402908440400d0b460304002408943ca00c2d509220310740c010319860180f0f2151000701e80c004c40c5e61703440da0b401e00c1502da4090b00200d40c1060320306103030b106904480082051004002c00d101c01805d00000d021001032800a001040d26a8105641420a10500006503001042c807042c0e803c4008980c0441da100380b0040b4081820501d0004031444c40b103170640100c40700100422038000c1192001d5510071b0b001003210b810010410f040004070781d19201c00d140905000c0300320315180d500303c58845280070b010020301ca100f948084880d031b1084d040050307200b01c03c0e0748020002c500310440d031084800500306035501018900401c9a86c0c81140202207c0802804010150302e00a40703802030400105d02c200c0d545036a064200c1401440030f031400e0780016410501c1803500802580400c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 130323327 1250 130322077 130322081
    0x60c030d060b03160201020708031902070b0c030907080c0f0108090708010609140a18060b040b031b04060605120403050a09051c02150c030304020f040b0a080a031701080d03110d 78
    0x2d00010300100c0b0100c03e00245040f00d8040303e00782c0a05000851502c1d09a440b208881d01000b01840c4c1620b120b40c1044400b010181c068940041e4000010403880c1011100900b168204480c1203100340305030040081e03078000008154030800d00207485040401c0e001c000440d00c45400514580233445060b02c000740c0c01009228900080401e5200000c2c010310403038418102c0007000d0401c0e42c02904011490703103d040100003a42016902410000d0310021840c0810050140111995418042e080003050310030500c600c0380d041800d04a60400c14030380c460a0588440c0070f070308020402c4520860000d030019020307100030b2661004c64105400c5095444000402c0100001c1a66441c000e00e1504a0304500b8140409100124070040440c1420401500141e80b03000081010b807040038071158449464480754003c00c0c10b480b000c0c0820140c26108d511181d50b546420304114005189419a049c4600f1a220524161070900300070301000614901d086010b801d004e42ca00d8210242003181d5411041c80f4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 130324577 1250 130323327 130323329
    0x3060506220b1c03111002032e051c0c060c121d060a020a0b1005010c15150b03040b06040b060403030e190f0f0803160206130306050a0b030129060c030d06 68
    0x80da46900c000248400c0c07641c1044400450303665400e005100b4050f0022024003440603003540e440029427140201c0d0013882c269a5aa800307240c200040b24030400c1c42e030243d00c0426a0041c0a8001000200d0344e58004880b00c2c1c950f654068448506480f110300960b110789000c8800c041c00e0180d0340c0c80f401c400f000241c4268440d001100150340404821800c0203140c81c03070507034400f00c84c00d11000c02900c0c00700046c140404d070200c000d2055140b0004ca41005805901001200706107a07090624140c079400e9055081d48243c030300b035904c2d40900c00003a50624160103880801d84019003e00c3c18240745035001c0c0c5109140740300d00750340910a4440c0003036030900c0b0040c0900614030f651070303094924036203400c81941d10900d4100d09400d4004010111010840082084840d03506880c00341d83d80000304015000310160340c00007451141803a0901180340d0381500306800b2003c0c210000c02480003100d005500031b44000503400b40c00c0b1800034004a092801102402c2c00f00400f50540380b81a01d40c907075580881c1c450b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 130325827 1250 130324577 130324583
    0x203010501060305150306041101032304110117010506191b060c1107080303010b09030a050d02030307031a0a1401020a0602030f010608100b2208031303060506220b1c 73
    0x3441d410800b0081e00d40a0b80c103c45c0c0c4064010f0710715814651504401ba8515a40003030505032110103001154119035a4101400100c042220803400d00b850508600052044440c1c0094201644a00900a1180007504807800103008600d0008280800d4200c0ca09080044080c0810410700c28402c0300d6004850404620421001903c0100240068582c0c40b11072050b030141d52040740280500c480000481781510007600040b5100c90780700e00060300e40074140700300802c03e0003890410f01c1e01c1070f0000050341c0030344090f48041c450749140300c295107008080003002076400345204108200f00a41c0080c944004072062060342c04150042e116582a640156885122110303000010803030507510802543d007050b107c0e1600d07000c10349403060b0307210b0f00d0142c862440740000300d2907260b580320780e0b42c00d280c4002040807109480d00c2e441c4402c2528811070300307440143c3d00e8504001c002461854104005011114203042c42d0f0030100724030701e10100421076911001d8011407205240154100e55070007842d6030b10300c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 130327077 1250 130325827 130325831
    0x909070908100b0904151113260c04050702010f06080604110405060306011e030f03120c03021c020f0903060117100506090408070606090507020d02011b0905091302030105010603 78
    0x80703011121850111104040520545000e404000d955515203041d90001d404c9640d0301da015610075195070041030b07003c41300c40001d00005a00304d601d210200c4800125100354664890900501d07600342d2101040d00d02240340b68210350520a07091409a011581004207032000040000200c04410100c2d00c203604112010341c05a070070401081901c1d2842e6005020640e0140b0080c1000004207580c0ca0060040c10352490b010115082e52240c2c8845040086401084040c2c030008142409002c00042808805015080085c0340182c1402030080300d0308010500e01034141d0307104c0c0304c120030020340041000004032101041244150340d02045203d0180815201981000103001c402c0c0e86402d020144800003503082c5800c1040c9543c400b481143c0c00741e00b00c806590f81e800180f500200405080e040400c0c11450319051240e050307400500f0b0880912960020403c4818600c1610300ca0030a89480e0030018132002001d1045042c500c1201da040b16400e448070001c6000e9900281c20759009801050020f6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 130328327 1250 130327077 130327079
    0x30c030e0318091b07140c030303040b06040e0d050a051e18010f030e071511100e12040806010603021615020901030b06070c051c17030a0e030301060504150509090709 73
    0x4540031001c141c018104d0a400315241c0140e00714610035005401014040c401c142000c10210201408005000c2c0700090559541e85442d142240417008160b681c140610318110300c50011400004500c00b00031210340b5071604000c0341a004441c1a480b8000f103c090304558158a51081e518001501d0303445042c4030603a01c0215010001803a10015012110405003414210840f010300860220b05907080c040400070b40c003c004005031020048850440300c248242c01d05500010030981c8200d2450b0504800d80b220b400d02441c10a482d4001c40c01584040c0d044040100201c5000b60f006000403004d0104541917482c071511400075800b942d1001403040c6400007411041503038184030701000888202c0b002c030700b09001a190b60300e001d91030b406154000c065904401d016408100c0b17840c1516a4081e00400d60402d0b070210204960304190703074042c1602c0c246404980b0040b8040192410786a0640d110703070a052401c680c0421030840e410034102402020440c010950301c900e020140300303600301c0d152a040c1e2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 130329577 1250 130328327 130328329
    0x9060d0b0910181e03030b060706060801181e05160305030301050f1512071b080403060c030902011b020613080a0309060201050705040e06040b060a08180105010f06030c030e0318 78
    0x1403400c485500c03210315864039110001801c01c0c4031500b01100344040084d141e000c1898240e00810300c81d500d082d071101000c101e240420009420040603074415000a00141c0640c1d04904a0040e41045c010b06c40034000c0d00c00e6040b101c140c000200454050411101e00c1c0184510000074242c03280c00035150394000000501041c00c00c810510340c046402c1d01c002203049403442d007180190040041e03945040d084480840c00c0e40d071086080d60230380303008150010080c1d265441c090206600c1440216200341c108414246154041e1140c44079040e01a100d003241d070000741d1601d103007940946404130780c0310205006d4580000007039100100a01080350040401140a00340903002d407c2690204085a0601c81041041d5070301c2400d032000c0321a42009100b41e03848034030008024101d450011600f0010202d040401168008180c0307004410071580181d40e1210202c0042c20b0300d000340a40c03200307542d03601e104005040c0305e80d00030804a5800c8c070300080c2c2c00d4900684503045900280442109140c0d01c040d420312 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 130330827 1250 130329577 130329581
    0x7050a030f0206190b0f120a020114030105030d080424090302061b0a0e0402040e07030207020109080a0215030a0f05070e04140f0103080901050403060504080d05010806041109060d0b0910 82
    0x705000910b07441c64a02e59680113412070f807100090182e242c00c8905516110400f00300040007009003d0300d01080c001c40d080d940c5007614142a8005070450182400300790b0400304890607200060080d010544040703d0070f59088001400448240102444101d144090160f510804840c6910040342000300760500900d445006800413451444450707094800038030702c0c01100c40c40032090401d0021072030400d000400074040c40e88035080300d10b0400108203c1c00c0d0b050780104001c600c01d8a40322422512503404039a0b41005c040001d4008401036055100024510041d55000a86201c08a622034050803400b081c0c2d00c05580c48408603841050224003490180210b52815520011441e4540341955000f0071500040c8005013101c04000790984090748150115800380da00036205101c0740c105403404140f294407030048845c003145086e0010942c10b0001c00c4803402190131540d42d6075404807510810408420107081e443c0c0c041e00f44258400000c2e112680d4901c1940360f14003410303044100a00c00301c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 130332077 1250 130330827 130330847
    0x6050603120c010c09171e070b0309010b09010b0a0c0f02150d060303110a020d1104150f05030706050406050901080a0612060e0c0a050a09020f0d0504140709200903011107050a03 78
    0x60010300c1c0c00000306d02c1d43c400582460144202c203c1c021a007409801c80c03900b0100540c100340d0102c82c00004225941c503054004802100d01039628000a0303030380312014030043c00b4165944000840c22101040030034000f501d00036002e40000c210302d0034213201c2d007502c440d158003054100702e040e6142d401c02c00505800071007800c601062880603251200050303000500410854a00900c1240000c404030519251507210030394007002a0000f100350340c1c4603901c0d08851412442014070910800c080401e09520130340c141c074201c07026600c0381824818200010b45601900606c4c4c5803840784e41f100d00050364515420040a143d0052000190040e29801384506001022030b9050107040c00341410803072500e4504060302243c6000c1e40040e00c80c20f00e801400814403a1103184c015041c10b04040c881070102c503214031000c84941104841c100c5560f49090300c1660744541480640440c0b0001040010326000014108070a0080002580b58010100d4401c41d8000ca141030f12182e11851040e400c1603002001e0384 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 130333327 1250 130332077 130332089
    0x60b030105061606180b18030f030a020901030b06160213060b0415030906060e0f090105010515071b141c020f040e1501091a0904050a06050603120c010c09 68
    0x928560421010034024401c4002201400d00f02402c00000c0c443c255100200308042c00100c20f003109481e0400c0d048a8806079400c0d03015040005100c0340d81341c800021aa0741401c00c06040b400d41e43c68400041c02034024030305550600d511689020160307a01c8400820388040841c0001a4442103401400105806402d0712411689002d04c14003201c82c2c810196421180c1304042c1e0800b541845404074090803082200604240c1480c0d004501000c1c0b031880030340320f44030001d8001c01c0c9540d0007060030309a0b0401e100729a003000407420007186400b03c40b401001e00d03d00400403240360b070213010003820802140e60b0000102c400d41c5408101030740b6000030045140340c54155000300e10103103900045c03201101c05480320702c02c580d101c0340d440250105001c0c0012890310104c4005c030310b41c0d5540c06040505150210b00c0b154410250b4400140e20b04030314094041c0790058000c1250210540c2c0360700c010301c8041e0055906100b8a02d01c0c600203480c0c02c008010600202001280d045001079001c0d00c1d489841d0490 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 130334577 1250 130333327 130333349
    0xb0607060e06071d0607080304030c0c0909060e0615100513090207060b0307080c0103020d060b030906061912080d1d0f070e060f100306080d08040b1e070f03061805090106 75
    0x10318156991784145c03180983c020310210b981ea20f076803070151203080c40710500a0811a561400040d24006684802c8945009a030300740030340b072a802d01058886908440803550105400c5889047d030a0400c100f02d00e2404500700f003403030101000c08182c00b07140207910089090340c0020340034040100d5801030320820300065001304400c1c2c0c1003c0d09035495018a1405904243d4042050b000c100c905410001c005c001940405a4a051681c040c8d600c1d0001100e04500607a408035180382441c4244030030504681c000e05a0b610004910fa071201eaa03070340103004841c01c85490755070130307400c00c0c5c5104061000054600014807030b04035000010b5081c40c64640c01a0041021a0200000740c0c4886800640c0000100d0341e004100583c48401c0c2c0081c0003580106800d40f154080c100d40691b00112614001d0303000c1c2452138070a50301c2110002404802400c01c0c88101c00c08400304044500447c224401445107060100303900d81c40300c0c8072201d80140440b020f1201603ca070107010030100c0178410079000d0007402c044 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 130335827 1250 130334577 130334627
    0x90708030c031207050906030f07030e0f030d020f0d06181506091205010e10090b0604091e0302071d010608151005070206040b0c0a0302060c0c0705040b0607060e0607 73
    0x241d128099480fa0602d2480070100056a0038440d20481c1c0c0d030144c000f0501e9449041c410520001c645040759281c010a03d000040c0354501400105000d0b001c03c103034000c5207440a1a61220081e4022a41400780c0782c80904c9030360708810752406400c001d031020711080d8584420004c0c40f9810f84e0301c0d000c0d121710044002c903414840300e03912401010580b00460400900c2b80349a16016005004c1c0100080c400e0090500d40c1c07480c090a60040410580241d1511015854040402003140c02800c0c0c0101a584071002c0520720900c1d01c9203000b20240280140c4024a82e9a0100c0001c3c00320306402c1c0501401001c01400000e07000301d0380039080030494490302c8141c1c04090200b4020840d1101483c18010080350703150440d5605411038024012440c4400c0e11021030340040782d0742c1d04a5400c102c0143c0510320010b02540c44407001d43e20700381903031001413080c1480c010500c801040c49210303458000700100901d5002c24014051144540c410788024034440c40c0084000b4000c00c0300c800c04411755428a00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 130337077 1250 130335827 130335847
    0x1415010806010510021c0302030105010f08010506070b04020d05030307021005091506060d0204090603060204060e1e0d080f03040f020f0109081005070e031209040f09021c03210509070803 82
    0x4107070341929025100442ca03244c4032207050386482c041c498103480d4000c0c0100d410f50303011740c583c014504030342003a02d0b03a40b45201015400d40d8201400d0007059003012007400f04e840821140c00301203800c0350001d4410502064540c6031181964002c6802c0340150340044111044420300c1d10940354811007000251000541c040c1100d840c8a80150800c1d100300700104448840da01d1540c1240c1c020300c44c0260801032720b070350b914010010b0b40045c030508012a10142d421001d80c10000305140c48000212403003c16555200100101000f01800565800708180000104075481a0045002d10f0060f00e4180c01045244100082c8146001013a8108058550200804500002c107444e031302640c0100490b007a5941d0a045079801814800c15501d4821001582c03841086040100a1f031700c0103440030b00c00007119120031820b4521050000790031500c1e841c1201d180c01400d007183c01c0c455202e464200a4403411b01009080040c1030270000c54019500d9050200c01c3d101046031000801140003d14141940c0c29 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 130338327 1250 130337077 130337083
    0x1109041e060b0915100309050c04060e09160e0414071208031501050a050f03040f020901230105070206040b0d09060e100f0b0603010e07110a030815030715030908040503070314150108 80
    0x501350414987c8030b144d4101005018400b0003414840904104151a0f948219545118098030340420900845d14504100300007003000505840b4210240d19a03501c81c2c1c1e0364004140c00200c5480400c0c003071088085043c001010011482e140285640d907103e04094081d280050031200e2090705125003000154500e0b500001921940e800c070300b20303103503c0e995030f410b180041102214009510410250001c1103106100c140241c3c3c842610042940e2094004010b4820340706481000c0e5105030188810403022030540003d00c5104840d14022030f03a055269140000d80e18400c011001980007240301c1c104000640c8556158a03c40180c00d000564190002c07a5503440b040c003450100c084034400050400f806001c0402c0e580c078003c42140c0c40b001c01410000c5c001c0d44142c881c8480720550f580d51394aa80703400100c0c40140c032604e0200420035895480c0035002041c9130300c1c007240e8580040c0400075041e50f040c040c640055005207407107030000f070540c1811030502c03000e500c0c010008941a001400007003000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 130339577 1250 130338327 130338349
    0x20c01021018020a0b070b01080706120515041b0f0504030b04110a03050604030c11180c03092d19080307080703021c0c0905030a1109041e060b0915 65
    0x400000940940802e85900040410320406500050110000218190094001d007105800741d80401516625030203056161034051007030708001140520f422000b620281d000307541083c00d61000c28041e507038510210701074030f803c5038058402c1d54031103440600440d000313480304024007101d1510f14a0b00781151340320000c8540c00b801c05820003080091040c01a22009100e0003d9030b00134048600c3c0d4034040c81c005280d140095011140da94031861524118108084495540da1000300841c0050342c4044880e229900b00800c1c4500d103104070840994010305041081d907100c20203101c1c2941c0d54104008451800031200300d8a01120140c40e812004189108150781e005005440c1ca0700b00e545810104401901481c4491100c24502d42c407104541c0800390300a40e51150300d034440d400e015030303607a04042d00e400a03c1c002a00808495880c0402c9142c40c5200c564018815200c0311200740c240f40c0e814200c884880800c030303541d581d81c1c9590300c164600007100075031100109a000310789081d1100803460091403 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 130340827 1250 130339577 130339603
    0x9190e0a0b4515040c05010809370302011b020708070e0601020a0209010b1201050907120917030f07020c0303041401120e03030c1803060402010f0503040c03060f050610020c0102 78
    0x202c8a02e003420340b080d214000b9401114100b2211200d10003034900380d07007000c1624200c0c0ea41c10a204001441d50182003054410b00504018100e451450703003032010001c03158032008800c4002c0030514003c0708010f0321884a07031402a4000103802c802114180824440600b00e04250f40c86200d081014090000b40241034505050f6907210a803600e01c0141d20745140b040c0003d501800030400862411021000750010020078404500307141d036104144440014241c0307034200051000510030b16054219080610f10520400380c0340e40700708500c03203003c6082d00700756a140048510641444203050341007001b145410003c5001d1850146800005689560110002818400230708a00c903005c05c8160f00c0365090310808020380703a40c0d1511026444840e40080e880b030110740700c4e14500380801c0c140041c0e980c0c480d5606844129400100d003a0554494200600071a4060701d980ca0200c0080c001c0d000d60001351b808840042130a051003401c00000c400607036000b00456002800c8244140c1c0e001071220402e4403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 130342077 1250 130340827 130340911
    0x918030901110106050402041508070815060903030c03070507051806010f080a020918090d0c0f060b130903020105041202151503030403060213060908030a0503010509190e0a0b 77
    0x44440c0c0300f030240038030340d02407070b401031002c240016030920700ea1942c0302e203a201ea982c540700e0303a40e4000c4c2590050015618003c08a10035480f01c512820001c0040c080044000e0480c0d0030280c040400600d5940505011076094011010270003450801406001d600054400750300a10720300000000c3c000c81047d100c440420981c44080340c29400c6a030b04a034400b010140280c29407401d580c02d010b488a50690b0391320240d101300408903120030b1264103100d225951200320820020119100c4d0350140c08900c0b40039074040d4440d00f1208140da16840390307a501c28401d800100b10b034a094107012441c9100c0c00c0d0504259002481b450780d030140d0401e60144c0c0104240300a110341d151404c04207145010310380004025620002d1010241c031a0102e0701e4007110015034445a1503621040203549a00808200c034021078014801409903191040e0641e034810f01040750842c14403c08008030f810b455200803185081d4000d0b4103510240110142060b5101c03601640c2c4141d4043c05410804464000307441e890f540c1e503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 130343327 1250 130342077 130342097
    0x319120905061303080a0c051606020417071d0c1204140307050304050909070807090b010c060516080702010b0d030c06060b030709061205060a03060504060906060b090918030901 78
    0x681203a10024045801c101154003038034000e1240206100200d10035004078184100103551241075006d8490700c03810590f241820515090b2050035845aa803008a0b01940c0034400800c0c946207440c0f410b40a160182c0041000b6450017841c09154407840c0840703005100f1187c2080440804c4030211103031500c1c4a2000c14255969041c9025400d04120190005001c00620201442400030180042e1a81107900b14880d0725162030391030b80c51102c1c0c0300750712407500310039400c1043c01c150741c0c44011282da06041c039515002c2c4507514803003120302c00c84480d2181a180c801440c2d52a52101c0c90300c2c1e2100440c0002c00c402101000050714030055180700070100a0003201c85000c01000d504040001c02c03030400807540b00c1c00c2040740504002914042d40d8000f46a82c0ba1a91025681d4011140a500080c00081c055421902c5280c0a031600034420780c0c60a880c1c0c50100c0002da418400c6100404c02032490310703110040d800401500f044050001a16280074130491120f00c034004c0116107802d182400c007000c0c00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 130344577 1250 130343327 130343357
    0x90c0207142e03091502040f05031501062109080705210412031707020d08130309060509031f020a0323060904020a08070b0a031407020c1302090301051311030319 71
    0x1500003188005c0c01421007220134105030750a40c01a00549441d8110780107035a0300d40b4280760b030703540f10b0400d00d40c111005a0010020140162580e010035024045450941402036108600741c5040150484205600160b00000d026040c00340c2c0c448110f40e90f00c00151007440c082110213038022405440881e1242d400c41c1c0e02054050340c0b0591000050140701c400c6840c0c0741c0000380d1246030761411040424081d100051150ba0008042441c26515423980b14600703040590454054010005840c0c1600c9100c8180c0c144225400303d0310340352800075130050b0703440746180002001c3c0c60502120000360a09024100000314400c00016440201514140c041d0382d5a8000198800d00e180d004025a0003020f5000c51500104002040c0311003640c0c405000105001703494200308601201d021005802082d090a01c51500169645031840813507000b6051240d440f00003402c645043d11085508442a0b5011040011301016a90750140440c081c500744402c5080503004500710104110811662100d0104c403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 130345827 1250 130344577 130344581
    0x1b06020a03021e0a0c090209090106050a050403120e090411010318020a030f1a01030510051303080402092503051b030106050d09150513050c040c050702010809010204090c0207142e03 80
    0x130858000045002c0c0682d600400300080d844203203603900551000740046040c0707025100700c543c0d0340025590715107810320310340b150510b0308000042c000420040300042000e80d55403203142401740c5d0003020411480041000090100c85081707145000845101c000d150150b9281d034805030031170f0b80003140000d19030b405c5d141401c0e04420b140c0480702452541000802809000130308003d41414040302000151112610400801b2624030010001a5003500140c0107003084802a17401c5880e03000c85462000750354415030302d04491401100c0010340e85608120300b5110000041c1c08103100c013495a8690350500d040144144605000300f0791240d00c4091101c100920f4915646030a80366030410071460401d0000e0076030120403400103503420b10600b080b0283d41d1410340b060b4000300003592a041c0ca0180300394019140007000070038132202e42d582400001106a814011024405025405824182c0c1407286004010302548001401030403544202219140030840c1102a0001c154002c0820304140714100c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 130347077 1250 130345827 130345843
    0x140c030d020a0f02121207030906090602042304060e011217040e0a1a06030106030905010207120519080c070201111c11010b01020c091305191b06020a03021e 69
    0xc24400120002201d500c40307050307042c20b520b56080e00d00035081c804104040380111094080303800500300c045105c2e54025803107401c01500c236100101f8041e4090b2602030807078206071700c907640e29080480f181010001d40f00b45003c0a0404540403c11035007400c8001c00d001005006100308060315000c0401407100c0c901d44908403c4100c1c041c00d40e11a1150b5801c1c441c0c007000c4e07602d00111814121000c40c1d4a440032249410000003074041400d51313107000f00c01c1b03024044040c4180d4255500700804000328061a10b4144a0f42894548a6490126103070890384101c0220f95401080201024028001800b90448030103980910b00548081d1512840c3c034207086003c0000d54144166808010b0303e540c00c00c88030100d160007d0020841c1104d00d1005a88940092070055840711410001400413400444000700135402035007101e003000740c040030380a00f1a911403000c0d0b2780700c00000710118501d41040c003108090300091010305841a51a60069510355001c12008003140b89103d00003010542080405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 130348327 1250 130347077 130347097
    0x60a050c040b030c0d0609020a0c030503060109080303040b0106020c092503020f0c0601151d19080f0c030105250f0315030807020a09020702061e1c0219080601140c03 73
    0x56640e040030100d03014640d01c50701804d08114106500006c00200c1f41c4262109089640c59400c01040c0ca82d5084072a80c1c4020b1485048c0b0821071004030380030200b040558803562091002d0022941800f6001c0d1412550004040c0300b11080b800700030b8032480c0c4100503e42d944440c1442c2540400b09101513029008160b51802002800f1a03210103003074001031082e048540f0321820303980d038180040d001c5880c003901c030603061007040b103512005605090010803100030760702501009260390703100c0f4840e07401c19008600181147d03018a071700c281301e85020b105658022208645060700c900c1000018005411a8440c0c5410b02c54074a8582040c01e000760000ba000004050f144070138503032a450b14964503005400c0581c000c1d0300400b00803440024910031030300301607001054203080c0345010302c01c40410781243c810140324a009011484029031111500340d00d180c0c45a1016840700318841200d55001111419801006492010b102c01741e6005480d801070140340c40c50485d0340d8540c0a80843c075601c0b40880d03030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 130349577 1250 130348327 130348349
    0x19030c050f0a08041a0709170a0c0308030a0605030d090b1b0d02030403060e0c090414120706050a2d020915120907090507090b1c06090b01020f0609060a050c04 70
    0x402ca90550107548540325920031000c04810402c07110444603000c00c1215040d010a00140c1e0034400c00c000c0d00d20064201490314201c400b12601c1d07680c0d90f6103040c01c036801180c05070808028080b0107440d5014100140c04203800600242103420001000c8800c1c0d40f00340c14168400180703003183d0041100c940a29400503000704c8001c1c003521403000f55654060711042da90300e89019048641450040340580070a10010490340450701d954585c100c15900a5807040501d2003246c0d0881e0200e4140405011a5401013500080902c0c05034050416640d520080074041d41018030440c1130b450386400088a0440f80c01c00040c0c0ba5403890021611310218000c1e04001c40300302280103211400c11007209841102ca40381a160800d41d1050b0f0202590001d0700d144011400164050101b5800e90001d85070603a01e840b4191901100c0c00e613a40c0c11034845400c43d07401e01d40c9403032000300f83e941c0401001419142103c02020645010442c043d01c079403010309224141d540f02d00209070710045803015100907201048807 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 130350827 1250 130349577 130349587
    0xf0609050705040b04020702030c10110d02060a0b040507020607050d021308011d0a05030301060311040915030b060d08030f04050c060a0305070e0a030b040b0901020c120408100219030c050f 83
    0x8159680310500c21a0f10490402405011508081c002d545096601a0040c501034260a0404c503040e20607405a1003080703440305010b00728640c200f002400e80742c015006058607081450303036101030380c8103641441d001e5402c2c14140700d1503d60000d101640400b140c0340240e2241040345481010b0311820b141881d00c080205401b240318541035225550f81c041d81c403060101c9682080510fa1a84c0b81004090465002403004121a030f010750090030305000d41c54101031605464070003d80c116039040b0019680c03203c4150b010b00030003c807083c411790002d00c00c0710304000c815a90381d42c801d001c0c48000c3c00b0480308881c0ca0081402c11070200241d011000c00103041940320031128100a004101c11503c002c00111625811310981c1001d20620f4242d03600b00340d0b0040699074a4481c4150107001503d042c44540d403c100d112084c10081c000d5140001103005000d40e40c40c0b41c103102da460441042260000a4410490041840001100b442c02da044134140881c000400707641c03c0e00c0d02d01504c8006140c0c0000012 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 130352077 1250 130350827 130350833
    0x30c010603081804090f0314090a030b07092405090415270c080c0702030a050709060e01050406060e1201021c0c030f0b2803080c160b0903190f0609 65
    0x4082c140c1070326009400300a03c0c0da00310800003610701c5190042c01300000740c82d9240c0824801c140e0403900c0390500c2030709858681c02d50041010000b05510554200303c1110a12129a0b4011390450007450800054480e104401c554007400707a00c5100e484003400780002c1d920b8055141d6030041c05600c94000c4986043c555a503d8405007140d44203d034001443c140c9001e45401503013445100e010609540d2400a42d030340700104040d29500020041c0c0e89840340f17902480000d8400c00ca050040d141103040031852a2404c01c00e10020b10701038000520850611809010130340d400740700c1848010b000c4039002c001020060340c1600a20071090351036000b0083c54802414042e868014100100307940d50200302d003100c18041c103411207505250340f5600080800407080524102e01031000f2100824411082d5503a990390355800743d511282920180e40c111307007040301da0322469600031001020946005481c1c055080002a02c130b4136034400504041080700004003c3c007074550303150f07038540e58000344c20002c60303000b42 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 130353327 1250 130352077 130352093
    0x80408030c07060203041802071103060103060e010e060c0a030504031218120c020a090213080105040b0105010f0503010f0e0a0b030f0f01050a021206040b2805010e2d03030c010603 79
    0x301c1c10050500c9203480c0000c00034800400c850071030b0900005601c0100c1c80c2903480c4003a601c1442e0a80369840c40c060130842c42c0e50144840d40c002c44c0710304000111400fa081156081d0f90b40401d102100ea041101080f0b080000c1d40101d50280d6158980028242d403149020354101491210449403180b91041144420b000c69460800071406607005900d82c0141150498029614140003900030700c4030001044a904a900a480e1114680301c400541c55101c03958a82101c104680668243c020000100001e5810004601700d828251a103c4d1956041130000f1405003007a200340e1040454500008038800d810f940b2044903204002e00742d450700c0380c21101d0700c0e80d2019078100701da8181d41b914007c510205a90b01c00c031024400b03100d8605500b50b03640f000b0400104440d038030300c98001d0b42110740b02400c02403003007210300d001e1840060722007550704000c0010b0843c0031920103180151a10401041304004103080f0000100f525404610200079180201e800c50140d0b030341d83d100560910001100304404c00c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 130354577 1250 130353327 130353337
    0xa0e0108090a050c0d032a0308010b03011404200708030402040f02030408031602012a030608010506100503090a0204060b03040b06031209240408031206100f080a0902090f04030f020c0901060f02070308040803 91
    0x39070320027050766212500000d00e803100303201e2241c02c4078443c03484000300c9c10103800c042102007031070001415030004000e40500350742c40f5100498003018004108000c5140903c1400120b800c000011405c61409503100d241c54032014096089150a080031314000500c00d41201c649114420780781001c00903000708619400d010841d01d000482d050040c085141c640511596204510042a510355006007000a40b1607900c00380507004c0f640224800d0902507180c138041c02000f8001592110342d28070f000d05180310004009843c0c1031103600500d007207d1080062805560072814115603400060b45c0c0902041ea0441c030300c1c03000d4000e5507004a40014510030220103407001c402e902c0b0000c0d68a5442034104001000040690f1b0b010130000c034404c41c941841000410307407204d44480c00290103c105e80000303126035002c80389001504c6440042104141d0300082c000101c6a041c00146294211074000030307001c2c001400740c1c1c0e08010809440e131410700c1c03017000079900854210b5242660341d0307140d0952940340d0f801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 130355827 1250 130354577 130354583
    0x30d090b06090f01050409030512040807020111010b0d1e020409080d2d0522050d092102090a0f050f0103170a05090402030a0906020a0e0108090a050c0d032a 69
    0x8500c00160301c1d00b46840598400d01d00d4400a2081303a0a200c10000105201c800039001c01000b8800c010500c202d540310309000300d0290a070140c40301c41e039200045c20014101400e6a240e41400300e0120580c6030b480301c44d40803580c8035401d2070342e8090560441c4c0410000001c040c0d805070401c0788090503c85620001c0130381e14103440d02881820400c8000c81c0075040403903000282d0440c403020403007583c041036000c1c0d13410015264001c01711880c003802c940c0f1340414070903040d81c240d0850790700c04400d1030700b01c0d0303060b4020f01c024509242200302c0182e12a13204840b0400103400f42004800207800d00760581d0003c00d01058480040207035017001175405040e5182404122403410001380700d41584182320064800c0c039191035a81e540b5115848082c1f00107500b014242480d466150408200003480e14000f400013039100360f44102404c0c203100001130070814040c0c090482e5403c10500c40c1d01181010038004610207060713581e006110b602d49821500d41e040a42010041000c83d2104402880c204c0a002c0c05980 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 130357077 1250 130355827 130355843
    0x201230a08090c12060c07050c090c12061f03150b0c07031502030609180703020d080306010216050d02061e07030f030c0e10110a06060f0303030e07050604051908030d09 74
    0x11890070700846010f8080031070303d207903c0180002d40b4280e090300104512440340f81902c4410027103501003030702c19106031000c0312074120101d141928107508004055005104880c0819003e0000c2881c10b0407880302c000c400d0800d40c895000809600c0c46180c141e00405c02030088654840d0703158a4240c075200d00d070000311840e00940703800c290400c155000352806014001c000d43c0240d101d007582c500600041d40c51603500d074004c442c000005a5980548210914002c06519540b403a06600090070b04928100725007004a0a1009000d551140c40d800e586156040d1409a40c8100c84419011b401c07802d000d621100d01c00000d0410101a031010071200c2d00d1115884c2030044242540050715000041521680c010044026521800740f10706254060010340d40c0581d0862101608d40405032003c64002d40c0d440c50701070404004041c2c1c144070b48203045030501e000d4084a070414000450f148200d1003018800c0000b03441f00d491111a00041e400149101d1040740c0d5035800380c2c040c05020b090220015100c1030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 130358327 1250 130357077 130357093
    0x103050a0b06040b0a140a0302071a01030312020a0e040f060501200c09040809040c09170a080d020f12090c0f06070215132d1a0301030201230a0809 65
    0x100c2680035000140c0001040a400c15050000c008042e80100803028204100d81d10710101d540b000400501c80585180e60242c1d0303e4056007040450381030200603a8441000441c01040425408240c1c0604440c4111016a403248400c4080b907003501c25403030740d983c801e01e00103407419610001c0c0c1c015001c44d80d00780c8440401c004811072034150007044803144400d5420403901a07250341ba161702034a502c144214150703420806a03001041c212100d081a9101083c04c0b03840c2030040c001d40840510403244d660f00200750240e05035980c05054018406d07200368482c5c02054081284500c030f401e0301c9805021002150305450414640741c2d82d0408213405600418002140e0441410a60211101c9a8000d03045c244071005802c03140f81903900900e48800140010400804c582c580f0f0304580c1c84109445041e10344110310140c0034030700321480d40d01c01d080244c0d1880c040000c001101d4143da04680c1c0900b0040f0f1202c1a07034019810709010700e0a1440011000660151540d412226250241900004480a030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 130359577 1250 130358327 130358341
    0x10203010f0803070f06090213150501020601080d120902120607050307030507030204150804150f02070b0a06032003150c0c0c10050d09050c03010905060a0c080106050307030c140406020c010305 85
    0x92144140c06411146a0060000480c074a50444c24039140b01274214066040c0d0712007158120750141c400c03c4070600c1540d000b00010340c0d04212050140c00c0c0140581000c95400002038500981d82050305a81c50f10b40080c98155a140b0410400140d6038005541c02464140d00040240e4011981000400c0c40c0030089040248240300755001daa0f14035091841c88902000d0a03540c100005004441e030700c0d41d0468410840e14640074061011030b29150168840600b031a00c82e0084400424064003d0b240c000304101140390401c0c24148130081200100400e4003002c0824104480c080f022080b04420200b4485c020103030000500000e89840181c0c0d070003110078070420070f8110f524440381d00010020b105401d94120395501100607582300340210750206c075014001ca400d503007c4403010746042c0c00181c100882280d6a0003000880e912900c2c20000c250704008001d0502e01010701704004066a81c464048018011240e500c50409e44170740d02c0da1070384e5844000942c1c03040d14032a040e0000f0f0030071001c1072003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130360827 1250 130359577 130359583
    0x501140606180a080d050901080604140612010b041a030d08010807170703020d030c03090902070f030806010203070f12110309030a030507150c0503011517070e0d020909010203010f08 80
    0x54600404440c9003002c0302464580d00d12800e00180c2d44020140340c00501c141d010010045116100d44486445621071800908070f80ca0050407140100c1c1403400c00c0d50102000d000560344032200716030071b0455034041c282050042660740d400c150440e241600c02e03050080c1e0101f440c0c0d141d810440844100200240040b20100003e114000460344100c8043c0500e4040a802154604c0500200c60029980b500052000941d4400640102e01004080c009041e48005440050b18450505620b095410740d42c2402d4030541441c007400300301008010688a82c428422103ea05421034105403041c0114180252840c219000b0700b00450380c6550188502d0002100b542c8100070000d01401c03165505850079030315648181000c4850881c244c041c0c0050891900ca1540c40c130500740c0c0c1b81ca0300c03581800101c41d5280340d22000711003409400400c040071000e01400c620741c002807600c0c060030f00b020000041008000541c800075403142590003009070088055001e58101c13170121601c482442d07920311405807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130362077 1250 130360827 130360831
    0x3091a0301140f0306060913060504081201061112070317040501050906073908040602010501060f080c090d05010e030f12060d05120c150a09060e0115170708010216050114 75
    0x501900030305c000440520f00000116440010220503518031480f6540f400226402104c00302c60760700002c01c00103080550b000d40c490142090781051300211036040c00f4a9503c0607441400a88e42000061032010144143d11040503180d44880c058102e0a061600034060002201c0e0700c840c030701c542c800048035030b8401c01440320080800c15100c0401440c00c1c1d8505130f2068038145400460103a400f0709000a88100700a1005100950000900e941001e10003883d10f211100d081041100301c50610003030040003400c5400718041100d6600c10102c030b40c50240e0142c4031810010754180004100c030b011240102005164114805501c082569141c0c001c222070b00e4040080075010754000d24515060307804070f00003040482100000c440c00c4002d45c0e140c090500c0c002302d4040d10283d8903545014108140ca0040e0300c185030401000b03101c1000d54041400c1640b12070b00c102000901c04600c40c0c0c038118810f000e0340010f010030700c0003507540310210b10001401c6c00000108482640ca801d510041a202d0a00414 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130363327 1250 130362077 130362079
    0x309030d18090506042c0c0a03080a110109080d0207020a08010204030f0f050c091302090a0e0303070e1504060e10020102040e04022701030b090d0e0a03060903091a0301140f 76
    0x20700c0e003404104001010000d1089410079514104038030f010080b00510340030341c0311542c03105c20240c080c582507904210020b000203003d40d904880a10001d4006070950f940c41c4c02e40d14090340c0420900d003009006d4514130101509084002071001012543d680007886200d0003924031008048c0d451000500702e02c65444040c00b80d1844903441000504c0b41c600c0003000c0b60081c2d00311a203178860b540008214403016a00a001301000041c00021800d01002003944000800010040c07100c185a145840740310040c0400108841035180d40102c1da40c100c0d51140e9181000c00e402d444a0700d03800d010f880300f02d4412002e42702d072001861904030b8070b00c14000c49050701c00c0d04081e01c02da0303112542800f280400301e2002c2d41200b40c0c0898000c01d00b084440316540254000d1a944440c1d0405800d01414042072032522020061071501113203094850323000510072694410000194a2028201112801459001542581c1314029105a02c6074007001945c142c2d20400156042c8a5207801001311440d01c0303070030079 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130364577 1250 130363327 130363367
    0x705030706020a1404080714060901020a0b0604020c01180c0e042006070b090d08090106060203030103080d0b090a0c02010501050402070312090201050c01020703120501140a030b06130e0309030d 85
    0x40000202190060302c02c450039400c2120740c044654104c0106600141c00450050340b0100040040c40d90300700c04070b08102c40c2030300e81c0d49c035024200d00003d486d900b00c40d8000e007505141a02281054407554101c46002001100030001b214a9406090210204420940d4004698036001c50801c80d110030481c02140c0c0250100a203e10107495070144412102c00740354026002e10100000c42d0400740d03554070aa404101424000c0780c243d0014201a00c094403561180c0c1c0f5250301404902c0d00001103034103480e000324125844840c605221780c06071160400d0b950304420080103007c1081407030740041c2e0342c509070b940081c81135a03240c3c0e0501c01280a04607001d0300160201d0914030310800c095000c0780d90305006241c90b03885c04085114072400d80c1c0c40380b0070071800202d4041030701081c545c451140901601c04c68640c600701e90640c1d00020071028a174000239004884a501080655480e01c010151030800c2c594248000413900c01c0d0680c40760410014180a8018501011a001d00c51030b114070740200a2200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130365827 1250 130364577 130364587
    0x150503010e0a02040f090b180112060e0708070305060901050a020f07030c0c0f0b1b07030206071b18050702010f050c04060c0c0914010609060e03060604090807240e03070503 76
    0x2074803100310241680d00d006500b0800400e52401148030032000e06000750002c80c64400000510440340c0c400d25407020030812400c014043e4540c030140d17049040360040c8010036480700343c110322814000a0b0f88441101e05c6030340000010000042801481035040800070080b5031b86155500041c0d00c40d110303005045500070000540040d0041d011188498081c0302c940706090345071100030311800d02c1a001910840404508103a40c01c008503401c1c0100f01d112809401c107203103103502040c070900603044002c0c2107010006011070652403c16107034004082c10f015542103000500c1c2544004c00d07040e120301703005508201c0c003402c40000701c0c02654003840340110020716003031500104171009880b5a40840344001ca8400c00074404180340607032981c0c00d21022060946514154024003100c106034800c1c81446140c031141807042d6004030b100c4c0d5000c04181c0b03001c1049a402d1500c1005440344010080c140140c1d4202c016140144840ca1100b03905914010000d0040e800e444a541e4090701c03000030803035401041 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130367077 1250 130365827 130365839
    0x6150309011d07080c0111060c07050316030c1109040b0115050904060f142b031b0c03110f06031f05060d020307020c0d08090925090f15050301 63
    0x1005680c0400e0510000803042c008481d80b001c6500c003507082c960107901034201130202d03c00600c07040c4a0030b5001d081207101c01040040395038440b0320040c11410105404280101480001d004407624003c222440030320313513840b80c9400381c140a03407240242c8070040200c0c44440315040c003d6000d40101d42182061900740c0c60b0aa00404500c07004402c07400f002400e020000550b141e40c041e100c0071f001020a401c809509080c42da0416a40e9404071520410030709500c81c450031001034a01c07040354800d01558150701403905064407142c1c0485101c1219501100300740060004030040c10b4180d0b4411485d8042d041d4041d0b042001103032204a0003a800355027040801c41d00310342034034140310051400609285142e130398000140c182e0841d103c00b41c00c4940000c01c02002c40c2c3c1c18046444124812603605500c2940c41d00c51250a0181d1201240121540310100b540b1948000380c1b0744203001c4500000c800187c0c4110010134161544c440c20161000b500c002141c081a42d0b1032004004920750307141030940c0c0c40c0003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130368327 1250 130367077 130367119
    0x151815021c050904091a0702210a090b03010b0309010f0203150f0f0d1a07020a11370801060e07020307030804030e0a0f050906041a01050d0b03010911011706 69
    0x1822606005040006810f25121401403102e0300f402221850902e824801c14004003400040c1210f00f150485404d0302c3c1200151800b01c0b480203500d913009a01c4016000090b40c25003143d410a0041c4900800000341c01c500702c10040d442002510003e01c180000240c0090581c0810b580782c0c2c0d4260485d030001e0b809420945601030404d140109410cc6800070369001ca0403296050009487c540c500740b20b092007003080c5181079600a0030f544000d02030990580c48100c64150320024551141d0580c0d012808082943c0d5107400ca0f065100b0815513140305244650446247d1b10b1207845400d50030403800148042c5451252485002c15401840c60720140340c2d002c07110744500910450501002d0070f1040e5050300c0d003008020260200035003041c281070901c010004944d400401e0b0702c0c880c6e0f0800305400f04c285624902400404001c5c20140d441d0b4110070000700250180d00101c2d5099864032081d40180179203010350300140402070b00d0b0b401c90b030b021204009042400449140d030700500d10003440f8084070214 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130369577 1250 130368327 130368373
    0x90506090303070b04030806030d080402010c080d0e01050a0608070b03040b010b030903071703181603030f110f03070b0718140103020c030703021b0103020a080a0e010615181502 78
    0x2002ea81c0b030108a6902c0960200060f00d0680c00206035104001d1682001c201d150350032400d07810200ba403841d042d40001c000389580303100148000804180240070981c15040340c0700c4011100c000744039034a40503c00c20010403e074031400d0024483c480c00060b00ca1604c1c401c581c0140d4010b420100e00d40e0921300d0300f440c0c55201809940f81407104002d00c10226841c40303c1100d024000800c0c00c2d03a41d0600958440244460000c1c42c1541e8010080002c49101c3e01c600a50840780c0c5030a2507a540d102a101c19515a1910a4040c28a019070341c05140c800d480403000b4146180700303409111840d01e4031102101e11941b41508690a0007040c07000f4003914266182c8004200014503015191007041d5044a003190010f1170110050303804a401041e13076844540c90f030600300c0002c0c07030214100701a42200030b0140d0005009107681e80d541e4009401400000e411400c054480020002034000c40c5503001007041c10301d10409034000400e008041503903041e409010881d100158000c180b4803007600b420785041208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130370827 1250 130369577 130369579
    0x120c0304030f1a0c071109070c020405090c0a090212090718090f0206040b0d050105040216020f061b0f01050a09080909100e010906090b06030f0f040c0e0c03160c0309050609 76
    0x154003030080e0f07030f110030500143c03094100b0008192901c80c45d190881c000e441c08071807144a00c044030104548113034880c0e4500f454a030120b9002c0740c541c80750491281031600306ca280740d40000c2e1402c00420101c645400410b4000090520740c060b580d5084d505a40701e1440740182065900114903c5050a030340c0d0b0814407156005e088500c4d0072120035400651180e0256001980c0c000004ca81c29001c1140313407188038010001901e084d071030700c4600d4052300c00c0111151030080c482c1d204204044c5480d00c41000343e07a2420585400080100ba13004c1111b640c400b900c205440a1390308203800949009040d00038480c3e81c1e84e001c0070070340c00d00701c80800b0000319400003814205140191500000c0b0b038002050050300034100d0361070001d00d480c2001900419106590349440c0101010000d1103d071051041009034040b00b200382c0c1c40743c96241d5150a911885040d030200d000b10200006001c5005814002180120360b0180e0004002c0d00898081d42c50106945000d0046244618108000d041c80c00041042d490 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130372077 1250 130370827 130370843
    0x1d18090c030106060f080a09022409041103010e0106020d0504181e060602010606090f050d0512030405010506131506080702030d0e1b06030c1804180b060102120c0304030f 75
    0xc44a404a0300710f030000c0d807004000458541c00c00041c6034002040c1900500ea405040c01210501d401046601080540325034540c0c8500785440078055151080e03d003032020041041c801032000c0c2c4a4041d40d0340081c010344407545c2d10100005041c0d03000140c010541c04480d1101418145000300c2040072071030200c20a402c4075201c03c2091190800c00103410703c10500e200d000111399041480081c02c4402c1908400240942108240210200192298201c0300c0881d8008242e054624105040c20389200302c00000324800300901082041c10f400040c03103040d003030b5120802801c041d11000b060785c0d5801c0090f5204070404105000c00ca1140801c0b9505c0b1003540112440d001c0d014007100211111a5030101c01354028042e00001c4e1f240200d01d404580c2c80c1240d140c1e0075420151100100c0d845614044603003110013003505005071307d480d0018503003050f111100c055600306600b4030051705607040300e0b0280103005040c10b000b00b032a41c200950303c0c125184802141020308581e42c0c1842c103414514241c1d01c0e18 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130373327 1250 130372077 130372093
    0x7050c010806040615090905090705010207050402090a0f03050102041401030b09070c0203070b0c0106080c1008070e0406030c060807080705031b07050a050d0f0e0108070e060315041b1d1809 83
    0x17072954450705600c941c15504c03203107a986068884012501d01400094081d00004010440c07680d0005899013544c800301c0307005949040c809c00040c0b6101d00360f8401d400c0184c17002000421700006502510444280311a03084561413100c0044048881c50300129501080101c04188070a00c2040800c0d8464405411a880f1540300d5003030325200d80010080840c81e80d12481c051200c2039061000300c03003004068400b80c400300d40460015054201c0100a001040781615600482d555941c0001c0011508090303052589904c503480104601c07021981c2c080400c2a17800410000c5105d40100d0384030b113102400c80140c0300b089a100c240c0710340c000d4200755210700c6444240390102d00c1c01d00000580444944541d8600c01c48050b0140504255804c200e050249031020040c07411b412846e1108a1141140e24950302d42c1c07102c442095030074851420303640140c9040c1940e83c0e41d410700500e0750000c2e903441c0c8540700140c3c40c0078442c40303440030140e0709540c0090542411104a500781031015402802d01d000f600c0b184 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130374577 1250 130373327 130373339
    0x605070c020910030204110a02070b0a05090a0b09041a0a180e1b01020609071a0a020115080714040203010f0b0c0307050d090e01230114070f0c0e090307050c0108060406 74
    0x9250540e6014003004504804104520b030a00c07d44200c042800c45803410301c03829450103074540221348a948800540005c4041841d40703d003046035150603009101c4000e440c1c6071291407210b07400803d00d280c0214a80042c1d80d034800c0d03014507007214044005194cc00000d0400c9800c400080d80040440b0380e49484a002184007041407200100702a442c0d14454010907200f800240303000c02c007130a005c0003504214002d00c04000c0209401c800d02d0004004144e645502c0e8108900515000403000880c202d000d07004a0428400b203201822038150b038500e0f011100ca0581000100d100c02c1c49450314111644c5004c110015980f00a0052166810252400d2100c03e40b540e504041042a4144c0010620a014017600303102101c19405080c061511028241e03a035a001c2043c41c07405200d040c18041c14065681c0c444402c60201c8241e10340c030001c40d10b0b12600c00e181c025191400b40c010308180b054404001046030398008240e0350f416410000600b41414200015180b4800140140307410a840341c60100744 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130375827 1250 130374577 130374589
    0xf0f0b181b150304210c08032205010c09060201060f05030307060506040603080706050124021b0a1d04062a11030f03040302060709050f060406121503050f0c0109060c0605070c02 78
    0x100f00e0040e4210402d0b8420105d82d0030b4245141c650f07003011300280e0250000410500c3c002d481d4010803454001040c10ba5604032120700d074030f034071500405a40c2002c1950b148030b503103c19914100c9810340c00a004840e21100b42d03110b00100c0e8040c56070594003d00c100344c007146041c1c002d10b0f0800009000050825281d4a82c02196400b070300c0142c80075910744004002143c000001895203003072070070000c00c41190009000352201070011081d2003035200c6072442201c5586100600300144074a420802854080d80791944500c00e0444060b0303100791a022004c900140a000d40c42d20019a03041a10300424002c882038a001000c211a1000340c40300341304400710303013003480000d60244d0b019800908161414140007040041d2a40105000340401c80d00310038140c8070b9405880699080d801c100400502c039012180081c8044800800fa00b146c2010000500c03502240401c484019203090718030403205400191209041c274031030070b4001707584002d000700401c074207074012500800a8a01402850000e800090b2 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130377077 1250 130375827 130375831
    0x11a03101212020c0a0f050904061b03060e010b07030f050a090905070e0f041a04020702010509040c05040e0a060807050d0203030c1203270d0810030f0f0b181b1503 72
    0x2c600508a034180c46032034042001c410304140032102d41c4001e44c100300890642c0d010600c2118050031544004c10100b00d469040300c4a14548500c465030b098050b80c10040180406105900d450b41c51341c070010906103070550482d144142c068840000c070081041e0b00702c4003603100003000c9003000900c81c0d0210b013030283ca018990003510103556075420291048100281015000b0007544a60300d009284003001d030b9600c802090051007207900503150001800140c03690700c1040c8078030741d00500c3e00f96041d4506401c940038000391280000452004e07600c0803a4141103517001e00030545540c4c0009410426880c0c01c082264005102805983c10107810100661401040c203a00308040c6001100300902c0c002c0c0c070f06000110945035140440c002203a8544c841d10b41c0c03802544013003004004c40c001181105204050001564440402c000c03d180a0401410244c42008201d52212008010403105002c0246c0c0003101c060001c0a0259424440c1c841200e140000985a800c4800f032440c5142c1400d100010754 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130378327 1250 130377077 130377083
    0x2030c06070f030518060705030601050405030f060702010c020a030e150d0c0309021002070f03021302040b0c1c1e110f010c0309060f050c03150103061802130b03011a031012 76
    0x40c1100348421400340641314000c01e003a00005410a50200c05000090403941151650900b07581c0d0346c4400c00102c400e0b115039085180c0522030881c9440d010301c800a021441800329078020440e00c0c4e6400d8040740c454001300409000500a49000d0b502803400c2100151081c09502c805850b20803101e00b000c0a807003006001c00702003607440c0c52100a5003806045c500d20440d107880508105414400e44090713035209400080d0080504240d1115200c005504860140012006135912030000f41043c568809110403002c2c0701140d10000c100441e80100344090440300030355a00ea091004040e0212106508032210340c0c0340340b01c0c000998810600c00c1c420254540582d903030101e003080c19420000d0690b018000c011230b60610340010805002c1d10442a07a401c4841054040c05003140300c001200502542d8002c0d07640e200050310b18480c80000d40c1c0c0105100505202c8401440e6510907113154035001c00d104025140c030700341c0d24500380aa8000011a4010380600f06000d49640b110061a030a00c1c41800032 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130379577 1250 130378327 130378337
    0x60414040b042102210403020a0816051008070503090a140d030621080f07020a0e040b070c031d1807020a030810050d0b090102090909011a04020909041202030c0607 72
    0xc4003d0226a042120344500d40c02c3d43d0101c01800824000c2da1006000092081c01c20045165001c0b03039903043c200e0303006580080070b101015032200c0d41c590302c9920040e110400c03045c801d9000522400e080c0401d0308408855120031b1240c1d40e6051059607964001080000c0318003c41645d0b100180e00d5085c00700e60f000103003000304002492003001504032003050708014120800c0f17015405003000360b000c90802565020082c40d895020707204020f105801100b000a522a03040400440e0701d864031001075220718010460141a601c81c8002a1340340c5402c0c00001c0c00043d01105c654a40c0790054007000c03003100004d00410000303040344400c202500000c0c1d58940040c5c00880e1074a040c9a480001d103078100385100281c01420b40f4020003d6008400d2501c0140b0361700582c400160382030f000b94140d07141601c01032300c00429490403041040c0205598080703e00c041450403021403d50520340300340c45072000040c00904441d1a162118500d005100000070118030080200c104900e6041c004240203000b107441d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130380827 1250 130379577 130379581
    0x60e04020a121a040c03180f050a050613170c06060405100b040306050f07022e0e01020703031d011e0218060d020304020328060c02010b0d15060608040209010b03060414040b 76
    0x1048292403164a0382c80030903040c100c7d40d00320713420b228848004450b40000709444241452501504098103403101030010f0140c1d004003d01c900c11000140c411038031442000c151200152800816400f448840d0b42c0c0d1680314a001495905155002c15002485940c2c008982c0750741d0224144a40c3c015002140e560380c03200e060201d49000d11184039008111400903000341d00d05050503041302e191013142c038804201144903042003091294400c50403444024020343d690025820301501801d0080c0c0c840c0c100c01000c0c1082042007c0600c9890107054003180403c01c1803072180509006034010036152a03074084003480c84121035071000010b0090180e611405a101d04c2c143c010541030415500e50b0251014200d103107000d1240d201010302c140d00382c0c00040020704001340340c0100c0c010110040002d41028070101d580e0b051100c2074000303000c1c5016441d0207004142d1100011240703038030103480c001c0d001b071042c1006100100c0c10038042c42e0b0008001d40300180d0f030700d0300c03120a0a00c0d08c010740f8280e0b40584003000b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130382077 1250 130380827 130380829
    0x10207060b03071508040f0b010314070602010c32070312060509151c0503030a0618110a11190f031b0506010501110a08070305030105030f07060e04020a121a 69
    0x80d040d4807000440103041c2d494680b00d002c551013840f0b1106041040310042c005020480c1c280c1e984d0841581101c4029211360b182d04e0840244d45842d901c03c0101d11480100160b82407050081d4920380c1400d03601d1140080d03505000d1801a030134000480c2c2c0b400b03000300444070b000c0c60b04006807840c0380c0aa81d80c0404894030a003501e040302c032190003440c0110580c1d0304001c111111100c21100c402801d903240c010f0300c0c198048042d0600719010004140d4000001070000703025158010100343c0d030840c0d801e5050400c1c0301c20f8800c00c5402c2492001c22440081c0f100c2c8a20034050440c0f800005503280c2520803482d0360104440100920200840300074041d14464070038035601120120980c106107135544000d0415403140744c0d495905101c0c85040000c20009000b07512000d00850308441c0c0c0c0150082e486240510b0045c000c0c2c1c00901132039009224100600b034140c8030000704201103070141c0c2c0350441b0840c20038050001035031055141c0d0090204000d407946400c103240c4150a281b03a0a28804491840140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130383327 1250 130382077 130382081
    0x90e030306120d050a12090204090b10050901030b010306090311010603060207140a03080109020d0b03010515090610081909020d0606140402090a181b21020708031609090e01020706 79
    0x80c81c40070b5190f00c2445076100e0b40b80c1000441d0020078a03802e005070f480e40c0c12400c060140c0120003000350030a04100340795040000707003d10355020b00f6660b500a13800d10f845500f0300a840e03000344070180402880700d0041020902079440001550300034a44001c540f0340c40c824003420341c0c2040e4002ca864550011b40c45050040d55000c04038141812400744c1400c07031700c0d514001e0175401c040c0656031040d41d00050b451002003083e0301c05000800701500034080c9140c800403000c1c2020322803103003900030740c0903c0009214ac40c0062011119a00382d49440d2015202d4402c1814641c0364030301c0c4c1105141c3e5440b43e210160399121071800c5803078407a2202140300d0b820f051408d60002a149400c600032401400504802c0d075a401080302034030f4000d690b04252111180c9035001805174907200700c1d504204400321044140c0d10000030643c249286038010540c05517110b80c4022403281030000380a40005001003000d280001c2c0c4003048000052814039103141d01c802500048640801c0c515140d0385d400216502088554 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130384577 1250 130383327 130383349
    0x18150f0806010b0a0503150303091005040e0105010306030b0c07111c060e01020f0a0c020609060f0309060c090112200c0c1c02030601060c03050f0a0806190f0b0a0306090e030306 78
    0xc424031402c2000c04c10004c3c0003404003512562560540003481006034030304005442000d200104104620b4403d048064915441030081c00d000d44024400401c883d4000c3c042e005c03c0303da0203441c8940300c5e511610110415001004100e902c00c00e2019850820b541e0710040110060610140341c59107030191811008a807000c011034201d40c1d0042c041580c40141060582c0c2c018401400c040074807e00030301c0007854900c0f540346142c1c0d11200c00f14030f80e8461408200036600c200e00309011504c10f901c1d403e602a21034042ca200c1d003400152407511040101d0026006003542075542c02000b4500c0b000c91030061145e81011103c2e443d56801549000340034903210070b00a000a8280c641000c0bc4039186e00465142c0c801402a5403c0c0a6801c0d012420544a041120b4400642404003610341c07a0f0000700804003e000e03202e061140c0620711102c0c403460505049241182c03408002101d100e403a000404100b508038160400c2816569207000034042c82c0c03401848013404410b0055541c9180c07850400580e0191 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130385827 1250 130384577 130384589
    0x30703050702060702030301150509060a03140703090f060b030307020d030e030c06040b0d020a0504030f05011505120a1101031e0b030708061b030421080a05160918150f080601 77
    0x4005020145170044101c905444280600d40003100c00c4c85400d545500c20580c5041c2c120000180300809164907030b02c0002c001c1400c19901125843c0c418040307040da41005406001441c01c885100d0000329154064484060064242c2c0d04002041d00003c5485c601d82c102580403600004000030700f80f400340001300c1c0d05c51040320310908140c2002d00444417070154020f0494066030009252080c1e500610070ba4005545c45218641c810b0f805141080c0644500c055000754030311040b074081424945015824034201d00790b0000d2070384580b56140d01d9031908805140340d041c50b90b95a8941c01c070402c80c5042d0300d100e0f40321044c0492503404000c181460b000039644001500d8220b0010f02c0741c2c400256045101c00700000743d5103901d903102e504298152103241d08180c0300c1030110600540c07240d50441d0341c10744142c900d2141081182d03901c400702d448044c03102040303800007507550400b402000700000c45c4174402010f1751703000100c001135100040800d0070750741c000c0c0e0303400d400c050401c10045e0700c02c01900c1c1c05025 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130387077 1250 130385827 130385833
    0xa1109060a0b160201020f070312080a1b0e0f041d0c03010207152007060b01120e12031806010e0a050a0b0d030804030201090c0f0303030e0106030f03050d0f02030c030703050702 78
    0x101c2c0802d05011402012030300d91951007091441c0d015a88200805422900610103403003020359039180641c0b148403035440d4100030078564170024106642074400e1140904003005102402028203008070344c600a08a40c0991102c0080320311105525144124007004480c00040d480c44081da22038145404544005131748260300410501c000112034421030200e0f50b010140128802001151100070f5405551440800100126120701407100715088141c0a10f0700782c81d1117481c01d00404901e01641d003051303052525076101d04032280c400550000215440340d0010020f0307800131032554500342416000e0f0702a01120b101030702400700d40700c003070300c0b49541054108400f000324101f4840410007090f01040090300340200300e8002002e140c000c0d0041800f06510041240d805601da40040b1800c25942c041030300040c0c03412110301d8003100144210800d907604400d04507c241055076003140c15501079000e0313030002502c0328140c0226106a001440c01007030f07000c1440e40c591410301030003412504001c26180440d4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130388327 1250 130387077 130387079
    0xe010b04050a030b071704031d030607050a0e120f0d120509120703110109030906020d030917090d06060303090608130c050f1804050a0c06140d1503050a1109060a 71
    0xb982e010308035002c580e40b10a152100d40e690303070b0080d200318190503008180c51600350104410940c0c0711000c070f800189800044000e00050310240350f40c40b50704654110205000b00701088a03075004150100311050014180c0350030142c00365155092641e10854540c80740d03c00e124101d03003150040d40d12108088848010880342c40d0030203203607075107150302c01c110380c0342c503600140d00d10525204a1030b03010015000d8001340988075652500500b0801c1920598005015854041701ca0342e1103170240501c805d810282d141c0081c41c03209040c16895102010590b0320041d144803a81c001001030141e04021402511401c500718500390018191200c01481018a01181e040a04c0050b1078011040282c450523540c10030702d51000703404529488405104001850b10031420401041000203490740c400b440ba04180350708655408099610700d820b0752038081c601c0c2050084015100712584101c00c0f002c01d000500c0c0c1120358903281d80d414081545403d40e10034202c0c6000b6202c42c140520f280d0340220059a07400009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130389577 1250 130388327 130388329
    0x1080c040b090a090e5502100201020342060d0603050f010b01090e340309031d0105090405060d05030f0703020708061009020703180801060e010b0405 66
    0x584518000d00300790910104110156803518000c00e000703003004040030001140703104180c40c1e842000518043c05420311140c04079054403140c40c0361811403c1c0450110143d00310503914500c403c0d803440014984804d00d044040540d8814a1000d010040e50300016680d060049440028644204155085000e404a07008400329a4100c01c0000b40040307c030003110050000008481e80700b4848000403203810a0b1010060110100300ea441c49000303000200600d40011006440702c002902c159014030b059580040c2c41c0c201c054103a80c0d10120020100e03080708102008401100c21416402d400113031761014000c08040d0000d00341d6001040e4000c003001c40c41a03510008200303106040c6e9042c000c1e5180d00115586854000c91400d80070740c050309403078031035402010306070032600410340c2600141b08100e00081c01d0000451098000d0403602044046c00e4200480a00690b018401c00c80030403080390b865200d80c1403003a12100c06042c08100200f2500e140450740901c3c08c00603006100c10ba40108810059 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130390827 1250 130389577 130389601
    0x1b06060a120303020306130204060201020c0106051206041416260708030307230705010b1e0a090b010c020916111507030905240a05070302160311120c070f050108 71
    0x2407036a05240142e030f03d603904c0c0041182008541140c4914500109012540c81e8064002d402c0c90042c00000b040055034031000c00525003403140c03180605801050209000c50302085540c018104100101c503544030481a41c6c444c17040003580550030341419003505d54158080da034200c56150b84101c0c0208680c0781031040d40303034032480045c1940041c0f051018400c031602100d1190a402001d801c202c00e900c501182c03c00354007900c0d40d40041e82c41200003444210f90081e0131800c070703944410040c0802d40410b003850f0039100240032407841d6606010b40c0c407811400603501ca80440d441000c080d085c41c62aa5100040a001806164003182c6103411118032a046a00a00500e81c1e015400d4075002c1011001801d2a90a00903c0a40149030380003101ca420b500c00300304000a4054940c004081006a0b03c1003005c4040b801024034200700060300f007600713501080c031401519042240e4038040d210104414421816a5480014081e00d0354000b10420006010003c81c4240100420300306020103203800410148 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130392077 1250 130390827 130390859
    0xc06030f0902030d0f14040b03010905060d030207140616050703111e06091f0302031015021b0303040918021c0209181c02030711010306060c06051306021b06060a 71
    0x100b001517907007101c4c480d00c0c4543e0508114200c456549a80c4684681c010440d0758070074064000b0050a01005c04e000741170901164400341c0c1c0650207841d150741401000070f100304000309066440318080c00070790b039803584401d044860389100780d0050060070b2442c41c20a410f0201d00101078820041007002002504031818542e096890803228640e44401e00307400602001440c49020140c25081002588400e40590003540115200c0c110545500ea4070481815130182c1c501013103005030092039046824a069008450002c0340c020150707420103885180300412500c2c21843c0605c100c41c9106040d066042840c40c1ca41020611292816841a55008100c2d2650080d28240d80c041008994100c000000e000c100c0110341542401d00c2514131406009680f60800c07801642c10404640c48100340c6e40c064400c02c402c8641c3d54607018181200da8546a00404008020340b46003042800c245000400510050400700c5080c1460300b00041c105e00d075549401d41c02002a8064810450140240c10210003504 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130393327 1250 130392077 130392103
    0x1502010528180803041b080714061e0f0a0e03010b01051902070302030d08040201020607031401090207021917070b0f030f041e03030e0f1c050307050f070c06030f090203 74
    0x300d6002c4031640e5000c007500100c03402400207080402403104208001c009050f10016807107512868503101c00801d9101d00700c0744606004900b003240302c031600c0e0802101401503900303071090405030403e9030441010150300550060f03514500004010394116041310354424a010142e000700300c600c1481001030310382d05c20400c00442ca0701020540c5084644200842c0e409954080c00340e6031080280b0a0151075030710107480490260280302c000131a0548240703c0c002200c1d50b060761500941c0d00e0503c0c00d40c020740c003002c4142d81245840c543c40220082c0c0c01c0780d1200900b680360ba24050f401408917100d0800340c2d00c1d04501310480c800c00940d0003a0207a901a40e4205d1035072001c0c140c00c2d440701e261940040024440300e46024142070000303000d046d01603002c40740181c0c102040e90701e4002080394061300c98218250108020113060901804640308a010b1603010203e0300308586041c11108142d40c04d50070284c02101c101700600f0f02800f0310366041c0111310032a015039000f4415080c0726170010b500c1e510b41d40361780 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130394577 1250 130393327 130393331
    0x70804030201210c02010b09060301051b0a110f0a0519080706110405042301210f030e0603090c0f09043315050a060207030302150c0f041502010528 65
    0x12000303c011041e1254260060030504106450180b800a406442c16801041c8249620400a42541018047c8503c1030382c490f9915959040c5c0c054807409140c1000e0418010068080a01c1d03803003900811007168804c0707162008240105103447c000b483d103508421400204011514414000340380031082c0c2d10401e030b0000b40443da403007510803c0d02c1e89001e1940110b030f20504006081907505400c04a06501018400384e1290607070b2940450101c0c60074003c203007000d00003225462004103046854501225200b07240141d01c01010348002411600300b40e400907255040008600305502c1d00000b40910200207403041c008074609903c0e041da40e18040c440c070f040803583c2e42c5480302e03c5078140c009126019040404c04c12060b4695900c4813080252401000d0040320030b51808101140002440011654194024a60101880d82c8201070f1840038203440030300041407201d03598003802c0710040d201a00e0a0040c4c0b42c900700103c0002801d4880282004510306042c47c401900841480c4410000508020700 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130395683 1106 130394577 130394597
    0xa08150909030a0507020f04090506070f02061005040209030f1207020a240c03020705030703060f0b0109031101030b010203120a1b0503090a0f1109010305030405030d020102070804030201 82
    0x10840d190b40b090001e2091148208020404a4405855003070001210b10101d025540381c080d084403181c111100b08040b0543c00701d07031850a005a0310040440d0f007401810844a08058024903020703c3c6c0000340320200340c0f020003281007421200400c59a5411103402220b6058000e000c2c100d116001c449400504503500c0500d484124440741107510281c0c000300c0c000e642d041d0001c00704030158003407500000b4131543c00b400303c41e0040d401100d0204080c0d0071040050216a041c00c0c0c0079060156407401803000c6014000d24a03c208820300b0300203040e50780348006034518000d00e5039050084a80d4410880c00340d0440e04802000040e01801c00d468160001c001d5402c0d0100301e51092844c1e000b00340c100b0215014404000d800c84c0101c0c0d07a502e2a48581001c50b295401c240c10130b0f1119800014100228103040040040c40c6401d44001c5042011784d582d00c841a10461202034104004039007 = true := by decide +kernel

theorem cover : BRFrame.Cov 130215827 130395683 := by
  have h0 := BRFrame.cov_init 130215827
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130215827 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130215827 ≤ n) (h2 : n < 130395683) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
