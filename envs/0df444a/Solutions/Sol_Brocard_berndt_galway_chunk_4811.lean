-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4811
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:48:30.286983+00:00
-- url     : https://prove2.me/submissions/c7a059a6-966b-4120-b0e0-47029cfebbb0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 865107913 ≤ n < 865287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 865109163 1250 865107913 865107937
    0x503010b031525120509060702070911091e09090f03070f15050a0204060219051009031b060603020909032803090516050f0a06020a08030c0412030809010c0f090b 71
    0x40b1401da40350342e002c3d05004400024a4855001002180340d02c6016001403074107005180c9890b051000035501c10711800f80c00e070001c0d154241c80505920700815180d10350b40c0180b80700c0031122070107001c41260686500307040c80f902200b0042100d0140205810b4103400b200c201852078610300b5100e5031100e01818104070f41156461b2003826210aa07485664000e541080e00580e54520740a03000346416a85100003546807410042040051070010784e2809502c1c42e0384000c11003ca0505003030700d20705140e030040c21001d92600d884400304240c551048080c0c91003262a000b00b0f45403100455564028511944120303684a025500781c1200e40d040c02c0101e045038580860312030003691300e407400c01c1380a04025618245e41e02d002d200340d10b8200281940c1c00b8040d5003882600d0310b0808000d688490080c0003800c018000004902024081e074100e070043c00d14921096440030027480c0080001c0021101880694a44944000001d104299284105031180c2d4ad820100e4141031045a06a0051038a600 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 865110413 1250 865109163 865109191
    0x160507080918160906020309090115110703030806010315030f0b0402030c2d010212040b0906040504050c030a0605040c09051203040e1f0e0c0a0c050a0219050a0503010b0315 76
    0x25621940400c00e4414074803608030160140c0040030140c041385180d04010159001480650069200e500410741182c0045102407200d810501c400d585192480004440c14043d220303001c014150411901070040d4800c2ea41042480c555000b1200100050f000041401d2403e01410000c25a0304e1003060f04180001d0030385140c000301c00e001031035041008001180721a8440614604540581e030550b1822a00380040c00c1030100100c05241e4921a07070041150884010a20044584846007a40c2c042d12020300200141d00744054803008940089682003082030030004040f40ba03080c01d0194031500d800c540c5911f80441d081404000d0207a0805580020034407050000081941a494036140501c1c0c0f26005403001d041e10004459040805410900a59030740708140440e0300d80040c200c4000413002d28125851402c14a8040d041074103400000c2d44c004804600101c0501c441c062000c110741c012105401c1e0b891380d80c0d0600d803c1e02e5540005641c5600f00303103e4095075800021110b0750210202a00b01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 865111663 1250 865110413 865110439
    0x6020c100513031d0f012327040902220e03030c030612070303021509030c070e09100e1b030715030203180f06010314120d0e061605070809 61
    0xc11280100d40750b184a078484450358050540141360701c000040c5a6401030700c0c8030303402c4002c10300501c1c5550519040140240800c040300c803541c081c1c04104403043c40102e40c8d9402c401c12541c810708a0794100c2c01400c1c04070701c0c0c602c182e01d0a8810a4802640600040c1c2c0ba011460040d094407401c0042c03880c142901c030420948201c1044c8019803143c03010000d07880d102d040102c00c0c40030210800a4100a0342d21251060011980002c1e50241e603194280002c49241e4514846500314000c40c04d03250003920a01e80302141d85403906031a244114480012115594400b1100f80103540305980340040c2500300b074810b01e650f400102d000c018803040250840c1c0425558460381008000c56400701030000707902106100076101a940181d19141c503c40080007040c0c0a20343c07075512200188002040b10703403907000c125602c03101444442c0c8041c0400a0940d1140032442600c0081e04401c82e46c0d0000c0e004070000201180001105100481050390301c0c1c80c200010f0390b03242003490b4050301413107a106004040207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 865112913 1250 865111663 865111693
    0x9270c021608030a0806180a020307030207050d02060f0a141504020f030403030603030e060f1b010b190528171002071a0c030106051602040608070f15091206020c 71
    0xc2030080c03415400030f56680c0c415200080510102400039441105600513040381d0ba8011072100360032410041c80103980380c07924041503000788207800004100703001c1e25150440c00e03600443c401e8803c10780c40c07501c4500ca54800d0501802c42c0d00308601d0036403695448011450818202e03c900c4810f12000c1d1005180506034419005140c10403202100040e4841100740101a402008a0082e02c0c0070395429042c1685481144a94058a10305040300c01030580d0400725240250000e04102c50042c2c070184105e0840e480c01a21241c0c24051030340581045912800351900c9001e000b500c542803034090000141c00e013a20a10102412008071160f48600110b000d0001c40a10080c00450b1049488240c1c0003e8840d0711000140001d180c0d421800050004106039500f020032100e00c0c8030200320146644140e880058003c100c150002c00f280d2042c120b01060b0041e065000900342d64151030901d0050b807104c038084070410403d00030600701764514411840011310300e801512010074440c2c285c619420062501d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 865114163 1250 865112913 865112953
    0x30c010606030c0f1805041b0f090f050f1305010f061b0c051203040f140f030714010311040b0d0b0a080105090309060d02120c0a030608030306062a0d0302030709270c02 74
    0x207074089251105602e454440e0009c2c6032110200d0700d400c0c54007526152503c004092042481000d014503010500e40c401681c41c1d03404c54100710100d82e010441540c44918007102180180902c2010461214040300000121001005401c0c2d00c4904628070f5030500c07091049401114030003440b540320a11010605440503180140030b41020145150341c07501d0002041480c10703903101024041d0300124400c2c8206a1000340d8140320b21005e0902003542022482e81d0b0b401c9204a0b8071158206400ec1000f600d1011143c02c40002210704544980c0341646905039603003210400e498990095100700800c40850803e9409024201810b120050410600d04400c41200401f15800780800317100080014009170144100400b403d40840154258901040840c1c05440b13100c02d101303120b2208140d020050980c40c403840b020401c100e81561101c131403180f0007a020790010b60301c1030082140000b000c206c9200c80d40224110341030365001c503040d00c1d5480364640e0003000310325031113011409004200707801c5041482c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 865115413 1250 865114163 865114181
    0x504050c16030210090f0c090219080702031b0c0f060c0304090510032a0b120606090301091502070c120b040b090708070303120501090603170c03040e0405030c010606030c0f180504 79
    0x1600389152440c0d247c0b095208505c0d030803502000d44107224441c3c0f2054880310205103500c0c1d5041507483c503120700c07100f030786907019410845c4030420140200042e040404100080881d5003661203002e003403080420007c0d180100000751942e40c1c01071000308002181c542080d0780042c0c10358411805a83c483c0c5660041410344121009001c1c1c07150100c0b902d0300d8800c0c144030002e046802c1e4041c10645200c103000b1040c20007074180c40c815403001c0307190303400c42ea02036001c082601e03444074021181d4503401e82040007079003114000b030b940c008840e01c0001e03554841c041418100350b0f10644283c00c0383d071141d0782c400020384045e2a00417144a005004a055041000041e000c1e6010751115000400704549030f805540c0c0c140c0060200c2400c01d0310030130006001c4c1300d8000100d0031464a4944507526621518503500465002c000c000e00610140020302801000a000e1a12400028810f540d11014154240c030041c51418000610040300c48020f54418801d45040302c41006401721815500d0b00080c0545034400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 865116663 1250 865115413 865115423
    0x3070f021503071d01110a0201050d1d160b040b0a05030a06050325050d080427020d0605100f0504090e15070305241005180307080c03070504050c1603021009 69
    0x1007182071940e004c041c0620a40809180c0f1040702442514407540305e40a003040203040c03140110310018102c049800c00a0f4a414144c05154803040b56081c40340d44852a0184030b444581202c40424615441c6040301d06070303551407040a140c103143c40811039840c0c5c801090120240e98805001c2010365007403081d1687c00745120482e1030aa031081c1c980e46aa540154852407007808007656441c0010b0711002544c0407625003800358134000c244100301c05d4046d55658100450f00f07100151a40744d81087d0390080f81a03840644080d42402070300c103000c1c0c4040c0c0e201702c62000410030511040055000c0d90300920740302c400307180580d00009454641e08040c140e06580c4240441e0b102c0040028a01040810b600c03140c0100c401030502c2e1402c580800c501310f452000c00c0302040000205a040d500700c0e5003103c00c04100160845004541c0e481c100e645644d21403015611138002c001e4006024603140c01402c0c0035188814040745040d181103140d0f01c901030002000c80560007030f8030b0920030380d5045210b00340c490f038050 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 865117913 1250 865116663 865116677
    0x160c03170703090b0a0f180c12020112061e06030b0d080f0706020412050d0206010b090d2d060e0a051e2e0612050303040611040f09021201050406030503070f02150307 73
    0x1031a044003e440741c2140700043c88070041c010301f000c50516244142110306202052881003d80c0c0012a0407401d0603d550400c141424000514901c01c210882002c41660340c01c00c244540380e580403010750380c00c1c0b200c540d4069613210201000c43e00400c001c200b84494001e41502c2c20000c0da44001c2640c000ba844032015889508480341400814080d035421800b061010300242d40c10b20007a080c06000351a80203000b20588050201002843d6049a0381b5204ca03841c0d040c0001d00302c0b415440070260300c50003100c0039170030248004004070700003a1600758031ba0701c10094a115913081861848191080c2e41c604060302c10781e45481c1041171240181340b02ca041e016468084104d0080d040c2c4240c0d0300755070203200280744031541c80021900100a072600141c0c003582c080380c00c07880300d400b16405026681103130014842c21840010500c409600400e80b1911608003032020f0781c0d0381c4082008a0b0302c0741c44007030f00a800070401b090005001100c0706141c1440200b20108038044240c80200c0750b0030803a08400403e0003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 865119163 1250 865117913 865117931
    0xc09090a2312040f0803030103021806060706021206010e0118121b0f03030206071b14070b130305061006050318070b0403060618050910110906070b160c03170703090b0a 74
    0xc000c218001781c08894015440c55142d03a0100c0c0070244403032886940a203248000c2801613550350201d46006810007010b54562481800e80c4183c0ca000b910a01d000c10b125240528055004102e21004170042c4005081c0c0c1d10300d000c08650030000141c100300c64440f9074580c10003140060021f4503016003881c0300041009407d500d0080d181910180a500900c0480080e8184161901c1e4100e00429405581040702c1601c005030203140c51440d4000e161004004a103c21301585174039a08011240100105e603080c1c0c41d4504201d00c1c829250141d0303400504d0403c0080c06900795419030f00091122803089440c6590f4808000402d43c01680040314a240c403910308001e1116858034000b03a03904059002c01c07580c1416100f0583e00c00741d801d41c111000c0c1c0c4405075081c2d03401000c016035184030000761141f60b0f070304030916125020440c101c82440f440446840308004042c0720300a460001585500c49012850102611300d00e4000020300c18810176403a540c03488005071002240c0b07800f480341001c000c605980 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 865120413 1250 865119163 865119179
    0x1b09030b0916060e010e15180a0311040506011e02010f0e0d0f030c0e060301080d09060c050a1e02061207030b0402091302030604140f010501020c09090a231204 70
    0x6000760014110340d012007164001c00000340124070440360305042202c440c040080040c0c40c5060341465140c2d02c450080103410983e0070b10401050f02c1d5240190040540c3c1d41c0303100b0003416455601000c0c0000c40c0c007030111800c5040903031141c7d800604c1418010f0400c418029425000c40c160848040141d45400000c2d880c090306011789000000c00340080c2c41e0040c04200c00512040c0070f8102c5d401059107170307180716000c540100801d03564208042c1c880c3d0364035030b140c042c1c20360344a01d001d2101e4000b0b41094000035049202c0d1403081d200300c3d48100039040000d4030307172501007902c03040b03090301c00441e215101c0340e1006035612001402c01155a908440b4140385c40400642154100e04840c1d000340e004006c940c21f1b80d5515602002940c0c20010010784903129240410000e100360740b4914401d00b41d020034030200400d41d0450300d0407210300364226078071b411003c428040c41c8401560544803076803095846d4000100b002c08044a00f40748044520b154070700c0400198945201c0111703111400c203002030240b00300c01c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 865121663 1250 865120413 865120433
    0x2309070c0c0e0403080402101b050102040509070302070209010b0d1107060e010506061624180c06052b0b060a1106060402030c030705070c050a090204090b0a0b16020102011b0903 78
    0x302100100d0300c007503d0140c5001c1c104030700003440244070320040d20b60b0229042c010316a5000303094001100d0000c0d0106031404074000d601900070b20384205040000035412a1190007160310035030f4042d10014542c4d1038091907200b590440c105212010340c980d0071403a0050282c10191069a000340030110311038501321649421140054145809038004202981c800400960312211295001030807125207c02e9941610f100c0070b007440004112400d00c02e1580d03a819581c42005c03500c1740226000c403030aa68070403054030180b00d41001d0300b00c8101d034002e400d08549007043c81410400040d07100494200c0c0c1000c00603540354490b2440c1d2000c03c610101d82040da550410980f640001c0c25035003103145081c003044090580c04010a490104100011101c040018982750a80141405049002c074103454017170f142c0183d0094000c120200386000020062032800d40e040108803041800c00300e150840f00161180b0750903c5440503810341d9226070709101103000183ca00c08142c2c02c0c554584042c2c508525240840c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 865122913 1250 865121663 865121669
    0xa020309060a143004051209030a120c0506130c03171b06010602010f15120201120c030606260a0b060403021905013506011115010810060608012309070c0c 68
    0xb0613107510801c00044d1000030718000781d4a00d40043c41e11800203c0c0001c2c582031000c07000504202002229550b8180c1080c5007018480c0710720180c07a8565550100d0901d40c510801001e040c01000e04405c0002c2503000c10800c90011001d0340c92450400c0320740c0e8506542100118594081d400000100545a070a101e07480e000c00305910b0900100c13240c0d680c03400015086004144020001403583e60843e80502c2001804800c0c62600340032b03040f15400060300403c540d00c90b000200300071b4000b071181800e200c0c0038a44008a90700c0e040c401a143d07242c00d074004100e12402c0d244c0000c01004040301580e40ca0100c0480c1e402c06603c2048018100000102004060040000e1048041100e2020110856230944a040d00302401001a07907884004030f904140c0b0701c0340c0c8101802010007440e035101c001e5404505071032810302228092110b44420204075500c5105420000380d80d08014058859006d8520240d131204644100c0c0b20b440701400039264410940b5828040b905040c01c1d00b0070041d4100c403000c01 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 865124163 1250 865122913 865122997
    0x180f0f220c150216030210050702180406110c1f0b04110301090614031f1e09030f110318030106051c060b15070204020306130617010e030a020309060a14 67
    0x40c4c2d44003200f4680001c40e010007841004455101d4580b24882d006075198150024860f01c040000c0911440c031004054409550041c200391060614860031400c48641030302c4040108400100011100480d401090300e8004064032000c9007889541ca80c0200d21001510611003680c9516040a41e400c8840c10b03404111009070040d0307140304581c1c0c080b41c60894040c140505101010f00203642c10010006084c7c511416040b80360300c1a1044c200b40d2007060680e20070380701c0080c000044002034035102c090b40801c4049070320820a41d1401c990f030150f0f24104810280010480a40300d0000078880c80b1003040007005c40c0b103a14400001d03c01d2078000c161096034161166100170841e190090910b204a101c00b0b40541d40000204145882d0031540d1f80a132829074400300101525140c1c0002031041c8000b5026081d801c10f1004001d461010044406400654004510b054004001e016054100c4040e5505101500d0b04240c4104107010042503541400706944105d00e1410740ca42640c00054040015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 865125413 1250 865124163 865124173
    0x170d08090f1e101a100804021f0c0507060e090a0204080325020a030302060a0b0604140918030c010912170a0e0a0f0b0402180f0f220c1502 61
    0xa040401040200c81907148040158040300c01180b1103181002d41d0303000600c0343c1e140111400d00382d103014162000072801121868580c524054086580c9030050343c000e0b50007600d920392002c001c0564201c04914130389504220208900548071039081c5003003a480711000c51003140800c8101c4ca44041e003990300a4030400300314207290411040a68900a41034007045c1020f009003d1901e140e0b85040c2c0e6180c50f07074010011641640ca0345030094680a003610840682810f240400705a4508141510141c0b00c1094030800360305140c9003003203140d0310007504a00e0000c0140d1401c01024200388000c00c2820000700010503540220715103ca60480400796080801209501c075003046490351551680040b0384007c003080741c5c0050b080740c40c01c02011400062000f841440c00b001044505400c0364480c500072641145480081c0c0000ca04c00c010842e48140d0958400c0d000036090055440c0329508406c22004041040045805880348203131110030503500380c0e403050410040e01210f1000d0410720310781031000d44 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 865126663 1250 865125413 865125433
    0x50c030106030b0d0503121801020d0b090c0903060604091b0f0819031710090c030504140105160f0e09010803071209060504051c0c031a101a09030106170d0809 70
    0x1071b101d018894084c000c800000c808101d14030303c200403440900d11020021992421003a010100074443d8520840c018808000003c40041d00741c015101c0342c82c070103806004250344110401c4020200ea100485001d11140c0010440e201d91240d1280544074240c034400c42103042810f00b52078008198190744413942c0c084d1740303000002d41c010f00072958000c42d05403040b041d89402a18010001117500840034891405901010203985a04a00e01031380c001d2102000f0444200c03c080c0c00e0750022075001d400811101d1302d03261813034842d226860700368295107081018050301900081940074203901841c0030341e1020503a04144810001075408805150a08043d0079260140160541c003451081602c039502e0386a028035401900403401e1005030380462118603454480c54031503d0b415150716045c240302004000600c0340e060240c00b005c04e848072402c510347e00c10345202e10803545501603030701d04d9059501c030500000e0f8107403042500d8209141c0314000d03100800407101e0041200c44020300c02c082650244a80c2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 865127913 1250 865126663 865126673
    0x180f030a0507020f01020f03130f12020d20210c04140105012001020d0e15010b0405060313061d280803040c32010f0e040203060102070504050c030106030b0d 69
    0x110340790380d0b050f201510411801301c0140e04002c0303030f01c01e1540c0c2804002101c2500d01c07a0108070005860181c002c1d0050740f130303d07860038440c403040b4020003e4100c40c0000116010800c030742c0201070768a81d104120392a04841d0070220b00000041501d0100f4160342071890300708040103101c3e2200c099402e40d4200202034150a180070354540602c200d03410f005001b880d400c4852201340e0400e08858800780255640c00c1d011042c90014071049655001394050340740010302c100360007420030707049803044d601c100c1c00c2030306000810032543e00207040260b50b040c90955602c00101c450142c022103681004800200840b905500c5007024100c680541965210a400b101c0010400c801644880d4200300c4a64a95031103280c105c550003103e4100c0044604200602c141d120303031401000c034803082ca007481c0c0000c01250000640b04010407510603804651600e81e01589070400f5806545d02050510458668a660301c011400700c440540394240410320002c014440350345c060240c40c035413600646a42d1001940d94445c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 865129163 1250 865127913 865127917
    0x3120d1e1404171b0604031b050d050a0e09090c0f15030c03070917060601020d03060e04030e01140d0b0f030708120a030b1503100801150e0a060e180f030a05 69
    0x40035911140d1030f0b908045541e41c242e031441c649036079401d042062200d2250740c0d070344000c44007200014202c0e02c80001c281100d0341c1501003540c0c08002443c111059510544483e0040d442110800c03001440c1c41009650785488580100441d1b0040c00100c41d5010038068440b0040c207107640510401c40714504a004042d045a600c22841c00300d643d1a904c4151085451080e207034403414030000c1141d076100850001190340c0d80540000d800700c07282e6070480e5905034180c8040d4842c00c1044400100000c2c0030902070b07001d40310b540105140009441248400001c2c886d040200700c484010b6031034500c10000c0c1000c03080740c000e01c00e0807002411894640141d6541c0c441411032505400c42e0f0128015400500980040c8000341c3c004284800c2d0f03420344420782409820490710300e280c619004200103440c20041c40b400c5a80c03510300f1303000041182810380400c6030b03910103441841c499070b0701e020018000b40c0382c208450140a13400d45541360302d070b0301c0790707400303191003400c0b10060601c1d0801c0004000781600202 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 865130413 1250 865129163 865129171
    0xf040c050414060d0507051c051e0601030f061502190b1902090312071104060315020708040504060305010e0709060f141f05090114090a03030e03120d1e14 68
    0xd018600314400c80041281401011038141c0413600708070501c00d903941c10030094155071045001c0100b2400b40c6069003804e44100b56040703d00706080101007070707001c11803a21880d80498103040100e25070088182400890f038a50340400354400001040c0450594180a208100d541c3c000d00608814515110703000980e00240800c5450b0744428441e040c1a903013501610110a002000d17103400321411810080c01e40e00c07001085440c0d1107605c0d0801400e2909120752411749400c400d0104940054401c00c8000354086031081c0c3e0006c0c400d00c40050039990301c2c001d12016520410000c074075050000805458201d05070080701c0c0d0141071801c14000c60340205140011521021806001812083d000c513450440c05415000d010b0042c00407004081d81141c02456109400e903501c0140f0303a1060043c4001780204050701d0303406003070031030f041022030302c54a2242240382004042d0703486014060306104841d88881001d80c7d02a840d0500b854000000c1484500d4402e0403c2040c011a410049031010080c0024 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 865131663 1250 865130413 865130429
    0x20f0304031208131209061e080a1a0405040c06080708150103020f07082113080d090203010b13051006091215060b07080909010501050f1207140a0305060f040c0504 72
    0xc0c001031421350a0311070308840b00d07041421192030100540001b0142501b0740121130115090850464003c0c0c03072100240002d944e242d4070060192141322650f0040c09100f012035034002030884030b2a80503507561250f14090b520900246241614000001d046660020000d000784a9060100060800d00f48000c91130341c10246001669012903030352006a602030a0b0000d040c84101140035104506002d040c030421242030045031110340e80701c00c452304400c2e1003010000c003003010030b001c2401340544a8000d107046c035200400109180b133100010070741013480e00f42c03003040154449042c031a41504081101010b03100030324001000c241002080d1044211845004049904444e2002d080e8420b544c4140d010b040c0c410910341d0380d2605801d10725042e411134500e1511603920f080000030150300850460301644288041d230303400c00da000c2d2101d0318903447c020404003c2c4400340e810320141d035901600038000d04c58942c03400103084c1404800d0005149122500c00e004918110f01d80e0100e43e0402c2c02e503030841e2185 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 865132913 1250 865131663 865131677
    0x1020c01081b12070807032403111305070513060306050f060a2f010b0402280e0d061d0607141e070f15050c0f0304021804030906020f03040312 63
    0x80300d01000340c0c0f05000c0c111402d40400c409002c265035100d1001405070075550784c1400700d861070418410a010100c6090015540d00da602080041c0c0b010700071a06280d001052081640304110110b800d0b648101d681c8130001d1000629003803c50550411880502075a01e400c00115007450080380a40003000c503118030030781c0c01040c80200c09100f075080c2000904c1619440360501c1070b2900d111110006007140c03080f41c5d424403e058002c1c0c203051003034485007054568000f58503440b49461003440880e1880c0c610070081170744150032458840d810305008152164000141c2d0a58140904080e54508001040c0c0d54120009000b00590f000a174207440e1426a2003c42c1c1da01150910301c0790f00840c130300703100078407a0000c600517080c08202d00c207119003540100a1001d1607000161282d04640c01210b00c00c41c3d0300824000c3c0c00c1411a103e024551192001e071000001158034401031511440032a0b04800090144106000721541800700c0343c2509584402142802c1c00c642c1e4a4142c90000708806082140e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 865134163 1250 865132913 865132951
    0x8041d100303120e0d020c120105090d11030409020301180606051e090f0a030503070c0e131e140a150207150b0a030210020c011e0203032e080102071101020c0108 71
    0xa00e5000101004c25901203c000c2240308001940300d01c402000140b1507440c043c82c426100d01e040c09800d1185480d50094102040000e0301a036035180c02c3d90440410384800e00010401e8205480203601a00d03510b565002c2d03c0d20101014000e46503943c0002042082c144201c03950303143c606204070380d030b03840014201da224103642010484901903480625845a03000d4800420b100010008048590082019988203900c844102c0000340c030035980301221411f40b1000c040800c00c80d80ca40700c411200424a512009540d490740c41c02126050410281d41d040308005800300684000b09003e249550308007941420003949035550035008002108580302d13114480c0e0145a03650a01a901440e4000c041400c1380000c0f00e4003c3d50f0740600061140413928080c00445801d2031001d1a0908465560085181d40d6481c5400058032402e148640c0c0030310344080580801038910010340d005400d24034001a21003450b412f03c0c10200b043c02680780c3c19508a00d00c1ca520f1a64442400d035800f40d4900e00300d4602d040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 865135413 1250 865134163 865134197
    0x9030c180f04060e0307080c010b101b030306090614010305060102070b07020f21030a08060316090b030a021f0909050c0307081801090c1403070f1217030408041d100303 74
    0x80c401e40c015030000140146c2000030b6040904440d0059900810260b1000710030700540c06035107081c0401280b815107881e00d01c800109001c241240c464900411115580e001c1c5070255a0580c00c044130402c80300710061059641441500e40c000750910003005490701d0031030351560354800d00031301a018102c428010110741c0c40e1003080c4900b480304000c1c414102c03842c4803601c5440c1c1c3c210070070f28800158840041409880c0c005070004100a0020700600424903103540700004210080c14150103005218041c005652080b6540c12400089481000812400f0000403e200c1c166080814554a0041030195220512060741c0c0e02c070090382002031072629544100f0100762190344046080d58203040d20081082450516841200d81c0c042d61040800e00c01010142c884031140240001940d10a00c00c120a00b0341000e006089801002445030300d040c5c1c0c01103034525503c01c80f42600c031110009000c1090b01e41c40c0d2040a032072180000c45200505095130300c0b00c2c24410318400501005500311040f01001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 865136663 1250 865135413 865135421
    0x140f07030c23071a070203031306091b080d030612030503280209120d0e09062101141806040602070303061e08060702070e040210020f030c0309030c180f0406 69
    0x39070b40303100b5188031182e5030b002c521250740a40300c00c44104c03209000d040e00343d6410f45681e9000b590a90099801d6503038528074400800326421007030340c041e0b8507000e200c4041001e0720f0300d034104059840c400c1c0744400d051800701071810359146911070405203049020480852404890b1400e55410302c0c0c950344da6245d402c5945515844100308400140007408448442c09059000301803511084d10526994441c0c056181d0315184140e44c060040f410b10400c10040e40b61084442e503000c14001c2001c000310442032480d602112002e25802d034076a5542c05ca00075402551400164400d12907007101d512800e0052119480398006480100032980207e07444003010b001e6044640075200076003da41f4040c6405081c03c040784000c0c45400300b00d000b40000308414900c00318440095401d003014080c5640c86613400e001c1c602c1c1032030f00c2840c01c5000303c55078110040402e0000340060350b500c0c030007180c071100400d040504001100c250648900c2050400c202c018010404160348104014480452583c642c01c0000c060 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 865137913 1250 865136663 865136687
    0x30c0d1406010f0e010b04061b051f090204051b0406031802060a08060f01260406020909070c0506011d010e0403030b190f090902010e13061e0801140f07030c 69
    0xa004000000c506001404009822031341084035500890341e0b01c3c03080480d076200318014000061261500d020b48a48481800043c040c860002c0b505840011200b02aa210034401481c3c4a5629081c0310811340c0b500340141380d00121101007a050300c0c6901d81e021580343c42140b2902c0149030325a10b101084054000d4410102500504484d559040c04a402007400c80110345051245011442c5907405510030090040d039069800b02000c86e090075800d0f52900e03498000c00860b031441d003c01080c150358403980c030750303e00659180d11001380041c0c42e03281ca80d0500b10142c00480b81c00643d55000c0700003010903050141100c45550428103a0f8890341000c401a1071100103141c1c00c2286d0820b012142c209840c840740c1280e0b4030400040125440740c213a20f003038455107000640040c0311085010352a00c1c01d03203507002c610368800000143c09560b4403113500031541c1d1440d064001c1d006020b410818001c00703004820030300d503140d03940c0c40b96803410320305400080402030800c004043da070309400c5604900030b5410680e1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 865139163 1250 865137913 865137953
    0x1803030f130c121401050403121a0607080c0f0615210703030801091d1005060612010803090405060d12050901090803040e0109140405061b1c0507030c0c02030c0d 71
    0x10396900c071054041c0c42003000c901180e4007944401d2a000c8584103106d10f6025540c556203580070804d84000d050040c200801c0018400300c1c2d03401c5c0d03865256540c81c0c020440148540a0300c2d03181c414111346141001c3c400341510500f60058001c1201c5251007550841c02000d04465035070400c0050302a044400400c5d49082d1928401c0c12004070901d5000050303d41250300510040c4110804080904506503900742031f4041130307100b14028001800103420950340414060a40c505181c0c050241101c546002c0e40181116000010380d1030190400e8052503a0062003940c0301c48400181e0398070009440c1c031002c541d40c10003001081040150f881204404001c11410f01200e07212a00c0d0252500040401e100310300d0742d28074203040b40d0300184040d0f0b00e2611407030300b1030003400302ca0360740c6547c0b68600780348000e515000703c0d0200729040b008280158280c4552444541c0000c10b441c0004000c0c0490380314041030001d11140d00040c00040c3d50004440c40c0d0340c101a84e16071400d4840b450001281840714101e051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 865140413 1250 865139163 865139183
    0xb030c1c0818060a0929070818030d030e100203010b07030e0f040c09142d04020f03010e0f0f060d06090f060c020a05011b0923090c0d051803030f13 65
    0x40c580d10014000944042c0032080c0701d83d0380200807506c00001140c10718901800180f00b0000840c0d041d0b0090501041c841c2d2111000003900c100003802c14003588910408640c0d00e101c3e82d4140c030420042d01c42c501c110180110310f0355062030f05107462030242240c0141000500107002c0c1e40c0340c071507800c1c444041d00050320500c0014000000907012054074003440c0050308003081441d03018600090010384640313140c1500c040703400b107000c400c81403080d121582c4d6402c540c08021801c521207040c00154003d0514100c490f0440c24030b074109134102d200c00f401201d0410404070030b2007c10f40e0703440c1d0400000d951080d000100b1070301c00d00c0c200c0310022149030b0242c01c2526046056107115004181400714510400c000c00101c01c48803801004d8074000890300001500f508000d1221103450991042c501c0c0c102030362080c3c5031070808000b9150b40411240302c102c400d404103030001c001d2810f0055030b400c43e040042e103511741c80700d01c04019600d000007407080f2107800507040400c40c1d42b0920a1402c00d810f130080c02040e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 865141663 1250 865140413 865140427
    0x5060d0506032d060f061c050c030307110910230f0907020705130e070302010e010c201206040f0602130e090114070c0c0501300b030c1c081806 63
    0x11411002d1020110383c5030107a000010424074020702c0311485000004c1240c074268112180e038074812484200c0c01c440500c95010350442950302000502607891040c0820820068010107001d842d90b4041d03c6501f100000000500a5180c5000380102c09000011035070090480500081d40b10b458960410341c104181c03c081c0034020b40d000c2819000c0d24029155043c11940b218010380c22511180301c0b9221030781010206000642c0b28580b10248107805151229031280346803240b42019400e06408481d010f41419550b4150500b03800da040242c200a002c2d0140e8034081d143c0b030f911540506001889640d0018101d00c109500401c240007820351003503001600c0c03514480c6d00d40200045c031401e008500300701c00020358480c450581c20318410ba0002c008402c0510700401954502500320090703210707510228040da4959540c1c0700f0180440c00151022640f003940505150811025410103401a586a02c0d201400c1070131011507001507a006100c00e07901c603010901003200d0004a4036480d80728000003108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 865142913 1250 865141663 865141723
    0x3090614060103060e010e15010c081803100207050303010e040f120201200306011211041a070c0812070807080d0501090f0e1b041d070f0303030b010905060d050603 72
    0x2081c4501c000380c030701300491500c6a40702401c1c02824824000c920b8040702c0010303007962181c03141140100040c140a0340e20b0701c0fa640d50140740c1d0803503c00100c1165041d5203071131084c941040518040306001008502c0d040903625095168881406043c08c8122418041001c1010105890100707640220710b1444442866000a000e045031008001d482910590341a0010071050200d80c01181c058440404403001d8104420141108240007803140006020000d030868014038210765618156540c16941e42c078514000b210004c09400070300350380d400390340c0b24480c1880820494807580d4120005a8537600ea6280090b41841800c810080c1c4034145000050404000d801c0070310030b244402001c2c0720080a2000c500d550b4503201a098107280b124188000789401d0582c007180c004410792540c003c0c3c20300700c00000d030320b400e0940c0c1c04a4081c001e01c010410034184e01d07202c3c4d00446042441d05840141c601030000d80305015042127006110369820104400e03039000c00000c0c1c01480500031070a1550514842 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 865144163 1250 865142913 865142951
    0x1107120f140615030102160b0a09080a0e12150c070c081002181f030e03040f2d14010f120c0f0e0a03020d08030403020f0109210509090a0507030906 65
    0x1c0f0301800e0160300540c1c0246410b0094504011618100c0d031011505a01e4400908030050104910030303070b40381c1e0600086256003005010001d40b544815003c03080c0d140a11200c1c00708500b000400e504441e00286100c0c0c0304a10454004200c0d0300030580b00d03940350520306400301d11030f80700c00c1c03191103071203043c0c0a071207056000360003e040709086030400510008240314810300d1943c03c0200b040400407070b003004180207600c5003000c00d0f0704208132820191100b10b42d2402c4a5a40c2183d051400c0ca0080d4400c405031101d12104180e0410030150162468007148144403000c0101d5217041c000301040c40c28026108d050070180035005260140080c0041a8004d0b040281c541c0c00880022074000b903031092400c1000301e050031a82d010f8010807204640707889051080c2c1016000f10110b010b0b00e01e90901241c0c090040c0d100c80e900501101845440e1004488407003003000141900f8407409205140544c0e0361603140703e90114ad1000301140966411b801200204031074100140480c0c90300040748140e07840409 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 865145413 1250 865144163 865144171
    0x121101210e0105070909022b0608030708040e0903120a1e1e0c05121603180309090b040b0303090120030f03040b07020c031015091415011107120f1406 66
    0x4c404120355200c491741000ea102d0888440c8504800342c0d42070240f501e2106584100c0000e12a001440b03032b84691401e03040d944034802c241c9002030003081c24000280790340c4005402c07800c900001c62400381c1c0d00c4a208000e85000304040c1d0301590700c01410708904401c940e20030303010384500d10401000d4440b094002402c44031030000ba11140c03030520038840c501e0080048880c087c044520701c49440d502c80318070308140c031200c0e01100304141e1945803860020000e0b180448010788280c64802d581c5040130600d0089a40c5a610544142c1c1428174070b0f01c80d80c502100711003e0000a19100000b240810b140f00c000c801241e220799140e110005aa102d2030b1250340c060742c021840b61311407590a8032442e01c00c0f40d07200001e94290b9031540152184011040701c6134400142580c00381000c94031a5a01d01d0644120344190148001c0003102908103c1d040c444104c415401e00e40900704190481345140003150b551100380100e40491b4000740e0000d0506c4412400e0f89a042d03031200c5021841e101071a622a00e425041d5 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 865146663 1250 865145413 865145417
    0x18020f0a03021c0b0d0b0c040b0408031e0f030112110616030e03150606130f090902040c020109111003141602191a0c0702030a05030a09121101210e010507 68
    0xe8114000411034018416580340c0100495008169921052804c0402510300d0901039800c100019028190801030401400720101640c0c0303824001440c10000a41c038507105101402c00c0048121112014040d03c0c15180d02003405400540b0a00c1c0204640292e200c0c0154009800314141c0320100a0030584030b41140320340c0c2c03205120f00d5007006040d680c030450080141c85c5229a4000350080c14120b024008284c01c00c003502440941d80e1000300400307045030f00404001d0b40c41d8072001c8154105070048204402c610320080240d4000c036151b003011602f51110403482180c42e0038100d814188690130006101200340140042c81c100190388a00c4903400082d0100507006008840c2e140c030042c001c031a100c0c145c05c8a08003401c0d202400790340751401c20003400d03548040320a001140150301d0820408000500c110700940e61031103155400f502561159011006418200c10003400040e40202403203282c070030070709010750400c0180c0c1d06c1250303803004456410182441c000804100302c1d81508901c0c003810140d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 865147913 1250 865146663 865146697
    0x150905060f030601030c030f02031606080420010903020103020c0703150504050c180703150e09010501180e0c040f02160830040b0c04230307090b090118020f0a0302 72
    0x70200345a1100d80900c80548203c22411040011581210706505c0d9184014190b070580c0960111a8001031041d401c940d00040d01802088204043c919039104c003000000d900325403c110b07004c00200060640d000003070415402098841c038890003000b400b0060b40c0d201040c0c200c01c180e08050303180140b20441e4251a2842110030360240b13414800200408124442040b4003166038058051b000b40c0404450300c156501b510000141102003107003102c0c001c100010010489515120b103100c800f44400e0704c09180d1a1406048565031031001409807110b42c410b403408680c12481c40b20070402401280300400c41800e89040e5034040040b140010301141d005810702c6064000480c00c00146c07100d1140554001142d0030000c01d021404c0e4605032076000540030700c2c60f4503090b00d900c50322551982c0010064854000002a080780d440c0900520000c1c0448940400884801c1c9001079007104040c030074030b01c44a6401e25162403107221a011501e111001074038050b559003100740024001c0d4003e111000c240b58803 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 865149163 1250 865147913 865147939
    0xe100c030902060406030e0a061113050f13090c17100c082202030a0204020a0903021230040308160519110f0112090c1a03090304090203070315090506 66
    0x307100302a180341d0090100c40c1000e0903c0300580003440650750b0b424040c8205801140000d40c1c1b23005648403032024031210382c1c0303d618000522200310060740101d4481c101d042410705044d03d4403d03d215080c030405c00042584038890611407001d141d40d401100320780560b03620301c4030382402c0081d0708518401c0c1060100846452040c0848503006d05607100800c0751218011240100c00d0b4003900c900c0b071400201a500f8007202540041c0032a80131016240104402c003000300203602d40340310b90091812111005d0100840b005548008905002030034000e1001058460480702403003405440155a00c24040d980d10466202c2d10902c0000e00c5204845500c0b0f4403000c20303d0400b0004030202003d0f0321080d032130b030486000000c2110350344081c000c0c0c60400075a00c5041c031030250300780600c2a9917030140d40740a41050402d10302480144c060030301207008203800c00038800040e0002049500304c400c000c20043e243c4e29100c204401608004100e00c000030f00042d00803c0244842d40014001c80341103441d0050411 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 865150413 1250 865149163 865149167
    0x45051b0a150801060c0203190606140402070b0601082a031b1305100e090109020c060714041401110105160219030806100e0d0c0501020d082412010e100c 67
    0x140340d41440000e10b10740010030140c4e02510500c00c1c0c651009042ea00d12074101000c60101d1901c0c400143c4000da203582040191500b4020304811a10b03055805610f07102054451004501c03000d072107541000710324000124036010381594058031118200600758461102c1c004008a90401d82c0c5800501e683d0701029441c1aa030a0704454050800f4072001120625050400c103020200e400780006000412041000b550349901185000e440c200308010307243e41d0074500d01351400e80001c0c119024012601c2e03410294101c0301301901d00f00c03407403085524500b4a900004a407040c007400015000c9600380b030203022100721038203040c1d1003402c00c5038200c4410581d0300700d00042c15502400d002e800701d0100e8010501c1030811801011960480341899481403089201240c00700c1c640c441c00791189902d000040c0704560741402406803030035151138006003508120762a180c031420440f80d810340d004481401581d5035100c100c003a620850303000f17008200034895640c100e61070707202d001041c1f0141890320050b868100c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 865151663 1250 865150413 865150439
    0xb0d0510060f1e1101060b18030d080a020d090206030405060403020c1906050309030c2a060f040902480607080606030a0b0d0c0945051b0a 61
    0x410b003503907040d4812156641d05140c20000300404410420341141c03036038540b942402864010501262407540c1d0350188070100c3c1038590040009031190700511140c220a50384083c1d85900300c6600000144c1e0351070382c05408c0700100000e0390b000350440e00200c20401400000b00f6400e1081d8001d0b02074a41c1d40398610200410b0301c181d01040d49601c00300003402d109840c4104050b40c0c2c015040c000b242e10381400ba81c0c1e424540b5100741349101103682c041c00e80141c854108110f10850310310580700c00b810413500010515031400b03180100c100b43c540c08514080b2400984500320150003444c6011410002c3d6014070081c21080c01c1011688948403450725900640f0002e00144140185d64880340991a1001040b002c3e50001d000c1d4040360b070300c2c0c0300914410f035208012148801c2c0700700089021545845d044000381d0f80803001b0000da1001006003807024108610288a9a003100404c2c40c64245011210190840c0c0300d250190542c03155440e0304600454401000090308000c071084002a42d8031341b2040884 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 865152913 1250 865151663 865151687
    0x3020f0f01080c1e03010b0304230a08070206070b010806091b03030a08071205070203180316062102131406191407151b0201022a01060b0d051006 64
    0x140801c0000342000308000090540c01c0c441c0740d56034421004d2280c4480294000780c01c241000e880000038002040699038003064203480d44032440c130ba1034100c084000c1d15030500b0100504038540006040003199030380021a0300a40d0302000080d015611181c410b0345e5601c040715841340512841c4c6888841c81c48102c0381ca024200010015850003d4945049802d180c000c0e000701c0500111400c002a00750650062611070b07003a40d4002c0d5160310301090f4401c1c9500c000802d66000c0c1e000b845041d41303a02040440c40051340d41324203142004c800b4007208040c600c1940d40c1614882440803451801c000c40541c058012505103800001c40401004108801e600c110f800344801c0e044444022140b03140202c210003074006000045034102111902c849031b05200ea401a0401e180c2e40d100d0704880c18121080000c40e00140744021400c110304007045c0e00507607140c00f0000c42205000580140d40c030708250040341c050103240c4501a1500d14a00d03043c1c001d00801e640007841000f0300140440c905104213264401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 865154163 1250 865152913 865152917
    0x360602070b0906180d0f030f0801120201021b010908030706050a05010b0f040e07030f06030b1f0b0a0809070312051213080715140106180b040b091201090b07050403020f0f01 76
    0x9004e0078a114000551008100f441e0000d060100c60000b08580046524150b0300030b0b00e03282031040098000a29141e0160442401802e2440e880c00151341d001414034000a042068440c82c2c841c03040060347c1024107030780a20464400040e10008001c0183c1195000c2c045030042484180d80300c140c0b41c2c00da0300079007425130541c035001c2c0001c004003c8600a0140c00c403045080c000303012424801e05c841654519041920180301c2d01041c4000b07a502003180300c0310324141803241403096091020080e114070409c0103003010803089101152010800344040d000a50380811942650f2110020260085e00121401350711058424001203040004101240031154420411854208241c0d00d4512600380c0a03411140c00e5990081c1c0170b00882e28423041c0d4003800c1d19032917a10204c0c810b41418948081d040e00000ca50040600041000c0c101402c26100d000c0700c00c80701d084010040940040c010028104090104110343c4148650310ba000300c02071040e03e0094520780010a102020301000e0045d80701c0d0030780 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 865155413 1250 865154163 865154167
    0x11e05100203071e06020706050403020c0f0a06030b03190302070503070f050108041707050a05072c0609040201110706030b010e062a030c01051501270303360602070b0906 75
    0x8000344441001c41c09124540103c04000313600350720341d4000c0b40c01c1036078100c4110b40e4030300901c0245a010807a20350354a608513405000d042c0b0410216024000f90b22400d41815141c1003840d03040d075410b005c9590845001c0e030214210101c0c0d0b060080d40d8607164031919009000741d48c00800e0b0307001445004800e4880685404005071242e6540c0000c0120313084502100000c01c0c440c02e0002003080c000c6c01500f0b03008000421109042c54007072580351240950340138081c1d199007003e211a40c1750503202a4401c03000c460b07404480e5034a00042c4c0301c48902200c9010b25016645001c030b0b020750590300c012115003080e40c4043c01034492505003e51791282d0b40b060310750340c182c0115401a10415030390143c031141c030320342c26a070900321404101802d448050f0f5103000940920341783c0d448039582c4000c8002d024a101c58800c0034007444803440d441e40506030f02000e010003a485039030b040f14445003010034440c003460750202100420b041c132004008440c0350291900600904d540041d02121400c103441550100900c118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 865156663 1250 865155413 865155427
    0x130e1504260a050d02091e01020606040b1503090307020604030f0b0604050c091905040606092409090b060702091815160318060204061116060f03050403090b03011e05100203 76
    0x2d070f1141c2001c101003001c1078082181108a03200c8240110700351794284030003a40401c4000c00607080440092040c0c0c0079514040340713100340c1d9962504d403018103441c40081507500e4859041c1641076200c0c21a01a4000d500050700000b00142524105440c0340905407000d51604c07140100015102c054a20202404003413240103143e01d00400a22100c0320034280105843e80e4071004a002e541c0c66610003030110f40042d07400c01c175070300e000065a807400da64100704030007072203030880080c10001060240d81d1180b40c1e00d4061185c41c2c3ca81600710340c2515002004041c29103402100d1104c0000d0802822382c1d0360145000d0143c10743c4002039020b004155144110717070f80c0101408110000d244210080001c001030484a6001c520984001e0003d07120517507c603050a017801e550540713841403680e2044e03140f015041c030410103568800e145004040300c034a400300742d64803582011162070031030b03420078480030400100016400b5400da60240030007983d5204448103e40e20810450242e69a4080a0140e0000c118103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 865157913 1250 865156663 865156667
    0x30d050a050f0708282702010819060320120109031d06040f060201240e04080313020301110a03180b040f0512070602090108150a05130e1504260a 64
    0x5030b502a140c07202050050706424010700d08500115080714805955450201e1b40d20345090a1010086050319038642d400600d5000130180c941c000c0144c8820031890b01800c5008207280c1203500110341010740580000f201203441c11a000341d030400280700d10000d95105110383d1060040d0610b403501529580e40103810402c0c0c0f140600310b9600310300e51042c4204000300798044600c08942c080d188650000490b130f81c603c900200300a0002c658a81e04a0440c0d50400541c11a100c059602c40c1c0c0c00212380d40c42c1e072258071907002900d19540000b9499400c0c400b010b00843c41c044040c0803241c2c00d50350180038141500c07180d46c0341c01401c070002604c203865103000100030030300c1ca040307084407144540100d815000000310001c0c000d0300103400480c1d000d9000508489150780c002030180d0444d100c00308103080500d400002501805052144c14051040c4c804031601305240d0b54030444102c0d4040050301c51a04c010b5000000054003103908235100d1210440220240c44070650500e02540d40a0685240041c42d03101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 865159163 1250 865157913 865157927
    0xf090f060303160c031e05060c0a0504050d03080a0f0c2003120f010e3315070c080106080706050a0e0a050604060f0320071b03060e030d050a050f07 65
    0x381640500c070810206111040882c0194805409083c2d141109801c41c0341c42d4411504003940c20f00520100f0401074046900400c020b030f0400d000015147d0340b02001d8001365017034002c0e944400d80c400002c0390b0000606400c5030449120706500c4c8030800201301c48642290441d2906002d0b20000745896180e00480d00d91200d050301c00f4a000c800b124105149402242ca14900459400c4000d0459000400454140c004016000400c1c5030b0303641101c3c12208114003e901c0c29203403c1208112000040c141a03d0b1101340c02c8054100c1c425040d950352131070607c0c041003641841004015842c1140010390050080740c240b098030901c0e581e6a1820f8081282113443c0c0d5841c050f00d0358400f084c0340c0005001c0d61848003c200034042520b400a604100c00406000c50b0426206040361411100d1800041240d050442d4200f55000710440380342c1c0f05a45031103003a4806600300a02051038001014540d072000009800034540b41001440ba9a42e081102002d446003500e4001045403030401098510380540c01c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 865160413 1250 865159163 865159171
    0x70609020a1e060e0102010501030b0c0a110118020a0e07020d050c0f10140f010f171002040803070b07170105090703090b0a02041401020c03030a0e3601050f090f 71
    0x102804003191039860b0481d010200e41c1240c40c042848010030010349801000d8039110800c2400204080d41c51611440c000e2000180400741c68080010b10001c014010988400c2c640e08020080200d40c0010340702e0b101301489901c00ba40b00303003038135038002485041580181d480348255074050001c014a01400352056006546041c1c218042c42c001c0c843c1600b801c012481c019240c20b840840d096a000c01c85242418000d480c0444443c01c000c018800303114201031210440312448040045141c190b403c03e418602d0541601040a000203800180301c80c000002d00f103014060490741c1e050751900c00302030301d00380c03520340900c0300c2036450100400851410300c40281e407000d49402d004c45e90040c56900e091030100100d840001e8698003141c180320010704864406074102c000c2c0001d121250090001030340c2d0b401110041b1b0204428808808003076214100c0d800b80100b00f50010a001e0044444519114405407030f41e6800e903102e0070000034640c9428442c1c0300892070003800b81100ea0300d80790440c503900c0000074 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 865161663 1250 865160413 865160419
    0xa210e300a0b0f041e020d1401180503031024051b0d35040b040f0c08010204090506090717090102130905220209011e050901090b04061a07060902 64
    0x2001c0400704501000803841003044148092040ca481d18190f0212012120384141030307101d1550b03003001a15802c50000c0d03455000001b1a05240086030760601401042c00c14000c0c902d0f840805508001000015500070180e0030340310f0150948580090109441030444490742c1c84056076803809250245008224030300368000c0c0200ca04200d004028a031a45241c40c0341c0004030221406401e60b041c6950fa200001d030300240302c2c03080500c603805c40784040c500540080c01031010340010408001c0080034109049034801d000e0035109549004082c000e4009200304040c007801d20b800a1440d1901c01c048520030390349911045280c64a04452544010004140d4600c3d90760070404030f042009801541402071801d15404103991400102030110000048440c4000c1c85110700c010340142e89091a0606540710500407000ca6411408400c01c000d02c0c0e98002600484c1d403e0000c5001026070f0030a4001c114151001c2c042c00e59150414951145580d01e040c91003201400082c001400caa002090041c0c001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 865162913 1250 865161663 865161673
    0x506240c07090606020d140310030b060303070c030b0a140c0a1808071401030b060a090b2b0c030e0609070b0a0507020a0b040608010b030f04030e01020a210e30 70
    0x103060028202c4600f60026000f5030306c943c804100e210390240240e1b0550040e1102c56046051034000920041450301004003100031180c00601151010000d84811301d40200e4a901041d60300c3c10000c03500c074010340c0c1c089100b509110341c0c44454040c8030f10382402100d141141900d8050548070840301007515104200340c49110350400a1005070801400026088810307244400312505c200241c100e68501d407080e80203900c1488541c040300d4116642ca42103803050503902e507907a001d400d50003080c00c2c0a00306000411078490283d074002100d40c0e2100d4030743c1c01a500c003000080c1d0440400c40d07848000701c462400c950300c00721080c041103542c00043d06ca014454200705040081550006284031242d401066118a0214040100680c000503540c0144a80d407103191650400350f2102c004140020009400e014001070910741320791080203074008258005040c81c0e10031080c2d5164184c944800d01c14a0005105641c41c681685030409074074490162600d500c541c41d55501c1e15950084800000da40b0f02c0340a8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 865164163 1250 865162913 865162919
    0xf010f1d07020a1a16030614190b03100510232a06090c060a020c09070507080d0b0a06050a0909090c1505030a0c0903050606040f0204120c090506240c07 67
    0x15500400441105042c6041d603861704500003c03030718640703a204000301420300d04208001c0e20400d4045d003000300151001741d803c50381c0180100c03021001c2c2c3e011503440b400000800c18200400354102c0300751002216181c64a4180c0390003117455084807c0c1c00441040c0d0700e8050405044400c00030100076030214008a030700d00c0340d0003583c0381d0040d83d070100c030750380341c01141c01c00c0304464040c0058003c0200c01c0f03940909040b50804000e56442480d410302d40a15242c00105007036a001d282580c40c1581e000e8004d5a075403000048120162003412080c1d401030a410b90040340941c0100d043e2415081542d4810b030707201d46419290b038040c3c442900c09036000940c81c0c0c40444c503281e4403010510400340d203481d025507a00b0507400762003c940c10400d400d000c01ca800c00b0140005500421100e81255040707402241019151409034000c0c0b259900140000c40c2050b001820800072844900c100c0d5040c40042140317580f01d00c14045544520010180856080c4d0000c44400200d900500401101c0000326520151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 865165413 1250 865164163 865164173
    0x1c0e03040602030c0706090803070303091e050c100801052d120d080108030403031422090e100506090112060902030102030f06130903021002070303090c030b0f010f1d07020a 76
    0x200c103411550068100140307100e10a402000510000c1c032052404040703072413900364003035181d000304080102010b413100e000c2424404400e8400c444a07110701a2030081402d0f915200d83c0e9003c440c0c0c5004d000c0e009040c440c04000f809180414100c800c043d00c81219031401c420124455002c038200441c000414007401c0f0a00e445002e02c440000c1c0c001401000c18241862002c0d0a503907059010f40b0041e0300410040c0006076106040702100001416a11340b034003250740b949004030950390205080403a1111002848da4065000701d01004880410355181801900c07191003600c030200c0c0e00c541c20804460040184070008800042498001d030700c00601040c4503130019003640e00c10740b5000002400201401540d1034001ca0b4407410701503109041000649958029440e0740c0d103100a240d442d41d001c20004d003454000d80220a98551090038280e14649a00d001c7c00c4040c0d080d20021008500e0000105003100d010070802d0a841403540901200c0b1000d02905001c55002402c00007140101c03001313940054 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 865166663 1250 865165413 865165417
    0x10515010f1b1a090a1505090f1f06090b0d030e032509140f011401091a040e09030703090312030e03032403031806030903070c0b070213111c0e03 64
    0x600ca41c3d03240103549448400c2c41d031800740181005620b600140b9440d4005404130b100028160ba061030007003466602c50b801e031402c1c054241c0480b5041d000308103a4001c0d00200150a1458101141d8100041915100b81c44111200384960940103a40c0210440209000d00d4646c3e001440c020221908851401020503079034800d14007551005186000078030102485009031201082111028009442c0c90710689420356410301c1000110204010100318a03440b039017000d4090004480240e000e0700c032039130050702a98081d11030811001341c01d4000c02c00c1800c1c00700c111403640b9050707510040d4007400d50300c81041081c0ba0b0028001415500d0714058400d10b0144080d40c0308002c2d000b140b03080f403a0b03c00c0b200e43e510b0308030790202c61098000f0000350b5030805170000c2400b0002005d0b1040d9880e0f9441c0c203543c51862081c5036024044c0001e8060014031f040d05070004048040c829502c0034090b460381c000b60001e070742140904118050b8240250046402c40000c09429440c100300003140030784e0b907441094115 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 865167913 1250 865166663 865166717
    0x1305030a210e0d11010e03190605011406040306020a0504091d1209060d0218090f0115030c05180112020408070e0c0306060301120602190917010515010f 67
    0x34040105101901c8404494140a42510303820701c64801c5401e0400910301c100400b800405407121901c86081350b0f445488209090407000e0104e80045a020b400c01900e020000c034120f6a481c104000451481c102900e010380c100380192050303040034216590800030f908070070b4414040201c1804000f0300341ca820b02400a682000408003900d60350714540c00c909041d041c0002c2c1007904020080c500c11034580004a0f80200c0c8410b40c01a00c1742460100300309074449000d4010f6100c80c0c0c0f07006001c08038411001c150b04035050b645111440c22060714045e4260313040d1306000008100d0078054909a60b050490702001d140051412070454000c41c2c004a0491700950080080c5500145050000e400001e900707640041d2440c014034254074090380028114401406440400516016001c041114640554680690540e10710700a044544001045820b4600ca014030f41b40b02c40b40c140c90418418401c44d4001d20240c1c164a24030006200103541c0e40c580003504c8010040c000600e4280c5940c4401c682c000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 865169163 1250 865167913 865167923
    0x90a150909060b1e12100905010b1c0c0501030e031c02030a0b01031e090c1505071104090201020d0e22060512150708040809210106150e04021305030a 66
    0xa9890364100302040f60034041c2040d004940d581c3c2184401008109820482c410440f03203140d07103c168002c543d042c81e025891140c0000d0400045a04000c1d06402013803039580c0c01d0740d84a011403e42000e90141d10720550340074040846000702806954440e800c807240e416641c0b000c4a20700302e82c02403410b80880100d19031448840c3d012050100e07040300c4e030003240e07413000003481c01b0700841c1340c10411180101407000c50a503a1550321405141008a80d1520030014001e508000c000c103c0b07000c1014003658005c410455000c50420000c904034540351040e04882034060b80186160901e07900c064400c0a10182240da0240d150211f0813080080c0c51249101080910b2001c00c2d0b00e89000f051040d03c0103003214008203508940040701c0324845154049134410910700d8111001c1d100e1741040c50143c0310781445184c200d1000241400e004141a68028034180c54000822031150380340c60403042d01e802020000002010001c19420b40d00e000d401901d80d01a91445803020640d98400082c50a8142030013264 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 865170413 1250 865169163 865169171
    0xf12010806010803040621060b16050706030e0c0d0615060201060e010e0f0705030c310816050607060b09041a01081204060f02120a0c1403090f090a1509 67
    0x4000c08040c00030500601c1c1001c01181402d04110002d04828040034007105150404050010705800303507080b95000b003882001e041d54468402c2c02c0c0382d503158215030060b070310791140810020700c00d4031034030412901224200c003400b0040e84540c10001950442001a6041c1c0d0b02d074440c16005510b0940d0b0040100060303000014150700d0520345001c0402c059110721a408540410031400908038a4a61350220171740c0b5116950f130f81c03282d215a00701d0140c01241c1c00b03103580f498143c0c07080c0300e2860070518080035814003c02040e0340ea4254079030b403100c4014481c0d580303030b120450400c12070400002500103944900d10104142e40310310003040c1c01e624101c0b0180c0d00000d040340c0310b42d030134482c0ca24842e0240c02050003070a4140000b90400d1007620551141404000c1040ca0f4244864030a2201e00d20280800d026a0340e51017100743c00400c0080800c00c20340741310041000003840035030000203d8801040190007020300f030783e0076010003009406c014100700109403104020307030220380140d55840190104c05800a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 865171663 1250 865170413 865170419
    0x3130b0f0403051902030c01020a121d07060f090314010c20060f0a14091e0a1509050304090c120501060c050a06020c01020c0109060606230415050f1201 67
    0x550124006040510103404080900020a90040440d0000071510054440652403184100d2551280c4132095406520200d042c1c814150310101c100b1512150000070301010001e2415580d40c40c8a0701017440d2180c0c80703290100102406019844120180c40c1008181c8581d40d40343c00300c2c030700500808034403165034400810960171f07004082c1e6000703a4080308540402030810030451340c0d40c56015010200d0070524000049001c0340c103030480d01d03210304000756005860808800c015550300000d00206a54501012440074081d03000621000c0c96800a2800c0010031009205400424030540251040d000400c00881c00c003000e170241e441d85d400c0c80c0c2e03a407200ea00c01c80c2000c441101c0e81230700074000b040800902e80c170100d00b00040400400f078200d140181d482007088020f600922031118850700c207508202500082c8486544806c0031110f6503124803900d54221082031910300c8c60500030f0140c80c00c0500c0188170701300e243c0d0707003500003409582012031400310180103100b4140c000c2c4a080201e041004014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 865172913 1250 865171663 865171673
    0xe100c090608010f061218050a0201110120070305130b120105090c0d0b030c040c0206060907050a0914030a0f151a03032203120804260403030305090a06020313 70
    0xc80052040349032281070382d4103022a800d00c0c00c440b48565420013541c0014844010082e41c020b0614013032803010300001404070705d8407544880074810103902240c0a80300b0400d141406024a4650b000d4030301655a07207502d01c2080060350b1b0403504040e800c10001f8010f40d418808030610001c06005d45044454580c169a80210b401d00c105030041801041000144440190000d0647d441c8104c1d021000c81d08031a0180820300c0c01110f02c45d182c1e8010304001f46106410340208029002e200c040d030b014070184d503441c0d006403400d101d01010302d40000c0c2d000800f003150361802c440c5190111401030039101161186e480e2400f015100d80e105440d000e0b02410b40c24800401480b0b00000c0b03040c506d43c00d1020b01d8110700069140e00a030300032141c03100f0060545002c40b00d018200880a16842000700c181d2146600000300900e00854048500900701031403210101c5030f0107103c1108a440660f075078502400c0d81e404501800019000040d00e02c00e20964000288150010b10702c07807d2001070074640c0d02814200 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 865174163 1250 865172913 865172927
    0x1b070509271209010e18011206140709030b04030306030b0c18040e19060b040504050a0b09011107141c0f12020f030408070203210a171303080a0e100c 66
    0x4000030650107814403030b00d6803410400750f40700b240b03090804001041110021565080c042c0b5650a5900700d42070010942020308004a4080d034010502007006416090f160070100100742c440d034000c206001001c00014a090307a007564050b200e0710740801c4d0582d80b5582c40a4001e8262403a610ba4940818198074a0030600008880175600711410b005150030203517003984502c4010702003100c0c10202503084080c06986e41200c1c40c00c840180040205140c40d00f0020344660201e00d089411090700e0011460340a814004d050355000350081c140d14012081e51031070890180c0740d21420150045a0494110800c82d020004449482c2d854506001c00040c40c0100b1201552010380b501c0ba1041c00724054200004090300c1e445a804060959900300c2400040d01d003110318911800032110102518424070808400341840e1501611124140449411650440d160480b003407030380200c0140004011a20810402e9001130300c101000072030350400591941031166984600b410151036031807808001d45e104c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 865175413 1250 865174163 865174231
    0x60d14041101030c08180106030f050a06061a0f070303060914010501081006091e03050304061805090103020d110a0f090504150506062706040806060102011a061b070509 74
    0x1800700807903da64007000d0030504010304807098201c0c1c5c10b1b5184250010951228000c1c0d500451110100c541c0c2c1e1030000c0c0d654016001c101c40c41400c01100040301ca00c41140900e880c2d40c0c2918031810710103805802a52a000702000303804054941c00002034100e0240301e1540c601003da03100d220340c1d41c101800500300d400054103030664500d21050400a1a80c01074691043e00c00f44003c4034039031000103445a0a84c9440e4102610324000080c0000717203290000301c00643c074031500036802103a03aa03403030801c0f00d40102444003a412442c40002207002840d80c02003508940703c02042240c2c511303100e1002e2071103400c0d02c5c0c0102c00907555580502052201d42c40307200340000321032601400a0701d041000718509001d045180d0808074440c44010104003081d0011500002001d000075482c9c030b0b0740c0c02e0355aa4521058801c503015500c0c00c20500b04010885d90001c0400f41c029003240d20b4071a140310411181c40c0c21503014a1240150100420f25a0740e41c490340d030064500f09034040b42c260035180711505400c2c4000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 865176663 1250 865175413 865175417
    0x6030f0403140c0a03080901060e010e0403020d170f06030a080a03020c0c1c4706030d0e0613030209040308091e0d0302030901180c08070b070b06040b060d14041101 72
    0x440043c80d484000501c0b0b0b02c0407036062500079942c0e00c840e0342e02409040c1c1c40c0c206e68242c0c3c074010f00104481004120071340c41107000e0307400c80e91001040f02094802d654052454403001c0c850310300107034048030175094031500090050122401d0380d0943e210400c040e0003410035100040c0d00080c0180500b4400c000e940c02040c01203907040c20451007101c8140c50241303292801444850700801e1303400110201c1c0800200407174042d420005404d903082c0d0315424400c803e692140c8081030000426100e05000502417400c0d4001d48822541c5003e03170003048880d070024100e048a40c88540c0000c001a1118259035001c0c501c01d4071030304420705129050a040000001e651070541548402c4020803840c00644150704610310306005a0b641ca41034105409041120b40742219009041140c50800441c0c0004008640d410019a8a541e071104c20f0592944507a081c0940010815004501c8a24060b80145420700c0f0041c022840c040701011080c00b80c608101c00c40140810610070403060044100060000309424 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 865177913 1250 865176663 865176667
    0x3090906080609030a0845030909010504112b1808030a050402040603230f030906220314010207170c150711030c061902070b010306020a030b06030f040314 68
    0x158035a513881c0680d0300c41004002c5e4582c00b10381c00c010b0a203d01010034104580b290441c40480140d0064003019291004004811400b980140b80700030003641c030403582c02050000c0c56440e00301000080c100d0740c000c98030710b400300b00708d0714081c408010100b110181c4203000140311320250340e8210b070440b1140350200c848601135042c003d00103004401103a6000d40190703000141600e46002140007020103400041c00003505601c281ea034422110b0307451403403100c00022940c91008000f020b41c0c43c1e0040f604401c1d0809028460024501c41c01c80c405d009904598003614a510b60b207490700600440304281488841c0d40c00200d000074401016945103010a12000300c0307140101c0e658202c0ea98040d000d0094101d90389910201c1d00481c41401c101154402e98800c0325103810b802c559035915407406981e01d8030511399041e140881c0c0090380c000e90b015650010051151790380f964030744001030350290540700100356803010040021381e2000e002d07601441920151810368070709850017902c0d401c5e0314141286202c5003 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 865179163 1250 865177913 865177921
    0x7020102030d0f020f040b0c101a09181615031a0f1302130806010e060907390302150103053c0c0a0e0405030a030c0e0d030909060806 59
    0x455500044203480083d40100302e50910b40240501c0b000e100001130002000940d014002000d00340e02c0e54808144c80350384030310381ca000b42107429100005150f015800030b084100e2800e01407040c0d00c6152601e01c11020b4442030810340c18820000407102078200560401d014141e0150882840b400c0207080401c24a42100b00700d00d0000300038258984913101c0440c0d03011240d11503d480c4083c003144102c00350349403141d603102c00000c2c0d0241e0040d00e05c0c0e44600c0d000098050046030006001d020040c1001449489040084a40d08000d4a4200d45214245565560b610b860071103041480007107607039100f0f54031180c5402401c0c6201d144030002948072600051010a20110702d5541182d0306403044144c00c00b5a0048a040712029803a14481c2c080354850410000008159410a000e08542c100082900c0d90316003000042c0c00d030b0380549150b10900c010880b95001e0761000c5945c851504000e11803074000c80020300c601245d100110f0000e0441c200c20440f90390540113220192180340050280d03490 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 865180413 1250 865179163 865179167
    0x1208011d0c030c07051f061401020a0f030f2312010806190b040908121b03130b10090903030c080112050604060b120f010506011403011d0603120a09080c010302070201 73
    0x405000200c200e038000516130100703c010840c0840c2038001049800d03621945182e450018060380c410004294072114a86074203610104501703009a81c414540528182151411104180700000301028403162a1760008001503078404d013140c0d040c60a22880d502c1404200c1c1c40c003001c0c4103a008002d0744d841581400303026807621070104030900f103003440010395114070030011700030700342400c805001e0820009640006500d4400b4051042d0700402e03050a421500606043c0184001c849452442d074580c8840d000107031007010419000520041c5403112551103449100444071044822400b00341c0e2214044905500149424010048201c0501a82c07825845407a265800100014111550387c0380700341d4603070b8a6200040f032541410045600407840c081c0407600a007415146039003c0750300d00848240d440790480c112810703249410350341c1080b20302d1064051380014000d0146075040c0a003a89011010643c080030f4940c10182d5598403060794940345115041c07460400c086c40c1014010400140540d0b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 865181663 1250 865180413 865180417
    0x31b0a05040e0c190504110c0609060f0f04050304170303060f0906130b0a080d1d0906060403060504140f0d1704110d03030b030d0c030e03070e070e030a1208011d0c 72
    0x80c0c01a2044a168241304e14000c46044554100d6a481803401c242040003444450251050907001c100f150055101c113909143c0d070743c00803117007460900045000184401d41e8024101e030050300c290203e070304041d260448400142004202481e580e8004000c106461038103081c0d049081d40c0a94600403e41802408144103142082c85511210340310000350386680c6603481004004d0080700c0075684c00d05c2e040704000f00078003c0c00080f042140203415851800d454018101409500000c01c498134045c035659907403001c4d210050080d1082031240180e001441c0c4188024543d01d80a0780107001110100e5101924003455402d9504e04107a403581040f00081840e460302c0366009044425100210705454110050070010490b681c041c015000112140b64100d100921640c0c42038652110081c2030303c092550fa008580b103200390707a0042c207001c600b44500030503224070745003400390542d4070340c1142c0d0301e866a160746a07d01140000710303614010002c440f100c0c00c14006e076004007418203000d41083e00e1608401c2c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 865182913 1250 865181663 865181683
    0xa0506190b010e13022b06060f0504050a0501030b01031e05010513050f010e06150d02030a05150916050d02040f08011b02070e190e0109050111040302030a0609020d02031b0a05040e 79
    0x1356900040c444014201031003440d0100100020030110750150010f0600074002c540300350070206080c0001503862030f0280c030560302a5400a48001409403801004402805207800700c40d041c15510002802411032480440c846282d0215011429502d4007060110302d101d8442c4010601b8602030900800c82c80148c68141128418150104562030b4440040d0040b05507400d0420307011030004a400c0908015009180b240d84c60f00d40401241d9201d0302c0c800c910b41001150b072a0702c10361210005940a108840f026206002840c000b802d010001c501c41e03040303038403a810000c0b0041074920300f003080e29402d00400c600085140b04001c0301c0c5002c1c1402030b40d44c003118040c00340c40103640380c0050b02403019443c503100710000072441407140100749815035000f400c8192051300c441d400d0048002c0559010070440d012654050f00030582429117464441c01008649022a8400c601039140c0c000360364200440c81e4500c0d02c00c01542465000d00040004075606548407900036030504103000b82119020600e0010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 865184163 1250 865182913 865182949
    0x30e0102071505070f050c030a03090504060506030412111609060905152d0607030f0e0910121a0705030a0e0606010e01030f1d0c01020709061a07050a0506190b010e 72
    0x6980018901b0300e080458034a84250184560740e4000249980040320303004807101980d040022984030024040e0a2204032809400700500c4113200194a00c03a00b00741615400c600107031080300e50800c5401080d4249035000008294079190305000c801c4c031610425070401c4000d140c24a00c20404404250b081c6a0420704658140c41e07111480d00d41081c0360320007100003a00428003585c0340210702d030280c03c003036042e00e0010002e40300841d030540f141400750049010704031560300398518501e0060701c0111107018804c201c4513545241c5a00c3e90840c59112161b001d038105842d41600d0f860315100140484003c0c640e04122980988107003c3d040c0d8000101d1a0002002c0c603010400807a07540e07210000e030001422a944890560450386200c0f05c010039031610300c3c0c100340d094805c1c080e40c45403c0c41c25610203020361080090540130342040a10204010980c080c41202507a01984003900d54a0401000315014070450003184884003c03d0604e100302d24004009080455071078022a01160042e194401c82d034007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 865185413 1250 865184163 865184183
    0x5070b0a021e0a050f040e0403020c120c1903060e0715090501050a120902032d0102070c0521060c04032f010806030a060e0c0406050a140603150409030e010207150507 73
    0xd01445003003264000c00010b0455aa80c559a00f64410034947c125000d50060003120040c1c4144e00d0f01d03c4a22880f0101d0a00600c1b51000307204c10080044c02c0600e44a001d00d1003201c1c0000010403c0c0104820040d014000d014000d00d003101c00660300143c400b60104201102506100e0350380c201017940c011038124a4100707251403024070441d00601200c4806941403003030100301140c400c2d401c10054800240c4400f421070f100214400c0500340d0056240080a100e0034074028402424941211030443e2040c3d80e43c86c24100750001001e007020810384d00140da000000500b80301b13002a00080da04c0c4403040324503c20345191003040010b03807240d07042d0700103041084640c04076030595000c001d401111a003020b41040390f40c1d15070741034030764a12408a520303020341d060480c0060b1900c3d05521140c1160b001400100b80c0d619181e041251030b5100410000030b440506041881a440c1c0c4d100e11100c8900c2a1103124a4509440000e03207482c0c800e511080e209a0b0150400112551100941d070030710707600140e007807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 865186663 1250 865185413 865185427
    0x100302120325030212180d1103010b0402070506011a0f0304030801050a12030e12030417060402120d020604030c0c0e0c072d1e0605100e010b0915180a0605070b0a021e 73
    0xf46400074143c0a961f841072160000201380038404149510207082203000f00001403850081c00141c0c00350640c0035040c0d410141c0104841200940f01900c01c1c031905106500d0600400d901c10007940082c0c40a42c0000d16490040c040f030306040015201800d409604078102542603a8001c1460250042940c01403440c0b0960f400c0b504c0e410002d0360f000d48025000c4500340c50f500811941e6030704084074168804e02da1710004001000003c682d0950210a60340604100c5d915900d003034501407443c44080f95001c1c8a100c0000381002003d48042c0940c0341482510395801c0c5504011910ba980d146100310788800013061003c242c03403925211940c0950000080c03200101c0200402d80d00700f048180600000c0c00c00040006003000d8400800950b410040756004503600c0c3d0703400f4000c0e40070300c2501980085004102c1d0f540c052000010348040c2200d10800c590009482021600c400d005600c1403020030706c040740c1e1a080110481c582c0f0b5014800b04411802c01030720140300d004000021114a04201002404d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 865187913 1250 865186663 865186687
    0xc0312010929030f100b030c04150e1302090f01150f1e0201020c10020c1e100e1f02181c170c010606020a030e0f0f0603100302120325030212 62
    0x15516507544400c1c1d6002e17442d40225440641a80d85140d03100f80034601240f001440e00348130340c0324070010ba040758001540c180724002000750f0001d0000e0001079107080039000143c0e50f42c8001840387c06102440c90881d403500c41d002c800030706900c1e900401c0c003460100030404c0a90061585d1a003031409c442160215041c0d12061703009124034800c000305405200c24001c1614115002400b10710241d07411105c0401020440c14500d5065290b8000c894000303100105024044d41c100c2c407105541c03442070737911004a0342d03142c240030003858000070140380d000710f003035910658034200c00c1d442c4140503a520450002540807001c00d101d141c2030001c10800760403000c00943d0980d1000d0b904101001c0e4001c21509844190180d41c3d01031043c801c500103800d003c2000304608291400c2e0b040108060004400309980c24200710050700b00510400c40504241b10000142e5503d88051400484400185585218070545017924107101e0014282c0d5003200c18885c80004c0d4000303401c1d45842040140135031544802c0340c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 865189163 1250 865187913 865187923
    0x200d120e03030114010f0203040303020c0409060b0402030f0103150902090a02030a061508060a06050903031603050d150306050f01030b0a0f0b060d1d240603030f0c031201092903 78
    0x14841444040004a100c260500001c020307404c0980b50211201c0110000300e9480c8503a01009006030026401a04103051940000c41409c5c07181c0408120180030340082030032600b040b02c0c61038655510600400c00c6c022a9688000c2c1a00080b20901580038190040b0360780c000c000d003007210070640c00000a1021801a88000b000e00100486d10380c401c7c01e07040d4002e06c512000c1e90014880e9617503500018400e40160101d80340e400001d03000c0c1d400c09540a48551521040302c2c015428002c0801c0104800040b0384078111003030442c8606a08030314190305100d822a00020200c50b0344058075001070001c074812558007036000b00042c00218800d0040d030013174009007601c43c8a01c1e400040109014014490a800c210038913100480d41c04403158580040e90b0303807110f00100c6040358600c20458103c1150504215951160001e03044910300400c0e4041c00107a0f074019410a49940c00104844180100d0079031451f00402d01c8840502c07030404541050140c461480320380001ca1040d00e0718210850703c0c203100c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 865190413 1250 865189163 865189181
    0xc030e031e1b0102070b01080c1c240c02100e030c12180402040e090609070506040501360e070c0221010b03060f10061b11010c05010603050c01200d12 66
    0x402552601d00501e000c1201070001c4c0598101e6008103860100240ac1c101c1080c0100300783c0001c2205880f1668403001510b4502c2c580042c1d5101c1000b10080100401b03000c0d19103100210343c01007a1100114440e58204c0d0904d1000c00c0282d0400c00c080c41345c00380e00050008103441800800c1d9076840031410100c802a00c410780440c0c00c03a001243c00502156010034082c0302d07441344416242d031a0345444566440c2c2c003141c041c166000343c0c140700900803544504c2d40300200c00c4900445100840030400010600d160b460410040350324100014460407a40c0c7e203415421804a050401a003c6d03e50300180f1040d4500d068a83c02004104217511002001d41200b9441d0301d010303007078503054246088442c0380e403882100c84003180e111003080003502c28460000c40c1c6001590009001f034010309640c8094a03021901c005604018100700c01c0b03c045982803146c0360041d4824001002e460b25844001351105541150210780f40520030541580d1803c04030b000c207a10031301d0b81b074100c0d418040c102114008020b180 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 865191663 1250 865190413 865190467
    0x7020f06242101060306050c0304150f060302300708070303030b0a03022d151c111908071b0b09011d01050105120606130903021f0c030e031e 62
    0x262002c0c1c190181076001e501600d00038101800140d80b89465550070784002e4400512a41074100f000855aa007a40050907101988001256080d50703070b0000b0705c140300c0030075070b2403140710342130203100e0500d0300001504004109160160184c1c619041c40e964a500c1a4400582415140c2c0d40c10545070740c5042056014640c014900703a0a03201b15142c0749030034240070440010b2a805041101018500100c021412450303000c1181d290186c0b00d80c0001100b0001c0d1030b00c1c0552919407400740b1701c43c0c1030030700a050b40c008002e4004210523004100203091182c050454006d100540b82054240300c10b05400700c2e004e0750010f1000030543c9505440500500c00600103090700b98843e981c4692107907041d0400c45c1200c0d01115412500d0104540d00b64482d0801e882c1682e1041c00703040c0c00100500107402c1035002c1e41c000c0c0140c80120321080441c0860540307080611085565580c0800c030001e40500c500a170490409004604104902c0c10000015503d0848840c410f48041010b031005100c04a02021000c015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 865192913 1250 865191663 865191709
    0xf02071a0712020105070908060c09060d06051c05010b04090c0e041112100b040b010e150426010e150c091306032409050709020904022107020f0624 65
    0x71000084c002c04040d00c01c5070000f5500c1400040e01600012007a02078018500001d2402810030b08100d02e99000213252000552660000a06aa100084000403c401099003490110300c5d2414030b0858480e0b03001e1903c29850190110042110140040b041e1220f440359005286c5070f80c1070403042c00019070102903001e16894003030192041d0201d407084600720420303014090241004100010380710f411a54500241022910518900c0d04054804402c901d4980d41c91910b9100c10f00c44102251040850750f280400a482c08482e000921400d580401c440b00500202241e003402c0b01807060f00502210f003502404107944c561540c0d5001d01d9101000765603410002e250762494501c0540c0074041000c5c21020120082c1c1c01c1009007802100c0c1c000e940800540061400c00300e0080080d0010810160025428001089440d5040a04d1140b0a50450192180740f41c6200300a00d00381002c0d42010705904031300107008644c1c8066031042c2c0403104410324154004940d0313011491202e24411450707102600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 865194163 1250 865192913 865192943
    0x308210c0d2307050702121002041502030a020a08090f0d062f040e36010b100c02091f0f1526190c11010c0f02071a07 52
    0x4110041c41c01200720802400400460045850000c04040c074202c0b01800032400192000c1c8580b0040400030300c001c2070600d464242108451030700d112100c030390880c0d03030307000500303110862170b41c645042c1c0a03103035200551a0405045009480c0d0780c14000080071820013060503010f5944050a45141c80d0b000350982414403c43d0900c00060060401e5410000e48206d6580311004502882c0b0304c045a5014081880d09183c403413040c03641c01d070040078964581102500107044403003450034440c2c40042e5000c02d55000100300d0010b07003100c1854100c46e100e59680c00ca129000ca802182060590f038044030007400c1c0307548465040d6540d5141c000203080c1c040b127081000c100140381d104107130305444460f040c200c41c500b151581079809011048070392040049070348420618070070100f0035692205206130b4101c25002e000700e05805075201d8842c0030000c9258980003021881c1e09100e540408152840c01041c280c918103401780d00d031038560207071000600340c0f050a00c0c02140e00b6022101c50651103c2c004020300d030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 865195413 1250 865194163 865194181
    0x2a0d05130f05030307202e090f090902030703050d0f1806050708090406052112130303120b0603130203150c2b020d0501031a10030821 59
    0x8014400816140c03189800400c0203906121440d00b5944060001d610786411030700c0300804400850b0041c0000242d08545400c180c94000940408080c0c17405413031010100d06519280c0301050102081c00c01034034400c00c0098481d18040e800c129400d440001442c0c001c04e0022a043c0b04444c0c1020f425803250315804440e07035900c1380c800b05403800c050380d5030140d400d41810700d5440c00d0042e10600d030014000303110100100da1204018152040010f0000980340d46e45c2c00410420300c070f502c5194180d500d1a03201690f11020901802002400040c02149071403c4040361450700e00305800050308210100e00e054410b0384403540103200c20200182043d4403443e1442a00000220101080707009005924006074042604070110380240040b445450501d818100c401c07411041046020061302000d100c800304000c0244024041d0300c01c003002c045015810b40c100015005100e10003418130000d410104983d00345d540550310203890b4052591541d80344905204100c84001a41102c4400c3d58101031091442c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 865196663 1250 865195413 865195417
    0xb150a03020403080a050726030402090702010e121b0c030d05071502040e0402040e010905071a040314010b03010b060403120f140309150907031703040201260403031503082a0d05 78
    0x50f08c42c10300032002805005078240301c4050100c029081d01030510200380180b0b006000720340d0100191000098030101c3e503080da40f0b0803401d924048081000051003813640c0c01c4c00e01c001004080038400070700d81005d6880110366a08190090741041041c042001402c000a42043c0c0011100955041d5207e0741c59002825890400383c60403841a0301e419072460010700180126140650020080c0001c00d2414a07a00c840700c901c41210950f5072070400010001614a501481c20a01040c2c00021780b50400803d250031180c011034a64880c100c06e100403c000f400c0300100d41070040d0b1900d444032101244810580704003800d82c4803285040c1c0c01004004810070006045149000c0202803107680e601d0740d8010580341c071404d01014001842c00004403400c00c3c041001141c00034410324080c0d40101c40541c0741001d4660710300d2085823001d0003000703000605625004241c030747c5006000380c0c01524503595a01d5a18801c0c00807541604014040070614610b8003103034404101d14410a4501c9102509030040030f80e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 865197913 1250 865196663 865196677
    0x8130803040e070f0c0212120706061e151d1206060906010306180b13060e1b040b160f0204020d090201030f0c08071116030c030201120b150a03020403080a05 69
    0x600080d01c00039044900c01d180844c080012034940989400c026020f01004481d952595501880b0321203400b03200401450080c0012030050b00002503007420402440c1c1002030000303007004103000d42c48003840789460002e17041d101c0719404d0034000381d0310521011007080403400d0710f1525805500c10b411603000b40004900c1600c40d00c0304540300000d6903107050040d4111389950041801001580e0644c2030551115402021a154010706d090807a0b03900d80740100681d8815007109810b44000001c2c410071551110072070300e401004001d000e082901700f0180480d01c0c0924000440d40c503092031605414003919020f098100364001d44159550750000b10050302030403907481e00b240002d140c42c03258110001c9510810850b52150b507110300c4c1e1034031112001c0f0f030740c00c4c01b41000c001140101c8c40d82c804c84075920304000009620030011318104510b10b00014000d500800f98908146080c02201441036a0303512060301080700c0c8000341034803150500c1b000c900034001c40d04002e060010016200c0c0906c1e4101002e0444 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 865199163 1250 865197913 865197929
    0x30712080604050c04050f030307080310030c060503060108040f020607020301090501051b0c2508070609091406030627060123060c0706030207080d02032401030b0303090603040813080304 82
    0x2581d15040c0030701c0111481201e5032100800c06000600151414180c0e42d007030390f5401400ca90400155450b1100990b0040c1c805c480500003a000800c1001180308980300100342c5401d0940c254030301140003904900005200800070905a0380d14011036849030291031409401030b0080000301030a1030540e0007045c050729291084000c2c5946403d62112000455540c106800041c3c21185c05601c00c080d200820340013000d40e4004d00c41d8010a000e0010003020000748802e40d0750a00f0341d481e00103030b142240c0c209480c0050042201003000001e07140042c200d40c1112610819031001581f1004e4049a8440d0003c440b405014103800001c1d20604880c8900c00c04611904200759080c44500f0440d1910800d8648159a0451407003085424083d074040c110050090071221f141104252102e4101d030b00454070f010310304103e0f00f40f504082d11401c0d1302d01c502d940c086c00c003000b0703408295000a94034001c030400b8606c110b10000c006401c00a51005550840d61880e00034800c803510b0310f0590b5180d0b0014050644 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 865200413 1250 865199163 865199177
    0x30201090807051f020c1c0b060411090f061605070e10080d08060a030b1e09030a1403100906081c05040e010504020703030b031914010b030c01051b030712 68
    0x601c0500401d4100450301e0043c00d00043c2e00756035200c0d044507442c0d442c6038000c2d405036101124451302c660030f1200c0d0780d000300e410400c905035242c90441c120300d001418807030007140303001e82e203c0d010b04444040700d800000444201c4070140c011400038900d8410300da101d407070848510504204000002401d1010382c2e60140c2e0030078542d605d60b00b0301256403106110b2003a42d9800a01e15640701409a2549604960b001c2c040100341c40c0c032a2680c10580005481c3c070b40d425148036060340000020500c4003070300a0f90000c055864600210801800418803003c02d03200c1a8000000c00e44201048000400502030100c050112980e105541a10b40d030380101c00b101e098a94000c2081064030a41c100d034107031852032450742c4040e420402480025044404101d00341562244510400d83c1c041080d8018034842d0111942403000030f01d05410300da403540c0e512103040c0c0c0c10290b00146030356002c0340300c15040000b80b90450700c0750300700140340040131491142c100d441e02002880790141b001c204a505120112516406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 865201663 1250 865200413 865200419
    0xf340302120a0f080403090e070807030506030703210315090b13090209070c240213050405041a0c070c0602060f070c03140c03040e0a0209040b031f0c170f0103020109 73
    0x2550300c81c588076400003c2444244803000c1d4056000aa0418001d10305800701380e40b035403a0314040c4007083d03400318045107044040041d101d601d4082e90741d2040041e8040c0c81c0451540d6640540100c0a4181d0f00200c0f07500c0c07420040702842944039600b6101d202003038608a645d190f041d10028442000c10f81d01504491640e20541500d80c060010f0a40c0d01505c2d04450b6901c03443d040710510030b003200c11901c54068421040c00aa5840b000100d00c0d2100e03080166141068850f810020001d540144d00070360400042102103100044c1302d07940c4801802142c02d4660701e09031501d441d407003042001402069641004900c3d5680001c80c81e100f01d100c4985035003561078500c3c040d1585094444002d00054080c00e41a4003010800040c003c0e4049903011a81019200c54040583c00b10850b48800f16550109a02048d07190600031611a00310540c082d00152141410b817007a16018000e40c2a00191145941a25980300b00025107201d441c0c000440303450b0402c100c026189510030b21003a400103031500404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 865202913 1250 865201663 865201693
    0x20c1e071205061306020d020d1b020f28080a0807031512110a05040903020606240301031410050106030b0307050603092d060709060207080c060f340302 67
    0x100030160404000c0c0050755a585030400015401801117880a40a1264881000490000c1c06066908030307804244400c03540745024036130302a01424011944a50000c1c1140c1202140307401e07446041107540c1c81c0500642c168114008180c51001b000d103c00000c641412a0f40855824010383c4035550a100c00114160300702d00100c3c0f180905a045405010b1140000300b460203030b00340c0200c002d01500d0240355980c00207403c032118544160003680101003046a03500d441140360191860070341d20f40314081d0416a07000d0b90750005000c0103100d10012150070030181b80400c040380c00c0800106040c400c81d0f07161a07000700641080070703030903010f1301c14100701145a240602c1528807600188006040b403907080620301440c8542c0001d03258072449500d15216201c001804003610418817910341c90149072030700400070702c0e01c0d0481d03000758213540001c00c2002041c0c4ea841d0407203144541d140206a01ca4410012a0701d5403d07100c0d1900002006800c05107003d45549030300d081c0c01a02980030764070380440c01d03210 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 865204163 1250 865202913 865202939
    0x224062e0306060906050a120e06100e0f040309031509080307030f140603060a0209060405060309010c0f0806010c022106070e01090603020301050a05040203070c050a080d1a090a050a020c1e07 84
    0x4482c08140107005581c4042c1c400e0340c42c13901008e023038080441c1c0da491007000241000401d4a004980e10301001e4244074040c070003000b954002541c05010b51692410351001024007a50f0b0200409500c54920200700030122900010102d5801460031581c0b4144090068000c0034040314141c41c3e20304140d280c0940390124410304d88901006006011140d40c3d11181d000203500001080f40d010109210100b4a03842e00c5000e1072041c16010000500c4100c4c0241c0600ad14819468040411070b0000030409980d80c00076000e040290306540040c811400460111940c0e1080720f890b100c10b208140230021b085038000c6581e01914000e07240c003850582c4401e8110244e12090003016040f042c088010042d0303050a500856004007513181c4035020480a5a80c030742800f50104003a81c0d021004500c00f4151043c507c910380c11003214644c001c25500007800403076000c540060244d20b400d6030740d80000d10301c5411b940440d00c0880b2a0819a404040451003580c051000c210b400c500310302c541c506c080740c00c00310400 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 865205413 1250 865204163 865204169
    0x6060c0706030c2c0609031f02090f09100b031008061501030509030c06040f060216060515100e09090715090905010504290105040e0108030309010c0224062e03060609 73
    0x700c48001c00980c0610a01b039105103032107034141c0f050701c502e180740d40d8000d0025502070a607044c0250b071743d22802041100304800612030320b104e003542005100058011010f070504840d008094552644d0700c1c440007013100e45580e88464030600624040041300300d2181d4804035223180c2620108850f13100e44a04030f40e240126400082d1603480000420041030f5410b0810310000d1003821301614001381d1295049401a44c104100e070f1141c1c40b0024800c0013032000d11907005c1c4440540d01180c0e608152000207107030028035030580c0c0c00b0f0690b10000c40c00c003034810300280000d800810000c820301814180f0040c0445110710403010a5441c05001064030300c0e2600030220385058031121803084030070070300d18180080344c0005660305004040000082120103d03858a00030640140915140e01d8901442401c5d1600c0c0c49192045411074044440d40d031607000c000c20300e0000041c07802009551071201080180303d1090b040c107404d09031101d031001d80040302c1d240d80701c20140031798042c4030096503048251070b8004240 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 865206663 1250 865205413 865205477
    0x17040504020f2208071205010e160f09110307030203090a02120a020f040b0105070201051b01050a0e1507091e03230f0601030c03060b0103021323060f0d020306060c0706030c 76
    0x10750800620b200040b450150324040c200004030002d0040091349810080810009050603004041250bc0ca81a90748002030021034018440183c0043c540c6000e44070052040c0c0900d503011000c2040000100187c261496014011560048801e10711903a10041c4500c1284a40c240e2003042d201030916020b907034072511040c5c558138280885540199455009011f40482030580d041200301813220034014117000700b200d2940050b0751b80180b02d07514104100c00114202006409007404400c2c0e5200c0e44003021250000110500d0301000c200d01c01c1802c1841e031001d44a41c2e05440e0850f16054446100c0b40006290300c01c070b0355074600501d07080c0c0d01c84509200c0500141c0e6800810004120345801c40008100c051400600e040c402841c41d045643e00f41d00407040840c44510308481c10700c0442034880c00300e02c007100c1060510388087d070018120301c2403041c20301c0d2254020000c1742058503900c05a030301400710041030303810f0691100300c0140108505250342c40020014a100303400700300e0918404107400303001 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 865207913 1250 865206663 865206673
    0x150103240902130e100504030f0f03020a0f03180803010b0c070e1303050702041107050f0111180621090d021b0d020f0118030b090c0105041217040504020f2208 70
    0x1140307002c3c008080740c0f182d860540c06401550784c01e07107850384207052140b842611416a218907894000700803a00300855101490301c1081070b10030064116400c0442e4264a01d40403a04000d940201420700c2c8818200410300f21011001154201c0d1000140c003032940b03050308854449a0f6500c031080b06030425071b40b50200311f40b11184003010901c00c40042c031303450b03001600101d400c07882c440001c15940d100b0380042d0303010740184014040c1ea0383c081c040c0c5200c8001c1400001c0c01c024540669680c40031003000c40c18403404000413400018101004941c9599112281280b598542603011984602c804480d2400502600b1400758101d040c1c003041d0641c0c1e9030041d10a4001104a03030920480b1042d014540341444154184403000300840000e2101640c0315212030300442c1448540341d4641080b01220790b06201c03080c00240201c9800400d100003054205108101d0501c0b03207131000a5078401c41d00520b800c6070002813860701d000d41900040c294100840034a15a42d410000e02507a80001c6000d60000e507000 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 865209163 1250 865207913 865207939
    0x61d0304032018100e041406011e0501030e0c280504110702062d0417151b0d0c08090c090c0313032105011a0406021e150103240902 58
    0xc03009140768004003e113030401403103460b20301541040744101c50840c3d6001003110030001e0b00400340401801800034555400c0d40c031040c46030f40802c03000a401294100340e035a500007000d8940400c082440068050003c0140c20700c4900e249640001044070441e00c2c1307400a00008803801c06120b0f050f950089048000e05205450f0300b0002e690780820142ea203965009900c5040c00c50b130720581d08403510600e0350655500c03442c00020645036440d944d250505500200601c014200200315610750103030008200785896050a038081400b4021808001c0740140b80914011000c1e03002400c0034011000e000032119a03036050410000260300031078010304100c1c41840406c81002091141c1c01c105403107420002141f4840c1804000050401000000c00c47d0701c410040007820110100c04c00d0700c0080c01c640c145070074186031020f951041c1400300750794801c0800005904102c8180032001001761011824040c40d41d403410702460000c01d0380a01401101c2800c401003020034944900c40072145d010f0160441790300 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 865210413 1250 865209163 865209199
    0x71802090d05060106080618040503031303200d030501050909121602130902100503131e060e10050606070c0513020405100503070e0402071e061d03040320 68
    0x42400303103903000301c07000d440200051428040c0ca03010307080940c2c599040f443c0900800200c0d09003a000b031307030b51038a00d441400f011510120840b41d2040c4002d02c401da11103030034a012200807030940c05c8148840609580e5009001c0c011842d082416110758090100340d07251810410f1802c001d5945861940c010750350b03100c0c0700e484c4502038070079203160b0003492030294115000714001030328200aa110b169036a4401c06d00710710341101e52903280704180c034110b4214030b80210218100c096850019000b8081c840b8007516030000d0b105041412030384004140440c000441196507940c0018501a9030326040100050050038600255040380c0d802034503440d8028684004d000c0011102c80c0e84018894003000085070580b40c140c04214000403a07034030315559150103c4010709481e10441c00310f104500421503030011800b01003030325505003c0c2e0844182e03103001615148000f0648e8081003401035203890a0501040e40c0413004e00700300c0303000d51241c0e80c50780b0f400c5403401c00003685908807981c0071200c050400c940c00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 865211663 1250 865210413 865210417
    0x10816050910112b02030304020a030b0c090409050c10212a091d13020402090d0b0907031502040b03011710060b0912010506030718090b01170609071802 67
    0x4102d41850500303202c02c10402030820748101c0805103c104109030721480e100402c0540951091584051425810540e0000e800d00f29180f00180c148542c3c500414540981e060488000d03401c01070040001c02481e02c0c1080d162821440c0d030600c81c16075503c0400f800ea018400c995082c083c8449107514180c50a0000c50091a00c01041c09400d600d00e00d076800030b9125030b840100300088940310150924039100001e440c40050141e4580301408007401d200c025415035200d08100360b070403100941ca803507803240460401700c0d00600103401c119503502880a42c400129400f03064a0080c00d0392100d8034594401881179206520805140107001c100401501210301c0b000c10311405600251102c00c107410458805841054104c614051800225a0b078145000c1414041d20203205000348202d180190000e51207212a1103858900090003020415104a035030007848201c0d4040c0b4135101c2540c542220f0b40d2242c412080c4e80c00740d0703ca004080f034210344000401c0800c45120110224503032000c203000710041c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 865212913 1250 865211663 865211689
    0x90d110114010602161e0605030a15030c18090506010302150f030c1201151e050d02040f0602160f03110643030c080c1204090504020108160509 63
    0x155610300c101105801081c91450007030040d50700524580f500c840c560560181c0700d40c08030621401040d44850204500c031001001c40d12076040c101c0e00d0380c0d20740002101406290060030103c4240007404410842d003400c802040c1e4101510b03000342400000c5c5c0300421511040405004c59201e140100014a0240da494040f4516a44d1203070908a08482e0300585030401c6c2c8141c07110520101e102607140c00e4085485005000030142c01c82c1803541014003400c00607034019491103500a03491800030140c0500c04031034480c802140b08542d9503a0b52a0300116040d0240110720042c0a5a80b00100e100d61810045043c0c89180c14250085881d40e620b6030f10014402c10801d070840018840f812006251f81b840d00402c02ca113000c03101c0d174030491000711004400700240d500109015040c000021a03449081c1902096110071100d9640003d141c20a1030202e0170385408409060005002c00c80c162190003550241d4803e8946e00d4054484d04081010b022100341d0842c0020350a2200c2070700e030700d030cc002e840850b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 865214163 1250 865212913 865212947
    0xa05040801230a061a070614092b0503310501050108150f0703091b150806030d1403090a0b0c0a140a080c2a0307050f0d0c02010c060b0301020729090d 66
    0x15000c1c10b546500f008601c1221a270a0f16084981c40a80400503180601c150100096242e10346081005014096000250007425207030b0180a00c000104c4071500400d542c61400c031000c20514400b490b1460180209029800080c0940140e0450306000000d0b120700030904122421502d50b64480100d00500c0610801d03a4130710410000e00040d1240310702c0d080042d14910f8104c50600301e0020002c2c01044003d0b001c14001d52042881c038400307035071042d082504690310101d40b50380c80e02c8100740ba9142200c1c1803400b81400c604a028088000da00c0401071a003900603890b072251480f80442d1000643c0100b882300720205011500040c820032031100103081c0007842d5003030078283c0320300311000c03155910410312180071513400002c040e01400402c12400000740000c030001c241030619044010269004580000d052003003400c600c3d410042582c020484507500600210744903401c5c1d061410742288056010402e03002c401001100199010b4286807099100000800440c51081822609144070107941c6e54 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 865215413 1250 865214163 865214171
    0xf06030a06120b0126190507080607020c130e06070309061506020607110304081e0f12131e03030e030c220507081006050a05040801230a061a0706 64
    0x61060012900c284003070b00034030703000f0910340c1416030300016983c4c0415900d1040304450022059a14000f5000c0e50200e55052528400451443c0003407400c0800e80181905004500400c2050f13640051030480f4410101c034045034200b030b600b003940c041311017400303c101050304014001041107000790051802207100b1680001c80e070784203045061030038140f83c20440058121805000b000b5900c0f11000c4120035080000e103203010310344220259a6811114424034080c081e034844050b00d101448500510500402955001c400b4400034080c00d40c4006101642014400c20219103121420107020000d50300514580c0300c0303800c2d510300381d07460320710300384c2656242c800c2110140d4552948148401002d10b803800d040901d10020381d000c0180c85000f44030108001e18201040701c240200c0300302100719502c90816070384e640d1248404450512684d007044803c3d600f0040c03030080074440e03101610300042e41c082d901482522450b81210a43c0c08038803604450450b00c13203900590841c1a0001c00e034003403181c50300003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 865216663 1250 865215413 865215419
    0xe04050703120e030307030c030801060e0306010509070c0b0726010612050406020f040602070315020a08010b09010207051008090601060305060d02060d0b1903050d0c0f060f091e1407050f06030a06 86
    0xc5c65640041c0c0d080340010a0030150104060304125000d0140c049800c00040e034138042c03004241d480c1014800c09106c0e0040001080f01180120151508203400803c0b1080c18a0a43c502501954103c84071581c4200c61101d6010881003260525041e180b01e50b6803107a5450005001a000c3c3c00301400c250f0700d00340c1c03c1000307059000441000700f0007892580c014085441c0307035061180300c840030403c0b503003034040c01004508045607004841d507040d141c04070800740d1100c2032000100c0c41c007000c07904802d170802512491040c0c8507400c40d01140c41a02d6400480d1910b0b81c03030740c80441c16124183c4040303401c807910a44090043c5400c0018281107031010200144405082001a0110220540c4004803544c8040e0601c18040103110f80b039208005428100e180a0540d601e10502d010301078400360600e6980c900c2d070140c0400a810807203203d82c00030314031940c42c000107450b4aa030700c40d440400c84600007680c052030710703400300414030340121540200301c1680c0019010a1102e20340c002800900e0131a5100004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 865217913 1250 865216663 865216669
    0x702010e0f0a0b0406030c08011403070b0304060917030906070c1e021207120309080a03090e0406021201060822051e10020301090f1a0f0f01020109080319060e04050703120e 76
    0x384c001400f0755503000c00c5e000940354000d081c400301030b0082403c01d258424240c40304d4500141203800c4403807041241d6603075612400d00070001c055038040101100912114181254810300266014a48400a44071140ca0f1100241c503850f806800c02800140d01003000032002c803405160382d038a1030018242c2d0010303048442400b414078001760440c0d4910826422000c045c10b91180c5d12002074103003034008002e0b040c0140c6020f0900c80d441d1280b8141c2016420000c1e00b080155010f403102c04507441900c000b0f55840f144064041d040869029010100345647c0c15040c088185180e00e030300c3d41000c0917000b83c481001d981000c510a1888280341c0e44180205600040390301d00c0214001c0402000c000340e45851001c010094840b0075040c241c505440d441d0300c4403d682c405825802c4a10110b498040d000702400042c4c0c0500311600e00079100c000c001c02003141c0b5510030034003250040d0390b0b00c1003005015101c80c10201112400c0c0c7d40a0050703840307101c080c0002001360101e03499032013490030b16980c110020000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 865219163 1250 865217913 865217917
    0xf040f330e030f0d091203051912020a080402010806060f1204081603020d0f03050f0711010b040c11010b0103020c15060a03080301060536061804110c0d050702010e0f0a0b 75
    0x38810060740113480c50301645504c0135100020f001d00c2030480300f84141c203850081c000e000d5100c0c3c40302d00c00f03070405d45112080c2c0100070043c0c648080d1a030964450000302405000c404085505034045001240050840c1c90502c04075010329a0030100c49040079511503082c964648000e00403904c20300100a00b00803040d84280c41d800c440c0c4654010b0041918644000700310140340c0b01094149800e00b401d2018500750b920100d0340c01034040c50202407c25610b0f030500d005d0850144510740051409501072403450f4019542e00c0840b81d8400240b002c0c80003480110228807403820986460741081c01b10101e0300d8041c50145411000c02041300c03c600d038803a280c1c0c0c0b446501c01e0b440000801c80001c4c18090101d4003d13481d800c4130040d02e2070b1800c1612506c0b44c05c40102c48046015218210004406035086140c01800d480c60001500c104a075a120359000d000707540c0403521040d800d1140842442c60306118200f201c00166040e904d00e490b0580ca0f8060008039070085c101e1a40c02003a41402280741600100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 865220413 1250 865219163 865219183
    0x80714040b0301020f04060f090303080f0402180a0204031406090303040807050a020406090914070501050f0a091701060302130c1202180d03030225170a090b0f040f330e03 75
    0x31805079031b2803070248050911494144840107001c02c11104001203078000c000746620a5424800080b141d46500c0021132003400761505a03140c620900a01110021550103801a40c3c0710340c0d2180c511f0b85840303080c5c0380d640c982200c0050715540204009000640314102812520f44140111281d66040c2d500080036900b070b1303400172078055503aa43c014080c46100f01c2c1610803030f488400500141070801000a041e4481c8034800440c00000160b050000c80c440c04110380200401c1d0100c18041c1c2214a0381800303000c0921069200303000302891300c0010242c52080d4248034400b9140c2818140405940788040e4020701d01c442141e9080c1319000000780c40e01154001c82034031903503006a840100080c0780c07182540ca42c00700703c188541c0013400c40005004800e414113501110f408141c030392406000480725004248c0044050050104859000c958448041d0069400d40616040b02130340395108286c900e05d01d19405985e00800140f0004001c10006541407900b04074a0980085022030012a02d0107070008 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 865221663 1250 865220413 865220437
    0x2040305010b0a091b052109030a02070b03150d2906030607050c15061f02010228050a08190608240402031e1609051609080714040b030102 61
    0xb48401d10b0b54601030041c60060311201da4204509405103070307809540c18006040000f488400100310320450540d980586241c04003409491062822003501910b035085160f101c4050b104030071010410700c00c600161b80c400c12191241282d503140400c100143d00024070303000c1c1c0d152141019450040703c900078001c18100641008910681000c0d400c2c10710f071400c001c10078010004103020381041d40c0c0d804074440a5001c04c41a9080781c275190701c400a07141c8031500d11020012103c82c101e4200c003a8064000d82805441031000d0350802c035003000c403000294009079600b4001001040700d203410310301508045800c82542580207034003400060310101222000d40203a2150f03031260085225905090314690729012064880401504060b030109903142d145402680d0003001448260340c40c05420031440c07041c81010002003200c02d0755601d400c070080609441002002282846c0f050302c444c042c00302c810444950f80c004101c6540790040060042c1480c3c0d40c6564040e0302c4061101d0f15070340c2400a080c007507400c9 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 865222913 1250 865221663 865221671
    0xc02060d02160309080303090c04110d0c02062e03020111120406050d05010f0614160203010504060c021615030b0303160b06130e0d0f03090b09010b0a060c050601270204030501 77
    0xe043c0580911010391018a15034010001c00144100200f0640a503000c02d507004180800c142c03d003d100742c06041071404240340703420440d0450990000d5410b0080071044108a1640708400350300c00140c035a9074200e03882521440003040154032841c00b000c19000e070754042e5100c102005415100d658003039800304000540115178081d9080640c82aa40108212050319440b03501d01900a132040313071640f0391003401c2d81001c110140f19603145c00c1c034800900c2d4010000c014074641403402c440105401030001005100305501900d61410408034001592141600114454218201100900740c038420b11034050000b8400080d0404100f1040f0445c00d1094614844600d44441400114205100c100310b8007030601e2004170801501281c0c00c001c418051070b21007002c50041d2015006011800c400601e0b40c0854400c10411170b406504c0158180030880d64a282603544e1201120f842120080c0a40716411460040020054a9980740d402d610440408614a1001c80d5548100d802581c0140c0c1d10380d440d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 865224163 1250 865222913 865222957
    0x20c190b03040212100624090f0b0703090905270309180702070e0a1a150403080304020d023c01022503050f100621060b0a05100e090709060f0c02060d02 67
    0x7d07509405000d00403454203140305031406200301c1d050442032081d28034401d0002000000c2c9072143d458031016103400e010501c51401d0420402e507020b41c29006a00401510045152000c0c0000c42201c040e624000c00c07411031200016880a88100003038511001d62003800c0740002c5081c1002e41c014411507400300005544e03c98039039012110300c00da0400034403803640b070b203030005800341d211040d0750649810036009078583c0c2d25407010031841c03540383e500690b11948005042200c07085d00d40e499202009454941a8505488200c511440b4201c0e20180c0c0940c0102e01c11888620018814010300c004007a001c03401e040d565100c01c4e04000800c0507104803500100c000100c1c41d141c50040c1e2000780220810307c420180000c1055004080b2100001c10803034580005002c5540c40b031b00ba10014090080030420303858403880c40582604c180422441c0a020300c0c400082034140101006812621141c032480485902e081c0c04031105148008100d0f8456401d111200c105141840038050321030b80000e5000c26408 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 865225413 1250 865224163 865224209
    0x2306130f11090a081501090207150501173c1005091513020604061d0a0b0901090506031302061b100c0e191e08010507020c190b030402121006 62
    0x5002c0d08600d555601441c0c01c2200d8104030300042d030447d8660400162a075129180102c1b180d0f0000078104402801c02002061103480446d000e031002089104480c4180c130318a0081d00d10540c030340d0b00c04da00d503c40d00190741030300b03103002030380c07180054083d001d8401000b24400468200c070001d40740d0691590119121169500710b00e035000d0b070441c890141c8810350340c91541c0082e106110b00e01929041040c00d074444407000c002202c4542066200401000c11316440c0c0c1200b4816030402440d07140081c84408000425081201c11240241e46a00741881d85500c950203122071a445008040d040d0700b0702c24892850740506100d01d0121140000f00403803241c0480e0b100070041400581c1c3c0510541620021805000c1d400200504480d410514681c201c40144462480769005a20a007041c2d4213200400c140194042080d9040160884844529000c0c40c0100c1e0700710030320b5001d1100c61003c01c20109000d17183c45002200b000c502e0788221182c0c44803a00d480c0381581c0703d1342e00900b07a06400010a00e1a50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 865226663 1250 865225413 865225429
    0xf050307081c031a2107060504180b030a080705150a05070804021e13020c060c0a0504050607080732030c06040f060917030601032306130f1109 63
    0x4400104421040c00d02000b180c1510400c2d04400e2694410b981030a01c0c0506860b46100c1000400700000081302950801252454000c142000c0c020800080352650150094400751401440c1c01100001e0788038554008040c0008003550610411103418001007102c402040418440c00241c200541c40d0714643d10355603006440000300a0030001041129036014100c2c03503105804803185140041c0003207140d0303c200c032122a42038104003400c0c07003800c40719042e030014010041d40c501211240d540d10f0345c0924050040c0040c01c070005000b044104071516044010f85441e0b0301420099203800304a41c1c440104551458009000289003690002066124110346819480200c00707540303400640303140709803a01d100a10040c0040c102d21503130010b0080e42c0d030000c1c190310b40c0070030003c40043e4030084003500d64204443d5a80024104120300c52400d64421a40041038455942c0181c9615a00304200750308580800382003019075200c00c0d417038160201e40a031010003030b6036901b203940d41c0c3d4820303082c41954 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 865227913 1250 865226663 865226669
    0x20a060f09020d120e03010f051506040b030c0d0f14070305100f030201030504060b0306040b19200c100c050406200601031b03050607200d0e06070510060f050307 71
    0x420714001d201400358445030039610b01940c1c08801071040b545800303010740710200600300990f01507281011800e415403131940114050f143c56116a20524000da00300082445540119900610284040394003146582c2c050200240044808607079254140300840031102c00f5400310340103011000a0250598151292540201142070002c02690070146200703100b8131180300c001d04060352400024103120055001841c003000c02015201142024108030b449940150707400c1204a8480702900303c007000710300c100c04c0079400d00d01821012070009040c030012074000200c80c8065026022040303800e00c815208040c80c03032000d512140d0704c03541400300040c01c9100b00c1c426110341400da030340c071411038290020300303181125404403607160726000000903524035500031f0303000a007103200e08800d00505581040c1c11000d9013451145890344081004003482d501d1828000500200d590314040c81814204880180420740c016411103001c00b805082d070b10103c2e461544540f4280d40510320a0000c0d2906105801c01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 865229163 1250 865227913 865227941
    0x3309070b34060c0e1e060c190501060518070912050307020a03051b04020403050a06330501080c070b0f060a0b0415091a12100504050f09070f0305150a02040e0106020a06 74
    0xd00c148000b61210110441c8600c07521442c004920b00c580b07003c00b006246c100d60744480823503030328412515240c3d000c0c0035580503043c819075140034803504040161514a105254507030301c04805503d001d1000c0c0001042180680f1a40020006000580c44115909004600c00c0700101080400000e400c0da04240c11007080f441280100003c0021600000345503140725040720b070002d0072a90201c1c0c8401d8140c500106000040100307040c45004000c124000c4003144c401380c0302c03400c156903181040313503003449408001000c50090344041103401d0107880c5800c2d40700c84007078400000039860b80803121850300244c0c003a0090f501c2c050759021060b50b001d5482c0e002080607158881c104401c3c01c085000a000303c40070064401c0c4d148000030201c1210083c65002810050420041801c1404c44104041c0d011100200c0510945a0010300b410465000000301ca400c40003400c049038041c04420030251001d841c203001181c00b4040814024030080c104c0c0c0c001c154940050040d00340c54505001520f1030b4400c1c1c400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 865230413 1250 865229163 865229179
    0x7020609160905060a05180108070b0c1b1c060501050a150807050d09080705031b0c010c06090804051816180b0c3309070b34060c0e 58
    0xd560501038003500300ba51845100401d40da518400400d1030940b0f5035011030751046a400d070001004075040c0f841410307501e00e101940c410907265100d00d03080e03111324408003996034030102d0136041d500060711000625460041c00d0246a041100c11004001030000c4241c82840da545c0c010041440c0c41d02400c4002c042030616425010307240b034030103400650000d0a40341807100000703261415400355440004400d80c00701081d40c4681c00790402c40d55036040714464000d401e034000d8210b41c16003070028502d61840c80581d0340c0b100030304a40e0303101c001a0255240456001d90240300c08a130642e142c8100c0e0302d1014401e0b2201d800b51a0030701d020480d15290001480601011000340c1513407449a5500c00280e5592281e690b99071030440365414070340700c00840e9102d4080c00008049550140c2c500383c0200403082c1031000181034440c1c80003203440301105d11400c0071030202044803038000c240300ea90007050301c0f81102810f8103c2d0307440c01038029101e4081c0d900b2940386a41d6031038030007555000404211100da058400c18 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 865231663 1250 865230413 865230433
    0xe07090b1c0b0415120507091d1b09060d030c0204020705010504150212060f18090106090b0f0a171c080a06090911040509030c0307061b1b080a0311030f07020609 71
    0x4c0200e003041c01245110045d01d0500014480700701b100c0c80c01490841e4042007802e8040c44010000009101441075030f01941ca04441001c0c3e60807072046c0300c54002004103040307071100310410804500d10b11040b4280712140c0303070510150380c8520240480a00400000c00d40c0d150618108000c00000700b400b10300d203403050051900b80301c075540c0c005a214006407800024503807200d00164440c501036600031113134001c613020002d2201040d00704008403a01a2800d20800426204102c520b1400306130702c0b50080c581090030046402e8041050034105e00d40d50a94031804594080741d07212100340740c080d101085041c018400715404a208403001049408420015155560307245121510b101490310f200e140c5910100d08007490070700c119400800d07460300b1030369506400e103400000380c076a03a044d01107255804001c0001103405001c081000307484a03900c4032280103055071015603036082080349100305540c50a0902c01003030403000075030243c10130b88011002807074004ca00916048006000c264145c10811900c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 865232913 1250 865231663 865231691
    0xc05010e0105030f040623150a0605121b070b1e0f06060a080c13060c15050903070305070303090204051515181314040b0f06190e07090b1c0b04 63
    0x13243c00c070782d100e540424402e078038042c0c0f0780820100086040341c00d6054828070100a0280a0f001d420001c10b540750b0001941d01c00c2c2c180c4e6180204000d032a0740401321000601318428205a0300c002540ba0900a03007401e0b69511810006503044072161000d07103c41005c0d000c81440480c09540c042030f040c40d015090701e80394010802ea40100c08042090064540218200761001300903212a82c40300341042c1a0a5541c180081c0300e420750354410303280c4080e62081c4c182c0b12056401120310030003030340b001980340400300e0707078200d8080d07200032020f40c1050390710111140140d440d1701a2502a0394002d1800b04101c1044041040554580c01c02c0321410b4810081c400c80f002c100c9552400c800002c8030003040752201c1e009114007a068813601c030b803200805c203010401000502c2da06c103401042800020440c0d56602c0082c0001000e9810007071040900142b0108140581004a245e200d541ca2910b03542c2d00340c6c0e6641d0b07070b50300e600703d0380c01c0e00c140c1c00c2d4231110110341c0d141e03c0c4980992060101d60070704c100e1101c2448 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 865234163 1250 865232913 865232941
    0xc010e1207080703030b1e1309030905091806010e07120902010f030902060405030102030c0729011511010e0f101401030209070c14012c060a0203061c0c05010e010503 73
    0x30080c010340b00803907804240340c080c2e4000126107401911a090303210441600744011407015a42c90310038411a5568000c1042c244690704905625032201446c1c641005c040090a0318000c180d80ca1000103021984680c4600b80143e83c001d0101052101a030301741000040d000e0640c0840000e051843c1c00310300005030380e008107007e122001c6400d001920706861300100c0c049100c0e540200e40c0541c00001440162010320340102000340c000e40020400b410b400e0340d00362103244000d80490200883d080140001c600ba28903403800c03d032240c204218500e84c00c204003030a40300300180e4020941c11820108026081c00c0c05102124950380308204440c2c030302803150403410711040c000607000d6204840014000c41c01f40b0b032062110340d00321440700030507081540c200c0d01074249403c600c443c01d1200c0d200c040d00319044103a802e5041c0e20072009007490f90f55000101c002900000d140c2030340402c00442d1507600d04138034658040031601600c00c40c40060b040000141c4040d01e6070400754100141001004060445020 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 865235413 1250 865234163 865234177
    0x503070801180b03070e01030201030e12030f0a0b030f06010801051602100e0f0318130b030616090521010501150f03050a27120206130303180b04080c010e12 69
    0x6010038030b00c4441180280a0409116094410040c0220f086d280c031001090480c0c1c405d82e403d1202c41141c240d80364560020881038040548240081800488014083e646c4012030000000b02414003c0000340ba05a51500c2000c564222270010700000b00d0038054254401103d4100ca00344101c000c01c0250381d29455220f03105115a200741d0800206c2c3c082c0510464800703107004a980328090309011108030040b040c82d0600c594103440e04408203000c24002c00884d100c005002e061a980c4070303100d1400340342e040c2101d4810808540800700d40c65940c6000c1d0f0794241d46400007a0a5840721115042c01c403441038001040180d0116a002030b01039000c0801e0141d4802c2e131501051030303150840d07000c0140c02c0318001142103000980540240704542d072030b90030620b406805440541d510000003a40c407070b5402d0b141d1140400e900c86904020070f0080d003180c00783c07810f4004400d41481003903c038000c017540207580469090780005040e0446007030900503424100b522402510810896109040551045130 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 865236663 1250 865235413 865235429
    0xe0d021216050d0f171005040506031006060c0c080703080306131107030c1109151212070f0b1005060403120507020d030e011d0f011b050a050d09060503070801 70
    0x440e00d5104041d240001d1016500c04102c0da0300103884540a086400607240d900e00050014428818500382480070700d0140c00c0c40c850300350102c0d007004140809440d00506c4075416101b01c0f1031205810342d0704d1058200414041d0b03202c103180e030028607050071032542540c08030f451a031100300288042510b150071280c1000040380c0e01c85607401c01080c407602600101e540700f0110800400d141003891f4100d0588915944100074484403c0c005904106004005607840e000b030380c802100d41d00260410300761510311040244101c1d001441040035245690340000386c221645100f00b028442003180a000305074200c0b814101d5524603a05100106245004030722000c1e185514443e40740720810302440840d070301c040c2c028205413031000241c10042c02c00c0402901060000700b1004c3c85503144002c111952070080c0d00200300c8002c2c80111001165004101100e0714a108801d5683d20b00040301080f2555609129001400d08240100809040100740340e02c294107008013042084203d5500940301c5040d00d40c80 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 865237913 1250 865236663 865236667
    0x50105072322171f052401050405030316140a051510051003090c08160b0903070e040b0f061210050c13260102040e07030b01050d14040201030e0d0212 66
    0x4680790281c21040d804102d007500702c010940784000c00813840309020070252040c41500e041e111412000c4510446131505485000082d40314000002060601810814503106052686400020f81507a02c64080e80683c80000b041d84c0040003d100c180741903000c0c40700050060300c502038986c1034032540350800c0c0000f01c580c0e074800a910100d01c8020140640800b4158543c1c03080b081c0c40107002003008407000c0c0c03440c142005002400072030010b100c1e04000d10414441e2401480e00c03c02e980e507074124600b9298103014041c0080343c44002c03504110703c00c6001b4008402141005d07100240d0ba000050540c6d401000e85a40303008242c80c0000d000d1144000140340002c00c1c2e540c1c0d100003891401092812544000800b07000034030a0f54126404000a01c8001c10403500003034039240c40e080788660f00c00d45010700c05140000e94068040d5024480240044c104107292404140c080d00891f01d00750312182031160044284815941c0c1889204085c4000c14010171550400c010040c1d170740c8141e91140325801e200 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 865239163 1250 865237913 865237957
    0x160e09030a120f11070c15020307020d06020d0c021606050a0503010e04150e030901080105060307020616021002070602121008060c0702060d050a090311062202040b0d0501050723 78
    0x550700407105080d0030001000711641c0001205210ba00050382071b2000b2034089804128502c6000404c0b9800b4a0307a001035103011400d40c2070010100441c0d0090301c1031a0b0901600c486800c4a005490862034150301400d5802c107890607801490400d0703003002c41000418040a00c03150381010440781512580148100a6603d0340381250002e2243c0400c2101c0324107202080c0940700c0e00101130181304a0989a00c0100d07a2a0b805101140c0011204a401640460007190041c0541c80c04280426140d00c10342d800c0030100d0510900360780c0b1074a8100c0e82903900181ca41004410821140d80007a904541040a80c0c0b800e080d060792014040c002c03480c0100d000400c501107564070400c640070354240902c240035500d0001c00d80030040503681403d03000308041c116004407101001c98036034810400d08401d8103c2110601c200040322902d144101d07040fa0340d03821484025516000c0c1c07010140d03c5400040345519101e4401804840540030075010a074056491440fa64580000d0315a6010a010f101c0c1c91804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 865240413 1250 865239163 865239197
    0x16170f0117060105060315041517010605031f050618070906030b0306041a09010f06030f0507050324220501050702100b0330040308040911031e040201051b160e09030a 73
    0x10010b48001c9941e00c03c0da2700000c10721450300f101209908031000801200360f940d001d0603201c600202100003d8003a0074005a200f00f465030010390080c0e8041c0203143c2c0b03403e4004488824401c1610580b001c21141641040341c0c80c1d00d806000d4480c80154060030403414903540301d4104840c140b6621070694200340007d050f05000754428084801401c0341031120341c1d62070509500500c500902a1100e001d01700c804201420002458048030034450080869040b807410310a07d00903010704241c01c02e03460440100a400025a2200d4003a401000005540e0806030006881c08940342002e002d501d00f0010011401e83d00414442c041c281c8400d0004d0190386102061003c086c2c8a80141c403102c04081008824021900045d200391024400c080000d0380e03211403500306274001150044100c61104103294401c40b08020f08a4010f44103041a0781001140500c20b8601c0020030450320f06540200c1128641d04a50035001008000d0f0068a030701500308020440e469218a0303c02e081446159042904900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 865241663 1250 865240413 865240421
    0x91b090f0c0f0f040306060605131a1b0c010206090c1315080d0206040308130804180b06031f0909050c12160b0702190501020616170f011706010506031504 68
    0x80d8100c00c0ca9990f01d0300384040902c950490301003510760514010b030200c0e106000e9821036480301002141c800c10980740031911740801016103000d02c007a00050115444001807600318240e440e1106019125880c80200020f15104004012446550000fa184425900d46511140c144e102503c004a21003000c0403040c59420002c0d0302c070349028481e100f8280c81250f0f0108079180110b209035900d04154903840043c2d0700420b00c06a02909103c0200420482161108581900030780c4140303011801e00030304800074070107800032202c80342007048000c0400107000103c10300002400307019004100c0c0301210303200d01d903030b0f250010b0180c1d0241d005098400d40c040010040c080218269528807810152510111501342d000aa02240200b80b460380844c580c00c2481116020b4800c1070340245150340d2604600e0501c0030200f20004d050002503001c0750b00141010482620900803500c1d0004a54504645613400807403130301500c0980e170013060052042d9903580040725008208072180c1102d0301a8040010300034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 865242913 1250 865241663 865241677
    0x30712080c0d0201061d0702010b180a060b030405060105040b0a0b0301060905100203070312021b031204030806090106021c03020f0d0f0f0b0a03170f04090203091b090f0c 75
    0x4100100050810040c20100426045000405507120094406001d0307003680c815001d0841c020302e503815402019103036503131147d51220312840041200310181c0d02013880d84410000b0326036140c5854003000020020707402010024111002c0c0d2500d10700d05038850a4a1b0135060155620540e00c424606400743c2d00e160a1102820f008030103150341303594801c400352660301284600c0d401713041c04580070782c4414004016101d1698042d110074040e0201c07402d0f203100a50000c502801d034000100100f000702c0d5020005032107907551021640b1014242803d02800d50f0000500c0743c0d2140442c100107001e0f940d4007041181ca0400d880340303020000449103030150081e00030810205c8001c50045031480c0701218a0708000c1c0c40c051003a004100202e03000380c1c24001d0754207400f070352034204620300004c100007400741580c6c5220f0621501010b040c49403c00c1b10084a91160340b02c103408035004824011620005d0102c88080300f1503244d8005181d110601142c0c0240008020b204811000b100190034002824212040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 865244163 1250 865242913 865242929
    0x1060e011d040818060d0606030506151b12040915051c06110732070b0a050f1306020d091202100806130507020706020709060b09060d0b040c120f1a0f0307 68
    0x446100e0604480103244901c80c08c3d000a05010105a940c00e21482d0040d2044c01003580629002c2181c01d1040941c40b9901052140d00c140d1150040c004280c001a2000d06182c2c0404101d40384902c10680e0b20700c945400c00c521400301d100a08012108204460300115070090021644480e45591166207028104014150414070b000041e034401c2c07028091020b49680107201304a10f141c5d002d16981d610010f0090203405102048401c8556005401030084c2412116146180c5064500196090a0341364810b00c05a80035117003907180c0c2904015180050a1f10752403510b6a81c5085e000140301000b129010414480c2440c0400c0c45da4407000c00d003060501c2c55582c140102e040010000396124841c0c81810018024001f0100e400c610070300580d000c0301c5696000c14207025024081007810b6000c8051144915500d505452644d180c1d03018054240b0340503241d00350003121920f45041170f906600204180e0509e0111360001c080400310303c4055021040d82d580142c21420004a81f0b413003500c0c1c01c100a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 865245413 1250 865244163 865244167
    0xd0f05040914090607020a0b39040807080a05060a090f1205090f0415030326090d0f0201051e13210e09090a08030c1b01060e011d04081806 61
    0xa165800b01c1c0b030719004028000c1124942d90360100c0817030f01e4504081005055100c0c0101054440500c203040c00019520f41c7c060a188070401803908440c0341c407504001414110200c1c08110f003000074041ca000a01d20b03500079000303401d940ea0b91a5104c1400816661101c0c0d03039041d186080c001c0d803151500d1280d0b4000b00000c40c2c0b070901a405045174008848161184a101c00482d01a01b002d000d0388400021880040f554581140e4068881e0358001c0040b89402410507504403550141c1131059004842070005407a01e04c0700900d006003203007102003001d419681004180400704084110004c54110780d07030146c01668403010a0401045003c0c0805840f450041c070700083c5401815500e140c0d1540642c40d0354230280c1403841070003500c60301101c03000710a802041c2e02d58086030300340e002580e00c000000e80d054039103241507142c040084460a80a20359030755a00c400d1007410b05034102c0c2409480c4402503038002c080c101c4042c0f890b440008000501e1600003040c101da4210307802c022447d903c00c008001d26 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 865246663 1250 865245413 865245431
    0x207060c0207080615030a14030c0307030306050307060305040b150102070b0418051e13020103060f17070b1c0f110f0d0507080105010503060603070e061c0b040e0d0f050409 76
    0x250b55080500941001c1d0180710085071034002c90241c40c01c400301028018001c41d200320f44815070040100c440146050104001049140d1014001800304078403d8500050325810001850b24000709a0003010070316183c01c2c1840301103004200c4540c5d1007008580d05007461082000100d04080d00c550143c00561004140443e0101f401c450f006000f200d000b100f0405596400c00040d40381c00500c1d03000016241000c046440c0d041c601c1c40d9007a1a07801810003184182c0d90300701d550a01c1c0c1966000c01d50302209030040d0301e100f4100f40041c10040503610421414440d4600d0391512103840311080903902581c40c3c0401e0f4030202e1a81001082050284055885191590200259602640f180e403d041d14080004507458081c05920313058840c1a51040c1c21a510b1000b031203002d6002810039010702c001c901c510031080da107180061030b20000e500c4600941c4080c08686400380c0301554000c0d44154101810342e0914030000a00403455403042ca46003d240800020a654511460300700c0031440d801c100c081 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 865247913 1250 865246663 865246667
    0x17150603070e040b0f0d03050d020705060a0c08090106030c18060f080f12040b0301061103130306020a0f0e0303030718120305040612091106030912070b0603060f10180207060c 77
    0x200e000c2ca02664140085a010420080d003040307038070441c5030701005444000000c60321860107000303841411240140b0f041d05644070345140503c210b4648101980b07801070a191107922440441d001302280c3c000b40500e41c11070f560104000d03140d005454200c0c0820004440d805c005400002c000c1813460b00eaa801c0503242e403c0310742c90700403204004003c3e12402c601000020280c0e02203500315880c82074840d040d82d0030414110b40748180001ca40d01c85d88018840c00b0003004030202d460008600c81c010060752020000f40281110203107160b40740c24003040d0701211406132408011030707500080500c0c0644490240e20008600d000041e04095050b402e90040b03e0f040540000040040c1d031201e40b01d040d504441d4510700b005803807a8241c0100a40140f1a801409040100203181c01c81040001da5480707052040140f04150045041a03031946005003d01c84079003002d0000c1a009244841c0d114554501130000c01102d0310a8890308002d4607026070307d40944112a03041c0d8000c0ca90040c0c0034004200f0081d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 865249163 1250 865247913 865247927
    0x4020a03022203030806011806030207140d12060f0302130b060c0a030804060515130e2518050c19020106030b0112050c010e030c04090812011d090d1715060307 70
    0x8502041c14017012983c0c40d801130180700d018005020140c645981409012000780d0402c81c001c440d52000941584a80041404014203c61181e624803005010346842c203000d6511561100c0d050754040c001c14400341e11850421700c1404154103000ca035120300c0e180403031541d01c200d52064203c0e02a0900010406a005c0d84550280340900b20600c999240d416003405641d00f80f01d00c0550081c000e60311400b0344d812540202104010171002c1e150810024080c007a070900600e884000d003020030758001e114900000d0034818055218102c20081031425071610b041c140f2805c0c107201c0030300c1090260300c1f400038802d401c800047c5900032218415540c0d81c290f08103064882130000c07581c074015654405800c1d441100c101004d441c00070010102d01200c40140802400b50110540c2c02040801850800b62401c51440303009041c0c0064003400d4051341c04000307070000b10161103402503030404541503c1041d4029110052500c1001da400c480da203074050018203890000310103581250002c0104101103403c030b15 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 865250413 1250 865249163 865249169
    0x9101d060912062707061704030908060109020c070b092202160b070f0804020a05010f0314090d020d02161a070b1542040911071505130204020a030222 66
    0x640280a00742d5046864a0310360701d00500780000d440c0c40f200c0d421f034009044102d40280c000d0428901198481c100305040c50400d1f000740c3d0b01b464000680c000c41080c1000400f00418002154600308280314000404003040c2620a5000c1c0f01c0004000f925500b0320f50440b00807010780c082c5004601d0840c0b82140300342e581202c038080425420125118513901500ba0740e4072036070f802883d01300d120b814080156405058204881c0c1015503076a00320502409100102e406617240c04020042070180d14002490b2200c2c0e283c5500854000c004c0215085038210340d80302c2034440740703404010200c154410801d214000c0610161024552100b4040600741c0c5030240440c0000650b41d260304131501d501104900e0f141d508030b406403412480d84407208440220b0100d91301900031030504d03140540c2c9070b000b14250383c1e44200c01d400c003a0001a9600400c404205046000e00400c002480350380340291090030001020500139015039000210040d100340b01e0380c112015410200030181501c0005007080050040c0c0740 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 865251663 1250 865250413 865250461
    0xf1b04051f260114040b0705040e06063105150f09090a0605030d0203032a07020f1908031209150a0902030a0c08010209101d06091206 59
    0x100120701c016080c00340407580080c07401c0c2015a41441d000142c08181500b60004580c0c6110070740c0300100003401e0154480104900c0200d00490409091580503820040d041e03100340482000200410520050001d902030811070300d980d113440350106984201e80300f08500043c410350107180c68640303416010503001a143c099800e00c07240114621f048609204d42140340b0110281440380218910344030040c80e6020001481c04180340d652040401d203030228640010000d6000801000450102105503003881000c1111828501101d958101040d10603058046d000c2c40b403540b1400d1386c646071910100034036034405501d01901d43e0398035a03898803030304503002403d0000100d60104004540000e800005001007039141c8585c1e0311481003110003480c03c0e000c03c0341c05005204d00358000c9101000313100000e150210002d80e0750000001086005a501d40d01d0750705008003565408209000210080c40d10902034031a55542d0040300001950b0100d101c00c00c00c0d01e0320400080002c132292600850340c11407000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 865252913 1250 865251663 865251671
    0xc0f0705010e1e030f010203040b070e010915050a02011104060306140f3303070509030c180a0f1b0203070201080c16030c02061309200711010f020f1b04 67
    0xa80c00444101d0005a1210b074024101e4400500300000b4442c1541e4540b4000c0840e120008811480c0307080e41c108079425140d0040c0f032020455010340201652080640902c0e0105245040c5800d041d15401031001201c100000483d4404d0500d001b54011070385400042d0000da2544e54a110040241c812030181054400e80301491144504004002e8580000300514483d0f02d29044140144103c91180c880900ca09040007540180721100d0021801030043d951420303910510941414a000c6c0025501c40c011a0f90705403040c5506009801c00b0b4001c00d201001241c200c00342501c050150003281c8542204003408901941030503000401850101d200fa26421060307900c0c1c030902030a5028411800d0270480500ca440c1d030000c0c0c45001107441d460f200820f600e00307007600c00d0710240d58004c45400640c046a91070071402c1c1c01c1c40c1864a200c3d503000c1a40c045500d041c101d5aa481041c4d504941d003503050020803148440c015009000e501d41c00701e0487c04403414202c044508d01ca55140342c41003c1d010b00d1030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 865254163 1250 865252913 865252919
    0xb0901020f1f0c090e070c232a190f0f030c03030e040207150509060c09010504120201020c1e040b0d0807111201020c03071101081006081b0c0f07 64
    0x841c9952880740001c0d08a24005038404825000e042c560340300b0820014005804100d02c0c0c02c1c4402039000b180d050b40c4000c0c40365000c2c648000c030f440403468103e88239003e4110070305513603900007283c03104981103c00030140940f00c24000c41a8140b0100e80c0b50b031008060240354181c0e5048080001140d51801d004246581d8a048500320110940400b42180002c0401440420b0007864440000c00000c0c2c80180740041e141c440d02c0c94900214043c0d0760003a01c401c02d000c50b002e01009840d0300140d0364403905180901e003a0000c0d00701d00c600d11070740c0c100d5002d222094065a009004010b640c0307901402099080e810200501700380c0720f81d0303051244500d26042c880c100901b08017154000d0076a10908082c64000503488842070b07280c45441031584526040507501900740300303001a0011002480085071100c056261510510300319100e4581044120003c20904804020f070800403a0b509081107074103900c03003415038030030014004004000c090000070091528030002500e01c0c0017180d100c00340d8140c651 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 865255413 1250 865254163 865254193
    0x120216141612050d080f010306020a020709020d0e10020f04090504021206191b0f0813081c05010509040c0b030c090604030c06082a0a11010606050406180b1e0706060b090102 76
    0x601501c0d0700107071b071014400510010303006a000b0702c1c014000d401141c1c42075548442c0c0d402664002c0c103d29001540310340601c807100c6020405446000340350070042d800d03c440500100b1107400fa5100308201e468546001c203040d9201e42e40c02d0228803801206450035031900f040401c2d00000844c003a645490f1610a0440d2101e0000c030051001034019501c0d860500100d40c1c0417580c03100c2c080d100203461003044400c0e00000300960010008540741007026124481070804400844e14140d0249002d500914100000104c9003440d440558100b241059282d40b2050400c0c0050300408448030b03001003001a0101c00d01c02e01c25410f41c02c44030107951740ca100390703240388940b141000402601243d401c0314400303940c10005000e015003070f40e0f121441d02c1048000c0300391055095820303950000c0d010410000d01070142c5580046850010140d880c440c0c040985000348855461040844220200c020b00304590a4078045208544500c0e070050414840c05440d680b48401c680c1c000c106d9540548520800c001c0040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 865256663 1250 865255413 865255427
    0x1121202010615050d0b0907020f0c03010603050309150f0f030f16021e0a0204060e100501050a080105091e180115030203071802072001120216141612050d 68
    0x7840d0300f203140d001c1d546080c6054a650300b10b1203468803183c0d01d0f51b62566541c0c59105c42c4c00c0c4280d806a0003403003445402c010050802c0001c02303803140243d0410343c00b88040f070400411103e01100603100138000e07020102d91240c950041c5051044508000500c00d86554080400b540c09a41d14500707440094540e905000078407101d0741e01c004d0141c2c110300e964035460b103403d40d250b020145142041c1d44108645078009012502c2c5a00b10048020712281030100c101c41c50790b05440501801e0030a94a841020b0700050b21207001480b4040c4504010070010304c3c0004d803000c1c22140c1d016000320350a0b260400440c804a0300000c1038582d0441c2d840c1040107018201450021022644c01801805a0354144000c0f152040e8410b084120311580812040c00001c400010034480b1118038111006010310b03800004004080c210b10f8031002c0c50043c444070b45982054401c1c4007010343d0060194400c2c0100c82c8116040203c590000c1e40350006040d000a90115415607081c40c051180040c0d0324030f88003c1c407007a981c0d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 865257913 1250 865256663 865256669
    0x150203060f0906150a0507050d0903030c06020c0a150b030607030b100c05010905250f150804060e03040902120c03090a0b0a0603051209040c0e0310090305070b011212020106 76
    0x70948180492a0400c0c0031082c0e003050b400741131090300c0c0a00c07444440d81548074846420015600182070000d10209000310002e040161410a041d02d00c0c54030700410940e1078680240056500144035200d0007800c000c1d135104540d1100c90340d00d4041c109a003000050000f45142c9020340035034000150454400e01c1500940135004003808580380642504448034407030101c0490b1159682c840d61804120308200040b485d00c10080400350403a60f54007510041c0115910000d180d0004a106101c00c40c0c5080180f5100f404c10724001081da80c1d982490006054156004036680c0000640844c05003c55002014100e500019210442d203410810305914802156041c103a84c022403404070001d12102d06154010500c880f0114882c2c3d02c1e0340740c480c1070140d60341c0201f09000d400511940281098043c01c034950006003009103080a02101094035003600c480b580c100255160540d00c02c00d4010425075a030320f5002101c080482d07850741014401d544100d0390540707042104c03920f02c9980301d20502504003a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 865259163 1250 865257913 865257919
    0x3033609090303180b0403121a0108071806120c0207050a050f010522092901140d020f0304050c030610211505061c030503041712090a15020306 63
    0x19151500c4444030003001071101c101c007015107030440f0903200100289041203150242e1307500c100d6801d00740341c0600700710b03201e480e0156640d0600010821a034400454025210400c0c200141255100344045610746108211381020049110703002c43d40301d81c402d4841c082c8001c0160204414000b40000780c0c1d0707461292040ca0b80c0070300f2844040c030050900c8503585002030010b0502c242014403030145a2240c80300742d1011403c1ca8010341003086001d0721030064403510560403d50f5032260403902d030022500d00e18040940d041c01082c0001d010080c1c24082100c0d07034050681d501310b4656241c6071007000c0a90094070152414480d810b0101594540410058003c030032503420421070502e0071051411240500c04803007c084040010480460581441c4a0211508040014003840c10070200064982c600107610f03200071940207100f0000c0c0c0c22030216504150820724a19490102800c160054400c130004540b411150505011032240001750601c0000e01c034126481c2a6a540001c18080340400c44203268 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 865260413 1250 865259163 865259267
    0x31e04030f090f1a090f030304170c0109050609121903020f10060803120402040207080c06041704050609040b04022118030306011209031707111218280303 68
    0x7480782a44c0002d01c2d03030080290030345014020940020b41141c201e5840701c81c0442c2580c80b040c150f0303c41804461400207090804007c020b007044007040c50360084c6001c0b07a000b03c1c81e45400c0c4080f0b102c00c2220a86004103600c581c01540c0d03075881e000351101c041050885c0c607481460191240810030f40240401e0310b00000066040400c0c402c018040d070b4074054000e9800075801c2041d4400304030f40304000d198202c180d60081c140307401c0c240b41050746603205200e405030400061000f404a80d4443c0200c1300c500d0000c84020071803c04000000d030003813190341d11241002120f424040c065407003034840b40f4495100184069074504150560540346e2004172406030008004e14040c00c91a1020303403001120038000e05c1d09240c240d031031514010140c84203640b98000316406940c03414180c0c4007000400501c02ea00d10809003441020fa0131070b00400c209018052080c82242070103100101c14804c0003285000c41072103e041140c1e81e0070090501c858481c58808a200d62444078816501c07003100c441314440300202405 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 865261663 1250 865260413 865260449
    0x4150306150602060a0e0d0c0c09050408030708061905270108010e0d0201020901080c030c07150b0a060c05060a0e0316060f06050d020f04110906130905011d0606031e04030f090f 78
    0x3100703170500c0d401c1149e100184140100740304a0381e219040c426442403c5555807400c100798081c1040800031302d124421001c000301c4a0380c4241b14030f058001c5540c00d43e01302c642820203400f1303d420f01d070490050300e0718051840d000058000d81504440300b0990001e003501c1002441c05000c074282d104602500d4003040c04039003c41c1c001000c000c000c40d4400001d05595040c0000e903170300c400c1c24003103200721f10100a844041e0440742d440c180010f1030040100e8181070900d003c003a43d985c0c2d211000100300c070800568540f0140c181440900c11a0203c48140142d03500c42081c514214004050030004090f1080c81c0c0500429036040078584184429001007806142d0f628400402c009450300c00b941d01900d1805000100c03a40d103400340900b4441070350103007200c4076605044604c0110f40c6d050f40042c80c0c4103101a1002030001f05810340d20381010096521b01e50340c0d0394083e00c401804400e0011511511080c404003c00e01d0b078041c112034040d203c2556401030440e80c038454145904c1080c0500000200040009 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 865262913 1250 865261663 865261667
    0xc081005011407050607020d02060709081203070507050f07090605040c020a1119060c0b0c091e0105040b0a0e12070830120103140d0c0204150306150602060a0e0d 71
    0x44031100403489072545414800d07521315003803a00540d81400907030700ca410040a41ea40601019500900c02c2c5441c22410342b40c4040780c0d40c1d0b654482d480b00034040000022840017845070003260f80032034010301101c00107500c1d4000655a15011301c05c4040341d0b40340020104003480c150042c14003003c0e03640c0c02408211690346030307001203da5003200703140c1c1f01d00103440380c110b0641da02c43ca240050501d03446500404c0418140403198031401062620004410442100030369a29000082c50480c0115071036075000380e860040c1c0e002c0c0705a40000b124880c000c19403592096200709144152601618403056045c22081000d5881c182400360a0b22500801c421704004002005c01070211515171701c0182d0300440440150109a21501500810700d00100041c81030103a02c0c150b0300200c06071040141a031030602e0000818a40e004e06000380710703030f4858a41c00c0c0d8825a051041e8007031608401c0800c5031181c0c0c2c1d560070308415024410301005d405500005400000203104518400c41c07110080e0403035092100003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 865264163 1250 865262913 865262927
    0x7030f0305090409140109031403100b0d0e2a030607020705041a0607030c050d1407080304060b040f060603060b120412050c0d05130b131e270c08100501 67
    0x2c01c907007013540e41c2c400d003001c1081c000744844072108441c000141c00301e0508006100580d806403800c02804104244602c08000c882540c08881c40303602c859071a410401c1c180000781500851254003403150070303180c0d409042000c00c6d28980c00814102d00e0481f0790b0134014541c56403802c450350b00168006080c200701703500b01340d0004d41d1034680c06803024907070003182c80c00030b12540c000010a50003d0180e040f001c0812508006007038a10f080c03820441010707065880030086ea841104e000802000c404404102086016046120f854900a1040c40300c2090800b405009040c288501d00029081040000310420088112a62100c0d100e004017850b40d15a1144083c0c2d84200120500f080001c12203034014620602c00c141d08480702c0d555030b40c2d99201126090140d50501c0d0810042c521040000700042e4145580000445200d403842410883c0707042080f02c811900c5d6071081196480340c5050290716001150a0040d441000303508100c3c012034440100e54240c0100c5e9044141c1117000d006011079801410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 865265413 1250 865264163 865264177
    0x1212050f04050423010e19111611030615060306150415090e150d062406020601030b010609050102030706022a1020220512070e0907030f0305 62
    0x500519160703641c00414100c9039060124400040c4e40400d51039000762603c0101c4c01450311040751012030601540a6860314150201190140e1352045a030800303803d0301050f20390b0701040320032007500c182c8242401d20014108406941c440d01500000a01400c000155070040d81805071180b402d5640d0b200074002510710f00601c50043d02c0e010b01001408141e03c4050b000b05219a9541d201c09510b040311000d400207010f4a1001c0012881c1d100c00f80c40e840d0000c5100d031841d08403102182e2401000442c40c80701c59070102100003001d155a01040e001e80006601c2d040741d10840d00d04445a80e200c90403251220b81d4028640160020000c4e02d010070703586d80103030032a504820768090706a0f600003902c4003d402d10200f10340c902d4008803100702028280b807107800c03a94007801c074800802d41c41c0862030058034807a000d0241980c0c609015a40c0400012151441c050300740604072038030880f641251180e50303420910500d40e0240d0f160002030314400c1d000c100d00040f41da01c14410f0099a00c0740d502982d03a504415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 865266663 1250 865265413 865265437
    0x5181e030c0f0304061202090d060b0a09020d0b18250915030b031b13020c010e0a030305040209130831030803011e0518090307050604050105010f121205 67
    0x101110501e4a0244102420500310800455a0724070f4904007810b40c840207a84039100c01d105205a0a90391188050700500c184d1005000030350342044030000766504a907030030030001c5510115002140224a5001220243c01100c40700041080e12a06078458001154400305940b041d080c44d2201caa1120b40114030711040d81000e03034501e134540751b1500420b0400d403884070000307448801d0310078142000e000007280d07848401800403800148a010400ba98107603c41c401903103900060351b08040e0001c0d031000c02c44034404030540710f00c440f803814000c02802082d18140c0c403a0754403c011070f070130640d1140e042080543c480103031810103040410000c076144903110f1142c0050f0049001c4104a108032240c240694460103c0988950600008000d400841040c0c1d07448185030341c000b030044d9610611214000070f03206412072140c7c0d4074500120308500400308010081c0c85040284401c000707064020358141d90710684100161a40e802e8603040900d403003880039003424180c0c482002103078400d00007070201d84901 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 865267913 1250 865266663 865266667
    0x100902030915100314150a020a020a14070f091a06040e04150e0a0b01060306050f03100f060e04050d12020f030a0c0e0d06050a0b01030615050a17070c0605181e03 71
    0x252200d0310300c1d0745c54007040a0541c11003c0c40b070680e81d4103240341a8202e12100c01c11410080c611501943d41c8074200d10240c03071071903581203907220384074200083d1b8083c007200c0c00d05001e4143c2e95188203028140d400c075907041c0c00407075681c441d0381414540280c0301191020300540806440e1611509003d072500f41c0440b0240d5219141202d00c26800c000d0794403524400c0001036055854454000c088078103d41000d4450950410541180e90f070009443c00400e000050014483c09000502c500500e81580b155400b00103d03010842400307000702d0800c001d00e0098982d08417a1083c1d0ba4004200d10601c0c0b0003107103414060021402c11138071a4465902d01646040040c0381c2071030b030000170b8810f004401048078161707159010002d040c01c0c540580c10700300300700f03007824400365081484c2412144040a01ca004002000c942101103600c221855030181d40620715500d030703504182900800e480d409410a80d80941800041007641d52410540d000c1450080e01078034106000742600b404568811541484501c07007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 865269163 1250 865267913 865267919
    0xd0f0e0409080c1f0501050a05063405060702010501030c091d011b03110301120803100b1209190b0a0c023a090303120504021f030510090203091510 65
    0x350100070092440004000c001519000d22462291072107001c08030038150170140100010345480c01e030035055500071500c081d04c9103410030b00540e01c590342001e0103882415440389030f03c0e410303407191400c0d03805e5000c1c1080d14101ea80e980760580c01d84800b032100400080829600700300b985090380c040740e030f502d4400c00543c80d140010040c490a40706c803811840222070001805170b0206425203c1c0039400d13408200707814250340c504840807502d04803400d005083ca9100100065440180700c90031005428800100d40c0c03036180c038a0281440c00e000300e0740000715110300c4240b811044101090404420382c4194007043c295070b030a080c54098103101510405510912078000580800705040200304206040c0c00c002c4000f45000d5400040180100f02092100170101031010030340c0041e03505480680c0c0f0a0200c1d4603110381c07022132407880d803007003041004501003044004220b41c1a04402d020f000700103010800551580c030385a00700c4c413081e1099151644501c00800d8650b00b1228542c1d4040f865280f4080311984d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 865270413 1250 865269163 865269173
    0x501091a060a0b040e130305121014012c0a08161a03060d060f060504050c0d051b032716080601080d120f06080604210905030d0804210302030a0c020d0f0e0409 70
    0x327003502c0c18800314003503400078807901001c1c3e0710030b1604290074a030094000c2c42c2540c00c0840300c01e45504008114006034084001601c1e003000e610300074124041224951481000e403043d04421900030070107210101c107229210140b2090075a4069100100900d642d000d080c2c0e629030081c901e480b1072080701615403000296682e65480f9251092804207070041d5100100300320304003210001040840c0d401c030500d80718000c0070b4048040e2503119401e4000441c40054a41e0750728485140c0c403054062a1007111600229030f600840c00030100c0300714100310380103030340c8460700542c840ca5600c0c07036100001c220b5048250010b40540104848000c284000210320303131503410243c00c00ca0112016a80ca041c65408641144a580c3c2901d01c244211f241921009082100003a1245000017500d01008900e00100c0c0900820642040010000c070800211101ca0040003070080c0d041140c1d4020301c149441c1a040c1c180b800810b9440c0100d0300c2c1e540302d4140205038a010307074801c1a400c40080d04159200403e000180c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 865271663 1250 865270413 865270447
    0x8100f0f0e0a02090a05040c1a09060d1409030301120b220803040309140d060b12010203131502040b190201020c0105010b070605130b0c070501091a060a0b040e130305 73
    0x40000320140030b01d69110300602000b10000780c510f540700741c603100410010075190b80a00d4151041c1e0884107410081d204200b140d2801130002039507100b1000184c40d400810713150301040c48058846201310180c0c2d00d01d12056181d000074403076410318400076000c0c880000c10f4050072a600000c41c4075164601068030544444180301014110b0314010000300f884107041e0802c0c11400102294810300c808045407401050544010f60001003540c2d4417400040083e903508082c00e40ca9070000c00085489142280c00f46081450801040d10101d03c3c0004441d07007603440f4000c80302903030b6500f07509510340791a0102c990712400500040c001195401d02130b4142c0c052081c001e540c02040040221600c0d000c540c10524100c50b009400d8059034400c01c0303480000180c0340306820b540040c60040301d0b925201582013590144c1103c22008203c1240c403105104a44420741c2e4890050380d080d500410403c1c3c1b22035040c0128032883c050401424100000110141c0500c80c8220920780309141c09070412020b0312280403d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 865272913 1250 865271663 865271681
    0x10302030c0109081e0f0a121e0c02040e10050c0d0b09061c0305070818100c0c14060903010e0303091c140706060308120411030d050708130e0403050306090105040608100f0f 76
    0x741110022407802603400040c0420000c27900c41c0080e041607130640007602400c0d0300e00c0005c0c0980e0b02c40e04503000c451400c0c4680c1041815003403050040349031000000744564040d000350459607140455015440c18029541440b4100281850500b041014154503000740e008030202c041010401c00140058400700280c4a031191240d110204880c0f9401080340740d9442d16036130810040402691801309150603031000c1100c0610284510320000351011802c24401c010090360150b08051502c2c500c540001300640c86a000d40c8151900016180e1800021211041001d0f0005e803411b00448402c580b0794009188542c82410002002603590303881d805140c0045507021a840c10000400084c450005130401c1419403c60140040100c111000b0780035024840014003020408601c0024848142c0d40940207002c3c0041e10664074585840d0042c2941e01c1100c01c54054111040000742608041c0201c1003640c0029000d0701d801c2d103054009400804900103000e510b55290106e1000c958114400e0b2051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 865274163 1250 865272913 865272923
    0x30e2a150f070c0e040b041401060915081b031b0d06050f0601090e01150305180304080304060909060e0a09022b0525030813050901060503010302030c0109081e0f0a 72
    0x40b0019410a00201011a0310800c00c0d010b00d80200000108240d4025038410390040b0840841c2d0040c41c0c440c0c0c010403d0b078001e02142850412030031844800e8080d480c044a1400b800c0b107170000ca81c8031501d4844030111000c00e401d607103e04092001078403042c03002c040303412016000c0c5200504c03d403128415280705031000c54650700580240211943d10444400240800100184d40c0d07500d07000100f2143c0e003104420300201a6600045000411480706d0310305494481000c50b44c4071504d5090740d07034607603015100d080d0100c1d001da5000902d032140ca0244070100c0340124070116580c1c2e1b4007038032040a070042e210200d0f401a03401401641c03244100015420300510300020507210002840c00c185842c0c1070030128000030000b0303918000f0b02410808060141d9600280c0162a02c61595503603044900c0c0e500415801014400081002984100030b03504aa008070b04031283c88805100644010850340107015180c3c010a07110141141c8052a07142c12005e45000c40320281440c000d5076040c629011000c443c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 865275413 1250 865274163 865274167
    0x2070c030b040b1602030315011101050a0615030e030304080a0e1e010f030e060105060c0a05010606080a14060109030b1008030f1b0d08070c06020f0316030e2a150f 72
    0x209126025003c0c5602c40107402002100790070b0340e070001c4e40e02d0100504040e80c500b00104c030b055413a4890800c40f03801d00c02d000c2c024086424070400c8013018010f6405070031a0f0100070103842290783c0c03003805010082403028019514541352512941810703072151403280140400c0902c240c8607501c41040f4854826410711121510f44164000145100009041c12041506102090720048404516603045403001c0303540c56900c00301e1503202424580c0c820009462035103031140c00219550802c026521a2000c0d0408205c03040c100950146c012105491080c0059013a01c018000503910b8100300341c005c500003429106040d42c9200441c91236120800c0781c855160081180d41c40424042032144040880c000a00f41550380e1090040c0306a800420782c900f084144480c043c1030210980c100d603468140b19080315620701d0600c03018000b4809030f504402c00640360981c8000c280c1070210380640c04411002c4071001032046420544a0704100710380316175024840183c140c80c4010001d00800307001c0c20755080c4136 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 865276663 1250 865275413 865275421
    0xa0f030906030902031c031103011d0c04030b0708090f0304141207060c111c230303070e010c02060d060e041e110112091e0b0c09030c1302070c030b 65
    0x10503044840d844842410305000e2104016540480d8103a48011458070860100b02242c10460242c0a0b0880350724000000000108481481c0d4605440d548684003e092042e120190403a4280c07090b80700107815030103001c0200d0710f40b5100b031180b035400c0b03462141151001103030021038070700710780c0a61b01000c04402c800190406d203040c0402c60011841d00100504186440c3c80300140010f040224010f00311004800644c4160361500d120300b040f070000f07180e54803448409150102e07101110045690010003914440c8400c0c01001040302d100d1a00384e80d4998640e503400006480024001d01e040384d04c080188074030030614000e4840d0340e0080088030130300d03003480c01e26050000404415440004489040b16081004100326011200342c00d2001e192114240000d078865400826000400603c92205009521000140d0f0320b02880ca0030300031503c0100980b40d500c82e50866109006610b501600030450141e95031030300480e18511003981003805880c200040c2d44054001800d6003044406aa13044140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 865277913 1250 865276663 865276667
    0x240a090e0a1103071b050303040f0b090c150c010f02030a02250302071202030c0d08090f19050d080408030a020102180108071416021309120f2a050a0f03 67
    0xa0703810800a4408010342c2d540c5492210702c51000030004418000400300c00007a4040b4548040c0c601d070380060a5035141d0605d46880682d69a1a44007950480c2c0070300b0101c3c040d140080780c2c1d0020410014400038501850500c041c1e000d401401030013945541e60350000d00008810f00007035108a81c0c4000050380c51071400c030382480c40b50070844070041d1010780011400c0000c0d000580c40c42900d80202d9001d0300007101c0d01c00a0b2502645004d016080200f00d045d4208002d403041c050640c40000b141c4000c0080c0036102401504170740e4100c1445403100b420001c00c4941010480040e219000f40074241c501502e80c10340c03900d154041040280143e600055009541e072901500302e40c402403d103400315150401900042c211300000b2105072014200117041d50030020180c42c5c40355a160f000d07007484021251012a00c0082100c00410707217000b8906400316404603c1414401c2d10302e031070341d2180000180d0141d23030800fa00112100410940d2203454002c0d0200d14100a0036030410320409105c0c034810003520300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 865279163 1250 865277913 865277939
    0x70204020301240f020601261504020a120c0302061b0f030405090a11190e10050c0d03050915100518090106060905010512040c050a0f140607080405240a09 68
    0x11001c10060680400d1300750f60790204000381110001c110003040d5502d980515000e00c400001c12034a14400c4411100340241d458003100e12990080f11b0040d81c1035515442d550148004410040107199134041c00d000519210002d0420803d1202c0310716294800340c040f45140000104940c00300ea070003c101040240781070060150310030002c2c0ca09000c0c6005001e5004010301030320040f20f01408d00380c42e19918143c8141c0c1b400394030319401004003034001c82a0300c0c09000c6521034014034810f4000e50b400021014004d0180b94000c612a0000304030001500003009219000608401c492032189980001d4641da640e101000807402d9569500f03150401041c0303d802c403015580680280002c4041c100a03907130304002079175400c40d00312001c540707180c0d5a0329004101034010b8201c1b03a0302169a10700896043d035000c90701802c0e18208002c8085140c0000204a0b10b405151402029120200070511180c24420450b101044800422000d100030340b60403403000f6041003071464001185e00c0d20411400a025903 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 865280413 1250 865279163 865279229
    0x20c2b02031312020102100510030c080606060a050711300a0b13050c04050106050903071208040b0a031e0b03190b01030303020901020a0f0602070b1f0e0903070204020301 75
    0x15468107840c5a04007100700b2961082200c500d140510302425a402806181c50041005130100300619020b02a984000c449010640c2c2c00301013410b000ca1407200c005901c50003100010803450502084090844140e4803941040301c0e580540202c50b0a15110311b84400c103401d03030300d80c01d02000400b440544403240c1d0b074009030080c0681c09542a01c022840380120141c02218048a03280b900d200390034894030344070805c0003180e0040d00d02400014126841400f4018000e0118190386501c0d03aa90308000d2a0805140c029000ca07004000c00c02582c01c03150010903113850142008035010070b814080040e9031004091180100e9140c00d00c0548918051044030344c1d1020b075000c8040b00c00074039101c00181200c1400018281580005c1c107480303036030007000008040d580c4541c0d4407070102020b203080d1004e90003044048607949000c0d00421521000031000c02201e20030036151200680c64120141007404000e844e041090108100c40350140c0c607240000c5000e0315028071503550100e48841888410300b6000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 865281663 1250 865280413 865280417
    0x20a03120c14150609090102040305070e040512040b0f0a09180b040b040212060d020414090d1803020f010c0c180b0a080609030a080c1c150b0427020c2b 67
    0x3002d000c0f4035000c1c0da59280c005109440000d255582c40c10114020b100d070343c20261a0348620200000c100c0074081401d0b20030f03403280054800c410448110b405181c0a00e018601d0060428060950411244805010006524500f40071340c2d568510010005081042d000022652185a10500c030300f824041c3d40081107003550110b242c0f15500c400200f555402901d00f512030780e40c1c03184590070366855800040d10181041e0080e4080d0818100082e0388010480348480440c401b8400d5002c008442c0035098206c0344c010748460300c0b0100303c10045810f10304040d011a81d4001c031400c0030401c0802d0680305d0110010b11480090a030f41c5071030800103c0842540500c8013a0f004800700050510040b05960310098a0704100c0603a40b544003500e0b8a5005040b02400c40000455100041400c0c40e000702100161702402c1c440042d482c0c000c024140d11030340c00f5104030750740c2008401e005201070347c0c1c000c1c009032002000142030805440d4051305000d2070000441e03046c111150300240f21340030101d0758087c5d81d00358 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 865282913 1250 865281663 865281673
    0x1202010902240904020304060213060809070602011802040f110a051b01090c030b07172d01320604090e1207020306060f01110109210804050c0d020a03120c14 69
    0x40e44002d510712032040a01e02458011020804100503601601d1000b983c2d580d0b440001600c0e140c0050010504803501c030604d11641500003502c1d401880362280d00001c010301d03050140300c2034003480003501c2c18400904c202991020320b03501b91076040c005011101841c1d50f4643e628644032110180c0b00b00e00f000304a44991501ca00b002c00504241040022030344e021149508a580e00c040a44401d20319210284107641030808008080e0450311680350020f0000d180d0342000700c5020352110080302c0900540f040c46800d08000001a07041e15400c004c0c2d40a61508a4100124040130583c00e401961204c10419110319070600281814848a2007800e6600d0015041402e5074001035036651024000c2806400154003900c0c499200b400c1007550000c10700700a0100c1911884e00d500c801400c48505680d8048201c0c00d10a910321841245001d19008002400510450001c1041d98101d16000f240c3c4040740800000c00195031460010080790151140c101032049410114200e481210f2900096041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 865284163 1250 865282913 865282969
    0xc0a0507020d0c081c09151803080315090106080702250503030d0f0b0303130612060b0705062d01170309100822080d09080f040b0403051212070807020a1202010902 72
    0x1131030446491881f054030f8400c071100050003c0d001c030b9504940001d09400c4c0c00004000360102c0842c00c6140c040000d940c07c1c01c5681c0d844000710749100c0c00784d448800581050231846810310701c24010b444541c0903507840b20215562080040e1969102d030a1948a4948805812842040034807600b800d110069015600d040141c2011240c8038a840c0144024170a4060320020440410b07405140540ac8003a519640c81c0460705149545003011140e8000740c040e0708031800004a10360b021159036068908103030049900304403090034203c40c03009102d403981c4424003010343d0523030301c01009060003400e0341c070f83c1d070703110304191124882420201116841d2080701b4000400064040811100300012000300061480300514011109100d0382403803e1310048045404118203a4240041045a1048d0304546100126a44201080c082c000781071100010f40c0c00003c40c0240140d10003523000e00284150781b0070716401d940340414004401d0308500140e642d1b003258421801c0040c41d000200c8030b860320b42d00790404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 865285413 1250 865284163 865284179
    0x507020123100e010306020d153210080403021501060c06050a0617160e0f04140f030a030501030b090622060603120e09010e0c0a0507020d0c081c09 65
    0x500320201808007100e10001c0e8071102816190300103002c900c5150225542c0d00e0038100c0184d000210910541803601c4040d070140d2080c182c00700122148164241103034481010941c210403041181d47c0700a01d9161075500c4250f440c5207841248070443d4580c442d03581418200285042840c3d803440305910400c0005000407500000440c0c50a070b805040800d05549a4a00380090030841c0e01c039010b80c0c00800ca82c225041c0020444800c42000b02d01c68000c50360344d40611400a071400d8509030011003016000c1804a184480c0503842d150201048a40751005444440e2556224036285000659224014000c01ca14031011940202211004040508121401042c600c2a10802c2c44803540081442000c00c481900020300079030b0010030301c40e81e90040c0034003e024582c03108500e51069148200104030801c031542d10364050106180c04501f030401d001410381741640a02c1040e68001e000c0804074000420f030300448405404028050003020824114a40440c503d03809071000b030200c3c9180a1107994 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 865286663 1250 865285413 865285451
    0x10203090613030e0d03050d0f06030f110303041d070f02030a080106210e07170d1d01030f020a0c02040b040209030606060a050408070825050306041b230405070201 72
    0x14042c1014401c0401c0034a01a81e0210480c00090b801c401800300d802c043c0364004000d42000300d52900c0511205a28000703030400c40300c95020040c815076507020700e440400d460403100c210068001c0c0440b03181c66155820240f0365882400128000b03841841040742003507101c0100000c1084074001942000800c0340d0241458605010705810862010103502c002e00c04156081c1c0c9546041004001011141d0f0025464591501521700752406141c0110800440091700030315041c01d40e0394001d4881c021092644200706164034031810580c6413120f080b64825988000c00c022183c6803280c018004a034418030041d02d81c2c4179a298400d500c140941b03645910046003807580600c1c1101c0a5969910490007500c0c1030140b50803452061180d0b0070041140e180001d10300803a11054aa800808920002d0136113a0303540a0040b140c05070045808180001c6103260300070b0200075146c00e80302d03405866006025025603540c4541030381600210700c8030564241031240715040480c0e4030080c01400d0284105100c61 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 865287769 1106 865286663 865286671
    0x36021c0e0f0a0605060118080c030607050c03040e0405010f0216030206010510090e0a140901020403060605030d0906050c010b0d0f1b05090c090402040807060513080102030906 77
    0x925000160307507071100201402405403108596804024000251800341072040e81d407004000040c400100f50060500c81d4010940c036142030040500c0e06001038003080510800300700c0400701c4080030048400b42d8056000c000a2900c643ca00a801003001081c4501514400724410381d0714010b044030220018060303070854074141d80314030401a810016888140200f075078403904200e41800b036a00954040450700d000600440c100ca28480e034110226440c41c0c040c2d60025080c030810100f441b4650150905030003c10035850b08010207051200701c3d0007180e040c00400306205280d01c4094101450041d400350851480918038540f0511003112400c040700d00c0c0030040601100f407112440c1c3c1c02c04032840207024601684803191180ea640c1d01039940ba54200350204008200d4110422044000b041c01c0e542e120b580c1d0f05200c070311440b603808917041101c04c1d0f40104280001d000780002c8060304 = true := by decide +kernel

theorem cover : BRFrame.Cov 865107913 865287769 := by
  have h0 := BRFrame.cov_init 865107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 865107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 865107913 ≤ n) (h2 : n < 865287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
