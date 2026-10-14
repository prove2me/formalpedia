-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1892
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:03:17.909999+00:00
-- url     : https://prove2.me/submissions/26cc8958-25e9-4842-929f-d5b309b40921

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 340107913 ≤ n < 340287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 340109163 1250 340107913 340107917
    0x60f01050f100e040209120109050f010218040e0f0a0302060a0501050609061923090306010e060307060f030608030301140405091f0f060b04030303090c171504021c05030324031507 79
    0xe09003042d000b0400d07c90280d00c0402c92a5500e04d0b6500c10440c050000d00341c003c076004000c0d4100041161020032490b4210344c480e2145959900304200c000080c025010403400e0801030b00d07107a0344c940c200651075581c101c601808180c07500f0004207513440c0c080c096840c24000600400e04066201c5648010602d030314000b01c0500800c0c00a0341c00810001c0440e004500001c18002d40358050507090501d4000103801080e045e070403034030070000c068a0008644c0c0485210345084070722445c203103205a00070085a0442161800000008154103400c40042c000c1c1460981e010005a65642081e81d102c0e0b000c0c52680308480340c04030315800001c1c46500101c00c1000500300004031650b8550300003145901c01d500460119441300d0000c814400c0b02d5172000c0081c00c402222140300c0820614480e181c942d56541c0388040410384005c0f8042d900c40340d24894003003824100c0170412202c07500704940c2d260011180300031210515103042c802e40c0006520b9200c1d0b000060000c100c0200580c1c2c0c0c400c1d05610040030841 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 340110413 1250 340109163 340109167
    0x10080a060908090901080304090f2f12070807120209030a020f12010203010315061703040308030c04090e0708070b07020105030f07030b1012110406120c12020c060f01050f100e0402 79
    0x3d1555030040e1180200320000040d543c4901d04030030383c0306584c1d10042c2101410b16100c405501440c0d815848407007034440d000080c80220119460411178011100c0c0c4821a0500d981001000303500003001e0350281c0c4498549068581116171440c0681c4607002d202074144c0c0103030540000504241c0160501d045006012a403404080340c00d5030b089800c260b0050b220220300d000031015440e030510901c00641030003403400c60713230201c503180d100c1d40c9229600c802405200f00000096040f8002e2003980c026116203002801000100c0360300580e58805401882e01c14051020000703440c01c0c3c084116270a595060315041c1c1165100d0302c00f03c4013000014a020140b680321214981281d546440b0b8401001e51a2102c58000004840100448001c80244070f603000040200748446a0054000d10b10000348180104000c001040d00300d400c642c8048003010410b0000c0352541c06240082002885a20360382c80b10080b1346c3e603035810040e410103032105140c5c02c801c603883c002c0d11981c0300c3d81045080e03200280000d8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 340111663 1250 340110413 340110427
    0x13030e1e011211070803100b0306091902131509090216060b03010605220606090308070b0603070806010b0d0e03250609021e01020d03091110020f06010f06020610080a060908 76
    0x3d00c2d0300241040b1460403002041014880303405114001030601084520b096142005c046000104054200c00326584180a42032210140d07030101c8045000e10710b013054665540d00001c4640348001140c0c0408034115001c041962030031442911210100004000803800f07150300c960004144801c180c6415549600380441c441d180c0e208420b610316005100110324070100a452002c650301600980200300300b034801000030a00d543c2c2610f1030a9001509040c0681395100002d15200c210b0b804005580a003100001e07841c44250090401c1c0b02400300180940240d01c81050f80741d1045d0941482d0b464a840101c00015030344600240c2614410341d00010142c4e015000100d5032040352031154403520140404c800c59580c148642d00825865040901a504a40d603030065414900c00009025030b14581c121010188200101c141d10780028040e1031155840d1000300d01309244a0107142c5c054071030800415001d002c0d946d09081183d4480d0701030700002c200c2e0307034850001c1d00c0c10080650744104240104 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 340112913 1250 340111663 340111691
    0x30c030c0f11031b0706111606030f02070212011b020604050303041412030a020706060603050f190603290106090806010e0604021b060108010605012d02011413030e1e0112 75
    0x40ea1642844003c00c103003490b0020087c043d605c034030014540d9400034907585090004448600041d81d18a00f8003299102085120310001e0141c420040c1d404111511640e107090010b42c00981c24420350801004040c01191341640c1d102c005a42c020440d600420018000c6201800002c070a00c0c244410741c0e285a40200120607160001d48110300b00940c00a00c139002c02a1324030541c0001c21440c2010700c510f2034121001c1c6012000109640702001146007230f076a03c408035600c030382c0c00fa540c0609042229920303002e0710f5900e41b801506605051407408008280d290155075008200d4202600402a9a00b44442d00030700d9000034002d960002e8090150450700003c40400c0c428409200340142559031601d460b4038292555640164180b2041c000d28500000301d9641401c0f0b04035410007002c0c44084001c3c400c070300604034820000d031025030020030b118900600c1070306540350502981d5040e200221401c00c11089985131844505030b51580300801d085540aa0b200c038244480040e0f000504000703601c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 340114163 1250 340112913 340112947
    0x50901032a06020c010f210b2803060c0504080a06020c0114010b031f051804110405010e040b06040b1f120c0e130e190c0f0b0a030c030c0f1103 63
    0x451000351300311015004031542e0041c58005000c1c594076050b085003100198841c80c8090f07201032003030000e07210942821992075003d5030380d420554081041010143e1000340070041d01ca280030440d100c0b81404195090b441c070840c103072030948000c2d5018002038440c0d680d0f1715000b5800310b034110b1995502d9038090945210410f0400d802004280b040303569903d407070700c4c81005001200c1082203c01241d2101800a1b4444c4501d0881071204d2020084541c0c885091000001c0044c0502640c011f051000118803803100301c0d0700c0c83c000c52061001d10056100c8004200503a850080081d4000031440380c0341002215a415510410405041c411130042140f030303140051790400c0f14140041400e134049000242401da40c0c1e4804003c03d074800b0041c042068040390740361130600d00f071139012540500341e140c21b0055903070b0100000c00c102c5100ca10415680c405408040d003100042d90040707482c000740d03824224064000e00301c1c6d030951917a440302418134200c400d5412038a0400348030103501c400d2124220350034040381 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 340115413 1250 340114163 340114169
    0xb1e0a0302030a0f050c0910020c03010e0705190302090402100507120e0a080307081b12040f060305130f0308090a050115081e0d1d1e0103050c04050901032a 69
    0x15025990345030480b410001c1e10311420424900b01c2c0707001704204d0a82c11313076416070f0203202d401c0b6950904801000340c220300d440c020b140055859442c1c01442c441c0f40000180540881d02d0a5460042518000941d0907910060f4400a500080031030006001403a001007003888103921810920709020050b00e07440650038181140c1d0010420b200c20001d044d00c1c001807814000e04440000f985824055075506010340560121800250002060741403115001e2140000c0034000103c0151110360780c00340c50030080f110b4403584020900e46804206028450400782c00b426400800d6400248032560301126450402070280406006000d82580040c8080c080c07401c82030981600595840d00b0310030070341c2c10104e042000c0224158007000070780f02a080810062950a00c90400425081440916001041c2400c46195204418000c06a5000403c1c826102940000e030f07010082652a02c0400c48103101d180511a4082c0d98500108001111140f451400c540d6010001c0c81340703001c02e21690143c0e070b2190 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 340116663 1250 340115413 340115417
    0x6060b1201080105090f10021605060c0d1803050702010e03100204080a14150f07020a14030d05180a02061b0a0c031b05090423030d090302010e030c06010b1e0a 70
    0x40c010042c40e1001d0241581100c07080010f410080e6030300f060542c1c1d030a0241000c0c0013031a00030885403210a1204900d82e00143c00c841512914075001e0026503440d40a9810326400d42c0c603200e5851959030000405050403075064403203621b00031050300155544204c00e11602d615129071801c030708a06d2194000340008061600c0240044600e03882c00c41c94600c482030084074194001c07070103120154294002d40e600060703510110b409ca500d030344404906042d8078a50203072600d034520409200b090000402028040150701382084291030b4034250903040c0b6a605061703c03040e03109810080162a1100c0107006004100062410070500c040d410340c00d2101402003a5184081158100144242e81d00c03029000b540c00c10748130755101d0a002c0062f19400006d403001c0c01c1085d05c0380407084801c9000c2800e1508a90b8202281d44410714101c60070040c2c00460710480c0194280b80d4030301d070080d10010658400b20b02a5000e84090303800e20304ca02840e03400c00381503a4098490201c1e04164201e41c0e400500e442d0b07000e9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 340117913 1250 340116663 340116697
    0x218040e030714030a0e060f04030501020304080901020c01020d02031e0405040e0102070b01090b060301150e040f051614030601110709050a020711030d0e0f13140105040c0503010e0a0906060b 84
    0x3810304080c091103000030b41d50703240c00401140300c2243e0b0050034081006c80450311191640524006248035014940000342198400070511007030058840c00703070098803400d90868100341c0301c4800498a40003001c1c070460140e40240050510703007140004003201d054200c0321050805035140300103820f0340c0310203207440e02c66540041e00005000604241501400301c840003406200341c3c0401044d9607104c140700d682110403000360401a828407030110a000150024030030712101c10750000090003840161510b500415200b01200034090141803418a001c111107c41801d50b41da81c0015a2031006010b01d00e1218040d40c58080f407000c40d24481c90f030241c203100d440180c0310b82d894a80442c600f04101000e0381700703a00083c019944194002000d0000000644451220782c1540000c100ea680c0f0a6444003004c0e0704120001d805000a11100d604070781e03085401340060304481c41d0558003480280101c41c000c02c56080050b00d0315006800680310913100351000181c0540e00c03d0280d01903044120f40a002800c030b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 340119163 1250 340117913 340117927
    0x114030a09021c030e150405040906020708070c050405010602160e04050c0d0602030f1321050c0d05030a0f020726040f0806070306210623040b1608060f01030218040e03 74
    0x31114200c42280406e55541803860310098200082d802140300e810303c199110702500d4100320242c0c058071101c641c0201c1c45900c81005150030810071a0a0148500582c0b8200001552034800200c40c44481c580e00e00705c4294a082200c06920290300a0041c1c8442c840c0780040d5102c0e8407000c005007015800350400580b01d0a0152440303400e468007601e072107209004804c000700417600314042c0d542e040a4203030201c4400e044c0c0900c1500c607401085072122070740c0143d4203280c100319084001103105442c1500708110014020840404034000c1c403001621034400014440138020760710904070b5200414000300c1e410710b07580710194501071406422500841c0c218100340900c40d601030080c2e00181c10503100512614400d2024030139001d5850401034134076a1540d18800341580ca95014102900815070310400a20b4030b401c14190311b0320152030030b200c070740140c14007540420310640c25540030302c4009241802600075500110060740210071481c80e4050200f5149050703a5a42c41001400c13080d004c083c64507452 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 340120413 1250 340119163 340119167
    0x1c0b0609030d021b010c030f080703150b0702040f050f061e06160b0604050103150f020c01060909031103030601080a0b03250602010e0309030c06130305060c0d0f0b0114030a09021c03 80
    0x301a4800070305011000c1201b4002130f0300320b1407a950841052800709010341d201503044000d030506401d50303c1c0f40a43c40002040000402d00200400ea000382c509028a441c148400c0c011540c1c200d56500d00180d83c0d4002c00d205203040306038400007054540380c005c0b002c110f2100040c100e80c007012040f800c05102400c010104144000066072003c1d04490070440c0e585140c903100550074401b0349100d07a01d0755130744070b82c11841142e40c142c803004000320008000c41511040c0c0e540042a034428154045100000001c0c0450300000072a03124803010307526114651503601401c030180182e202e2880c1d05014190b41d000d8010f000ca03c0c400f2446451110403000c0900e0800e0117800c507462100315104d1038108100c40c03031f00f03501d00140481c16484207454403a61544140e581440b14041500010858001c10060019204054014028031513031902d040050308100c103195000c40b0342c846040d41c003060480d44400c1548200380007a5620090361840880c0d400c019070f000510080101803d5009075140000b1642455 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 340121663 1250 340120413 340120453
    0xc2301020901080c19083408010b070c03030e040e0102070f140106080a08070c031401060302030715020a031215030503031f0b07140c0a141002031c0b0609030d02 71
    0x8013900b804a290803401c606501607000700840220512144e90082480980c1001d0062080000c14803141501465000c00d40003d440300692480082c9042002081d1041d0b01130494031501c0e4840911204946565001d4481c05101d458041d8004da0300e107a86040e2200c01c2c001804050310071900009005603038502102c1c1c2803601e68401115a241c00014800c500f00020006203030307074215903003646950003840c20100b85410358200400c034460810aa0554003015007100040c0c920840c1501e8034541c9516148500452040d5a400180e001c0c62079803002c00e0148200c9481c1d00705c040b20118041c8203003008032428151691080b51658000800c020303025030784502e06d21030204d80b8006040003a1802c1c2c49a51540510300001d007602a00c0e640c1d180c40d45504011400c190ba0300034000c2046503a403040100014055650614014000c400907510304600c0841144d85410701c04007030307001071100c0c1501a4010100703158540e0704098104031071061660708000400a000c001d50040226201000710004a0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 340122913 1250 340121663 340121671
    0x417160b0a020709060f0b0919030b011a07110d0516060509040608011107081815030108060906010f1703090406031b090c050706181203050703150b07030c230102090108 74
    0x224640304c0c09001c2d41c11a00b003141b04451300100c4980d1250318071000141d2103811030301c800f0600209100000104404581524126803050746d03101e0b0b187c0c00c1c4581c42001c505c0f031464014500d014140015800789440768950080c24040c42c111141211494075000d501580f039003191000c00c1c001b0882c1c450034a414064000030300401402804460000401d070785141c0184175008000380e0021071805000045404c071485140c000410000c0380c0c0001220890700e81d84280505000c2c0c1c06100700248802900180c828104c6861030784248101d0320b00f048400740780700055800c0503640005c200b07180300b40d80ca07401180055406042100b42010031f8040c0310305003c485030f214020305401d000c4501095a0441c05071802141c0050010407010540100501140b090000c0103042e1004003034203030348003030749680414403030500c946080144016107081c0c7c905c0f040300e52080c0452108104158000a4864078000040c01c0c42007840d09100d03104249840f000344007000040040340e6000c600b20703180e50380c480011604 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 340124163 1250 340122913 340122929
    0x240b01020f0303010506090d0b0a0b0f27090115080601080d0f0804031b052406010c0f0f0503122a04060c0b04030908010905010203010503070f0503030417160b0a0207 73
    0x901601c81044944038001407003014030400d0042004c02d0551030315a10100b86503030085242090b0f103440418a0000c0450f0b5213650302518205a070318466080c40304201d000101d110b2028145a44442d6841c140303410000c29941055403684030390030140181e5a6818040c2c882a406000700390704101c4000e242200041a01c0d0420009502d0f1401094110360b546070010303018600242124080320403500320222442c00101280f1034481401c01e04e40b442042c3e0100002c103643ca401498440c04011107680100e1000507003850702048241c0001840346400744503451048007030f41d04080703e0841790091404101c9209040d0300c090300740504807160140d1001150690131103040c4c00d25003401d600400442c100d40005001c0507103200807409140c000c0060344003e201c09402404070010030702d0254041d40080c821680207208030b20020801901c044055026224040c0003942800e241c8202043e070105884510016030040c003100030302e24004000c40c08041c0c0f003c442016038030850440000d140051941c00540 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 340125413 1250 340124163 340124173
    0xf1208040309090504050c09090a1b060203040b030402130603081c060b31060c15050f040206071e0803040b0709030210110102270310050601020316030c240b0102 71
    0x300280d0441c0c541403d44100020000d402d03074507407a0061a0000a1000a1b17102044104005907220001191050684616409060301b412421a5004801d1500411002d60400d110500600a074030010310781c41030008100440c11910044600f08071005c50300141c490520000f00e48401c1340601148140504502c641042800d182c04442001400b030800300c04155988549500b0541d11102d80311041c114030038201820403540c8001c00f812198140108684860404d810010ba0444511405208007900d8a009286a80e2030b03081051aa2046104840001c10384c5610340c2818654a440c0b00c241d4402c4501a0b51381c1401d080407110064018010340401510007024001601d500c294040c51120500f0110404480c0d2211540680528402050799105512000380c0071008910356050a100030707011f4401101444d0102000e44004448c01070241e0b03c01c01c201e481c60401c04086540c428060b1a200300404060f50718a03401240c41480602c1007010f100d1000d00004107407003902007018007400105 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 340126663 1250 340125413 340125421
    0x11a070c0b09180c09040e010e06010e1e07020c0109120201020c0103021b03070606050909060408040e0402060f030702211e0a0e1203041e0311040b010302090a030f1208 74
    0x10000c40c58501035411180808114180c25403500c003a00d102200824000300502c0c41d144003c0c140942010032003500c9a810040b81121991042c400c180d5942040d1018100c640c0c20103084c0b644605000e0060320341c0000c1c0340980c45e001c01c1040195801000554044c107001c802c0100018141c100940095190045009207440140c1c0c0009a200d00d1520a080142c0c0b1a440003108400139040c030003145016002c006a00001c102c2198800425514104c5060800d622040701056407071408440040c8840070400051100c1c5600807030480d8031610051810b413411aa520404409030015106000035038010b00c045514200f1034400310f649607a9011641d81130004001e00003490045008509140c1c0c0380006031a007a4a1054010507240074015050f42c10011201400c3c6580e40d00900c00c4800400514266042d00442c016648080781c2c3c0204814408010709020800100041c1030344605050f800c021014a030b0f203540000800460040718080303003000c054102100b40381c00d01ea03010010850340c64100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 340127913 1250 340126663 340126673
    0x601090b1e010509011d03240a020903030d1509110315010e10031503052a031b0906040f05092404030203042c190f111905070602070803011a07 63
    0x184020810900c0c1911b004144ca413000c01c4001d26a403269505400355402190050320101030311001c008800c2c1d50802581c1e1421443c1049008041c06d03554107420400c454440044207070005000a40c0101182c1a03965460a2500c211000280ca41206603004408c1254142881040300301c3c14800382021008040d1820010340c1260100006405140c1d0b40d803030f0074414441c00f82003503014690004c00c072807541d18203a0000c540201e480c90b5140184e15072101c0c500440c18086400d80c914403141c0540e05417041000204072514400500440d04590b440105469190702401014012011540580356007070107001610451403d400310900b03444055024000001e6000040f5412110b2040e0a04059005084402618440741c08814013020780e007014010303100f82c8a4081507500c0d0740e01e8420841c41200701f0320074064941400c4400c280140034000343e45c074120408141d408110380c07442c0c001d01c1c2162076078840b4101e800845c0243c503450703000b00042c42809038481d4000250020189298100002c680d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 340129163 1250 340127913 340127917
    0x80f070609060c0c08010207050102070c150905011d03012a0c1a040507150305220c03030806030a15050114150a0c0206070b0405010902090705120f090307050601090b1e0105 76
    0x101c00c1001000c046003403c0c446030800c1343d4041c06694009542d00c05030f906106000c0d401c8580141c5a013036140c413000a4240b26040040c0800c2c9041d290900c8140c07801c001599020007640300d0100c00c10942c0c20440090343e003807003040d540e66070100d0784c03541507a48480900c0315070902150180500c00741200940c04035030140c0c3e0141110900c0030007910503a44515180d81840541c2c1e000d00070300440420301540c1c458142d00040c1c400e00500c00380c0c0c400138039141c6010b20340b80304444015040f01c0002d801840440c0c030031041c05a101b0406400ca074180e000950700d50500f40700c001040b0a07840c0c1c0d10782c0148088054007506441d411340071615080c007400c4540c01112184100d8503660107000c0e03009003180c21511440d0a8844440d04100080d0142c0f4280c202140a00360a100491060302c0d4980001c0d2280e0095050716040c492a00c42680141e48140b0030180d502c00c060514101d0344000c4c41418001030381082024040c00c100e40307020811008460600c140418840400481b1050728a8481c1445c0d0740070b01 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 340130413 1250 340129163 340129169
    0x30201050709061d060c0303040f050105130f060b0102281203050c180d08030103050c0307060203341712010602071d1009061514041401050a02030f1201080f070609 72
    0x61441d11100044c0001d08140300d0030a00b4165030101008000030f20014028070701203240514001e0101e952803006d1412181180c1000a1610307040404213004605258405030100c00180100c0d4445420230701410304038040a4030302c100e0303440040e1480b410042c0c0307101200d0103102c09040c1070203541800d0a42070a14004d0b6a00075590200441506003030ba030341d21551340070a80d045024660303a540c49091031619091011310060180c81120b07000501d2a10001c22241c9900e034003006c0391820040c6071b03402c0701402508440380c01d0350242c07060002c0105400c584400c8048800c504a45e680340078111710b1000c5070105a000c1e4044d508260820440f04903064203140740c92610225521305599448181030b42d0b6000d9401c0841110714200010404242001c504810900151100b03000040b0010595029201d1030003041440c103610b465110855004801501c585606401600e00b4201c500300038100c1fa4100c0e8140c00e0750146240010407000030244035803850b2001e450b02a1901505150000c0c0404810b88 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 340131663 1250 340130413 340130447
    0x105132a0e09010605102a0201091203110d031d060c12062d0103060f03021c050a060509070e0a02031b09010207030c0305010b1c0b01090b0d05061303020105070906 72
    0x1c800501e0a0340207601c84400303002d0080c91421900200a001803404940c1d11440385000305c44c001595892a2500b007682c42c440d416503072045e01d14105041d025083c2140d9030200c0900240c2014040000c07424007600180900d290313000240c0c81d0f40c01d2080300740070100380d516014640020041c00501c5055500b1100c42c43d005030101d01490325a0008038805001e03022244442500b040d645082c2c5100030000d6650f0204240d9080c0b01103611150507180342c0182d840020741c07001d904c0030146481e00b0a0b16041003114000c0084d03564045450f140e5400355182101c8201076508001001d000c0b003600c01050980082054900b1400e61400c101e4110034440b446074602d0320a50041040d40180c0c0c400c010510103181d1080c030b0a62060b507a460002d0103015002d8105100c0e16091000c480711956074000000550b400201071480303a4a00103443c00103062014980e604004a2400384002c00d03010050b0900802e0180002c41400589040080c2103070703005000c503001c20180c0c0c1d130200714155000c0e216014910000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 340132913 1250 340131663 340131689
    0x9080604121115010e06030c0d020907051303140d03021206041a0a060302040905090c03030304031b020402070b06030f0d1409030a0c06110c01080115051b0105132a 72
    0x806000d80c0c2c1c0007100e0160080e1442829610341c0384104114146048a501140c0d000c0d01d0340f034102c101a2039031f20018030142c1220000b140742c80036240c1180c1d00d41d0031002a00b022450324507200040c1c5203200c16034006480803044148038460900003008100e0a040d1546011404d15800302d12004030054045c208903c03c54403981d8a04041207450a4450b001000030400032034280d0340c2c14064082e4000d80302d0240c6587c90300c800030700c80b0140414500c02c2810000c02031869555207035000d40d1501c401440180c6464440c152000c01600c07240300900c40710303009584001c000e240000406141c44400042c9442981100b01c1c4242c00f580c1000400144400c42c640c03050711103860402280c41c0440381308000d49003070060400000c4c41ea400120f41070207a1208402e940d10a1603007401514103400030300c95400404c0880d900d03842020722601c0a88074500c210f1583c00120350050300d001d8203603901590518910752100000c1f41c10040c070790000710014141402c0500d82540018030b260160401c51141c4100200a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 340134163 1250 340132913 340132943
    0x60e060c0106090f1d03070302061906080a0311011505030d0f0e0310060503060108030a05180126060103230114120105040b0403080a02090a05060d02040b1c0c09080604 74
    0x82d00440050a82d80703030108819003403621100c01500b21410309408031810491544040310b004000c44005541540007440fa43d218102d0a0714809050080140740301d64911011980c80c5041c0245e40006c0d000e82d13207100c030078140b2103071023400c5a0074040043c42c00040c0c01402c014986000c00c9a00c1310410b42c1c2040285400d0317004040d03444c5007601404c00d5140c010035071040104601d541c041801c0c0e950603022200c4680e260aa410b9480c442d0140c2d15000c240180000041400c542d406010041e44c18074001401c4442c503d01c0c00c040300c2600d2a40083d082c08141000182d50303041c428a409080c030320014402c242d041440ea0b42e02c250701801101c084c204084002c40694842403030355110b5030440c6000304080d05e042d08044483c0075066900314000766603200070501e422010700a4402d0b075803004020282c02441e0804000190380280300d04d600054091000003030980303540000c0c1241d034100e10800c0c84581d107007150400840d01003030340940078000302d0041880103030b00c00034003280d201e81c1c40490b010310800303 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 340135413 1250 340134163 340134187
    0x5010e06040b07060e010b01050c03030a0504020a05030a03080603010c051809040c030b040b251d1207080102090a06080405060a110d1b02010c020f121c090f0309050a060e06 76
    0x209641002540b020000750100c00c00820358090031042d0030107802042980380c010011111442007110b040d020740e006001050040642d0350146401510062070704189640c1c800200c0c1c00e00e0100c09054000c43c0d017840c20080700b810300b8001c0614034102490401d15040800702e81c4610607a812170280d0044000c1d10001d01007050310020803002d035410940e0124a480d00e45051030752400120b42040101c032031403080030340000082c50b03100e15045258803004060030544410003004500403041548c803040d50745401701008010300c4194080d2490038005696010107105002c90007265502000405c186c031400c02001c80c0d0089111a000004800f01203107100b034140f0b01c034074a4040c0c1d07000f628415103480c01403212841c541d06282055aa03940090062201b0030400b60385070040c0c0ba4602e1080d401c040b4048200e41ca0120081011607601110644400c0242c20907104480c00503200300d5060b509421110181038011034440001c04046860340840f03420004010a800029940c050040b4004600045038817 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 340136663 1250 340135413 340135417
    0xb1e12030a0f270b18010e09040803040303111303050c1e0108101d07030e06090616022a09090610091e0c09140402070b070503100305030409021b06040c05010e06 71
    0x41e0345541c00f00d0480d0307210300c05a0059402070b0f03134103401c000c2d44076240c1d5002e50107820b00c0c00c507044000740000000d5403180c50300382c51580001e00c11010103544d800c00c000d103401500050700b80070016002241c42d06017140341484c0350400d10540e5900c50498001311b4189130070a000e203c94183ca0a00c1c024280e6203a103030002507803a005030018440c81c6038815120500d40c80c2c010025224988540d8240424881c1400080d00c03944183d8030007500e40c1184d400505c88940c0c600c16031282552a10440d54080341c1d08071003101e2140b00c51640d4004418070b6003002d105180825010350008640c4019102c5403d140c80300ca08080464030070b842d40103440d891040900d440d10011510b010651090a110307000301c03020001c00100f07003805115195010080d0701c03e83c608062081d074855641c040b02d800d6040e00c685100340c5071900002d01a1202c24411103002c030003c3c906002038001445840d001684031030310041d58119080f6075004110081e1f110804000101300c1d0f01e8511006c582007828018107071142280490304034 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 340137913 1250 340136663 340136717
    0x309080706020705100f020702030d14070b0a0204030b0928020109031208070f031e0906060503070909050d0e060d05040501020415020a021203030f01090f0b1e12030a0f 74
    0xa8030119880b01440400304a0340c1c0c401005c0413040046082e007060076030480c0590000603415030f1003802c2d00d050050280c0403518424480c08811800d01695aa035881c40400c111101494950042400c104000083c0181a04240014060051040880d100751221000124050290044855088256401640b86070007031900204604402c088940c00603290040544a0000040901d451804064402d00c11601d00e44c80c4003604400c9490310804480107042c4640d02920800e90300e4900107007030b40d82044041e00800b207681d004200c6a00c1820050f003040c0c4440030090a000510701805219076540b011140c0d80c04c8022800203194807a420305900a0046c2d800511035040000082265250006182c181d1544200d82c4840e281c002ca4202c142c03a40000e440c00c084402980b0014810088140c2000700007200d01c1070b00044061400d40002c0d00c02d002c603050b4180c815000488800d8900301184040326042d03044008600e0b03e0b40c000c0300205849003444540c01080051700300000d030450500030020b81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 340139163 1250 340137913 340137923
    0x3070e010c0614190e100f181b0e06060708031f17010501080d020a03050c0a080d020913050402031c090f09061e03020a050423040c051003050c030703090807 69
    0xf02032a4000030203045015214040000d44c0c04070840042d1486005038044589080082c2c14064604401400540000420640844d442e48a040c803d0a5400e0f003580701d49001c2d812454000884414543c0031801a4100c506040101010820340e80c5a010442e800c0c640d001207155945c0e40c07215002c103a644d1146501d40c005c040c00382d00001e004168a61030300724486144008000e9030b640c9001e116610b00510345060056048111b00c0c00101e40588050a1070308019815030b4000c0c8e28554440d52a5801030350008841940401c500d1201d040403003039a02c04451121003080181480c2e000281c1e50041221389124038281003107101052403040400200900e91110060b92668480c007080d406412207000d466120042010b19100d4603056900e110f00720794015118820140c10a001d100c05000344017901c041122618074181c100803030340c02c4100d100b41c0c040e0a600c48001d00300350811160581e810b03002420907043c030b000e000548038003104a0740c106480b400d0002d4518224540101207001d003d8018003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 340140413 1250 340139163 340139171
    0x6060d060f05250c0f033203160507030c0213020c0f010905060f130b070516050c010f03020a090504021b06040506011505030108030304060b030309132c0303070e010c06 74
    0xb0301d0002000c40c108419226000c3c9200f550604075088410b41c503004806071011401100000200780912981d1144503070707010b40700303006080c42000307810707813410740c1030358190102c0000300300030320080400300c0507c150302903142040c0341c10000d8500600b1001c0750304020b803040104d43c1004880440f10341c1150000c0d6010016241c3c100302c03842c000ea008050701b48045d10345000d4600041d4a0a510040e180e11583c0f01c40e0341c041801425840c0d203500718000804010a001c0c0800803100d10313010f0214403141540c0700e90300602c043e01040000510205124400302e040c907005000c0c0302001c0d50490000c0b809d40d40c0c03c0da401a01d50849020545401c0c608081f860800e0144800703010520034081407841c141d4140401c0d41200d40d1075000c0860f003a01c000d12500c0f2035034105002003000180d80e60030241c02104d00404990400c1c1c1200001240c403613140081c1c0013010b82d1820303a0b03a1040c0d0360807070f06020314055100201d0740500403c84c1c0790300c03440000e0881d810408851858003807a80200504800399800c014100 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 340141663 1250 340140413 340140421
    0x3080a0f0609180c0b1912140f0a2702130b191409070804020d050c1306060207050303070804150c0804270e030d0c021c090509130506060d060f05 64
    0x80022480b00f181618481030b644404603004002d4401c49064202e0202c64500c450030001040707908906180da140c411a4448a8404088007000362403401281c105410f4000da041800d090030403601c1361075152151000c400703240c0001c3c03014101e0104039281c040c5d522503109004064514000c050304135406038045001076442c070420340502c0184041d110781036413040c041d8001000300510ba500c21070307001000514003000a00141000d01e848100d4a1050044a43c0f54458100160b24289440d0070344510969440d41088100d50400c0042e00600c0306401841c5441c1207038842000303501c20380c09002c407150002507a5024070340c442e01e18460001d4003d50700c40c0c1c4503622800884201110390319030025281100188083c4403415101d020700d0801007000a519102004401c0d03006055005200d10a41c090182d180281211506003001c10101c40e035101c1035007500f03000401050110140c982412141c4803101000069070000c0c006070013850480700020892441d1500301c000c2c1140201040c41203040070180 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 340142913 1250 340141663 340141691
    0x1806071b061103011509050f040209030f0109080306190510080702030c0105070302040906270e03070b0405010501050a0f0602030a05130504020a0305061c0b130305090d0b01080706030903080a0f0609 87
    0x1e14166402c0100785106420034250454042003240607caa2000b821586030f01945021750040600c41c6024003030703499100711000d440342151a009015034810b0000010071402d07152641c552015410303121109106103040c0b401080d801e0360001c440314203000715407000c02c158600070400c0c0e85001c060074000780164a043d4a0050203504188507000c50703581000804224103005441c540900c10300c40081410321001b4070f101101034540d60707140005074041001b03500080390561185a114500a000218040d4907203000d102c25580c00b40d12002c00100024010301c0800e9000c001c68003000c15a142c02c0e9120b1120b015001051031441d0300407a0311501c001100c1180c9a05a0880d5104810440b40a40780b003500555602040d210550010410481400000d51080030306081c0400c0c54000e14129041c036100348042080a1000e2200f501c580c144900100f10f071b00000c01000020b400189802e0010081c0d0355009009103201500c0c0001c01a02c811808150984c01d600020050a207800300b488041544008 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 340144163 1250 340142913 340142917
    0xc09031209030b1b03071d10080411041803031a060a080906060f010e01030e0a08030f0103170703320d0e071a091c0f0c0801051806071b0611 62
    0x31600c0b03ea030880000c2e40c4258405043c01c2070342010642d1803071a60741d0103040300c0c0007183d100c2d407040e12080780302032020070380b900070b80d410280b016a00d41558034280b6060130310141200a030007620850502000032040c80403440304c00c0b081980340c01c010403030034010024041091002c219040d045a000308450703c149620000342c0e409822410151002a02c0f05414417062660905006002c50140e80514034079500c81c0e40180d204441460a4424069617603a500440d03a1041d1000011650b10310014000d00410558154400c41c25514640c0743c84117580d006060f22601c080120f0001556981e00100880c000803462030240c842071500d43d48035102c0007080020b203015140c813000da210308240410034141e001103000c003a00d4050f568904086400301040580250400e05c201112615a281c1340010b03070701c07100c15841611500e40c0010342c504001e540d50031100010100b030304145140d40450221100400c0c000d80040d43ca1902d619000c40300c00c55000001c0b87c00c00c000784000d10b002402e502c070710b1010740 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 340145413 1250 340144163 340144169
    0x721051506010f020a0305041e050411040509070306123504090e030301080a061113080607080705120105090a0b030303040b090c0a03080f0306120102030a06090f1e0c09031209 77
    0x243e0404820b12140100c1e0780d10414280140411410801804021804250b40038031102d00d00c440070710b00340c0301c201103802c0c0c440107080c5150b0440007050074492880c00550446c0d125040389400c00041d4030782402803000c00c140240181001c0901110b4040e04011030002c0b00d000340000d05c445811f44540880c9039501da100b44a1a85800d1038803410380b40c52040442100c0c12164241c0080140b250340342c95440003040300a07085103040d8010095001c003424020300f10002807001001400302482d1001c0040c01a10b001450402085030420902211102c1000d400b030541d070056501108980e214110304c001001006885680361001204001c2000742d00c00f0507603c60074450007583c0312640040188068842c49010003840c40205001c00032080303001c0d00145a20003c0140741200200400340286c0c22130f48240c07001e4a01c40d0b21100d040c00030b42401d02078844c04150411042100501c0c40100d12500f42a04183e844010380303038858120302ca8820409040595040301e207808960701003640241610350148 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 340146663 1250 340145413 340145417
    0x8011a03010b01050406020c2e0f0f0509010f032708070507090c020a110a05180a060b0903070605030c07021206090f070e01031112191104020408072105150601 70
    0xb60745015441030040d90103c03801c0350014040740344203d003044012459038006042c008844241d00c1e4580c100103041120244031901ea07034000c0c2c6c4c1c0c01c0d0002000b0304c181c1d5445c03601f807190070000c825059a006d0651611500607140c0014480702051172140ca21041e405c0301d0154180c8004501c0c1840303e100000d101e5240310303000700c840403a5200c0c410816a40c0450241000d0313017040d80d011012a0b4000c800c6003500c90010202d06001e6141c1c0009103803030300210b45000d15030200100700b240e0412903116400140081e00b0030340c0e092210110004c0d958440f90b00800f03007044404400310b50f040c80850142c0b0406a401802605a507040280980e5034a10890714a02c8074480c3c2003912035806008110711058a42ca86000c0c14039a086846050401c028401e420350054205840c0b540d5030b450910440101000b8910303044051b0400f401d194003600c9800030709520480c41048104101c0b6000600340046a68800300458040101d071020b640c81804250083c1c0700b4014219200703401c04c4164080f43c4105026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 340147913 1250 340146663 340146671
    0x10b0a08010b0f190b1e070c030201031d0d0509010905040603080a091406070605060303130602061b03100608181006092f0d06090e1014150409080408011a0301 70
    0x18008004500c0f4841440c90b1132410b01d44014030082003694000c00e5111401070b0074010290002194a14680c407880301030ba880000d504007401103682c580a035101d21840240c03040e5800c00800d0401d0348a50114581c642800000100c140181c1d014611040003010000c0040007002d03500d0074000c2442d80309081440000b1341c40f1902041c0b05d100100c0079010f90002811550400d03441c0d80e09e8000501014101f01c0c1d05201c2401080b15506a20000d00b01a141e140d000d4038440c00c200d10041c0380e41111103100c1c80e10700c8041c4200510900c104100e041121040c0c500582141c45881030104d000382d54000c4400355000d150010690b5006541014003150103c0008103d242030600312026a0108200e65588480d801024000507003803460240820034822440014455550f49101088480c440c1e2244400c0d001152a62507481c0c4c0c40c0700361032000300001c074070021a20300b01020b6084159003004a510aaa59031001c0c4c0c14082070006440240c02004001c0190503180d2403004200c0b201903070818400d60078 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 340149163 1250 340147913 340147939
    0x60601021204050d0c0b0309070501030b030307030210092a0f090902030604030f110f071a0408061911030a0f06060f0219051203130302060105041517010b0a08010b 72
    0x4001440e14410400c04181c0e81030030b05080c200241950400d0041da803006900d04d010038803024020003180034100000007030000c41e00d80000901944d03801c107130f6240300b501309109910200c1d0f00410500f000c0e003000b420018200d0302c1e5241481c46840c0304060303074494080c00e0411110f2501d189005101b614004c112107502540d03038294403000c3c0c941b2814000d405421410100d40000d00411702c01208036102d003480202102c03260f115a14140340455190030a51107100c040100e4024001c40003491140720a5140c85e26090081031542c82c1400b0f4401400078025080c1c45080d514194480d108600c1088038466482c208800c1000107000f6600c0140301c110301c1c100300000c40d6030003800d0301c14200025802501030580c4079070803442210801c201c29a0a401401446109440c000000303500c070711107201d0219203c035000d05000380390580503041580100e03c3c0c1824680741c50701c0e8402003011501d20f808402070715801c2e200d005001d8205880c0d019003144d5120800305220a0641000400b104143c819800f6492 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 340150413 1250 340149163 340149167
    0x605060306040305071209080f011e0209060301051302250b0601020d020d1b0609121206060503010306020c0f060903030a0f15052704150c0206070e090601030e1509060601 75
    0x4001c2d50000c01084d002c018420000c0d585025080da003107100d08181c001c09996000e010300380521a00000010395698161141010341e2444218000d03c00d105c0440c105800800402ca90780700600a07540701d40380940301e000480c0c2c41c0c0c1c1c0481d6945040f480003da841c4c1c05001c1c00444a60040304200d4146100394000b8405510001d5a100c0700144c4c2d5008010710f442125040d2510f4001421400032960424110400301d410750050580700e40c4a1440f00320407040031040103007c0722200004044060030703e1003c0100316440410781e410f40e50020307030043c0d0b50b620101da128075103013250341107860030300a040410204481c0440510701c11f0344000004d020108028801c8021900904103041e0100c00b00107051200381004500d903108020619524084100388051030301d0098000c0320201c0c0e03000100701c1110070390405030207a0f090012880c0010300603400c02c0440900380203c1541391a000e00d504600041c000ea208c0d401c40014803480350260f5004007210304841d140c1c40d100302c503503544034440d010108030307154 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 340151663 1250 340150413 340150423
    0x60c030b180114010c14070e060109061403280b0f06090901032316030201031503081c060b070302160807080a0b041704090b03070803030106120e07120b010306050603 73
    0x614440c40c5000340380c0c2080500c0e000f1404903500141084041110f40c0005181c030302c119200980180300038480c40349030184103000c500c03004100350704000401c4020084203800080500c8041021551207441e03075207004000c081da003501026030403141c4211a030884030070702a901074030300040e050f992005541103200500103548545001503400044050042000c00c6100910b64004078000074840d8464100722001d92804640008a03000b441d1041c00070001c6613054498110000c21104812604511310b44403500f4034001e6003000ca8001341c4614442e4281d800c0c81c1d0102003d01001600c050b1103007000d040c02565400e034000711242d0001c07208808227205900045072001c84002c0001006c0b10b045503070320050b8180020708101d07204005c170040c02e024404614094070142c8460500051401424420545070580d60751260300d11390002c00052107000d5016201ca440b8803003110f00481d103210b50944a501c1c00c0b1880c0d1201040a0010101d081040307004441103040b280610000e106e01d460341c40805890b0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 340152913 1250 340151663 340151689
    0x4020d0e060709082e0203070f080901051b0a0e10051c0504050c06160c06080a0f0b030d1d0a030b2a1603020a0b180d020106030206070318030f060c030b 67
    0x41e800301d40d10541c805455102c030104945c05100d0440d0424080700000260b8105456500200e42e02140d1610b2955101110a500c85140e0700203000d01e082031081054203003003100441301d0001000804814141c001d03200d150f45403034040e01c01c84030b44810b01c03001081078020050940007a410004603058103071660051a0246802c01e003e00800c490003001c104443c0d01403c4c3c8504500205404400450310b02281200208002e072a0303512b00e461710452410403500b4041d00100d205160180d440c5090320005121449031403903040809c0407c007221401311a9592a2000c03540c000d80707400001c810410b0003407909004500b0528501c120355411360030250034500c0d07074410f1038071b40c0da0a01002d210500542c018100440c001c3c01503030300202c425101c80c40d206200700c541c1c030720a211030016585440401c0158990400316440200111411580001d00b68801c00002404100d0a144840e0344a0099001c0320021075000c5001105001d45282c00b00c007a080c26a02800800d00d08070b04e2403010304100a0401c40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 340154163 1250 340152913 340152929
    0x8070308030703151a07020112090c06210501141005030403050306040b1809010b030c0a0501120c05190f020d08130605100515090307063b04020d0e060709 68
    0x30355a03030b0b50040f070041c600511800c2102e441e40700300050307002501041013500b00c0e03080c05456581165000261400041e4400b04000e103141600980110f1540c103000b505841561400c00114010030700781d051180f02150f072070300c095860100005a02035403015007500d541026500511220002c6409171101e000c00c131750140104004000080291500b82c2c0301d034158940040c085680040040502c0640f1101152140e4030fa071b643c0d10420b2402d250822072000c19030760440d802e200d010704042c0001c01014030b405042000640310340c00c504185028005503900b03d00401542510011003050080c209241402da100250080ea0000085288120b072035a00c12a000304241000e15004d6036044000c203c0107241041d00e09000e01c01007226030322400c400c3d15500f100b40010ba00e4880c09020181801990340c480740a02403414001080c00802c00c1c41e1070b0f03001c040140303a81401040007032500181d00004900550041c400141c1d064044040e6010312030100080c6c017240c407181c1c7c030b140f0240c2e0b03811494050803031 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 340155413 1250 340154163 340154167
    0x6010b0705030a0c080d09050303060109170307060f1d2109010f05090114031503280f0615060815010306060e12010209060d090515041a040f02090405070f08070308 72
    0x1480350007094a1800c95105d8454075140c6406003100300708582010794210740903000003086c0030540da400f015510180030001c50721100380551185159a92080300c02c01850301c0d40710380045039a81d00660140c1c0d6012403010100f03502200c02c2e001252900e0400180d00a0707030b0b1030201d0200c02da403408002d84130781c020103031900da20305400d0310410781d410340089031564104580c9c2441044414074901c05140142c001059036501d542010b0205824440c94a4160114984400300c25409640c0c071070844c0400e540040f0b24407070034501ea003007406c050701c0c191003024a110000c20700000c050303a0100e00c051107903200f80e01070000e0966000044050b500e05100307000c006109a20080010725000e500203d4a00200c0b0005281240c0c0d007001c0340c59600000c0104400d66525121981400400c0c400c5410600d080340a084003480c0a03911028002c00300b24aaa0018510741c0c00103007042100d0511904294004040360000c1c601450510b91700c501601036058909240c0c44000b81540c400500042a03e03030094002e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 340156663 1250 340155413 340155427
    0x2011b05150a060806072010060609080303090304030807140609150f0f16180305010204060f0206010b1204030e041820010507060b010e0d0510111206010e0f03011d06010b070503 78
    0x43c2d81d4074003a8240c002c130321003414941c1948401002302441140108501007502e62810102414a603481e5020b0004c1d0740007001000f82d001004001c48060f02c0c1d003c41c04940b12034860510500f000c0044c00000007902c90740d024011100c0340080c0600302000e200d40403030195034500102100c120f005130740f54105107420402050020f02e66440031080d0111038030780a03400141c00102c0d410b02e01c17200e610986003a503000800f4420654403210f56500804540003c0c88a9454558076100d6440b664400140300d41606020904040c0b1801070740e56400c50080c420b0000d05202c1c0180d02c3e11440c02001252008020702a900820712841940c4c007000d10140c43e240c2c01c207507060316264003803d030005499042000900110340c83d0345c0c0c2c4110300f00c8441c0c0180c004108903200c0d122034100321030f000c82c1140344a1005110042d5400041e18a6a0b401102880c1a0f10324030b482c180070440307480002c250b00d030b455400d110603208601c210b413208619042d000000c591075642d031800325002d03500c42e030340d809029500204005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 340157913 1250 340156663 340156667
    0x406050609010c060f0e0a0804030c0807050616050102270a050114160f0b0106050304050d080402220b041b080115020a0308090f0601150f0e060306010c02011b05150a06080607 77
    0x85091000713001c0080386e404a114180342c182030030342000700c412001c0800e051080c0640c0c101984090041d03d00100000f9040c2400119240078800039880641443c030312510400c9000e40603030340c2e80416190308030703085208155094141c0f6041d143c61f0703004a40c0000001180e40c03250055041c41c40101c01c00c0f510340203104229440303c0b03407500815a0441070302c0c0980c100241055a5007802811140d645075180d0401d440c090741400911000001082080c50034000542c3da646208002e2007080103404034198002c01030703903004d40010502194058500b05800d2103400010703290005602e89075403103484607078031565406050b282c0c061207500140d0100c149100000d0080000036044091042116400305c21104075519042098000307031b8900000c9856198440e8210b40103507822920303400d18000285e20140440c195001c010102030421450a14800542e409508411186a005d0180085903616810641d0f43e48211342d1045400d0240640010510900e0703125000903a0414030143c50300d03031159141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 340159163 1250 340157913 340157921
    0x170c09040e01090203030a0302070b0a050f010603050403201c170109050402010c211106070206040305090d020a030c08060609040b0a110d15060e030d020319020f0307030302090406050609010c06 85
    0x1e0801c45659500c0300c400580d4040020306900b5030181d5015aaa8207144ad081400e802c0c06091209898249818892100b0072008000e054940d5450300280950b5542070444400703407002d04c1201582c11080c0c082d85034001c0440c011904090039a01002c400901610482c1d6070002c0c40c04614900003044010311080000c0c0d00301c00e0300319005140c0301c020f10705143c1742c45403030744c103902d0f085103028400765284901c454018411201034410038018042070715288401a40300d0100400040c10882d001a40c282195500303c104201c09030058900700081d5100d03d401c00e041c4215004078500e034404c45c2e002075034610700309150b0ba00c20356010082062603141c111403a0041e18101d00903154a00091200800c0e01c00a4850421040d690940d5140b90918011000d0110301c0e01c015828000d40003480c040d8031094000040703542c81c007101100b0700700341c080c1c0d248102d082101c000542c0d0041c0c08006010424568590098a14208115010001c0c59030f95001c0008604c180800c2a02240b00c104042c408078582d580 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 340160413 1250 340159163 340159181
    0x60702010903020907050306040606110606010c02150706020340021c050309040608030306031519141f05010e06032a041e05310f02030601170c0904 65
    0x529034141502c90340001d54040302140e20702c0010b80040304102d414509800303880f004000a040801611645504c0b007900c0300c03c01401135050244200c141c0c000c6458000300c002d0784008040c0081d45584d400d1507c04040e5000703480d4410000e94048003182c00b5a0a6480601030181e0050340c0150840781164040003020654016a03110050741510201d0380303c000c03c05010544600042c0da07803544400204030071290190812a0b140d4070074130400c4010b0300c0010f080700300f51400c0c2480c02d8060390703160412038980c0c2c80300d611030b41c045007818180981d141c8581603045c06400d003104032000c0c4050956840c1100c0700c09214150004904003082041400c100008603042004004039914201c00e0030100c125015041200e03c9076180300040400c04075902100112a070034101c0c44007201e541c90700c80091880b01000b003074148890f0072515650034400508140c086003104081e0140b029128400f880e40c020340044600c40d01003628107140c000408403410701c4920444a012499040011341410301c001030007035007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 340161663 1250 340160413 340160417
    0x22090c020c270103060606030e07030c14060d0f0c080903030402011e020c0a03030905010e091521010504051f14010e06031609020d06080f030301030312060312020a0b2406070201 78
    0xc07100015250b080c00385000e140928400700b48940741c900b0007011141800f440c0959900001801d000140c928409001140c2aa01c81c2d00a08070a00001845a00c00c540703906a0161400303050003070500c2d107a00580c011105544524025030348030030226407244000c88000b400140c480e02807a11290603411680715091007441125292000d101c0811441c4400750015008281107410030045980e00100302c0c6c40d020802e95941c106420306020901c42c42c11480d00d40d92103a000c02441c80b8110505141c0480b402e03c07a20024052800c203400e010fa12642403200701448220b10300c8000000154601038041c1000c402c41c04030006a2070181404154200980b440703605016058841103046100105480641f040400c01640c91040043c003804075074560f0b02c0500c9a40000140c410026004020b890442c0e802d42400807400c611072612800034100c0340c000802c09011000501d25581d40040d2444042c0d02c00d000780c120701e4a0301190401c2c0c0090301e003d014140610715140c800760b810311102500e01a8418 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 340162913 1250 340161663 340161709
    0x610060203160c08031c05071d040b01300f0b090610050409020a0e0406050102150705130504020409020d1d1902030f030406020a06061505090405100b22090c020c 71
    0x141c01d5417411984103c1003844495000d85280346c0c88041c80c1300f41a001400c601b4020607182075054508004e80000314214840c83e40c0302584081030b4040d00c04c2c04050141c0c81302c1c69003e0f015001542a17490f60301800f8030f0b0030a1900c0703050184d81905106400315450000c01c4091580d44400810582e04109564a0708204041c40001807400290010b40801c1000d81c48845490848409200407154154422070466000c1c1244001450a6084541d04801d452414554030342c032682020415403000c1c1d0003160410710002d0000b40d110100d0340500548000240305024407419815803060309002e14410742c64a4003c406a151a410074903032031040710344040c080c1c418881240903420b0441e0000e510401c0560003c2c00b24a041007282e120f400040c0202d2030100c6040541d80b07400405a019486069010355619000701e1000348200020791300500702112016511144011004401c0420000c01501e915106d0408180d110b5140103000343e9210130341c000c182e541e100070204172a4040e040c0b80c044500e029 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 340164163 1250 340162913 340162919
    0x30c130306050c12101a0a020c0613210804141503010905180303100605210103050d1106042a030f03020a150b010e040c09050315090610060203160c 65
    0x1600546115104100d02103480f480a41e07645180100d0090142061415005c020300642d03100f2031303a40a41c0000c4c801d01c2502d41c400044241c1c070307120485048590111001c944800c501e400703d031001c01900d06000106a003c0100494030751344003100c5400420b044e8041c403050292400020f5100d1036007400805040d882013105280321000e0b0f1003030300701d00238640d20352080200261041c42035800c1c8441c0b1800542c55440d182848144400490045808201c40084c9410602d4089440b5020801c20071a4080003035940303151503990750000b11141004125440100c000e040f82c0800d02034800d03a0440418840c0254034a95002503000080c50030100003c003540100201d10714545c0d41034943d01c203400510412a40b400c01005071200c66004510150074002d51440c80c3c1d9000e10046410182903401080b844030128055404c080e80e0742003150140b0501035101070010794200003600440011068420649812403072224200e0140910805a4002c002c00da03da0f080d1030980740e001078094000d6516840d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 340165413 1250 340164163 340164173
    0x3060b0c1203060f091806090d0507020103050711030a110f0a1e02150f0a030b0603010321031e15120515090c090403080411030c0f280807090f0b06030c1303 69
    0x94901c1b00034a240361940c485802410014145c11403010780080401d0001003500408a22455600070b040540341c0c400f140380c05004040118520000e00140c0784c559004000007440d02150051034011072003100702940041d00c010440d903030780c140c10242c6603000c0d9400a10010601d07c0a24040703820100301c14158524a40c0a40581000740034031099175a61118104014160781a000700c003485054100010800208080880a054141c2c2202c040104c1102c200c10b44c01400300406012600800610151482c105617000d1002d00c007031448420010390b152400a4403485001c00d006195078010040c640c1403945801350b0540c8121090110b46ca00c0c2c1c2c0084c08280c0001c81558214041200c06042c001001030394803803013400c11403d0300104500c0300d0300b000043d214141444117500a44424a074032101c2c007200c002c5040801d01311003580c1e4135582e6540d034080c1d0310182031007400d45241c07170034007a01c02d140762502440e00140c400400580c11601c41100d128880d9100907006c01d0900c11a03000040018 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 340166663 1250 340165413 340165429
    0x30311092b0c0303050c010f020909150d0507300305041e05030d171f090c0e0d080301030b150f0618191a0c10020307140c01050703060b0c1203060f 65
    0x14841e03038801b622641c084104509540f4003c00700303015240103002d154031035100c003080b242d070000318604414003940102c004210300000e0040060502d010f07050003c90700100c00a8082240d1041020340813448000c0c900320812400300d0031005001520804c070801040040607204000b161900b45811101503446000a1400401c04a0300740804c0c009100849400c1140480d150300c6070022903110010456611068003592803800784942c41e550315006c20121030b100f50783d10b045c001006070250903446030034100390b1b189400910084480843c40380020313122407404114001c0040c4041d01045e010b60a40003000001e070015940078820010711207151415a450785461808201c5504685440c0e40c00c202c0e0310803501c8040c85282d1107010007000380000380300c4001054051602441c000588a480e0030320100e8017095840c0c0d25082c914170120714105601c01c10b600460103402152003c000c0d0b0f0796556282800d42c010044c4d0207855821259402003074615041c025580200018a000c03c3c61044d00c00141840c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 340167913 1250 340166663 340166669
    0x1141605060a0b03010c0234030c050f010f020d080a02071a01031101140403020d0804030507060806010f03050105030a02090702010e01090302030705010501050d0b152407030311092b0c 81
    0x1503407018003841520011442080740414041c0c0090200d40b820060103540ea004280038100c01c0c18801f5084c04000c05e0918808815640c2040b82d034450540e00d04124641e42e00303900415204503e4008000351a60003641290b80340b10007900a8149001610404e641c240e10041ca82c22405800b0007092000aa100358110803240c044901c1e4101941582004c545055100e041c150511400641001221200c00e044d2011650b0442d5000d45100252500c40c4007070185610042c003d106205010954603001a401032160000780d0b10391600c0841c2d124110705a800c288a8203406401410924015062689903a98032071081d00011400701840e240141c01c482c3c6600040d40180c00c0416074504001003805400d004004c1211f00180c003003065160940c100f4406040d480722081f8035130058525803501e00030310700390114107041002540c503d035800c144241c3c0080002c400092510702e050441e180124141c0c0e960141c013622450869030303007104030f4058100b18115040c14990200d400b0b00098200b00c20403004d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 340169163 1250 340167913 340167923
    0x1a1c02010e0a03390504180602070c170d0c030c030e030613060e0304050102070b0a030e07030b06040b1e0d0f17040e071b080304020f0a23030105090c011416 69
    0x840a148610031207074407071301090711900d01414980420345440700034484055a1040700c0000d00301c101e0005400320a035030720780000d00da280040350030000c0c0081040c1920803908408a800582c4440307150694454211064010105030340503811004a40310784400740380716201e0300340680f02c1d40007200028500300c822616403e0f446041155942000400d0003a4060000b5680c005c1d07040a0800b130003c0e450b10b04034010781d0089036001c189450308621913040003140d00440300c20f40381d9050322814024082003040741d0f0700e4062410f00049500d1030034000040314802036420325108503001c8200420800300780a00c0e06a441000300c1086a010510400350b45400c0719405032041e036603e00d0112003040e0240020315020500070009600850005500001c0408984c0a1030880e600d0343d561000404c1c0c120b8004c02660003040c012404550b400391081c0348100c410400c240003c40c0b03495030341094280c400c1280c000c074194112903420204d80d4014003c090009171008001c40c1024103030303c0764034904031100f002520 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 340170413 1250 340169163 340169183
    0xf060609051f030b1803070b010b0406090803090f01030218090a150501080c03010302040207140d0201090b0c04050a1503020f121005010c210e030a0302030c011a1c02010e0a03 77
    0x18082070040e000000240e00d1030020000b0f407035612150540c0400410785000042203001d211120701042c0104c03120607030301c030b48100086d5031182d1071810207410900600010550341c0f0030119104130000162641440000c2082807000344903001140603402500e4004c18189125074070000669840c034101c3c1c0f00c0d5900c903000041008d016640d032400f0741c40990102e070520074840c042c4078104220008407070560f501610056518450b9150106441c086c90703101c000d19008031800504d6196043d04403424503405030301180c4003904c5203400e9601c3c6100360b106080d03100741014800c010f2066100c6062240e00719609005050883c0404514115800a1b190600211800c400c0020301440011440b02078402843c1c101c0c00102c19603100010440f900c044200311000900d0858201d9114400e285441c0301c024080e1007803600c003071401940d00e4011950480c000d500340f48400512201503030003c1030030b9200400c0c1081600c50052408414010110b003130b0304100b440c08858000741c40d040500f80c0114031a090f124 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 340171663 1250 340170413 340170421
    0x50d060f0f0b01080705031510110f03091311251a0c07020603040606030210030e0c09040c15030f020315030118030203031f050a03030e0916020601120f06060905 71
    0x1030407100c9401c5a11100340c41d08010b21040e903840505a80e01001d54100140d50b5128580c0d8448030b4040004283e602c440002d81c1c0d040c245511250000f21084420100d42130082410701141e203074001c1c1c508860b0800300601c03003030f02ea03101e1680284d013480c502031403031900c0c10f481007240554401c0c2103104024210310440403076080040450070f0121802003070100c00040d0510000820084c410128003a2044001201140078004203038080d000455005003054110046140041c01030610b400d201513031030240111045182c00d00b0401d9034401c50740022001b040fa4100002c0711152009180e40d1400c1560302d00d58610000300c14070045000d01e003035800316071105040c4410142520b86075030180442001c01c05041c0e001a400000340ea070480355201000c03984400c2809400c1032640c00344c1c01941e00c00302c031860020505820008404182400355010b1210b99240015080f628100314500801a800000100070f1200e146841c492018401d01007a50801e9840e241c0c041901d099170030100303480c2d40d01e100380 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 340172913 1250 340171663 340171691
    0x70b1008151003060e0118060c110a020d06020a0215011e063209040f0b180708160323061c0c0302090901110a02010608070b0c0d18050d06 61
    0x4441d4070480000340a49400b01c500c1c00200c40a1100400310750303c41d03031054200c100070b41200400382c000404403880180542008030160135103030b1240000c12105036440340070360808944210a641c024065181d1312120382c3d1980c00a600428640c400c5004601842d020910b0303000c0700b18020020381781841690326a0302031075403034032000764003c80501c030140c103080501403400d40040012020f940d81550406070803180c000c1ca280b0982910942c00b07403511880c41517000850b0701a01300000305450320f45000c607183d80c00a40c424000e907003e101140d424000a440000400d0020511a40c1441d0116200050404803041400388001102070100d107081007001d0350808903000b0320700c038400c1c200401c6288480c0d21070a07940b40301404040d020381c0220300000c1201c0c80075008118061038001e8215601c0c550204001c3c000d0559005842940c02505c1e400034101a11034260750350b8400b42000b07071034039001c640b41c10b940d103558000280000b4290404000b46c00d944100c1c803024139902842d00464080c18600709 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 340174163 1250 340172913 340172923
    0xf0a030b0a1407021009020406080703061b0e0102060f1e010303020307120f050a0c0c0506030103081c1b0c021f02100506040c0f0c0804030501050c120f010812090402070b1008 77
    0x2407600815500b0308000e02d80350300280340701a01d50280c50020b5444614004540a13100700c0d003002e07880b8407502c03000000b0052582c0c0300001407211a07142c0d030350346c80c0d0445048483c10103002c1200d0051b4002c5000c00c20295108241e10303003000312240c2940c51034404034600e202d2803400740d2054001d40c2012032444240701e00161032003501605c501d010450440048400342c080d02421410004014061f01400100401e081000c1c000d000010001922980c9d40c1c60b00300307007551110b06c10740603040c1c04283e02001d00985001d01e050036042190202e91780842102e08540d1001c40740b00982c1d10204040030307121301c5c40c510494541c0c00309941e80034040c18070219021105640010740130301e000714501450f00d41c1e560b500c849590651580b9107040381c0c0c03028450400c4030090185410180c002e5203000184205a050100105850b000c05503000303005995084d50340161443c248255502600034131404083d140c1080014001058000d00050400605444403006c3c45811917003551004d10441d81070003840d20401c8 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 340175413 1250 340174163 340174181
    0x40b1b0d080a0b10050d0c02030408010f09021237020405040830010618090612020a0e130210120212012d050f010905060a2102041d060f0a030b0a 64
    0x948441d1308019584010038074451002d002d11304998440c21411058428800c0350003c0001400a00000b140410a0300048c28071860880c17050f4024801300c64030000104000e040099010040c016a8a011a8215210054146104006080302d14610050b5101e129050241e40140301b0f0948801881c2d400300c03100c1c0c2001c0301c40c034002d113500d10307180d903031114510100e9040d240140350040c3d10041e000b805d686403214980151040f641441000720b480b0360940c00d45030205000b16100740100303a80300b440e01c82008050356240c400107649181040541003d03c950a00701c05a40351101440c41c0c982c210400301c0e040401c140009410031001000402c00d455011000582103100340c1584154080c04500c880c40d2a00c00e4a0040c2c5034000203070226030203145020020035019200690740e00e5588401070400c42c030184210461030b00c8041c034002c58403180c400d0390140e1302d1101c01006080c0928a202122140c01070200364049400b03007114040e0b460740f440b100011072107000c42031000c0c200400442c0c00e944501c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 340176663 1250 340175413 340175419
    0x5030a080702040f090209130b0604020306061e27030106060215130201090b0a0513060201020a020d0e0a0504020406091d040c151e0f020c090c040b1b0d080a0b 70
    0x1842400120304038404440000b903040b5000112107014000202c05003100110195014801d0020040b41d40c215005041905100b88295205542d403c02004100c0c0400c0c0c80050b0040c400340104800108010031650b030220b00510010300381511641611150208491402d80581d04244260303520b080034003801002e408103002514010701e000e604412082d8006000d8a1080c0405070b8000035a4002d090b0b203005091441d42c002d035181c0e0f2018002e0199840030b520482c3e180c407070700b0000074130313900c18420340750f60300010350181031918000d61007100c51380780d10b20940d0b0b0f0000a00c2c1c00007609a44a01c0200010b1905442e0400d030986803c540c60301c000000c20108481105207810480007802c10b0038000291803404440d081d110601803030803541002c50845180c2543d4048401121040d040030320324000200342d9003100e91100040d02440b210741c005480d051904541803005200710b051010140622055401e0100c405111030b8016a14101c4404141c501007198581844103143c41c0b4051440803030815 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 340177913 1250 340176663 340176673
    0xc160e040209130f02040216120e1e040b0d0b040c0f050f01050307050712021605010c0b0a050c0d02120103030806030c1e03030c121b06010b04140d0b0a060504060503 73
    0x650040380030400c00501c907001074507240c140d20f400c011043d920040c2e070f16005041151207425071052100441c48110043e0b440600007465107a0311803040125524a1402402d600304030b520142d890146e010b40b07000c03269401902c410f4403140f03a0319001d10628a541c007a01e50801c0506041c2004415124560003c5074440080c05060240f07484116200302100700a01c1d00070380d26940e0b15000c40756409001001008000d00c44851503c00c2c0d40003424807074419809d14994240307aa1070006641d80c500e031410007001030890310002242182260711143c3d20410000c0c0c00c52078040301d070050108981c01b010a00c6070111244005205150744055000d070b00480c10340080c90080c10403000140c444646c1240c0380075480002d040d6202644040c81901d20b848100c2080301d241e001d0b82840044079030003050848200c24020401904d581c08006002c0d81202c010b90192860507090500554801d0f2802410f10780003001c0e00c41c8040001c0500c0b41092140d00411701c005411801d1a0401050329a584e003e10311035800 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 340179163 1250 340177913 340177921
    0x50603011202010806040b040e0706030c17040b070c0c18110c3a02100f140f06180711100b0604061b0f0b04050114040b0a020705070b0c160e 62
    0x901c100780c8411502401c000c40e40b03944040006003c0c000c858821a041801c16944943c005800105401915030645007840a40ca141a04480d0642c485000c1440c4c1003a400104001c00c590030241904030405160100c85400d140e111400d1200040e0701822100708500115214040940701d2400c041e654180e040f45442d8007502040d42e100181c0b001c000c2c9810209620b00303000034203070500c1008542c940d40500d855640140010352601405442604414144100750f402003046118450300340080c0300e82c044007502d441c1000000c035200142038680019003186107800008000c03081520824a80d51201f6100e00504496418000b488190180c65410b14541c101d0650b500402c1d1425210b503854000a001c3c60340c11244911601000c024200c20b07009a199820f21210020003440380c3e004400a0046095a4003907001c0c03c10120f6001c0d00148864000c0b41002015800511480d03000304120303035806072602c10b00c52513a4410296044640d1000e008280d01030301c1080210010032034503407191014a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 340180413 1250 340179163 340179179
    0xf0f01050f061e0d1502090f120307260d0b10110304140301140a05010e13170d090b190c020c0d03030b0a0b0418050c07020f010806040b0607050601060905060301 71
    0x19010740354107260228034014080f07036281c1c0d103824100b05030424802c100c49541405548025804a000d0502480c40c80e2484860760510241002c000000f400095280030526259801503400900386001800e0300c04070300d409845003038805000d408036280000940c0c901100304002d00c41d1489841e500c10710841c0c4038085015100481545c0c102c521000f41d06030901410340000b40105010031346100340710016400e220350720750503901c014165010002d8170b0000d030b1600c608008840358050744c01130180c428a00e00c541d400c04c0c00400303020b0004c0386210200e1824019515529a08400c0343c2c0c4c80b0810348030300c58080744100c1c607014070385060810740050100096804041444468494405810305440e20240c40035511140c100c040100b100000040d251a12411b11140d003090300d07580740004a06050216016090402c05c9802c0fa070341c0280300b20164491200195103160005103001d038030a9072056a51016185d03907008281043c424006490250b0510380003500c4140141c02c8203005080910040c0001d103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 340181663 1250 340180413 340180429
    0x822092307031802040207151d0309010c020a1206090201120207030c021c080f030702120f0a14091c05010510030b04060504060f02040306020d0501081609020c010e0f0f01050f06 78
    0x7070154030300490140c0c00e403800e071207240385400d03c001d4100b44001100014040d500d060702600c5200315806202005c141004065070400310001800c0076003040107100141e40c02410030a901c40d20260100300450741e250040740784090405015a1801e0300c600c41c00d1b085607030003c00e100b4510b6509100718141a02910020f200d940d05510080c020032201d4480c6000c24100d0f0a032442e19a030000100ba030341d0a00c2d441d5910585c10564545001d8070a01c8400074200000c88259901c001304000e003182490000002111019881440e40d41000c900704002100360300c2ea00d00310036040318090000c81201c50146000c1d800c40700300a1590300c0b400680041400003810071035002e40c000c3c1d000f00000c550380e10b49040040c01841d00c5071360504818400a030010400455030050b04100c6031035642040181e80e100c08035a21012085132a038841c84600034180110340c1c1982c05032801402e410000a1800c0321004803510300602c0c445100c180ea480084407107007503a0240201940030941c4010800f0350b04104d000f1078040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 340182913 1250 340181663 340181671
    0x2010b091b0c1603051e06010b160204060f15080c031e09030409090b181f0216060c03020405031902030607030c1106010f06020c030a0f02060708220923 67
    0x2800540000b019108105103a400781140c160021403542e40c1c505155500c00b8141660012a80c01c005014003840200b070032030480d01103e00d00751034885c0c0c0c402c7c0c0050048001d00c0813a80180e5445010034854900030044001e400d80503000307070303144980007070207052007500a1080e80c400c1010010845180d038440507440c2060b03021300b03412502d0745844840d6402e40c02039410100c040c91621160703005202c2030304c101d1405200a01c040700d103203588101086459107103102d040ea0415034200d820306446582540180100141000e1828081403981c0d2a40180c80410031484002500071609100c0d602c1d06000d0598208000c42070b116003e2100e60100b074940c00010511414160b4a00501c11954000d0b07004c980c010084800b500c05560311654100e030920350a001e1b041c0141f00340d50710b102d070fa803c0c0064101d40e1690040c07909031a0380070035820010340e5402404102c0f07003004240a26003d044841d40c44d01c20125a60b440002d2590511b494031048450060043c90302080030010b0154603008031170080c1e00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 340184163 1250 340182913 340182961
    0x105120a020d29070201050103030f020102070302060423030c03091009080c0402090d05190302010b12060a051008030301030f06050c070b0615190518030c130b030118030f02010b09 79
    0x602d80b42d03018101000440700d40700e040f400704410800400e906620090580c1d01c07d464407500f540c0c542104070308030b0285c101c0c020003503440507000c100412040c040321844001c1d018640e082c11014500c1440c1190402104a10303603170310124040603940b8100a80c11011070351032508601c0146040007082d40d8807000c0c0e4403980210703030019003071300c8507100e18803480d02041c0c000c4110b8222400ca01e10195500d0b007092401e8006500c0d10041c0c2d030007840c0c001d10302104208502c00070415a11500203100040c03502801b00c584441503d81d0019410340300b0300c061342c02180500c02c08120348140742041d80940d540104001320382c0c030303040214078002030138840d1180d001142035400c01c40c4000d00e00c16206042c4a02c0d01d02c065000307510140c3c1040360380c2c40700040041c4480c91216528048102c401d2543c0c8850000460760f00c1148004004580442d40d404038200900040001c15005540714008043d4003803203c00b98000b8070003400c2c0540c00c540901440c0410072041da003174811032900000c1400700007010301c24030700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 340185413 1250 340184163 340184183
    0x5090706031514010e10020c090a15050f03030d0606090f0801061203051305030303240609090f04031e05030103120c020112240e0105010207060201023414060105120a020d 75
    0x10f90340304510440a04502074441075845103d40800396407900704501c3c05204450810000e030f42c802d884d0040c4000407002101c040c20241c03c10301009445007030110826014403003072040649401207405040020801c50303d030420100e090005003411003110707810400e000d80c18024208105003038002d118241503018071341551181148000241d00e00f01c168800c0390705100210900000003018030307010394003490703030398000c1c0140481005003c580c0c0a90040ea035440b00c80800041c413940d8071000116070141c4207140c116201141d9a54468007100f0340d91400000840101c0140100f201d05800340300070740328504020980c1c1e9200c0d0700080c42229020044c0c1d103501e444a42e6403a4412110500310445070701c880b4440002511a2075079410b07140d092081a005201e4010009050b50040c03003119140460640100b000d00134042c0c02841008100c03171081a008462806800841c1c603020503070180380d8902000d0f105a501d003008000c08a0020a54245290080d10041005079071300088803124a600c0b81c4801 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 340186663 1250 340185413 340185449
    0x1501060e100513080304060e03211c060e0601030b0d020a0b0a09171006050604060e150c06070e0103050c2b02040315020403030305220213020c0f01050907060315 71
    0x80b15030050b8800009440883c160105400e60003002400035580195542a001d40e103840c101036039403c0c400d00e000c5142da42d03d4140d140ca042030400a0040490b4908036400c150903c00701c20084401c648d200c002000024003c1c010950780c036009041c41080704407407003031a10350b503034002030070003000c0f48101441c020f000a0703c0c031b01060290002c0b000074041c169000042080f45034070340362222414061845283d1414801207154600b103c25681505d003503a580720403a070182014401402607509800242c01c5003800304890b81001040000c2c4200d4550703507000c03050650100054261007010f0205c03001440c06000b024586401d40e080d022011014880c2004c81c0728034800d2020003485540c00241c080010b500c0100e8185a09400a0044a2190b0740411145e902c1c000ea01e01507000c0c020322200d030001c0340e01451000d4030700303000d801e0411082240014070342601480040c0c0340c002c1070683c44c10a0394458040201c3c580d000c2c803101009003007500b424420800c5807481c01030551441e009507804107032051828 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 340187913 1250 340186663 340186667
    0x1080f07050313230a0c06050c0703060c02100501091d011a0d060b181005010e0a0504020a021204180609050f0f040c05030303150906040e0606061c05010312021501060e10 75
    0xd030130b140b460750351400c4a540c000d002c1e5500e400c0c03c0e4106070346444000c000003401c03c1c0b01d403040311068409600138100c45420341d6129030103481000000b5046101d20003408042d0346007445801d000707142125001501d000c5010389103881382d0324002031075110b0b450110008611031145145824082c0221b40c201c510b04040d2a001c07000b400d00d0700505801c00a0408901000c082c1c0050f4a070081500a840e088100c2e0b03070383e004450394040d0b90417198001804400401c910b042175005400c141c2e2660043d40c00544118290507119003040e40100e20240c4900150000d0080301e21034000503129200051000e403405901e201c502401c050324419103220900006814454510001005400000c0035240c1c0ca00b40041002c0d01d000c80300b100c0c24402d5a139100407078500d1a052144a2402c5402406440282d4039401000110780050061110803014501c110000300024400e8501031407046014000e10241d003a0001e150011032450b01460708001d000500000390010081038440c4001c582e07800303411101da101 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 340189163 1250 340187913 340187933
    0xb09030a0b07020d090f0b04060c05010e0d02070f0605090603150d080a080109230c0a030603080f0a140c060a0203070e03100903110111030f040305070807030c0201080f07050313 78
    0x10140c20300000d18203020b031072540840d406a444060743d41e1131036400c1d1210701d0320030030300800d1003283c0ba07103042080100140c50064400418940c0030300c0c000102401034103074103030030410302d00542e60060704140f03c1401001107006420780984090f152007428900100046252031201400c030284404400c08804910b65a06440a04c2c1ca50321210494691070350f1000038103146400e0142c547d06505008070304a181c54207401c1d040400002c5c01c40740c009500c3e06005105140c1c460744280c401c154a401010000c501c62500505110141c042c006d50f80c0d5021020040698600f84855000f22030708100d600c1e1036201c0040c174942c0206440c0c00060b0f0300e03220b4200944440c00c10546940d0513004181d4400701c40000360b80180002d5009869041c4007004a4003030740d00300d483d107000001c03584000f0300102d441d500302c12000c07942c000d02c00c0c142107142488a4449940907005400100c002a5001a02c20119680046076582002c1060030041213800c04800c080c2042c0001000310502d05650000581400120b1076 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 340190413 1250 340189163 340189183
    0xb011b0503040825060c0210180b0a090e160207090b010e0409050d020601242001110c2104030803060a05040e01020723150c070c1502010b0f0a0b0903 66
    0x444803401d1100d4214480404d901c01441c1c480300c0c3d598000107103240200741042d060f41c0c0c010480b00c0700926507c81070740c1420250020b0030b8414092013000c07a000c840c0030021304480c28203403100003200386403403041c4803c29001800f414400301e001c032041c1342c001c1d0001044e0b41075444606010904070b07a0348c00120b80e00c84000c04a594014105010031040c08404103820307426110a42c01c0e1141ca0b030b2601d807822030b4100d6000007113180c0401c0101444800b8446d0b64010070400100000e80121883c0040c0c0b0f5082d10410707240d0003140c640008507240d0301c40c0108002020700340030072018914000786000302c0c41c590140e440041c02d50100080016801c2d80c0790b018a002600c0010010040e030394400c00c820303000b0341000804840fa035a000001c040f49507002e8600b0761154034040d0052141c080840300c2d2860b1b40c4006803840780c0c2c0020030b10560700080c1410196002400441d08590415408a0310083c2580d0010980e14000c1c10f020000c0c4400762944804070051318442c02d00241d0702c9034480040fa00e0100300030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 340191663 1250 340190413 340190429
    0x140f120c061c150501080a020f0412050d0915051c0e0106090e10050c030403031d01020c161205060f0702071e0303110f03030417300108010b011b050304 67
    0x240c107100e0740300b2031100045030b81d00c202c0c1c0030030800004120094030368a041c020180803c64100000b0707a950741c0b90b0000c0c0b8520fa42d00c00002e06240e41c490f042d041070312400350212001d8102c00324035400198043e4022000704149200158102c4502a001d001840340d00b50610000c6110b000b140c0070307914036410141c01142c02000800ca610b655a516500610140070140028040c8502c06000d075102c6000e078a000d402802d402c0c40c5103842e66a0190000d110b03c215120003a8529503180030300c0e01302807001d0500010300c20080d0195114044c1903c08004480d085080e280e102a004980401c2d00021419030241e2866130a400795206c0b44402da140010f1a4000c0a41e44602d4882c0100d41080000d4030b006c981c82512902168055070700360680300d041c04441e1165a900500005021a03007a8041c040c0300855840c0c072a290025540c135081c2d414002c2c0e81c8074540e10000302d14807a041c24042c2d95090050101c08000c100c10f8104400007040f10890740c44403114008076071b8080040c808240111001001c0740 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 340192913 1250 340191663 340191667
    0xc212502070f080c01020c090615030c071e1104050c04080a150f0b06030403080604020702060c0102030f22020603040515240102070b120a1512020a140f120c06 70
    0x24140080d603400d118040c0c03511034001e0403030004410b140094040782c100d00580140600e11a90010b101d03030520000c040d207030720241550036000100d40402c001c500031340308100c0441c1e440d1101d040c80c4245d009964440c4080c2c50203400860b001c03802c28000c0c03208040e0300300c03804503440e150181319001c580610381180b940c5002c0c0c49400c13004c20000191550b490001020240b0242419412031400c9070b07a08202c5030b800c4242040010000ba200351506580134000900040c00c1920325004240b50350003000300b00d8440da40c0041804112000d0341d0560b5401801d040c25201c0714064034030460700728510102c000f0f0082c240400498108101071002141000004140c019503181c01c83c031a5070100c41300c2002040c03514840038100510f502c085048000d070b86900d0700a52030180d522024220720540200320500d0507543d8940440c000b9002b4013002c00802c00c42d43d10114404550040022160b806d6119482c1070910854107440d540341c004070400d00d18012100b50042c038101c81d11303131414801c012045036880000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 340194163 1250 340192913 340192981
    0x90c080d030911030a02030d1119060b0906041b050a031e0b01180e070e0f0409050318040204050f060a09150c12030212061207030c1205060c21 63
    0x1250344142d032020302490071643d0300700041d0285521114011406500741c0c2001d04500401402411001c01001340342d0126104010000303403010102110820445429480e40c4500d0303201c1c80c3c851040342c0c000c4000c03034042140b001080741071038080b00003162110920101159205c16030703009501c01104205a46103560f141d0007003107a090001c0030444c03040b9002c01c0009000e5201610300000110030b5502005821a41c3d844410090325000c407450300844d03008511180001140c0c4850203501c29180c0308100850301c40d8441c1c1a40c510380c014194560f4007030352046c081081241d0381c180c080c0002035400e07260f080e0780302c1001d50221070300c4000790800746012200d207c441e00c00540c880184407101e800303002070144244000804070183d1180103081600b0101e01008100c0c075180124441082ca0100300c1200c0e0000d07565542d40d900205554042d0640140d001d42c0541800760611480b58001e03030036280e6620740b802c03001040f00d00040b00e03814141c4800d1990005480e1040c2d189034210410350348944444450070b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 340195413 1250 340194163 340194167
    0x42d021e0d0608060f0615070807110f030f0c0d0201030e0604200105072001180e01080f030309150405101b02010f061203181208040f0e0712090c080d 66
    0x400004101d5005103012000161007001055090050190b80e0640c00c054455074100071580c404880344900205003008038000041d044001400114455a2140d410002407402c2080e940450841c0c1030090700700c00d1001004a0b0049158015080b04840c058501c1e2040c2c00101c2c0180705910005003c1e109000a0105000703103255013103601c0800580f0031241c0301410740111064001e4203070040840b04948240180490100c072554081c580614103ca005c0c00b008030440c4080b1015807148408014000040c00860000c2c0240180c04800303000139859401d2400c0f0159441d84400781001c0c0350650003001c1810010140703c6007080c115115030a02450031072a107092000b402070400d000242d0718051202c82c1d1100c0901403501140da00142d40c8000500549095909695024500c1c812000382800030804581401c1c0c01611280520400c035280c0b81401ca500d03c440189800201c942c0c94544100403c07e6403210a50481110031000401c407880c5d40d240c0321034241c0ca1a0426640c500800c401a81c94039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 340196663 1250 340195413 340195417
    0x170c07120203030f0703020403020a0501030e0109020910061202040b22090c030506090906011404020a03060906030309030c09060f03030507021c0b0a06060c051b0a03050624042d021e 80
    0x42451328000b40680c441480c141d0883c8905e03c4020740028807241e00f0882503020303038400b080c03c990800010400540e40d80c0001c10750f40c01101c0c2000c215012030400e20507240d000e1241503018030291411031806080005074495805008481207034803020101514603030512610220003408150010300180315104c1014024000440d55903000d400b007000064441c140003d2070314120761f1001413804546030404d003071001035031080c410b5605050715144005030420061103080015030003030381c5200c211800d62030a00c00c80340340d5034007003810b0600b000001d04c0140809501c0301e04482e49414040e607100d0803032003c24039103c0200326441c5c2021010103041d09108034200b10521811242c0f000f0011b141e1134010548400e00042800380040e44000034120720060340c00c4580405103801001490070355640d036110f501d0603100716440302c0715101e50288082c2c200352008624555402c1110305001205c2c0b00d20b200801450071001e4425540c091440b400040c0103198121449c2d01218501030703008881c0070300c8010a903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 340197913 1250 340196663 340196671
    0x12030414010807050909190e030c070302040c05070b011401121d070b0403150207060209090406091a06090f0a021b01021c0501030201080f040203190312051006170c0712020303 77
    0x2c102403000182c0080d1042003200c031003d800070b00480300c50f110300c0324516035120b55446400c143c958400702d408210700108042c01c26446424010a0003505510520050f1007510b80400c05104042c0001c40c001044140202c0c1564404c41a8803000c0d9000300c0100d54041201000108191a001010300a0035040424005908900f81214440d694a040d40300e00d9108501c0042c110b84903c21089100f605150020920709000300009400d12403100002420030360142c40c1201e0407696040400e08101c41d4005800a1500c0320855151130301c1c2c028086580720740000c0c0014150b012841c00601030300b140d64180c9580c0000e08510114170120714082e1030003540206002c00140410049100b02d01c0b0090060364140c82d4181d407800b82648880000fa905510040c0c812030303140c050302021001c04154005002516802aa20748040401180c0d00d5130031510041d0000e4a6146052418041c0607000b403910240302c956541e40100366031f6a4140c6e00d0b840d0244400050040101ca22203a00081d4000061406 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 340199163 1250 340197913 340197917
    0x5040f0c0503061e040c0305010e1006050402090f010807110d050d0509010507020c120120120901050402010e060a0306050307060807080a02070c0e190504081e030c0313021203041401 80
    0x40c6a2500c040507910718044442141e0100404841030145080110890700315218240c00c0840b6500d0f40c0c0c419003940c14195403003905a0203a40c002d080b4401c14000c02006240030ba804501d402d40942c00f20300352902800c0943d050005000c00700d58141c2c81188840e078a0b03030800301941c2d80503101b000002c10320381c094081000c07450300382001310310038000c18400d650241c41a50002c0a014007424180b210340001d00b032284099543c2c40242c4060280300404400102c0c0010405a503a03005e0420540340800001d498084180c0c03500c2c08120050340c10020361600c5001c2220100c1d1902010002100600119005180c06000e0903038001030960b000001c00c1d00500d80d945568407641d0300d44c14510101d018040003d00084402001040702500b8004015044503100c205400f6581c040204601035800075903040751400800109040c011504003500031b1141c2100401519504001c1c841c3e03a4540009004c1c40c0000c040490700100310355400c440a62010030510030f07a9261560348d182c01c035000c01c14031000c1340 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 340200413 1250 340199163 340199183
    0x2100306051002070f0302010810331b200a0b07060c0c0507031b0801020720032b03271101050a0804140c0406080f0d0806030303220605040f 62
    0x60160012684c41c056454040c0b4040410345982c0045640003005001060314044443e0042410414100c00001c40346411441500c02c0781450081140000c0d44030164042040740750316031001600440c1500303221038118250035003285000003404d171000025031142d03500504824001481d0403045002c2e02c08a40940c000f0090991007940a94107000b40d2100240385400401c82400020554102020400c201a04958505854130f1807503007203911000040e02d952a0651340b17125940b04140301d400104038158090200580d0211182034410000200c0320071207034055581c01e4400e4401d500c5114082d10800f04503c6c000312000700ca01801d92489000c0d00d440c0f050000007071a41d4062070454025005903a16101c00741c1e2942c640300311080181800c0c0e03d050003000e4159946503154040c03000a007a080014041044030411042c1ca0400c19400b000d0521030b0a004100b543d170307000f005690f40070201d14100303216200b28050380300711940020700040500e440c1c9000e00090000c91850040d050784101d000d84 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 340201663 1250 340200413 340200439
    0xd0917190f050405180109271205070209090f1204060516050f0d12050a0b01050307050306010216170c04180209040606050d1101172211030105041209090b090703180210030605 77
    0x1d1200e03000f41c1c1c1810400f1031030340312340c0c0040c81e42d1144899034031262811a003000401ea000452995044d104410b5560054115000b40d090034404440900c0a001c030703031403920346054009007407801202282170311502044907100074060140f10b50412a00c40c00151202100c00140c05000713950511000340101d40b514000841d004c205d481494241c8005868a5055985060702151039030701c014101e0741140500c01101200d4550304804102a003044140078001e2480621038170302c2c0c80c002040e4a4400d90501e402e2969514400d082803025640548507150f43c0d50315400c2540103070885074081a0041c0745189104144050302c0ea650000e40c1d800d07680e1039424030f51040d854501c0c050070380389903100f00da0310f0a0900e80008000801d40f0514428841240364000110010f03007115002c6905a030030b04012941440c040c2d9206000383d0141c18055002c0020f4082c80003c02c04186000703082600303143e516215101040da4502101141e5540148511010540b292004025082903c83c103800303101195010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 340202913 1250 340201663 340201691
    0x303072a02211911010e090f0a091b090606110607090522140603060c0301030807062d091b0b0706090311030d0917190f050405180109 59
    0x14000590010002140150103010b84101d00c0e40c000c801c82d440c0d2044200043e0a010043c01d088145401384890f04c3c0031036141c070005010b521643c1402449030328150100814101e4803c0c00a4000d940410005045051407030320301ca00c944001184c00c101c0172401e100213401c495030b42000050320180e9035040d80000400c00b0702c81c4d0b181c10a45964000c141e501c20144194200001080744074400c01e88040c1e0440e0344007001904480c1c44400400020288000700060b5007420030607160800000a10140b8642c9507456811160054023070060809888a841c0700c00c20180c4030366189140c0e010750784ea0300d000c1c14581d0a0300003000940411542c0380042c000c1d202c4070140030001034086480c1d052449280c14290341da41c00052041100840a0056100340f40588420800c09403419900303d00000422514900302204101d200d00d50030303c1c005030200b10002c1c00c0b000e1840c204582003403038104030b004604004001e499030f001e10f41040b908110f100140700300250b1010f0003107040720010102008016820812 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 340204163 1250 340202913 340202987
    0xf0f0307151e1104090606080f07020d021c170f09010f061203050c16030510050a15030618080a02070608060a06140d0f021204051b100c060905030307 66
    0x80d0910005484400d180e20526003150880c043d0f82d140c241d15180c0c545000b01c0490301d40b900040d0000d00740e0001c10200082420469410038402e000a0415100c41400255a025032a0008440204c107801e4248618020502e00c50509403039071880c00b5a1500d4021421074103400c441030b00056080c000c8003080b40881d84580000d40701c80790a00720145605481c1510a03a2012510380f8561007902d50003400300d12100103042c00f552144018000740c41d0350341203040a41c0e070050141c40840345030680d0700d000840c83c1c40040c000c40c0d901c008003080021030610080c002d4400700c0409001c41200140b0700c00790940c042514026500f55480364015a11003400b1b20031441e40f02d00812005c298100841900c1082140c0a08801c140744500450b03031030000d494a00690300300d0a41a82c1c0142000f05220800c01c05001c0501900040f110007030009072003c0010303c81d0f030310310000c140a106000d10f074001405100d80180301901d0f0040110b82d664144001d0040601028008904403a40da11050f003120341b80f2800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 340205413 1250 340204163 340204181
    0x60109030b0105040e0304050904060e0d05031302040509032802150907140607080a0306030204141e1b120402010e010c0312020f04051201050a050c04120b090f0f030715 74
    0x14010078942c0c2400700303100090450b19480c02c202c0c40240000542503070b4217006103114a1040a01080004840d00a82c0ca040340c4005c0c001d043c028148100700800d502c4442c45010141c04131030125094648039034460943c85251404c0310b1024108005d005c546c0c00941000400d03c0403603007124100b610b4100c0e241c640a06c1a070701c1c4600c07504141c80800104120303404a10083c0300044c0700a107003245035664121154001e0101c81d0203c0c3d00e0314810015841d00e8824848200f040c170403803c44c00e2506664445004a0020942d40300e081c0c0c020204813118030000d05200840c0b076541e000d541e40d2a0042c51321302c1c240b600700c4040740041c0c2c030894202c900307502c103483c040300407941925010614064501c1800194103e6201803010440c140700004180c2d0301c140c40d2695080040c000040c00c3c1c2403c407003004c01c0d5000100030039a05c90003000100102c6031742000c0c04845980000407002d198561403005810446210031021080c8510154641e4184001c00200420f900c1361032480009040c920000c0182c0321062 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 340206663 1250 340205413 340205423
    0xa060908030d0f1d01050a11160209040615140306010506090915010c020d1223091e04020703020f010c0c021c0309030803010b09120a1e06020c03041d06010903 70
    0x101041d207422000e6008a0740c010400b0f070340801c22224090708400314a10b039012079403a50303464000784800400148501440d0f850302e002440c0c81c1140102c0d40c8540b841c1000c0009019180000005041c0842075001540c607080c4030605091042e62001044544440c4640080c4a4011940002050301d000e4003100d0070b1006c0604002110f9440300103034200041040001070600000202000040e5203183d003405031144100149009070010b60002401c41026095103074010803448121006a856a42079130f12240c130444030100072000b608503812101905854240d0080d00200d490f008043d004a603008202e00544001c0040041110341190251080f003800fa400c9040c0c01d5611821841f10111882010702a06112070a695203545041d41c0f130344243d0000492041c04a682c90030752610003406503152a01d00020085100141c50720300101000480714011400c2140010302041410b40503500116402d40680781c4880c0e9406100c2e000d041d5500500450b10031802c0015050340c042c3c9140707000d494201c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 340207913 1250 340206663 340206667
    0x61211071127040803090c031f02090316080706080a05040c0e060607020924013f060801020403060b041b030c091715010e07020303070e060f180a06090803 68
    0x18288600c074061507810381400426100c400b54a2a03080c91818000e40c03144402d80c0d6070b03103840c003089800c101f8494034491090300b182d180604880382032101603080003075804005a0300c82c4500006803034903030407216240261302a00c6000030058408161041102e540e5100c5ca00d059a070310191504640c0210340050255040b000144110f10380403003402e5100801520340c919100b070503000100004030444003084902000307030703484100851003514100011421b0920509810001e02c03000f10010090501100f04280c0b10802c420105400c0c0b41c1d90494040700500304070164131455068041e41c043d0206035040d42c10000b101d245402d0a2103541a0b40100304044480501d2054003200504101105a020480711102c0841c01941ca030f8001036200340850001d081e445c032180d2030300f600508142d0081900c0142c010400c4403646e00803080f0b03a8041c02d80d190514000706140001000790180c1c81086040d444045240c2c00d54a9040c4540c0c190040c04686034122199944003c4844603c2c9001b000340581003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 340209163 1250 340207913 340207943
    0x304080d02070309031407030309120f0b040503040b0d0e0d051c050a020c031810080106020715021617010e01050c07020103020f09270114010f1d04020406121107 71
    0x20303809040d840c0c0c0f003071a00700350141e035a80313134908122540c0d40c10300080c0c0c00104c0200105074000c00260001e1452100c1d128640b01303c1d80302d004481c00160005801032800d100001c080010910485018012889826841713002219984005000102a140e80ca00c03502c054411282c1c040d205640340d480c800c0001c0200391803c2400500a00000b502040da195001c2c13161a9600809001409050400030003c890f880c40140404c410060504002801d1055440c0180b01869000c41c2c80702c151560b00c01c80040e04460a4000c0b40340000007400c4040c00c2c0c4d94100c0101e40702e00c2800c0b9034042100e5582c0288004e411000c410303070880f01c0c10707600191407003001c1140b0340055010390050195005030101c01400c0a0101c00424007400005000d040102d072810408001030429100603170252413411546170a5401c8440060450b5120303c40c00010b010810f00c486c0c3c0c0040c00d4610500354400054010f5445a5541501414a21a400507210b6030340c203101c24014901c0d4480300303643d04a908500c070800b900c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 340210413 1250 340209163 340209187
    0x1a0108160623040b0705060604090b0c18060414210c0f0102010609060602010203250e0906060702040c08010807060e0a060c050a0501060f33110109170a090b030408 72
    0x142e40007803a0a00c2010011604070301e003900000e0701c0107146110040d070f650a141d14095052140c014100d511441c94400001c000c5003590701c1c0c5941c80425161100c3e070f1610441088812a004610320a500610008012810b940c40c010403400104064440e2081180c4070300030440802d010407001240c0760300007101413001d8584491600c42c02d407410f000024030581c4a251280980744550060381c0983c0d000014003e190f08004084000d008488419848240180030010401900106218850f002140c041881031740c50030304030344190340d00500070005c01c0c8001001803c20302007442014401d000340500051843e00402008449841c0106550612420701e01c1c243ca184190007015a101e2041a0103200095070902c161030140c6845001d030103400b031401d104503c40d40030380528804281969807174102c4064028100c001d0701105410450704080040b076415005140704c000250114440e4000580102034000c0244a02c07121030b80c039035481644a01000c040c41c4070680780201048000c02c480c2c90805 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 340211663 1250 340210413 340210427
    0x7020f0d020d061a181815060f010e130507020115030218040302071a031501090803070f110d1104140118020309012009040e0d090302091b071a01081606 67
    0xc076445845281a02d00c00005c070700f5109400000904043c1440c00f07000742c0d0a20010b07a5070785107043d48000e043c402016041c241015001400b5103020f8801801340120304e80c00b4a4401c030080401410214078410742e22214405024107990801c0903510344400780000d600407206040c03d40350040c00c10301d281d4018003065800341000410940031030050354404554203142c5821059110310703c0c04400d4582c04c2841c0001040745032015030905200010800704035641001c400d0382c0c5810b400403400b0001e0242420700d403581d0039210003400c1d40249030400b407030304011600603d640766440954040104c41111840c201c0d02000a009003007825401580840340b104079a002103a0203540c030f100100c1c0b8104084a80707041d10055824000d14180301050900c003a003400d00c01c000d001d40380c160040135218440c2c10b0181801c80e1602000e40640070240000c0d9030000340001f031181c10701c144500581d41c0c80c2e00341014541240584425541d0110700750001074200400240e455031404d81c3c480d070001480c44c2200584940c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 340212913 1250 340211663 340211681
    0x20309031c0213151205010e0105040b01170a021b0105060a12060b1c0303150b030601050702010201140a0603021002010605060307260127270305070b010b07020f0d020d06 75
    0x569020000c1280c10f10000c00c10000070194481c1500c0a400820405030208000248044001e4078000040240076100620107046660685000604010390340048811a81d0041c043c11828008000c0c8811406a54005c00040f070401d5402d140400e802c1140500b61201030314180e03070011040d08107010140114034810600e0380b2a1800140601500d0049400c80c00005050301174040074140c0c0d542807503014055494030310344c0d0200c4008010304000c510686030102400060400030f0104400007164000d40c40b654108a411030028110716010403400003829003808224018002c3c00da10b0180c9a0050040c0c0d4152a4024a0642503940d04081190184007000d48424034104844d4104400240b40c0406400f80c00c0b55090312601a1300d120009916000200c0e5440741c0b0b41c0742c4609540c02d10300b180d510040071040c0003488144800141012561406440f00140200310150300005201c082c000c000d203d02442a20240107000319113003003201c42c11944034081e400003c0c42d505000043e20360340c490851 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 340214163 1250 340212913 340212967
    0x1060b0418020a170703060303080f06090414030409060905060f091303230c010c09171e0120090102010c0507020616060e010f0b0f0604182703170a02030903 69
    0x4004c00000c8500030050040e2005000700340d4a60b8103006041c3d10020050340711600148800b00d40c00c040c404284820300080c805020178103001d00d481c0c100242401210300600c9141010310900d500c51000d08020242913907917902c505c1c0400d84510280c00c0ca007c256125107071203a0003202d00c0740a07803019902e403841e40c039507031400d20041104900340300b0f0000040c1c080f8041403000021949088040601980d04a4200358864540300d00400403901d00081d46100c06030051015a242c0b220410a45014214a044202003440c507034000c0000c0104a5011b0040f03447c09900030710500c03c200b0810b0f00d80d4828130b03801a4101204104507804004024001810b40303100e450300041304501b58500c642101d55240008000c551500d100401c1c51800d184915030048040b989140741c24904695400c80216100008112540320602d80c5104041c001d001e00d60341200d490105910b460b1450000c0c03100071a0001c100d2080452004515400020310a687c402c00e400d000452405161201c522a1070914400d0012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 340215413 1250 340214163 340214177
    0x1403070504020307120509030313080702030c031203040c061716020f010c03061a0301060f0f0c080f070501140702030d020f092e030e15130c06050c01060b0418020a 72
    0x4998581c1d00c02180701e903c07607a0b03458082c580c2c414412010b450010384050156030040c814008024501c5000e0001c0301d80c800021035480b029803010038280741014500a030706000b014010a14190490700841c819841004104c810365102c0718182d0381001d00c0303140d00c8103018200300001c0c1058481595840c9078070240c0100c0302c42d0b00c1054034042c2900c0c1224038400019031911010003102440c00180034514031103c400c54250b40c1070010080c42c40c60b002040d10304100c05500070a42560090748064070842e08507403c5071790746881204030645544041e2084a1640c40c0045205480f0180c5241c64003902c0716a000e1031034124000c0c0c4a2010350010004880d110104210480403581c0f00c0280c62900071181e5104000315a42801142c0341580e6401d40500341401c2034081890608040380360a00941c86842c1c09009031102460104848810f600050110701030350400700c0d629800c5406050700406500003400199100c1d0180b4800d40607900c140ca6000320964030350040f100003a0060104000d030b43c80c002c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 340216663 1250 340215413 340215419
    0x21c0501060f0813170405040b040506030a08031305100203070f11060705130509010807080f0a0b0613110c160602030423011112190e2103191d030105070207140307 72
    0x24403000078030300f00905e030500000c04100500303043c0510902e11008903000c00441c5000e8004c2030700c45c1b554600084c0021310020000c0c0d00c5645a20000b2045034014003103824070031101241c00003e510a1740d410780803c503003c07001c00030188034840b145200c6403050090304041d1075002040e11607402000910000040e140030109241d19100b81442c02004103000410f10145040000c03801d01c240040c81c20015001021000003040f421081d158200d0401d03604101c0140d00c0d01c0b5800d005000369510f0504500d800070380440e000e900091901c1d05007051b00342c2400c806030354001c140d80d41d2065205441403940c0001600b00320020f45e2611410940c2c040c10803480d400c003a818158240840403000f020114004102c800902903c0010500b0554103410904402546100081c410143d040080c1806030718280c101c20305810180160340910280028204030b0540700000582503030030704011802c0106100102c20024075050003040e0040a02e80c019188d03c609007510b102030f520111008980520400e0000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 340217913 1250 340216663 340216673
    0x1050f0409110c0610140d0320011811041b050304080f0706090605040b01150c030305040507120b01030b07030204030309050402090102010f1a030f010b06040608070207230f01030b06040519030503040801021c0501060f0813 97
    0x105040340e04c81d88461000c10314900030001141c085250740c80180ec0304405800020ba08502280d80250b004007680352100301718030261004c1e220b05a802000142030040d1a4100032090300520701540c810043d11420b030b80c0300e000c00080000c031444800009107280000c0d00100b0702070351080350003a0081d0285d800f515240d401b80800b03c0e82d005404c49900c0d805100400a1041c904840744c5c104443d858158505031450314024110b000074000c44d80700d50f90003e500d542036030003544004221509014240f000145c565103080302c1c10385400702103009016245a00040c080d041c072035075181e60b0000700040d061038201401152500002070840c0203522500c0b40120300440c0d4100c0403800c05042e0300008180d20f01c00c9091091340c034401754009040c1030600001c582717980e0365581503600b0342d04240c0d8440740710341e403842402003881c040e81e001030124000054041303030700001074009140c091401000303000300550a025000455009104200001d200b2003006840e491085507403981100e00504051700c8100d00c2d03220 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 340219163 1250 340217913 340217951
    0xe0d08010b071703090f0f060601020d052115010e010c0807082a07091103070801090c20060604050c0403120e040906020a0809070501050f0409110c0610140d032001 72
    0xa00c444075404005206c41210007080340418444106000c8e0216060032030010f0340e039440016880702480300100c1d81c0410041d60380c180c005003903410811008907050000c0328490150790711402364000303950322010000e43e502030050311007601c0d40030400a15000c416101e8018580100200d80160b5918a8540e26100014560038a5421038400a0054a0f2610403008100c1d40d07007584113003440109200b08404150031254250440d4814030000c6584a0107540c01c94510304198070f4030150224814035000e00c032000082e12032040d9800e80d0300f00401e44a8036012003481c0a20b2000501500801900007503441c40750f03401841000e800340011a4a00155607030700f050340c200420307060014681c00704104410b481000800000d04013800d004d031505c882e8080d1007080d032255000c0c00f1102e940700e0f1424500b60003200203d4030f0010412040d03034a02e0905400b003042044281c8100c51212581e410680030915207640b0b00148968107072030340ca40441d845c04002c0280400e00c41c400d001d6540c0c681d600e00e281c10031148 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 340220413 1250 340219163 340219171
    0x5060a0306140a03020f010f26010e01050d0503071104180501091119060c0c0905010b1804060f0521010f090501050c13030b191d010e0d08010b071703 66
    0x340440d0706802c2501c401011040d100705144a000400820000b6803180100c0f08a40107003032034207000000c0d800c0c00581e101e00c003040e14100c0d10309a81c5450a0402e44a080c4d80d410f07611600001d0b40315990310f40802032200080d0a001c0d04079001009a000000c040c08005007a011011344041841d01b080f203108003440107500805d03140703651640002800c102100740218100c06040b142850228a0108400c02010300340c020b1009004165003000140721403889404002c1910392401e00480d03071135140c4104140c0001c41c2602d43d42000e040c418110385460300441044c1c0d40074804c0c10800c1d0345804108008a68044030001d903808a100191720702c03040c20301520b0480e5401d140e000c52001860700c2c00c5401c50301c0040c01c102c00701005106100201101c100c407201125040707050036620740c41d406410081150100c1144d18607034a80000c074902051403071240508428074000801049103401c90f01504c3d081e4095a001c0001c07011001485028000800790132060f0250400400c0030b0400100a1043d40c0140e03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 340221663 1250 340220413 340220417
    0xc0a170106050403060c02121c0b04050411031b090703020f0c0717070e041509080c06090a020a0506180111010908070c0e1803070b04110405040b0403080109020906030105060a0905060a 81
    0x190a005014440c0191b2210075410b20007041400400c4080c82158000c0c0c540c0d0400011660208611407496a0000f0b0030b81c0c42d0040c4108040e00307052400ea000b4074601c1040c103020740a400809405440020100081220050b01101443da60518110300942c4009000c1545074000d20408010341e90403c10080a0304403209103084604940c003d423460308581d68050b48412032400304100000d0104ca80c40f20f1245643e03031000c24000142c2c5005406c41c01503c8015086208500c200090090005150749a0318000c2e6a0a04000d0301c0d1820701007144102840702d03210104035003c1003419427084624041010b025030001444050566030010103610040042d104d01d2581e610030300c046044c0c010915003009000c4e00f0740d040201002c05850301c1c0e0065400151032000c01070000b4050100075811180c0d060302c0140f041215107094900301c2181201510f041d03002806c50000031840d0302c410303c21034004d950014600790942c0e00e008200a2150702010102c810440c1e60740d00020b003510384001408061f030881d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 340222913 1250 340221663 340221667
    0xe040606030302071e0306090206071406070905010807051b030c030f030a05090102071a04021c030c03030e0c030712020d170403110301050402010e060c011d0c0301050117060c0a17010605 82
    0x1414004c0c5400b6940d005400c540550034040892000d000101d0421242d01c1540440ca00761a800082c666000312400034202c00818041c040c009840411a544981d0040d1255812692102d0044981c1d060840e40710020070700401c0b4008024921000c0400c0c2840c01c0b2040b203281020300d071012070458203c0c2100d42512407000c000d00602401034080c030b640c0308008100850815403140c072441986410072603c4602060718001260941d01c60245952506064614103501c21915260042c0006a0309c41b040d40001d03e441c41001d105000402c9080401c0380081c024600c2c0c038209605d0740c540c0c50110b00d00326848020803031300e980040c0c203804400c0e0400d41940811038a85c1e1079401c11200c58015102c020b40b083c3d14002c20040141e030401d1284526a100741c45994640e41200b4600340180400803040c0e01101850303811041a400004900d0b03510101500244039991b60317072803078281407003407500010950382140000450038000d00e13000e0b0402145030310345040c281d00700311800f04100000380c1000c1c00084e00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 340224163 1250 340222913 340222919
    0x30c031b0a020a0b18064302010c03110f0a020102071208010512012901020c040603061a0402091c03180f03030306060809100e01060506031003110604080d05070c0e040606 75
    0x404c4820b90341c00401c00c560106001c0040050340d17201c0303500400a01c4041e40703921416000607131250100e030342c1a484a5070022460120746070000114449450b1030010341c02d05000110240c0f2a000d031400c1c8800001006081c040210075544003070b0032158500007150341c20302c98a4003080c1c0c0000801014240b58032907003600d5040600340140244c007510300d5000c9a05107021100011040e800b400b080e5110300d001c002c00f040c58440101d0901000c00442c590007402c0102c0803051186a9020321040c400030290a91450411410701c010780c003035202c98aa01840056100c0700c0d001100103001c071014424908204c03540740001ca00000c408140d00405590404008240205901407003507a000d4030007030030221039919141c11055965954080c0400040e6190b03100023003010402d41080b0701504000300702076101e10b0310231840c0c8400c1e00030b48001e5491130441100d490290400710708131802e403813a03003014280d01d00c22000140ca25074002402103600c002500320004e207520280c00d441d40110700ca04804200985 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 340225413 1250 340224163 340224173
    0x21f051005060c0601120c08060f06090a06030b0103080d150609060206060109080604022211090f0904120e1302030403030b0a09060602030a110c0904140f030f030c031b0a020a 77
    0x140c110a0003050300f00301210440c84005000c40c1112039090762440003520616000c048a00340382c4c803905091049905002202c0310300b80b200c0d0300c254401d6500987ca90780f1100c89000340c401034403014004150940040c004070360107500900b8070300c03150350b0040398890791081d45001198466220400042c1c80c04814408603505004482d0014024600360a540d4108180c2903202e01010744000d00c01c03040c0030200c11241900780140301e10020340c01400c00103864500c200d52119170041074050300c03400300041d1040103490400c011900841d0004003038030307000c1a0001c0694403082215401a4020703031280642035540c0c1c0b60300007984203c1c032030781c1c004c035624401405104600c0880d401c1800c20701e04081c024001e4030780c0002642c012074914900809460702d001401c0d41044041840c0b0307030300314004030200814042d5025992102c1c0e44448200c2c1d0384080c091845585900540c01100030420f02080402c00103c81d0030b0265403c801e00004400d5512040f460f503c050b50712900715000941c000c0310a03201442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 340226663 1250 340225413 340225441
    0x1b0f080709031104020c121b0708060907150905090106032c1002090d050114010503070b040f03020f0f09010e01080705030a05150727091a0a0303050a021f05 69
    0x54040d05100303020390b0541da140c00b080020f0302a12070040d540412440340505003006600110701c081a0355070742e2080507c14180800f89807100302d4070380d0b01c5402c0380091072000015142d0310561003440500f1440e41071020142030980c04a28400c1000740d400300118156580c0001c40303008041c580c500250380c0c929070410888503000740f4200e02c450b565450001d454130b0004120030b044001400380040c0d9035484500007489074816030402818541c0391007004002170100360305407410390b00e08a04039a07400381d0b80c03529a0301d07a1048ac040c00d03c5203170324841c0800c01410141c0ca004441304009040c161a075100030042241d0410903441082880094401042201000e0080b0b1002d0300e400d030080d01c209041d58480c16680d8034007a031544485008040003d0348035209202c4044590540d0030560314209042c1d03607803224a11903004001c8290300d00880310705034024001a030440040c2c080c00700b550781450351b1400e03550b540180003000203600902c444041184c076034030168030001c01e0712900011036080030b000c904888 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 340227913 1250 340226663 340226671
    0x91608071a12010302010813080706050f160e060306061c0b10050408060c07080702100c0b060907020a0b04060b130227060409090201140c0120041511011b0f08 70
    0x341c0200300600c03150500c0c0c42443c0c1540d8080c2000c80319074484000240c4481110030018004500104144042001c0ca4015a008080103182200c5a0712410b444000f250b00b80b0b4140400b095085a005500d401d14202440e880f074070051550381000c2403d00601c5070b41092105007e010f9594902ca0040b03490b18002010b000102817034131a040078200085180d40300c60262001440400101d01c240c100642c00080301c80b42c0f9806010140443c00184e000740182c4546d107012a182c0320544006001c6051803006d861144401e5802041c10420719111000004809041500c038640c641c44400300d10b48a0301c404040b9903522503070040e81c0f402c000b41c10324460031302041601714140740d20251080f41d40d00e806c20740d0140c0d8284800010509514130050b80d40ca200810300d110b0200004c07501da0310484042d84550004101d00310380c6146051111021101c601c940c1c0138881400140600e2490f026200d407c108102101850001071402d03080d402050031410001c010000207001d0305070701c05030103501021647e00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 340229163 1250 340227913 340227959
    0x9100606020c121209060c070f03030f0801091104050613030c12020111060105240904050c030f06040903050307030c02120409020a020f0606030709020c0a0c1701180203060f09160807 80
    0x14484003803242c51034034445d10541a2140c1e00229045445010601031003004080c4010444e82103a43d80ca009410a0b82d4803444401086c095800000c404149004620b40115038100a81c0f405050a0400141c2d03042850000803031240039401000042407240c0c40c001038030650503c045018014800180f40c50324040e80d0b007520b6045500100602d0311950100c5c0070a460280110424443c07041e0312400500801c00d8a030f61060070300301882804010000118040d0f0800e0400303a4031580d450052100740e98580c080100080c00810001c2d50140c403da0103403440d0501c81c4143c070b501001403001c03448280c01c6a0003a01c003180c0d00040390710340150100001554050710401520300d41c50b00100080d00e4550703610131003090580020f07508141d2507081c002d43c00d14550140500b41d5480c0c03542d02c20307020b41000c094503c00030340c03030a82420740700903114000d20205540100109100d6031181e503c4041400041c0c05030031140300c1c40c00707503140d00c3c031180b5119400390115100170000c0750b20b01059510340d40440c7c982604 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 340230413 1250 340229163 340229173
    0x350f0d0207050d0f050a1a0711060f0417070b09010f150f09111c0b040f02070b0402330a0807050c0a1209080a140706051c0509100606020c12 62
    0x43e111a07074450155a081a01003840010718188a81040c1c0404802030113549000b00c12990204008030b41c6000d00c60596400110440da9260241d4034031090324070300c001c418801c00240000e0101c1c4011000c1120440c41c140c00c08404d0f54580300100c105846103003644e515050710300d81896451042c414441504071101c14090720300401d0904503116402640c08c900d855203044520078840c2d801301c4215603d8002002c080e07140480080700246450081c8a100c0c5040c8403800200d00d05074002c0d10140c0d1b8004503d15429101c1da401c004190301c80e804400505048013039042050002c0150417001d90240307000b820303a00c6030796030710040001400030058814840207200c0c40750120400111601542d900c980c0c3c0005c815003a0704107035007500c05940041c20318410078440d8000c0103003e890000c0844003e5080b80c01c801e0b21100c0c207945500500300d200d6480070701d10201d610011656084680c021500d68103840c5c400306480e00d8031042d074216400400141e03000301c00e10110f0341807d00d150314241e02804050700c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 340231663 1250 340230413 340230419
    0x30614070c06020d060521060a0509030426031b0105010b1612030905070609090f0b01022e110405031b0105031602120c07050907030b0109350f0d0207 66
    0x351441d02841c20103401c842d4049505141a80c050707002d10054070000f003121030880e98903e8002581e914844c00700b0414064000400c6558013540606400341942401441c02c1a0926140c0c0b00480c0040402d8680c00c0300c901c80c0002c0d00c0e40140000d101d80042442500c1c1400000c1e440700c3d096520691211301801004c000c0103284248420100130102c0d80000c059201c01c010f40000c40141441c900d001c1d20302d0207420800143c150b0050400b03401c41c2c030440818841089080420b600715280c01e00d032031740981c10a1400114403503c06c0001082403902e20480d500310011000c4403006c8a080201c50004010005030600c040c2c5000c10040d04910309185501450b0744091000a020b408040c3c080c9143c041d4103000144207a0003800703900d1000f1100c00086031521640c102959903600b0324070500e03003d01e00c0800031800c0c1d80d11038060305c01260011386840f0003e602e08418200b0315804003034800c0426000040c80020069140c40b10301c1d03e1442c0d000104014001c04000d681403042548070001503601c412010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 340232913 1250 340231663 340231667
    0xf040203070b12042a081e150a0e101a04052d1003020d0f03030b010c050d08151903020a17100b0105251505011413020c120403061407 59
    0x3d5800b0b6406080d4403c10740802520a0740c602651000c561021120a004180b0706000900300920b104800038418109104228071500c07144040c2c0742042c180b008400040012100d0703045040300d10540c00c212128001c3e0b907115101220310702d8a0043e00c103109032051405501d0b06d80070311508800030540e94841c0ba541904909034a11100f802c1004410041000800851010000100a40e0003800a01c5800024600403200c172200d40c10031400b29103040020801c070352080d0040700e5843c1c0c4c0300e4010b1807240c1e645c08040da6001c0d001000c500d0703403034140341000221b40c44115403241042c2e0314818070340c0c0d0142103204100444c00b0941201400e101c194000c8811502c0000344580e100d55500c1001590190b80c03070048940d44120300c014008080c003074a43c10400d1135007100d810042802051201e03e20b440100044085c1c3d402031181e000e405040400e010a24901124200c2c0e0008002c003006181c1342c0f554a00c3c500b0401005108180030380c01007410802c1c0403c60003a02503051120102014500d400840 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 340234163 1250 340232913 340232947
    0xf170c06040f030f17040f0302070902040e01030c0909021c0611070302010507080f0606040315111605070803090105030403030b0d0b0108010b01110f25030c0311030f0105011a090a0e0f040203070b 86
    0x10207001f40d20244074100905000340301000c007500114000355641ca44801204125660030b110856100010001c00210b40072a031261a2006900501c0c040b10050301e04c016080c005420101a15541c0d5507078180ba0181114100511700710f840fa40010405e450101800b90289200401c071210385000c0800b04202d503540c000807241600e500070b81d0140d01d550800d070001e0081c804201454035038000002d0303126124008401c0380000074450800c580c41c06403102d281a48a0007140c65460204501b440402c0c0024026000782f82c00f00f8016000310b18005168590800401080e8004c61040c1d40d9104110401d5078031030803842404100000070042c81c0e2503011401e94802c206000341030364403900a00c00c1c041c0c401f1030704400015034000742010f214075183d0600750310015070b82c01100d01c24030132404009108801801624103c2e1110101d202c043d0100c3c09126503203501031141c461703000c0f171040d00221b0300400d01c0440d28002d080d0341c1034080c1149014030503d881c1c580550030090191400b802020349084034624 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 340235413 1250 340234163 340234171
    0x60306041d070306141b070803040f060c0306050316080d050a0915030b040f0b0a030b180f060405070503060f0c13120b060a120f170c06040f030f17 65
    0x280003030955100089001c00c1c1220507080d0445002d0b038000001484400d80291031080c0741c03051005046d80741c200e41c800500da0003418400c0b070250144840b101141e980c2e8081c6510a0007030003c540100c5142c1c2d1010202c3e90303005041d0740800d07903940301403029040401203485256502401c6903031150904c40002d544092400c02001003080001c0c141055910039031101c00180251048072070020380000000d8094842c840b2064011803030b00c007076280505443d000304c00d2034040150601900710f0540d00e94221442c8018068440c0c401d038108820000a0100240e64168010001404682c1010325180e41018003e50090b0320980c801d006120340344011104e02a00905036045456464150022300c980703803a40c1d5404403100208101980041c0a00701080074441c2c40c084420000301d0303407902442810714080381c078080c2c24180301d0f1280c40001029810100160035800c0d000274103220075840901c0c6030401c201d030111103040451041d001010340140e1a5031083d000e0342001a101e4060700700b03844034508014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 340236663 1250 340235413 340235419
    0x10b0f0609090a1416030506010504031e1e0b011406120112030e06040902030f06030d02100216020405070f02060705040e0402191e03021309020315100902040e1f05060306 75
    0x1004101015090340c00070101c0303411320114540320300e80b402074040f10318a0b00c403d8101084c103000000d081c80d80704002b1036003503030750080c04508001c0c901c0c002d43ca1080341c0200c045404c0c0d0301c1014580c0e0607020800f851000340f40f0481300c1c2191076040603800d914800e01c5400b014000c11003400100b005403601003003076040d2941074012201c46001c40c10111070034560041410780091001030040781030881900110b100c1da41854140e01103803669820705a9424400e40d174440142c01980350a1a105e160790003c0c040400c440c0c8180038079462030f8001404a4006591142c04150040c00c10307190241c051041a60000043c1041424a031038001da941400c0b1004000038400c01100c0e0240f8418103100d00c1c204003628030200504620b860341e8020581c001e42500050f0700c10310084110041200340e0b400703882c01c1030750b0107406407002e52602c041010441038094071018a1070745051000c100340d142880030f0802811303020b0308480c081c10103c0414220075a65031000c000700c80c444809210710f0b110803007103d400050079 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 340237913 1250 340236663 340236679
    0x30314150d081204110f0d0c180b0a090207051009080406030f0e06040b060a1a0d050c120c0a030f0510060f02010605180108151b0714030d0905010b0f0609 68
    0x907180618083c45105000c0d8492442c00042c07100303100c940e0f640e007903c100040d114400d11950190801c5007190108178010180a10070300c0901000003280101c1e134030b0000ca0180410000f520400040b02580c2c0d5801c80305056902082150034880308100c846110081c0040070002c180701a00d60410074462030080c90203258440c40d0708440100e66500c004040c41e00f15080d28118206403425881c0464241c4810348100c0c1d2100b408150440d0341103e0500c83c041a1640c035262061080200c80545401000c1d000c41e9002800461212198000c0c81c62158001e69590340d9103004421001d01101d004480498689207403208000c4803802039448002034035460b042c0483e10030042801280504201c1d00040d030460300d0403c1030011102000d150078180e4000c8001d03640003103100030002c00041301c222103070720740720f0414030101c207894040000030003500d4060202c841400f449071480c20b1865100310f080240c1955034415000c1880030a225407410340200300c07545a40c1180c007400040942c014068101e00c6400b030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 340239163 1250 340237913 340237939
    0x708180d060e0d020706140403020904030e06071406070f020d0305040204060f08030c010c050a091e2301030c02070501020a020906040905250503210a090503061303031415 75
    0x203100c851030645034404418000000814441e9484050056000000d0f01c180760020030810b01a207080015406035000150619107144c081284a120143c819014002d2400c2100f80702d4848800420095000320f071030ba00c10f050010700c40d40c8fc20300d00902c0d810402284520840c0b809601087c108403800b03403494003040710746a40c00007400500d856803003071280d400c0c00c2c0c0c0c2c000f030714800c040045c1c400c03100c0445c000c210110306d560090b41c940c8107461041c40007800001040c8400c2ca0100c0c9070440b83c121401e0704a44007a11074402161910341042c43e071007040d2030342108460b150307454040d61082e281240b026058043ca4180040e54482e02164001c2c823030a00100081c038683c5542e444921700c2500242180c0c1a505a400740107a0b45085c9c105091303c0c02e500e10f4000c0b62501f0001101d071042000c1c00a82d803056040080d041100c2e80007440780f00108260100e00140355034007081540e0003440ba1045801c4105001d145c068200c2d403803420f82d150b842c01440b04024030903500900c141240c9406851045580b02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 340240413 1250 340239163 340239169
    0x527030d09060e18180c03030a090f091b050703110615091315020904020708040603060f0b030705030103080c160321020105090a06230709030209061804060b031203040602031506070818 81
    0x40c06c0554640611011403002e4040d540221054200c903042002c4102050b107801e42c102c103403640c03414203802d1000d0381220409918403030740041016a00030f14104000032078501e902400c2c180d064030501c41581c14144c05000380d18003400ba29412038400403c040d0350340d4140e80c1e1075400f0748050200c1d083c16640030403206002d403a16012030303090a030701c1808203a49039110300001d001000d96003e40302440400300360214011800030101d9009015075160706003180c1c070b195155142c541c00200242d00901980701c0103407540060340d807401b0103940315a280018001040d00451481c034141014042160304100c140003210a020681c050880c2c1c01c80d4010681a03180c155504280c03506d110b403c2210940c0c1020400300035030002e0040141d0348201d4050446444a10401064110ba940640c5158004c940800c00284095001e540011805815111440c19250b0022026007003202e06840c3c564000041220259202e10201e801850403600b40e4105074254640c612079000d048511303e10000014148003c0744e03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 340241663 1250 340240413 340240423
    0x70e090717010b190207080a0f060b091510020a11060708040e0a091b05060d3809010504050f01230d060209040c030605010527030d09060e1818 63
    0x307001441c00c1905580d00e00340c03c0f40a07400080b071030007981c0450f01c50308840c92000c544502110002e0300241100d100c140c6880c481c8810528045501039520a040e52540d00d941d100ca03881130f91030862101c00c10003c1c2c81804402042c0700700c68011501708000711000601921109000050280c581d192121064075084482c2d20454005403641183c41c0100044d816040e002007404503c42c122501082c0c00d0406034101c000564080c20381e01450510030804400c2c010360080424001c40f0a0040d0101c010804900140610b400725040414000444d186c1c0c50501d511681d0043c502680c0030000e610301103035071003500041801841d0106203450061281002090007642c0c0091000b0040440c41d000c500e0050000e42c00076003000d015504144011641d207003c0d204900c11501c06845c0c0c50300d864103000c40c0004002903590f908510b81485055007215803004c0062104a040035150041581e08045002c0c4c05200301d84103503407082e401d42007000414048140f61907005030090040007444000c54085034100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 340242913 1250 340241663 340241687
    0xc010f1107030309051e1606030c170618090c0901080703020306011701061e09050a0e06342a123203100504092127150503070e0907 58
    0x80da0001b01c64016864020a0420030289868030300c0c108140d44400c02e40680e44001810b4011a81c0d10b11003440828500c2034240d030014004010802d043c0d00c2034100c505104050b03401c103599500c81e0304413000900706001280c2c094452200201513071451a80000c0d0750785014000c000402a600d0040d4001100075013000c4050560301d4158500700000101c0c54650130250f110b120600740c182408a082a0f503d031007200f14050003034000d070003a5920503c0c03901c0c4182000c861035041d084c102500c01c00940c204402c00c0c800172070317035a01d5001c481600500c820720800c151007880003400c01402c031400000c513004070320705030032260342840e003510080d0503005400c881500d80c8642c2d0b00e40c01700010303401c0d641c0411f0086100d40030f40040c0100094039841404100c13003001000902070b0100c20001d044100034080002d46402051403ca1070414030740b00119506986003e840c1941d0030310300740c1401703e6032a0326180c0c00c01d418146000340c154504900028210030744d0000300d40c00b6a001c0d1000c5040280300b40915428 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 340244163 1250 340242913 340242943
    0x3041a0a050c060712050f0610211107061506090513020d0c0201090b01080d140d02250213091e020a12050f0f030a0c11031f020c010f110703030905 65
    0x70b58a0144d201034211058260f68140d0f0074640000100e080c9010031a0502030007001d003030714028065070001501c07c40320102031180342050a003280038140e13105000f0149030300394101e64161641d07800d10307040c030688051003548400394140e02c40a00040c0c3d0300c40c1c440303021550100d400d8140c40089040350350081c81000b0303c20f01ea00303041240d042d0019070150001d40e481c43c82150004116030340d034040c0d90389494184052900255101320714461803040301000d0300604480400051401f00c02706080c020886071100c403940d000700c161032400150724040300700d48480348403000103000c945ea2a541e0341d5a1400541e0104803042041c1c54414155100d04407071001912044168a1024500b030800c60303030391800b91aa11106100b4140e41c20382148002c02510201851074030b4281800780d40759920032803c0080c1000c41c0e0913105844c050344803000c2d40c1d4508021440d901f4401030f690700b03040c0500b5003074401858000c0fa84a04010401c6d01d822080c408a81d440307901480c0000e5100e18900c1c1c80d07810899502801e00e6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 340245413 1250 340244163 340244173
    0x706300605090a0218030d120e0709050414061b070f060e01060b04051903020303070201050d09050d0306080c03060601050a0c030309081201050117061323090f01060803041a0a050c 79
    0x100c0030a0f240d00400030003800000088034a0030310420565075203101160040016090801200c61000c50b0300441a03290700307030065442e215104c942e400d084030750485060728641e00502115200c0c02042c8240f582040c180c407490701003048920309010803446400b0006100c00c1c1100300d010140460741d0700c03101d50f07400102c00030b01c0450780e030f0811504960424002c1510884802c2d2440d10411000d0f11940c2c12a5070281c051402c0180c1d81c1c005503801c0d04000d03260308102c8c1d11048500000350302802640b00c2064941c50005000b03003000c901030700e024103034103120b0b020703a01803406e2002a03038101d411b49003825214a00a03030034140a250480c09490307000d10041100d00086a400741c44040f040409050f24030a03681c402100a03000c0210ba40e6041c01c0d1038550700084158904100b03130001d500041811f84a010002c540301300321221704030b4600700450701072109411603403168801c14001c0c0100b100925034000254206401d0030182070341052100340b508151a400107048061a01440075208103500981c1582c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 340246663 1250 340245413 340245421
    0x303060114130b0f12091e16030f05030403060606020d0e010c0308162a1101140315061c27030801170106081204060801091406090a1e0b03070630060509 67
    0x90703075a11582405d04007152404210210707008001502108c0c2020098024041455034941208a03203600905603031728042000040040b800c1401500c0042160358001c050542650500800001110000d00e040040c0346841d000469031213404c094000344100d211a10303503840d40c44162032101d21220007010060b101000d0600098075101058100f40c0a00c02405c4034450a500450320590454045100c500f82840890156849002051580391380038001e14a041c5803854034035142400140743c81d0510b0b450303181c44080c3c15010745c006120400180000c4e200c0014658015002ea403050183c400405038800700102402d2094001030002c0945030103032803070750500400095055029009000108404600000d810f5220b4840c031a03022812401550030703501e800c03041020b508005800001c140c0c0e22002070640f10f0f40340024900000413455000a5045032800c14141420615803000c024040381d40c4a900090702c02000044a060340d4803100d000000000c1c04243c01401103800482d00403400c02c3c204 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 340247913 1250 340246663 340246681
    0xe07080718030f0b010906060503130c031a09280b090a1e050f06041502030403020c040e0106081c230f030103150b04060515070f060e0303060114130b0f12 68
    0x1000203c3d01a059100250781ca45030320f40107807982486034000040007040040d802150100320407a40d14400d4007518007160703891b01c03040d0841280031400744007030301414240b20007242e080011402085150200403007403503007a1720302c4500440c034180107096900c0c0b410000d00f0014080c4990114a5071100488841c080881da00000040312002c0807282445154110802d0040006400d8440c0e86d012402d606000354010008000e50006402142075104642c203012590f5114003d00c8c1e00841c6c0703d070000510702d144c070801d07070f1030070303600a100200c820801e030b1400004507400441003514a1580300412801983d003440b5160a00c81c200d042c1e44c1d540303c04800401044142614218802402142409440c40305810401141e1503845480c0c0d1108024a00410544904020709aa180034071103144900003640c4821040c0e0749201c03420006030700b0020806c011582c025050080454001c4502070500170b1095100500200c5030244020003103000c2264150841001e0864107a080c64020308501c42c20b2907405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 340249163 1250 340247913 340247933
    0x3090f0b030106030e010614301c020712060f0b0409210c112b03050d05010803120a050c090d0b01090540050d0807020c03030f04120203010b1215010504060e0708071803 74
    0x455400514404100601a02c0003074080d037540d00c0c1c0001d19040310280d603260320007090004086030312030b501c40c02045096552884be04c0c4070140683c8031750540b0307444012800c001a100f41103190031b2120040d4880c020459129003056613100c00d44041d03418509021210f281d4208022498048130b05941208042650000162000c058041c009000990301e601400e500c9018620308880d00082c1c181c0041c1e03002a09410180d040018034070401d103060380c24004160780701a00b403415600020b0030740041184100500c5505c2c0e011007480c110410482c54041d42817015000b070201c04030b02d40d20308070032210040802d04692118a03070040c121141581c40c100003402000c1d0440e80c500250040c80550107081c01c011046545280c08140020f1070700e81014164161403064180aa17050365803004036500c66261651004030103505c460040c100c209514003400c00300c900c140c016a0240d410a8410010725980c06411908075130b041c20700001703981d6080c034225010300c482c2c04851041248090008280429070034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 340250413 1250 340249163 340249183
    0x3040f2d06090513090b0412090519180204080a141219080c310815090d0e01050306010507111e03010f05090706080403090f0b030106030e01061430 65
    0x43d1a00740500b50b025001c01c0b40c490b17000c003600360580180060002003840c0c80001e04004a42001c1506c00d03107030030210f90461006440caa1500201e008140504070031800c0d01010010750850a41c94170742800259a01c81117000313070007014020040a1604494401c2c00080c1c910440e12442c06c1d11140c1d442c0c44a03680c64569440d101c00303d80b5040c04102c0000d40d131030441d80c1926130040c850014140440c1c101c92640324a41900d003429103403000c046100801070103084210942611131103418104864283e0034405203c44440c18012141940c000a036004000ea9501003002d01705a9101d001f2400c2c41c1c1e990401409000350f004101400340d640214080c00e400c1c440f007005174000c1180000b10700b0780c0030880388140c81000f41031f23101c45000c000305413085400301d078010300c01e02d0728024050341c030042114070002c181c1181e4400c00e40030005004880e0700d0b09c604060000d00c0c00091028900d400c651803412003641407000d00884107802d190030b1070745204606440c400034004401c403101ca4450f140d140c840d80305c40e03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 340251663 1250 340250413 340250419
    0x10516141e0403150902060910030905030309010b090903031b09010203070f06062603070807021201020711010e01050a1d0f13060e01050d030e0112090b0403080103031103040f2d060905 81
    0x12030300701d4508040c070442c1710260b03010746080e29144a5000300140404865984030805440c2c1c0311305000504180013441c052042c2400100d50820380a0030000354190050118502d5402801007180443d0500d4120064103034840d03030341d607070380c001769004030f003903205044010b0b000385205102c02007000059800802100d40100340e000d07400180a421380c001851080744200315500500001000c108607100070003100e03200500703102050741b80c4201e0b03500f6a0401d10040c0d400080104d21050156001084e0024400003464440d1034a07441c080701410091850000d541256811080300740503486045c0401d8058100070800141001e8a0b16074001600c4030740140380b4074024082c00040e9905000e1101411998103480e01410801d01000440f04c41c200d4000500303d1070741310044c007408242020030881c0514060341d2000107940c19410080c2134041d00c2100c101d0350b6171042004008100d41802c045059800340100c4003041c4800d000e450390305528903001c040d040402400d0001d001600b00c0b205000729a015 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 340252913 1250 340251663 340251683
    0x6091b080d09060207170106030c09020c07060f0c0f020f030307051c022e0b061c050601110c060706060902031612060b070201180b1911010516141e0403 67
    0x6000202c82d0907a191042402507440303150103000e241481c0c00c0001c201c006840000030100d40c4d03504c1e50501200382340c0c00300501d40d0740061040208035060090b40003609080c20300b4840e81c40fa01100800001c0405d0003d41002c2600000104560318a4201059108e000301100e488228500f01103032210f01ca000c00e030a030188052400d03c11240003158407060001000c3d861112200806040444286041850a1604d5448880c80203643c1c505026120402d400c00d01f80c0c038521084240e40c0c04541d4081c01391810700c1080019500c40301e20029510440074000c0e5407054850b8103526103a005007a10303400c00001c140c0044101710500211841c20b1812420542d66044007505411100044481314001d03089140d10402842015500490011121050300150304481301e56600d40e007007058206110b000c6103c40702c0c0c54941a0644e21162042800e00c010000300294100300c0300030000001c41c61046001d03c946400ba0020340102c0c0c0301641c0e0503100072012203101000050b1845240d40c0301d80001c54643c488 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 340254163 1250 340252913 340252933
    0xe011d0105100b120709050312030402010e1516080c0d030e1005070504050607081306080106032a0305060a09110712020d120b0301090c03060203040209010b030408030c030406091b08 80
    0x91500c0e002c08803058000721a2030040308046072291580b000b0061004c0c030a0384500081c2c1501d040000000904101041c2600ca04003440010540d4849054551095081c070404e0039950941c1012500780c1500007151070f078417410750301d000d8103d4014501c05007160b0060350060a80250140c01641c0305404900a0b900e036041d103450980220f50b03050710f4003000a08c7c04c2c40b09026600303109000300546401401f615080c00200828900c6082d41a0806800070f140ca9004001e1310390140500610302507000804c40d0500b010360000c41ca144030541241c01095110004501180c9030403a0440140000032810b200c8044c94040f14410385c1d021580881d00107480703880010300d440c40882d040b020403140342c0d01d5078402e06240f01140081c001c158241c0c1c2d4103550360303026040011841845140151320411016031680340c280108a4520070592103a02c8a50b810402c20000815a00450b6880884200c1e290b48a03110741c1450300040c42c1c0030000511080580805880950341c602c41c0d28112000c140c120351080351 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 340255413 1250 340254163 340254181
    0x4020c0601090e0a0c15050c100f0608070e06040b0a0305060108010606020d09081b041b1206060809070e04080706050f040b0601020106050a050603040809040c050c070f031104020309010e011d0105 86
    0x44c0580c0e0240060280200501c804520780398411042006882c00e41d05160032030702001d0070208400c015030010b40c0c0e1110f0145106446000b81e8000f415042c0241180e070b441c0541403401100002d0585203d60398503c40303080103a8035580110051904102100c1c4990f840d0b680307141c002c02450181d1000f600c1a05040d0b9189480f400d01d003003d482c3c000000c3d218014001740030012182440300d4a507802500c03080c4400e4180c0d4017402d50274204409694a62034000d48660314011545a500210200440b1900300101403200261483c1150141c40f003a190698617410418024091207400911450030442030080c01180080035a000301c0c00340e103282026840ea0001a800c80d80d252160903004084400b00700000d15203a4040c0d0341c0701c1e004030301d40380ca006104030000301191051142c040101d00007007040421a0400c02206e0080e114403009174903082d06645592412800032200320303120756000030004138449000c0d040041d400703102100a004491896a03001c0030060b0480001d481980303413a0025140386 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 340256663 1250 340255413 340255423
    0x321060a050405090f0d030b12030301080c060c331f0902070213060609060f090501050d0e0309041109040f02030c0702060304020a081212010504021c0f090204020c0601090e 76
    0x290003840508050325000520001d003070003c104107407502a0b8103442c52484003c1c000a082c2e90703459580002c0400e805e00070040322802d218140400d41d4400c1c0018800703020700003016182401c048940b03980301c0c8082c00c8220300d8905002520401c00788031b08a4680d900c4101030780201e0190380b40700040d41c45d940f02080a001408140340c204040c54403620100f000c40c08071350040030350500140400b900540801804001d0310182d85c014400a11805800c01c0900d40c844641204020986410002c41d803402000070702074020740c400703800300a548519060482c0001c004507841d079080580700b07000503807002c14030340a241c0000c14803a0040d410412402000041d40c421603100b01c3c486400e6030300380072060b02031080035000100b0480c3c200200a8002c9071071501000010031382e540d4681e00f41e9980350b101c800c003d210707501070f44440c0c0a1070050021186010f81b0303024420280800030700008a201c1140b65041c050300e0b100340040c2d000782c070014100315021004110f950513249001e10910480501800d01581c1d8 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 340257913 1250 340256663 340256671
    0x7030206060103020d0f11030906090d0e19081501083f040f08010902100f020309090405010b10021605060f0f0904020f0a03020a1707021e010603140321 67
    0x16040000050002c0d8080da0140c01c1c2018440300004040b4030703504500741261074070510425169004800c00c07054103020800c1c00d5020325a6000392154400b081c602810800402a03014890b90300703484d1140720609000d02400051190008440c4040c98600c4e1120052500380030710340e00c034016a04000c001800040480d880030008001041d200410400080510107051700d101003131400411000a000d841000c900000d0200c10000184102c55441000312a07441541e0031014048102e82440340d00d40c0100507074070101d50560b20320b00f26580b02d2400300c0c01054002441a400382140300c421308229800103101d00080d03404424681c820752140100034550040c12a00c3c0704040040111b0074400c202600548a000700c0580058280302c8600061902c6401107401030340025804a03011041c20307031002c590480c500203d125032403141000c040003911000c0d4904042c4410144081c40c40342907000754880d100a603004070400348004d05004101da140c3d40b0800c04410300d154001442e88140038040b004a0103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 340259163 1250 340257913 340257917
    0xc0a02030f0c1507050a090f0e01090509070509090705090c0c030301030f06022b0b010305011a07110a0e070215060f010804020402130306020a0f020303100e06150705071a0703 77
    0xe0108501405a40b60702100902e409805a22502110008080800c82c00f030301d00354071429140c1d0400c3c00010b00003503095103e030100c248002d80820888a07090140c6065911004010501d9941e81e00180d19280c80d50740b11982001c5000200312045001103211015103100311003100703050301c41c00a413411034040d074518140f45800803c01000082c400d501c411100b280310316405070500002d40b4090100c2c1d04040c21600d0080c111468907132807141d40344180c00200b04242010805941005120407502100f190300c40305582e80001d04006120f101d481019074180006d0000401540726003061511401c1621450058460008400000484c40840502c5800041c05103003864030010300450305ca010140040c1d801c03175401c114980c100c01190010354080e40c020356000d0b0b43c07100c030b00c0070060602d8100c4481408540052040c00400f9500310701001c2120950400000709443e001c5c009000c2607442a1082c0c5600da001603490200100880e044003191160146245212540284c040880c45101e40080c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 340260413 1250 340259163 340259167
    0x6150109030b070807090816090b09040b01030b060a09020d020d06080a030512040c090218090109060e040807110607050f011b02030d0c2c0f0d02060f0922140c0a0203 73
    0xa071039104e1035916070700038054500543d00c0759031039078010b00b41a8210598041038031206020300503401540600c0a41180c2540c1c144454942502c94007120340c4e06000080c001c540c0389000c249582c3e80c007074828000e00b0004404665403500e0b110003800070762091440c1b010150609074002107200d000b052408400f40c0688803d441d110010480401c41d07440200226a0710030000c8010070b00a4462010303040c40c3c00ca103000600c0c035140311401c11410100581c031800c131320f60030b000d8240822400e03600e9403a042540918195104c003120302e4004214001c40c41c090790888400700c0c400040c4100000d9822003681600e00070050b2001045034444040031946001015910070403018103031491a078820440d020161401c0c00c44a040411180c50135501120031258034118090442003070701d00890803c1c42e801c0c088a1a07107462a655001c60a20f020b140304610042d90003282100044d203030b08006071140980c2002600900a0703445414009224104210900c40c40316000291030301e0840049031607504054000714 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 340261663 1250 340260413 340260421
    0x40b030c010225091418070503070605090d0b10172b03060f120606050604120807150603060207120309020a051203040915080f070302060415110601030506150109030b 73
    0x70144400303020014000c4010354000107071381081481404083c0402020400d117908104e9000f02e103039902002880c1007600145d0040006550004000c012103c1c141400c03600c03050301000040a1008c403a00240c010241c0c00c080000c89200410800f05540d02055801c0c03003102a5410f407aa0303500d50804a070816a04c0c46240c401480d4264031054800105150210f102a01d03030316070020b03189407580808a962a07010512040004030300920b0040c2c8010703a0341c1801c00c0e00d00488a8078400d40310307201503c8102e0010f1100240008114000c0c4140381001081c4503440c0e0703078907200c0005e40c0f103041d0170744202800c081d02c0c400680c800e00611540d44d4004064041d03080c01c203801c00800c0c100f400218021480200000100801c003030280349642d014404824400e0ba15010b405400c01810000390a0a50408030701031005070f542801340d600380c0e442c0030082c0042000104043d1543c005400b8101d13078610802c000002040000030f007040c400c80202c4001440001103c00541f011051400003c1895001e80002 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 340262913 1250 340261663 340261693
    0x10f0e030c0d0f14011a0f0d171201081f02030f160e0411090114031303050d020f1303150b0a0e04021c03030504020307151e180e06040b030c0102 64
    0x10700d45403801030010080c3e8410b16a02d569110620301c20340300d01651919a0044030586500035201122415290490000101070006004860b003142c000c18245a070750092034002101d05c01c2c0c0710300e000204001d400c5540c49003400c0d40d5808442e11600d015242d50101103503292064000c1e217020703481b601c400407c0740d101c851140c40070649021002e01040051030140e04969500d01031180410100c0c40480e648402c5080010041c0092401c091900700081003440040514001c0100301d0036090b14042c0e44070b448840d9100c01920071070340c50800c122804100c0c00f02041c01031000400f10b1388240c80790008510540352502c151128600740640c40007902d00d04000d1924581100c03030340544000d1017000403260750221140c4000510300c094000035030301e404003c01c500f0304000703000150801200a10010300c0020700200601070f85e10104011800205400d0301d01800f6020302196010717002c0b2000e40003515444148054401220103178401c83c2407103e619a00e050100d1014840760042c0e0180c46500c241c2c01e21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 340264163 1250 340262913 340262929
    0x1e15180c101806050c070f0302060712020106030f15050609010b0a080603030702190f060c080405010f0e090115080a0c02151005030601091b090e160302070818010f0e030c 75
    0xe0140a109000e8541105040b640d20002c1c04050310ba01740c860220806a0785417603002c1d0440c8024186070a4180050303640d201c26079090380c0e030140300387c0e11045850504901400f1164002400388071050219030030895101503001081c40701d030030308001e1a42d8000401000403c288220400c01c01d04003d16168030f4030800741a54013201c0581224608070681e804514075242941c100394126401035018000e06a409044500411242c98039040c81002501c0d490305d81e01c1140f05440c10701c0b410340d19819259000d00034145500700000e203070b610f003903a481d0f02110544000d80071920002d411a00011844c990038400c1e526070101580c02400c0c0a5013429802d09031340c801a24100c0908184c410004441d130701048000e010300895100416121201030b40e0086c2c10001701d101c041400f00c0290180040c0300103001c140e520001214500785420040d10b0150000d07c912072014281c0c0790005006a14004001c3c00c02100c84421303625a0302d90040740b03604840342c03200d64402c90703859002150404203510301508 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 340265413 1250 340264163 340264189
    0x6070314070f02070e0c0a080702030406050912010f09050f010b182809060c120902090a11070f0609050706020a26090409050d03050a060303080f091e15180c 69
    0x4540c0800e8403980521700d8014100c8000d041520b0002d400351740c1651000a840d0885094002181050f0130101c003d0407a0084101e29401440121200e105030002500110300d8070040050030041d40c0e2040c1005070301c0f80204440145558205030032103442e41803141c0c460342d010300b00f1900307103065407a0102005e0445c07010f80351108400c00d040102c0045d5a2039813042d00500c0b84a40b8000560610f00103014045020048c4016082c0785804d0303030000075031605005140c0c031040040d00050549843c2400c40310a0148900c003401480d0001c0c5a030f410085154810340e6007900600840381407603a80c00f0200ea83d4208140018003c403100c42c07142c9010f03e481b8200800703480c400110f560801d41c0c500c2c0481c081300c10424064901394032901d003812003a83c01d4402c654106086220030701805045443c041c041c15005032880d00c009180c40005800c000d028856003080c0e1828104205040450403602d5a44407070b0740107502c80e820101c1002c01e5849444121840d00003507000090110000e0400c00c100c61400d50070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 340266663 1250 340265413 340265417
    0x5010e0102031b0708061602011a18040501020409020408071409071d03030f03070f030605060a091e0e04141203240411040810110f071b0b16020306070314070f 70
    0x4000032034a85c40034043d0510900b980c0c40101941e14403094024252900b04086078010860107602e9405a190010b2007a42101c0070300b0340009030b4982d4a4130b035009115a1303101c808040d01c0400e01140340500813484500711a00d40c504065080103002c20007072034203001e4a650000c0f90160505014101d000c0404201c021001030a0300c0c02d060000c51400440d500032203460000500c42496842c102d038061240318041c2c2001d0b02d56900348464004040c1244416000e0f140f1550206400556121500500702022b080361452000c07007030402c3d02c1c1903509410380c41150206400b94000d40c000006400b4244c0344648800d400003c041050b200403003040c6448075480075089619a0144c412050303466009000818852004100600f01143ea4000312903100b40008688013040000d00000191401075881340c0d41c00c01401103104c106042c00d218543c440c1c1c0d015200550000c224a0b906203844140f81142a009805a4446950303600c2c0850032548a078080070080a070725404500e00d24031a00281094206074 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 340267913 1250 340266663 340266673
    0xe06032415090408030708130506071202072a0e0c0909130609050f190b010e060604080106080d08090607090b03060102100915140f0c1602040f0b0a05010e0102031b 72
    0x1000814440c2c4422103041d207101034000103201d1305503807000107180c0c011081c40901540f409240d44540d100c3d00040c25001c100101140fa0124161865044070541544100044408024104104018501580340e44005656400e0008400d8190a0064401e03d00c10b0003c030301c1d086200e4108100c0143c060101c49580010110080c001000351141c0e40c0d10500500060071501604411203103807240c1203000600f0b5185903414400040d65050314541074840280c41038a481c0d0b124000300f2070b50f0041d0350145100c0e40c200000061484000b0991180d001c2680c0d94040c0e0039681c1c03541301d076552032090307406000140d0318000c01c020100200d4041c6070055014030585480910600a840036034074040400d64a900030781c040410044184e2058140c0386030142030044452615076172589507540010649010880001110b0312490440e038442a80c1c198024800c1040c44c510101000041400c2103405008215503800400c0343d41c01031640440311071050f4021480e00107520390b42c207241414159181e00703a02c14 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 340269163 1250 340267913 340267951
    0x9080d03050c04230906010f0804062d0203090c010e03030a0c0c1806050f010810120201180b0304031202041203030e0102091c0501050703050c040b0315030609070e060324 75
    0x1165901c0c4e10131142c8494070201d00c402990070000625030180c0118184080f541c0301d59411504040e81b582c0c000e0304814001000a02c0310750308512000c004400d0856684425a907604100c81640514010044030080341d0b070104100c801920700c1c0007240b004030b5041e071090081c1020b240c82a500000755500c10600d078080d0940c0d8982980000c2c0c1c1c803145184515072501824425420310100c9010214424a13100c0c50301d083c80d0b0040c60b41c1907101e0041c540840300f251100300640e40941030001001c900100719240d410b0341c0b01d0100861744c000342c6d130440c0006c40540303c0d170038110a14002c0e2025035006506e450f000c005917035070613001000d180e00001c41d10754007070100090582d1150089000807004c4001c100002d00d90f494142e0071240d00825580c241494082400181c1301030781c068406039801481071540e2038490300160781c604900444c5941e810b01c0383c00e080020f80107002c240700d000c5440000c118a5a902c5940401d03480c1c0447e07103046d01d01070105200502c11802c03000305240d0084041c020007956002 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 340270413 1250 340269163 340269179
    0x415030b10031e02031b0a0e0303041202011b0312020c0a08030a0203040209090d0207090e030d060605132403110c0a0f14010b0306040303050603010605060d0c02010c09080d03050c04 80
    0x480c014201d001c240c0da05403082608011550307050307482142c984210318518116590524048000341c1100113588042041c0d070b4224010403503d44c20040040c1100d8507035688031881d01950400800c200d000800d108114070fa040e0300d0070001d910056040e01d8441220742c101000500079041300217004071b03501c41c051401008c81d00400003036000c0c0d440c080000d0ba803407030240140300d400342c0041c056001981c07001301c0e110302e409d0740032600c1000e64075500340105255010b9410203145008010005094602d85403002036503540100040c20094541044140216a110022216000c00510b0380e030195200c01202c140071403282c2c2c4420b00c13103820100d00300d0a0026680f0f00700d26168040008031102e030703414105041403203800d6808400880d0f406000b440741038101d0006c6070700c6500c00390004051503141c0011a1840c0c0e0290081800703490040c10070303503c80d284060003c1c094a01c3e070720044059460b092a0398030035481880c8240959127441c0c010f20110590107401ca0081000070305d20100081d0512011640c15 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 340271663 1250 340270413 340270429
    0xf060403150615091202060f043203010e070b09031513030e0f13090c09021215040b06070f150c0e0405070e010e06090d05010c080702070509010501050415030b 70
    0x4000750000200741c2d003440112054507044420560912180381801c000145020080c55030145e415a21651203c420f130b40007541d41d00490b00800f8400f001e242180555258521030f0381140c0032000502e001403a80842854200d0f54059440161600034200911403521580c0003006492400340c00c1f64100c0b10850640d041a040030713100c084940d01c10954000c01c0c1607024040d014107800498003840c3d002c40c0d03080000d01406e6103a05a6010589802c840000d00600c08070041c024407085c2c4081d17503034a08503101400341d103504480a140c0c04c40308100741d48040c142441100c00050010b494585000025250700081c0590070303c04403050364041c0009a075290071400b5031000701c2e010392190248464a0401c01c019144000e09040c03c01180c032842c062980c0c0e20482615840c070060321a04d9445e91000017141d8003036081c00010f072a0390700b40a684012160b00100051241d0112360940c1c4500d07803207030200140c00e0000c0c41802d0018500303100900c201c400c01c100303004a817045804c0025444d07002d03d0100d140c1c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 340272913 1250 340271663 340271693
    0x40f0b04030f08010602030415110c06180108130203060402010c05030d1a01081503030405042f0403020907080912160510020301080f0106150302030702030f120103020111010c020703020f060403 85
    0x1c040b0300014241c1c50700018868003506013800a181010700380035400000300044212103040020034180307102c120b6010b00c101c1e501000080c1c8600d9541c0c0072807440e091401200c079001c07400181c0c8030000a003ca540c070320204d800140c1c000c0140a040e102c0e0380044640c251404420f59050104120a0408841300d2042c541d0030340c81810707485805015100007401d0070500400d00313591441c0301c5008954aa4011080354107450b0101c80005910f4041180b90301005c2002c201041403484103070215a00416180280c0100ea1086807100341c0f80c1d4075404102e401100645046e4110340c1312060b078500344810b000103004e0042081440001c4180c0c99141c0500d4425510000c042559000005210307600c1c0c24031241d5403064002d070081c440f46117002e8080c408040c1d00b06c915420154080082580d1610074401c070307650704000c261400e03194680100c040c00c86c0030080c170040780412008485c09482001c1809420f00a046a0300688001392640e02440010384003c101c00794884800c1201100240c0003551311804 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 340274163 1250 340272913 340272917
    0xe1801030f030f03141f21050705030304060f120e0d11010b0d0f06110c1209100c0b060d141f0c0c02030d110a060f0c14030c07020108040f0b0403 64
    0xd40c0000d4180500b82c1c410703000301e0f081014140b100300f880804100010b1900f03c00d640c0e032101011801641c020710448601c1e0040301c1d02c200b1100c08584041c000b21140c80c2210f000c0c0d425681101d03907402c1015601d100f2403107504089000c58104000702ca0088030940314090b0b6524000c1210400305c0c0880d420f00e4811607421001c42c1d03101c0b008a0000c03400344510420b030081a07900c0e080a05c123a07101d04821805c403081c01803c00d9181c11a007500640c06e001544e00b00e01003081190308814505148504039044041400d0041300d400070390f0044148202048050b90360440300340075040e1200018410a0305044400b96004007144568005c480d0003000700c0154030188000400d5040d08400000050b9400c2c520120200280c05081c0b4001d40d6020407820703400e4895050410300d0302160159035080c140000d40103099903280c42c541801c006003d40061a000741c2d039940d802045100002c2c01d905034001501c0d400c2100782c0074851800194000c4014a0b0080c0c003800300d00b00d0106243c3e0b28140600421682200 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 340275413 1250 340274163 340274183
    0x40204031112060441102904091110020304030b09060114010c0204060f090f1a0f060c0715030501080c010c03050a0c080417070e010e150409030e040f0b0a1d04030e180103 75
    0x1144d03603114800d840c0047d144003210000e6100800c010851101e4054405115560716595841000104000d030441030b800600068441400d050700651250020310041c2c5021117048009482d2040100d5072a041c0d41000c40c0302d207082c0300200b0046815002468089030001c1d80c0714404101d80002100c0b010082c0003400011800400a583c041d068a0030b850042c0ca0301c5100781203090455030350800c40104600282c138a40c0d200d260f50200c3c28900341469002c0c1301e081e00c01c84003841c181645900280e040e0b4002c10200e07103082314081d00440300c0c0c2c0310141d009400100f0500c54111f0f094403811042401034050b4800b18101070701e41038601c40006401103090100d6002d52010800c10004041d298014034280c29103403d20701c0d0020b903410b051319000160a00c9691b4550305c0804140c0a445603c1070943c01074410401ea42c907190064000744800040c4521502d22098005003c04042d1008074404141601c90f1050f07480310354094035004162119141c1c400c0c504180f540310b642003410018000d41c0600f14800b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 340276663 1250 340275413 340275433
    0x1150503011d180f16050d1518120512010608100b030912160b09031611120d080405060138090d0b160504030f0b0403030209040204031112060441 64
    0x180008041d4040f60280085003078040c003140c192080b505c200c856551000c5031b00c2038000303049d80303c00088400040002d040f00d020800c40a40c420003500300d01c1c41e00d01305400c2d540d0302d460054032034184c11904140760b200a900103201503004580519080000c0c2c200721410040f60490744582d6800004000311104606100c80d0140001841055003006081024514228503020001940c8586800203020802d0f81e40030559240c90b40440900302c24401f4090303400c1152045002000e40c001900e00340c4051254400210761030521001108004100700c41c200004070f0b07103034103d00c03c20380d0101340082d16000034803500c10725846a111070100c22703204401503071203450494402402c01c1c0f1200c00d030200300f2000340400d00010709803101811440760050051450350b40d0b9450708030061700c82d00304529045400894000108180b01503110b20321034080721070a0700b6162120403e55141401c5401914400c522049a1201c003004900b80c80282e01e030084d00350b9005400044203d989840e44400c0001d58072a07100c1c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 340277913 1250 340276663 340276693
    0x13080606090c19050901020c09042001032d0608030a080406060905041208041b180b03030703020606010c030521060108060102011b030f140c0301150503011d180f 71
    0x103561100c02000c0150429014110f0300c01d4000e800904001400b000044030b0314141c1c000c01450104100c02005a00300707252500e4542148482c0492000c0003400c0c0d500c0300d421a40c000e0040e00c1c0d420034504000c0319089120712a92010081602074000092b6480402150904061005141150325034071588003904251800d9070071956194400c658203071601c014000001c070400d00001688510b45400e11158a40c0c3c10a0550b941020340900701c000e01b00c040c005a1441c8130429002002800c640c10800309605505160302d91007250310060040c0c00c001c0c000340b92503020f80325a101c014003034074290b420f012170303480109030761a00d02d0001d54405c61410304010b107030b40e03025003000d601c032030f0a100038856404040403128901c02c6000d82d103818152124074103503400d80c85500c00001e012544401c002182481c459080d0154001ccc0203500d107041d0b00e03621200f07605010f003088038100da80071000c00c0f00514610038100350049016126449409003403111404440c010020030855090541c050801450510b0031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 340279163 1250 340277913 340277929
    0xc0506010e0f010515091905010e04061d0723031b1303110301110f070501060614030609060105210709060903030909050c0403290c03010b1801020313080606 69
    0x12810719030340010200306003019209442030440f001034915100f40c10401c0c03c0c030036060051030304480e007180e00d03c28607000d01b03808030604000310343c420380703c10f200ea541100901094518070b020f18424a911000c2561080f00394066041d40180b003450b0240008100300854800000105c005108102c6d010040c00113035042c8904021007001d01074403551902151440880600d100c52202410401c10403021042e191000e4000c640ca180c3e41540c4140c3d2505407601c1c01c0140e400000c01940c940d072a096000c5059809040e191040c2d07014154514110380d0307008200044041c0081c15a410010140030740018100144c580381803210b44440101d0f410b1038180b100501c000074580c8264100103c00d03a00b0000300780c01036005810356006041c08522940c803c94440f140380302d164002800280d60610b043c04da02c06109240001d0507941680100a403510010201140000c1c0a06c5c81070b00802c0207013242443c80c3c03204840a5203810300550b81480030104060018041c143c0c800c02e1103800a00400c916444c00e001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 340280413 1250 340279163 340279169
    0x5030f18010801120308071112030f011a040b070602040b0309010b030c040b0d0605040203030f0703020f0106051009050d0201030b10030e010f0203010303020c01080a060b0301060f02010b031b0f040216030c050601 93
    0x1070502d40941c503001c1d00b0f00020407004406010b1060110100f100da9108025052086080f5012911066210b080402d80c40c0d004998110070401028000b02e42541d4898a103165601400226810942031403003030451588191b0b022102c45501f080009a01c0030300c40c1c007a51003002c42d0800041c00450000c14103050403010481a4031983c54001c51140b00d0b981c000040411540103400041d840d605c40c8086441e5100d40b5901810092012946c2400c244c1d001a14400b0018848004d101d040e54803070500801c0030005e0364a0001c203e45030814131050a060544403036180c014500440d20032650701c00b203034440c40384158200c0025280c1c850074031605c2d8240107002d03116001000840c91076246440003500c074907441c002c8a0400c078100003c00c0e8002c1751744e00042c0240c0342c2403903000e9403540e40d013101510001001d20704d071026500702282c0001a180110f080000780f2001c60a050b6550608006c01c52603103110703850b4680c41a42407240c07041c81d09400d1150303c441880798480c4450100715003891480e0400583c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 340281663 1250 340280413 340280417
    0x70e130209130201120908040b0d020c07080c010c0b0726060f0607050303010909150e01050403270510020f0a0b060a050306070e0915030f0d090f0506090f0d05030f1801 74
    0x503030b0581c01030340d100a4880c1704401110000034411150725107203a40d44202e40c003460301e0f4030010403442d5071344805600a011007207404084568040d5961403180c0c42c0c0aa04241c3c178040355903a80610081480003005503404451842d02c0e111541d103083d6501a200e00c4014070364a464048801c0106c9400c1800b85403444280466005040c01d2103035031074569038801401541021a11040000304100e003800d018004800901400c1c044401d1840c850b0b4002c101c00c68090f4001245003007031a071440361400400e42154000d00303e0711210341c1000148108034011180d0141144503401c5200080201440a800c244ac07042580c07032001e041038802c014050f41c2c15000fa40c0300f034000f030040c00085500171140e84403140d015a001403040d0f9460301a4200842a0b039100c030f400d401174070b1003103400c8030010440e8400c04c041a00d41d00d800c26162004100c07160164010300b9041707041001a1000e6282a195201c903220b002002c145800a003a5511811034100c5803102d00800c50200c5c1c1d100d208074250301100100c89081c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 340282913 1250 340281663 340281691
    0xf2d0a2016080d2a0303090b040f031211030a0b0303210f01050114071b090f020307030f0203070c020f13141006020a0309060323010b071a0c091002070e130209 70
    0x2005540345900d40015003c4e90900411010400d0b005e600320301c011940200c0340c00c0d81c80c1b4207420044070303600c148101180002c40d520b00345401c24150348140c0341e011004c85445400c40d55035209500050401800e40c41e8507100030b00ca054555801e10842100d0408031342d60390581420540100700706164180c000c241070200004040352a5030120051b80d0605030009440030302c011880f204001c0040d419045450103d080c480a82001d04140e001940a00b4460b90100000a80301405908a0009580c050002003080354404090310b8600c0028202c0d803c004c21364180101602d070b0b4101260041c440c00c1c00c50380794580c2006850284c1c0d050305070041c6041d00203092040b03211b980041005d101c071302030003080c9076440308bc5980014103c4001d00984907254104040d55031503102941d001e400c0040c2c00c035000320b080001c0203440e00c80007034500d001e4003e03900e03168200340921040011030041580100d046200d4014005902d40d4180c481c6400760110310001255289c150041c041c017550f000305451203054034 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 340284163 1250 340282913 340282937
    0x140c070c21120302070503040e040308061203180418030905090109051006050322051e0c03070303081f0303090e09010b01020705040f0e030f2d0a2016080d 68
    0x803070140200c2203078404540c03619803511076000e40090065403c0900903201c0481e011680b0154200002d000381d000b62075080d03ea584040800c115481e001e42c81140da60028083da0b107921030740740741d0b00074115070060000c104581c1094080000342901e00040d0006420f4038010401401d10743c01c06e074050100b15209000f03d14000702d2984c46150144240400c100b000070004190340c002d6034460098210340c2d400c100b01103400781070650340c1c2c0c2026403040d00c620600b00303420340010744001610f59580c54050068600903145803001c0d28030207001484018034280d01030064142513610310341c1034003447c402d072206044142003070003034040b481004141c00d049a240a0f600c0c0341e030340e030000f50070000c840040f100400d6441015074184060040c001607044940f00c007007400c840b5004140054020303000c10510b01050003164952400c41007640980142c0d1581c401c0000d6600203104095040c4082e52040000650804907400c0360325000070302503080c45004104c40c041c0a100d10600682c03c2c800c0d25071a0201c11040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 340285413 1250 340284163 340284209
    0xd0905060708070212120403090b0705010b130204031707060204030b040b0702061302010e090703150b1803010204060c061515050d061e060c14060712060504180206030406140c070c 79
    0x4ca040321340400c6154020000f020140b1a02c17427403003c0e11803816245d03211492450500c2c0030f840041c400c14400d4180001124010070f040c401d407012a6003004400c24101c89510720740959900180d015140c0c590204070201c04605150039085c05284a0441708240b417802c60f02c002d00780f9401818540d042116180c0100c0542e90100d0001e100400c01c0340e018041e515410307001e5000f0320000c0d0b40728035021170b40940010300c0d0181c00c0c081c5c551780c0280c90790440b299400174200b40c200e1107180903440c0410112079070030002c00d94682c440420700d0f0302c0a0103583c0a1361544407040c80102c04451481c00558001101d1551082e2402242c0040040c0114074404c014000c00c1c00c10f040c01280160000c20041c03c480d6814440301031126116517050b4029600f060030030220061031291480030040202d070074414001200d00f8144120800201c2c20401c100f11300c01903508106540d40040c000f036501360344800840b2941401c860714036029403040000e241d0341d80001e282641c1245559440076040420a04c65043c0e00a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 340286663 1250 340285413 340285417
    0x30c05041b03050603151003020118031a090c030703151a0f060901090504090f03020f1527060109020c0f01060506071b0e07020313080a020d0b06060d0905060708070212 74
    0x1450a00740410305540344c801003481c21541c006441c1314000c0c1c51003481505c00080e4031074000e4070b00030f81c1c440381759025140290340c00c40403500c4000d210f2030481946070481501a40481c0c2c200941e441521462504400060310300310b5141c20542d5005002e442c0c4840c99200d600c101c030841c40900240100b042c00180c0018084088814401e000e42c10018603080260f100f44030030350282ca0020010058100e040c00c0c07810b05034513034a038101c0151188002003468076100041800a030750440051008a64407224010809158101c2159065480e41d1585000d00b001b8010705018121245c3c0068440c981c80a45620706400c00c100104142d2411000f40827a8552204031382c5459049041c11f80c100c40840300d165151182d90f881015904c021405004c001540131000b069428905110340180640307a040c40e0f91188061403000f5030000301c071600070000404107601280c3c0030790000c18141c2021700205100c015200801002c85031908044100520150006040c0d60000c0c0c5601c001c111801e103980e47c4003c98 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 340287769 1106 340286663 340286711
    0x11070c06030e070305191401021b010609060b220305150f220f03091707030c080303010518040f02120a050111030702030d0e01061509030c0504 63
    0x1c280010703c05040c2d903004406890131a0540c0001c24944c80c41c0342c021103496504d01403079031082000780b000c0c1440704500c091017141700f240b02c170341c00e401c403103040d00558010b0749400000d1002d005208180c2c1c03003015104030070301c1d284119405598480b2802e41d100901c01d02c540e400d400f803110325494035540900c44803105a00301c1c2c2c80700044841d05150000d0040c20301d4080e80113540c00700b1040b03a0300500341c1c1e000741003600b0010f45600080700039005180c801310131503020350300403c00c1007003040414008000403405542503505200c001349540014480a41c019803607880810144404010076003c000e9004041d15480c103400c9170030079221100d501080e41c80f07501e03007042511801c1c484400c4a1017031015a01940c90315040d81064001060207142d040c074191368862001c6070340161100c10101144194039416820b61071480c10400200301500703d24003580c1096600030f0132030004007081c424 = true := by decide +kernel

theorem cover : BRFrame.Cov 340107913 340287769 := by
  have h0 := BRFrame.cov_init 340107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 340107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 340107913 ≤ n) (h2 : n < 340287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
