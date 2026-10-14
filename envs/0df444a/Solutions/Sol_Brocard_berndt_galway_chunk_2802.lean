-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2802
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:47:08.247323+00:00
-- url     : https://prove2.me/submissions/f2fe151f-a8d3-428b-b628-589083ac7e25

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 503776978 ≤ n < 503956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 503778228 1250 503776978 503776993
    0x200619030209012a17070f0b090610060905010804030509060c010f110f091e0a0303020606090f07020c0d020f04110705010507020a1203020a09030b1305070501090f061107091409 78
    0xa0f00200c480b13042180700c1009050a4070301001481202c108240d62407204861410905150b8030010140c0555004490408a100a01102c0a8104215504046c03080500b49181e0300306403004010400740d20925040145240c0407400b0305000710b04484010f071001d40240d588a04090b10540038005038080d41103c2c42c82c240d444040e041e5107106541e90340348000c60303061074030400404101521004680c034966212034a001c00c146035035070751210130080d4030940240c0130078940307a01001208480108a101800990b60070060f8844e408518115208011501401e10b45d0a600101c0d58a0740c10b240b185030050300e4542c80355060801070307001d0045a84624000e100d0341d07441e40c20403620b0f1320a144009044100d50712030310003854041d07000f82460399040e18020b40703110760740d8031090b80300001070b15024076119200b5102e50600c0b40600c0424050807080c209004443c1c980040490380c82c40e04c0c8625010040d0b00008010580002d0110000504a040701070114072801030700b09052280959820b50703148240c00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 503779478 1250 503778228 503778257
    0x8120702030c100f2304060e0303071704060e06270f0706050f0702030d030209010e040e030313060b13060612090c170a020d08040602010c02070320061903020901 71
    0x3103446200401d00a07000d0103410240c503101038036040d031121601545404070380340482c017244880e410350f52262000380c0f500d00b00f0781424802c6900100311022250410070400403840d03002501d61801e052002c0e990b401c1a0744508010b0300800a50071062070a01400c010302031b0910a4a0905159003903824031455403640c642002559940e894100e9441c07504442c0f002c00c00071b802200680b404144800074035290403d81e40c00207080103050034101c40825800b05000b840395178004002c0c0345000307040c1c03020400262a8058640e0301d001c01004821441015a464402c100c00b58000008122000e01545080004440c100001d0f141e40d02a00c4005440800c5010395500300340920240c0c90341022050945034108440c59020f80e107606080e03481c5104022440c00181c80300020b24141d1713130048003482e4840f41401da0081c25500001c0d0084215400500d0038401701e440c1100026010034401c10180b4120b1580c0c0200c0d0b928050b694400401c140c40c0b410070540e43c3e406800502250200741d884100c154644c2 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 503780728 1250 503779478 503779483
    0x20607110a11041e0e0106180903080402040c0201140f1806071e0e09041b05030109030e04020a110f030d1118090703020d02070807050708120d0504080409020708120702 74
    0x4078018180b400584490400c0d030500783c1c072980200b002d030104101c2020540c0240b009882000d1561030342a99501820070041c4c62002c80c507061034250940510501c10079450003009100061301c040c0c81566030700504a5182e000350b2003120070b444110100764003860403c2c014012090125403030742040042d0f201d4aa00290b011440354032407200754442706a0095288030102000603510101c0050000a0195108903520200501d00c2079215990900c1c0c044560403101a100740390741d0160740242e060003e0b0304002038210000365200a0140c40043c2c80f1340e5003035800c9904200f111242c41103401021000a40c417900071008001183c00800188009009049640f0141c4110f0301c000d45a80e854410000040c43c00004d4290804d02d14038000d0305040c640d2650030202c1c0d00c4803404032807404002401c0403c00505206540040884101809102d0031001d9598590720580d040314200e103540781c0010702004103001c140c502900c400c0f0390031901c0702054503044031180d00c105c9001603203064090000b01d001e80300 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 503781978 1250 503780728 503780743
    0x30308040203010c0224041a1f0501020f0c09190203010e041a010501050f1e040602070906051813050a051609240b0903010b0409050c130e1b0d060c02060711 69
    0x84140c0c1c486c0c407044045800800382c0c4094001c45401c0c0150200d03880010035201c005021344082c120541200e01d20171004803045105a010a040d07401090758181c5590b000304100d9483c00058503603200329a00c044850001408421f001e43c011840400007040c44003502c040144100e100302c07045200304c2e01e515491004010b003445a640012010021110090001409000381e030300708981c1000c1a0300c0540004407690400c0e0024001030380200b00820216030240a0b6900901d0103a0f42c102108422201500e03805e40000c01e012205854445880e00b04101009139a21a503003207802e40754041021134001940c03000a00c12100c038581000701009608020480401040d2000c0804816141c5054405601500310054540c2d25558a6110b20810344450150041303962184000d00780201e101010424054404d00c544848540703448642d07490100000342c0001e060703084078100c1d03d01071480400079000000826008010b1800e01d0b042c908426000100c481c000c84040c1c9854180b82030f85a012030f03a6148 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 503783228 1250 503781978 503782003
    0x80109020403110d0f0b010b0307090f0509060d050f120d1d0a1101020c03030f0406030c050f0d09060603140a0227160905120706230a031a0a030308040203010c02 71
    0x2150f82010075413820240c03402c000d601c50354000020314000c1d00e40b0312810409a002040c20070000081080440d4040b4101e0090b2012508541002d42000301190514400801540c054000c11b40e031441803080070403d00c04000020340c222504a240d02010302101c1d004143d680450038201440400c20301e035090440341c0c000c0c54040040141303034090b07160408440e20201d0010f0541c05030070a01e01480d103042c401454a08101051203a440349822070007000c407140e100013001045424085107a01d042c500c000c4440500c140100070421107541d08208008020b00d80c0f00600404580c07007010701c0c00e2808260024501d0007121580d003075080c2e030078421400102c12a94018150140d80c00031715080700c2522a503000c000c15181c02d01d6100d0316030b0082107414406039031030401c81e4040d42040211641c0f00120b034003600310912205e440019214103910083c002e601600080c1919450110119030307804007450080000181402282c136507904020f001624141c070164003d509003441c1188107400060300c15807410 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 503784478 1250 503783228 503783243
    0x10090e0615040f090203060a05030105040201080a02030c1209010b0f09060a03061a061b28120e060a21051003150f0504320706050c03040305011803080109020403 71
    0x5880404000c0060620303205540350401c2444049083c44543d83c81c900501404940142d907401c03d801000100c0300550700042c403e078140310402005036444a1904d401681c000c83c056280d03250320318001002e01495003c2d00c10001454204403512605404c059503407141614401d42101e00041480709140003158031a030006603a07102040010720306d07030009e58101074205000d90310510080009100d07a01203102e0442d20380d040511a00c2d0b4440c18400c0100313005c0491f0004000305246980000d29801158025000449000450110f20300071214606008001410556214490400508440746604000c1e00001c0800520715104a980c4140c40c043e2921501080b507191035582c49480c0071044050300b642c0640c580ad98541a20f20078012a40554403032140900c011882c0c03400e400c1c00030002058007180400d04540044403200100b03c1106a94252801b15034907861103669610310f108a034002403e640c60503601d0307034840c2140c4104d050300301d102c1d955240890341e0f100703020000d078059804041d0141 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 503785728 1250 503784478 503784481
    0x708131d0f1609150216060e03191208040201110d02010510051207030f080f0304050705040b06030f0a0e070b0c1524040207150c0908010b01050a0804020f0a0f1410090e 74
    0x698070012480c41300c03140c0d10403034454000300c451840c1e0403003455110030023041d42907030104030b00d03c1c06001692280e03a000c01103003130911554030341c0e4800340a28159603080c011014003080c15644a0702c240120900c0007001c0f00d17601c03854a040240203001c100c0e08214541078550010849241039050b042240d42c1c2d020080444c0d509580b81c40ca081d141c06113084604c200100001d070b0018521001441c825405075000e80191880c1c44144015150081e031143c0c4910820410450301c40481908507030441055840041d40c0d44100300014035010301504006044a0081100d084070800060707258068507145903001d216032140503846100c1d40b000c030144014240c1884100c1c00e00d060503070280c01030901a0402d0106040d03880040300031100071242d0000020b034820343c144040c060902410010080a29101c1e10f1709590b107400410501000d440244503004080740403009584110800c8090884a4a25a943c0e50b9504034001c1c401440c0680c20b000b001030390f00e1000705502078900001141c2200c2c176403200340d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 503786978 1250 503785728 503785739
    0x4030b28140105040e071e061e080f0702010209060c1c020a020607030f0207031401051512030d360b06030a080f0d11040b09090117030708131d0f1609 66
    0x117002121004901c901c918600003450050314020741c410040901c0f81c4031101420800f005242c503240c0030000544031078005445041c59070062540c0d5002c0c04003c0025040d4480300d80890180c071460040f29400100803c40c4402018007041c901e81482d401900903c44400c01002a0703100d0108c04000b940c001070510000c80400e00520a560782612148161060640c07690b54504c0c0030340ba0046100c0c00c5a41d00c07410000c82600d44d00c940f00000d18203c0788010703882d81600e6242c1c0c7e03901c10100801034481c1c5940e400c0c00c901c2440e01041c0d024100f0420000c0d004404940203100c12000b8040a0700c0c460a00c80c08a14a1f00f00030840c03c601a800180c0140780113042000080e05500282d101c0030b002d0796910305564481c4106000c0d1001e841c0c0406210743d514105e0040024040041c1c0200f010b044011800041c8520000120394629600c0102d0544580c1c00424880c12a21030342d002d40d4000e80171180481d150300c1d410f885540300f40c00000c41500300d034441d80d1078090b1001c11588000041443c10405101 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 503788228 1250 503786978 503786981
    0xb0916110a080406050a021b2107170c01200c041a030a0c090c090b040504180f08030f1e180a05100f0c05070b13060204030b2814010504 60
    0x400ca114084418003001560740e030195500c01ea000b90001a00420b840781000d6050104400035600210781003030344250074001404452401c04400d0741c44201c0052022030344410300c07000d40188403c03801148403080c40d008072601e40042c0b81040c1d00060040c2c131442040c001c130740103010301404101c0052082200d45d80a00009200d103402203032f10501c0d4146404240e5070100f00607400c0501c030720b00004e00c0502d4254035000351403d00507034109014110b48180012245031003500c089900440700032941c00040201c001031a03c428101900d179903203210140003840000d000460041c08007034120865580c402c001e000c410080e2581c2c07650030112030350104030820791841d280c14410038040d00761000c8440320307600d403840c2c503036640c0400d1486902ca0400c1d40040e80300d4480d10065001c1418042d203450f0f02035642581c12400202210150701950b0300c0c0b02c0600c4901e905540245501400c50089400c20101030441008074419100240034049101c41d144c6086006503c05d00420b9184010217900f020f04100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 503789478 1250 503788228 503788247
    0x1404051522080706020415110618061603020403020d0602070302070b0408031b100f0504050c0a0303082805040812010906060504030609060e1509160f050f01180611010b0916 76
    0x1107482c0d17001e20000c039070002c5a0815030080c407481d0f154415074014080700a410a4401048a960049406464050a40040707106a03020102500080e08914105400d4009001d50740001c1e4100d01e8248280c810002207600811950303000c0d8013100e01441e42d13005501a240b007540a680e0043c0c20034403010031a88400280d0360721503602d400603562400c3e0b54064070000c4584946544070201c0d00d07002840140f02d401d004034400d6602c2680c1c03080100e410342c3c50141000d040036102c854009844402c4502c1841032005140d40c9a03054070080c000c3c0d05040c10252a10313005031003144001801000000391003d500d1145201300c07082501c0300c1c1d091500e552142c1c802094140c405460480d10740130781c0c13000c1003002d001c282200c800c40301c0c44202d141844a0041c0c5081140200034814603000300060080e650000c200350300300c40007140c49644c8070f104440100e400d12484400517901000415000c0b1b00700d82c11000402d60030100800800218400300c04100c120703902030b100d40c0d003080480010400c44903c1185041b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 503790728 1250 503789478 503789483
    0x305090c060702091306050a20030702060f04210f03051005091603090b0906010e10030f02121f0606030b0402031003030e06161109070c0c1814040515220807 69
    0x140303102661600d980701035440844415003815941e84400340743d4004544407427480c02100385070300e095250504029540c0d0b10b021380540303441c685100024040018000705e406403500b00030b03802440c1c42540d400180220340385162400120f414000003030300e4800240080c00864000800490309502d0f01a0400c0c8060442e0082600301904c4544000c04922210350a40c09401f1010040c203243d071428081104c418000361895109800081c420000303d0b5040e168031710180d0301200d0501c40110b03045d00c06482d2806410321a01c3c1000041e800b1460b2180765405501141d01c0f40e1024009503215008202c00c0b44000c4503242444800300c4002d00100f48603c80621210b40041c201c10310380601c42c000c9030240181d11004442414111000c10101c0c03c10840d81c68101d09141400000d1003d0741c0c0d5240c4002e1102d02504441d4400c401041310400c00941180c1c5995461454610a90615003131064031501c0c82c040c0740c60b44000381c401041060000310080700e01d181c14111030601d480c04c96580c03202e09902801d0107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 503791978 1250 503790728 503790751
    0x903120513140f0607170d020d0906050f013512040305010207021f080a05040602040f06020a02040635011b050309070609150806030114160305090c06070209 69
    0x4030740c1600058200060900c072107140c1c02c081d4444042042401c0740360724240c01814140091400900c115820b5034404603000d6900361240c02d4a0400c40090040c0f80b13080ba400c6003403868420034070080340d01480c0118003c0403000103070307030f00c0e9144611120406e1880072060701c200308480b800d1303000d041c03480c0c9004600c000c20f44040e09035100842083d600702e5081034629960000702c1404525150110f064980c045551940940c04108400f512881d0001c10382a5070503107500004040000702c1c1d0480300908004510380030100d4817100003d55900400404a0140c0c0c035018001c114040015904418805144030403090742c0301d800328620360781400b020080303499900ca1540c551807441048040c110169a0b6855545915020321030514100b03141d4040310503c0084a400d00c8140a41c41c43d41d00c54500c54140100191150300100b0b0051800c5c02d40004900008421711218600e003c1544002c0d200540d018480c1c0e8031009101a191100446019170001c2c04010120050520740000741c3d1201d02c0044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 503793228 1250 503791978 503791987
    0x5150d140703080a050409060617070c02040908210f160f030e01050c031906051309150212071d010c0f0311060c090a0e01050a09020304050307140307031e09031205 72
    0xc3d42c00613a008000d5103c0072030008982805000011300c0b0301700c0140603510f011521921842054040d01c1c9014227034000f009080195a0259221604a00074540d8010499039440c1015070b403460b0401e0140c0c0d80d280a00344c1d083c0c0400d85561154103404e0262144034021110a5609602910f20010307021155042c940c5610064060b601c2c00e03c10140725a80e105405d07541d0345081c920543c2800d041c502014001340c50103d00b032040342c50700c03903480981c8652074400141e41065030804020341248800e80c1008980005001200e00520f0404d413030055000e510341241e0201c5900b020001c8490001e1f203a800100c83c82c4e070920201e110280d13000040e90203030034901a40c070729a610150502d01c0840d45002c00300c5000410368164208004030714000c0810000000007541840e0014651090f9403113501025078020010506100d0140200c07855158007019040da1080041c005d5902c90f040f0400c2038020800000c0440d0504103500300e41203001c00c1760740c0c40304149404c42d80da581c1c90050400707550302040402d11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 503794478 1250 503793228 503793233
    0x60307110f060415022b0f020301181d0d050d020405120a03110d020604080d02090306010e01090507030507050d0c031104080703060b030109051b0102120706090605150d140703 77
    0x811640040075030003400840c685401c01e411128a000100000c0340d10422603844483c4081044404081c4021400300492003050940c2c809850315108098165100000001c0c405503180e43c100c160002d003c03000e02c10101e0b400ca0f664282c0c00800c4c05005c040d0041c81e07102c0040d44c413450092072912035183e001810241c8a0b00803583d02c08a644124851383e01030f880e88010706410034004001803400754020a13882d01041c070000d4403503034003420003080034070041751617a44920141c06484401d2070140843e450380da5140340d44100f0502c20710500d64180d10b40700116017a0761085c0103843c070500054a88504d01410400004010003d10010404043e034460218800034001c000800041a0235402040c109044d401d0031000c4561540400384240c1c0340a99540000e00080f403250f101c03a003200c5038003243c0c0903c180141d007000710203030b144140201c0000700e4104100d05940718120040c0580001c005598032454119610008000d0440e8030480b981c01c000c000030f108140100c00200700c1c00a0b5110710f6a281e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 503795728 1250 503794478 503794483
    0xc05041e031707060e01060f2c0c041a070812060d17070605061009051302040b04090207050f0c06040b1e07030504030b0c03060a0e070201090c06030b15130506030711 73
    0x1007060906100010300c601130007894003860344101c2c1400001c018140c50100b0340c1d207007504a072042c881c021000700401c2c2c44d0780c0c641031010300c60740b1196013040d503013403a054549208507031090181c110800d461a400800980c0050203681e00268403070811840d048240785210407840001785a66440240c011420340090a03601030b007060b100310000d0898841d08a45030103425103000501c2203000b04030030380004015a901c202220110751040e207160221065082d100700191055820501e00d0034400030300004e03903c03601da000b00400d0740542c0603521f0200c41102c00d55140c892400c0250340c406420311041c4007680d003007030090044440f041c02c0e045010080e0f44003035241d600020001d5022900c045820010b0245036170507168460540c0c694039149d0b1810100103555400b403801030602103903640e000220198000d5100d110058ac12402c10100c6c26030315403004001d03103c4a44043e00806508009040402088082c1e504540c8400d581004160508080c03001b50b8100030072003010800105400844100103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 503796978 1250 503795728 503795753
    0x60e030a050f0d030f0213090908040905190509030306010207031502091e0411070308040f0c0803030a0e010b0a05180411060d050109110307020c0d0219090e010501090c05041e03 78
    0x499001d0018600d0038840541140e860200750101c0500420410380e074951560007c10966684000014880c4240d0410000c14060b940000b03005524281c1030006406c403c034400d00c0c511014103820b110583c1c54840c401c0d100c0c00180c0f4500e000d40c0c8500c00c1400001c0c0d0350b02c084a08251000001400c2035558000211b580da2546c800d0542c4c3c140d8020b01c00e400d070829002d07511406000d00300040c6031584540c4c0082003070500501c041e224690100c1004100320310061000c0084c00580c08032602d0b402c005001c0713002000104a215903c0d0319214000409080600e03546040701c800030242c0d0703421b507444802c85115580050089504042120913400a647d0300c1c8094a2108040c0ca4002019810030079150100c50b000c0c04401c10540c7d040c420004855030010f014460340f542650140007200c680e102051068280751040542100000d0b07002c02d034901550f00026902402c10000c0c040c50740c3c4c40c1c4d8600c0403206040c07580c80010308100014040358003222041e030807509030380490041c41642c0c0c0d00c601c6147d800 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 503798228 1250 503796978 503797003
    0x20c070e090d0c080f031506030702030a020705010906050f0f2b0612151e0e0c15030106080c030c07050a08042d180b040f0e0d02010e0601060e030a05 66
    0x32814480008070400400c95040000d05000203a148a030f2104a40c0313025101401121000000004010010f422603000003850054002078607400c0a8601075100e170490400c10300180725080c400a802e41c424140c6104070340850b128140f030328400044140c42c1e948400b484c9196601c04000502d00302040705024000800550700380708200420000381003c0d10240e81c00007010721018030a4002089100c07981148202e01c11b0b90010301488100d040710481c102d1038010340445883c1000c0754401c16004101520610401c0302d10721120014400001210300080c041e41001814480000c0c074521400e500454004c50080e0340c15090040603034905140064200d001c1f1526071011a08200e649204a498100c0c234000780c49100213240b808071001002d03074039031050004002c1c000504c800084030075882103203100300142081c051a0005440742010700040c181405092040003001c0c1d05182c03042c07041d0140ca0042c14068041c592801104845a80000004940c1400390368600400a0320401c42e1038005075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 503799478 1250 503798228 503798249
    0xf0609210d0801080c0907050c0c041410060c080909060a03121d09060102150a090f05070806060607050309040b0112020a0216060e01080619031a090c01092106020c07 73
    0x1a400724028020300c0c040c0d00200150380030240303000c0f05076154800c0313560082e140d1400584815241c1e20a42c03401684199035500a403030000d00c0c10381d00c0031829115216a00840d0050f0301b0664901c0120350042d1502c03805401c144050015100d103140c030b00741058101d5401030031400d8281c0ca03074940c0684805440d01110200314820b03110366a10341c0c2c4003400008460b0031502c0d0300c00d5140c1800081e440306070341e0310f061000610352000241d002105034021981940c000c0c020004000f0207292460b668a840e0082642034070034038001800c82d03d0220119611960300101450600e052030052001030420301104605010101c5050014110188007a1a040b02c0c6907005141c086030045032107450740c00d140c020b00100305e070313804a08440d0b90700b0599550304800c042c1d0704402180380d488040c9804160542000341500300f495641104411109000c0340612040f1042ea001e88201134010741e410a030714130810035a04c0003404004040800d204142d048903000d4180940b9019450740036604003030039500002c0054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 503800728 1250 503799478 503799493
    0x9020d0e030c0d0806011106040f0507080109110f03060417180411190807020a140a0f0c09050606030f191b09030b010504150506030c0d020a0507021e0f060921 70
    0x3d9034003070b03501904400c1c2800c003517115910746040240c441b0002000074115401a00c0300c841002001c000c41c81c020810340d4000c000d483c0311890700194002c40c1020242c440c035074910038504240790114201e0f000e01d40c440701d201c0a6582c058000485070f0441c12400c6132022101e21603d0503601d81e4000c1c6282e190241f0f4034655602044821106281130301050a000c10581008020781c003500010041072190700300c801c800c4488800341c2261314041c0f06640c010000701290074200100201c0a0070741c1d00b40c0b40c4403e021710060303803504140304550204079070001a075652400811011105800b0244090059000c00b240404078601010300c1c89807054603060000d5203840c400c01c14403103580c0c400b9014003030840d07040c4801c1210f040120340f41001405003a11840000010464450341d5204469242c100b44c2d9055413148504000548107803c480780980c0610000043c240c81e002440c4400c0b201c0c108010201345c0e00f22182d06c03d0209541240c920550005810203548511862980d0f40301d200740c0e817400041444 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 503801978 1250 503800728 503800753
    0x804030c030c1806030302030306060706060510082406040e190509060a0c080c0405090606120f1005030d2313080309100504060c0f030c0b0f100b1309020d0e030c 71
    0x42240e0342402e02c00c040ca0b00d04c0500c00640e0201c01c90303401210840b030480e2a01401d050603c010104d0780e002545c0160300101e00110981c2022896104400c02041c075600c030a43c0140d082c42c0700da50091950380c0100100001d1001c83e080c11103081e0802c03e5070b400d0300c594103c0755881c44100c54041c0c80080d0554050800c02980b44c80e240a6406100000e1034201e42ea03003840240703040d031401107006440c800c0c9000c01c00103429031248000c0d2044000300d051214001e00702100988a00310040e41e020010f400040f034041020b050010340c02c29555425641c084040d440c0340c1c0c42108002c0340151011003207500304803540461050041e10800303007210401865030b684000c001c00c080d4041d24410741007448420700080210710717004040305100c1c9030000d2407070001140b1440c00b1210000400401040302100000340481c204241540318840c0e035404195400c078640b9a034010410340201400f549a0f00c500030030500141996801820321885c43d00800b199407540426000d04641180402004a82c400f00c6c58000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 503803228 1250 503801978 503801999
    0xa0203060c160605041a07050a02060c03190b040204090f1a01031107030e180403020a031106010f06050708040f0602101a1f0c1704050a090506030a0f0804030c030c 72
    0x200000711620561400d82c91144400000c02020809018581d03035800180610405c040074444c06d9180c1b42000d0200d1500d5100a44140c1001041e4001807048000090040a00c0c034200c90141403140101e40d4446c5140c4810f1016000343d090054000d5020f11002680104502910440c41061070f0003098035481c2e5900860b1501c1c00411050405041003950700e0002d0619003291ba9803905032801031400140d8a0210b0341803018070720840022036055041001f8140c0c0813408001d41ca120b41e481e0720040305003683c4c0541c0c0e14403e000300c0c05120b9101008209981c008d00091800500c02c0b442c0ad428036a807072180e0003002c02540d00c8500907810030b08144240c03805038811440c50b683d50f044207036030361120a00170807200e180400c8031500d19603103030031100c94041c0155100800345a00c4614804004030500351a8410b070420b106880c05811800b10204403500d050048910442c0060020300c411f02e15900d645840e10744946c8107850140301000007101054a0f5200100694010385030984480e1801501c0b06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 503804478 1250 503803228 503803231
    0x12a14010c0e030703020f100302130f0305011b080a150b031602240c0a030e16090f1b08100f090504031403130206030a06050306040b0a060f0305070b0f09120a020306 73
    0x18072036001318400303100513518201058109203090700c151004c0d84120070142c0080c882c6100d6901001c4c049a80004c1d415080d08400d825a80b080c402440004078a101c01285682586546008502e1080005848200c140e104a103044048401c20400907500c400074122075000f502c502c840440c2071f40305140c0346501007020b10501405000d40c1000024500300d40c3c400440003038400844000c0004602c038405100746c000e814218462010f89110310520b000c018000305252042c207920070300b0b2030041002d001e83d0b4440c3c4248444c0380406000e00144040003110001002031100c0341303086072071038045480c40c038040c04a400707081c40c81030000b02ca0401c0d08029010511103178100c1c1c4903000800800c0014030009440c950207590644050303880780c5520400e4000b6188139000250584615010003051250000100d8003922100d0302c2005200c0e25101030301c0e4000810300000d41168081101040501c1c5040c005010840d6809040e03805d00b0f14440010f80e80060607041003007030b5071003900c066080d49414072045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 503805728 1250 503804478 503804507
    0x17010603060203091e06160f050c16080c0a030506010e0c0c1c02060f01060e0906040f140a0605060c1506043905093307030c0b010501020102040302012a14010c 70
    0x9046c81d181502c4611100030441c21541c0411900416164107180202c1c15101032007601e01c2500d60307044400304407500640003486030079070310310070024518801d0a040b58410156600840a050143e090540d00583c1c400050700220404404000180641609001c1c03c107113140031145c0240991043d4000a25104000d40182c001c032440c02d0040003201c0e0844850b5145690940312034580c1e079150400a0010004901100003003070818185e5030302912048ca080f440ad5803072a4003080390359140e501b405124080c201202a059205007941d406800d0745086043d80120010008100c201547c40c40094440c24000d40c01c034200509103400c440400a0301110807080350710b03d8214107040b000400110007102d00490211054141000103900c104041100c00c20403200503b0140d80d84501e02c2c00a10841000406417500640400049040c2d07106000729401caa4050355600610003c0c3c00c0c4007601c0c18100d0882001642c007104d11040004c1026101141d448025000000c0000c042000948206e5500010f07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 503806978 1250 503805728 503805733
    0x3020606032802030f07082a09070c140304030f110409030e0d1407060513060206011203082502011e060810020f04120501020702010f051317010603060203091e 70
    0x10b244042030580e00c420960074201c0c0021041018a00202c0e0030f0035804501880c0c5c5004500001c07511180006042103040303075609101000c0c154914124445031510003031191702941d18070201c0c0d1101d02c03c1c04881803450080c1c40b070b2000742901e214058074590041d4400c441142070901c0c00024080144d03188882c5601c1a1814420026140d8000b00061101c0242c0d5104009d01e203a020203005802c0e800780d1103032126400b00c403503081d115030b005002600109d0011410b00c0c030054001c00c0785840492a80e0484020308040e4010b264140e4043d2503400e0010310b81002c080b10041390f6a40c10769281021403481082d5000015070068058205040500c91030342c0c0b060080c24600c081100401c0050446402001014016150040d08000740054070481d80f000b6403248080d0020424848191300400b10a4800d0b00c0b200301da00b8803400255000c3c0250100076014a10607042041600081c40034886441c500e14000a6240d0301c0341d6454040b80c0064808861580c00b100034000343c0581c0045030302c41c10b10b50000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 503808228 1250 503806978 503806993
    0x13050a1205100e031b0c1c05030a1d040510140303090a180b100206010806100b030a1e0623010203040b0d09020418050604060609020906040308090613030f0302060603 73
    0x390706595182c81541c40c00c1c1103640344003c90000d0014401d072400303000a10801025a04070105d625035604003408024810f40c02202c810304000c00034101030090340c0c1d004000e982090607480e401c1d41c9074071490752a02101180c580c1c03da0f0032581e45100303103485121510301d904041818a80800032030507100b005180258410014060700d6607034011002c04650406115003811111540050050504601d4264014142d805032250040d00801c2c0c65041e101c0d00811181039039a0811844000300d07103403060000c1d8550400210b2624455a041442181c2110340b4201c0407207031110464007114401c3e0b010700c2182c00400310604a0200450200c0c664000c02d20085040c0740c1014802142c5109011601d01c899550300e01c008110b4580d500520003c80d10b0a03140004c0b44600d003000d5880b44400c0394215625880c2150104041c281071003510708445000c0e09a500b0a402c3d03642c0c1107100e600501c0e200340e0083c014052034484189140c81e1700e008e0b40c456400c1c0504243c1a05d4041d02e45400505024403d800825 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 503809478 1250 503808228 503808233
    0x4020a05040306020904061a03040b24060919060e030c0a05010906120e1b0103050708090d051e070302031b01050103080f03071e03060f050109290d0213050a12 70
    0x2041c0d50640390031040040e600c0c8120340002d4000c0005601101c000c54910302c4a901d4868448040c44c46103000350a0302e003869450f443c0001002a2207502e850030000407801950740b0382040c2001c1c181940d4007030091151402e08403151a40c0424030380c48040010714400c4032500301c0c2028005800d46100903660141410308100010b8010300881c0203d4081182814a402001c41640c00c8000c0c444400019200c0300d1030020015502d00c1e001e1124640480c0c20031002c2044c3c544503010040c80303500c00c03501804a03010300a8048916034009038180d603a80c1060805045003421003c028103031584203400455845148449601c0360104078600401264034140c01000411040011a2112418460700307c0da03954442d2010381303510030428010080340344065200301543e0f030144c0c0500c00743c0303e03031418020903a640d58004482c80402405110301c1100300541180030103586404181120054010903400c0440c1e600b403c8040b07030001020340c004d000300c0f40b20801080c242000c02c0701c041c10018244c17500210a54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 503810728 1250 503809478 503809487
    0x10e06030f0a09020102150a0b0a05060310050108070201320907080606040209150d0b0a0f060e0607030912080415031107470c03070f0305090709020d1a04020a 70
    0x8004010058a443d41607085a10900000f0300c0d2840c220810035032810b02076106001000c1c940321450194800b000040f0f07080c500030b41035920505100181c00c1c926410503004491551002d0a0281076640f1003941c002c0010023a02800068442d0300000b1504030418100b1090399040170b00f40d006d16400c94582480540004241540d0102082e83c1c0540d480c0403180120b2008840c26100400c2084041030354286400c0310f030009404643c2c115000e1b110319480e01942900c0c4001481148003143c4001005121801c2880180c01514000d00f0b0101d285565a450010720000b9110125036008001606000d40c03040b41c0c25804046610345020008062003000d228001e1050f00c50241c0201e040301c0940d0801100304101440090640081440c07185008412004420f4884400010200c000700014040740404040d80d12035809550f50801514501c0003d4009141c05440c00d182c5009503200402c92010500052140d182c45030400070301018540d826001107807000c446540720f14010441207140e2a40f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 503811978 1250 503810728 503810731
    0x305070516050102061f0906061206051507020f0d020301020309160815010306020c120f0a0e04020906041503060e13140a020907050c0307150e0706090e0c0702031603060b010e06030f 80
    0x4500e0030342d0350f2070150005018000447e40c42030794071604149000c50b00c42d40c03240110746d214a00c00b600f404459100c20400c00c0a560b90344140440a1052102e000980b9014a06480713818000c1d21001d015592034002c6826640221043e030711583c04001030700c08010320b030f0039640f0003440300740054203855110304180c06651320184405441d5540200d1007058412060003880801c59140c082a41c0d1105841012507007600103502c0500440c5d000c00000145061034000c5032195800244aa450503003050710658141c03d00c0d4001108041e680d14020039000f401c960100d0050407510059070020700b03240f0f000312011001030f41441d035681202c0124801070311200750040d00300a1a050242e2620500b8075143d00c0d43c05034080c05000d1090052a10081004980c08411910342032800d0f41c02d040d450303030015100f03080720340704221218000c0000640e00d1122180070f0401c0a100038103485100b24002000c90000341143c005460190f44d90030180b2441d03820841ca40201001911542d00750705d0074400d0010a600b0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 503813228 1250 503811978 503811991
    0x90d02060c0c0a0e01090e011103010302060a021908092b02060931151d0a0605060c0c0310092102070b0d02030f01050a08191b03030507051605010206 66
    0xc51101d641003000d0086403038101d0098090461681e0320012000b0080d003e1140701040c5e4900f020062040e00306002e480c0713081960045070f5155918540c248030441d400300c0312170000c501600801c469a82002060210014058000640c41c3d80400f0100844101096000345102a0002907004000e01905100e61116012a1607503242e0300d451002c01c600e05440080c0d81d0102e1800b0703005d801035072440e207031040b0f528400540811440b16208c0020001c92114042c1002100c0c0182040d1032441001c4015544003441c0c00c008201720b952580402c03010340000d04210413980000c0000182d44c01e0030807081c507115010b40c4092100392440c0c0c6810311090882182500d01c840f42010300f01c8010b00030032014004051407403002c0e40c0c50134070440c900c000790400c0d2285d5450451180000031b0703d10b03010a0200c15200020301510b08c4031004d004080707500300000821188070908507400e0a600c0358003040e1000035400380c3c459660300e00d40740c601941824507407504514400f086e9881808566030020f0516800340 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 503814478 1250 503813228 503813239
    0x21005090c100201091a090a06020c01020d050114011106240a0b07051006080303010e0f0702010b06040906030203190807150b0418140a030807050f1608030f0c090d02 73
    0x11215840c89041c45a40d440071038002408070021440258154000c001d601d0103140411403168200d00116080e48003940e0003800c942c4079081410100703074168000c108403070305c4200051030302c850a0329000a03154264480130b42010084140509540c0141c140c0840ca18500c020701720f02d2618015554400b11804558260f201c179044d9202c0e01074407011507000103058000551500c920440c40c0282d641c3d0080024601c0303950401c07000081c086000001c1d40e041e41c050442d030b441e456980c2e02084103074150043c100c0c021992110a11145525210002d0000c0c00d041c904c0401d440b0f0a5005051030302c12400d900e0741d964091000d6a50118a601003a10140c55001c10800003409901805034050031440075581d901c1460030b64010901e501c0c10b0b910a0045101c2c0040c00b440140650030b05803035226246010f40030a0131030000402d9140710b100142140e0410300c00c41810000200103180c031101d5034501c102c0310210004140240300a41c0d0300c00d80c3e400742c18509450716001120f00481c3d860368040350003e0084 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 503815728 1250 503814478 503814481
    0xc1103031f05030a0602090a09062417100821120601020a0b0108010c1b02013006080708070f0303020c01080414061003030809070503072c090c010f050307021005 71
    0x241c0308034841c1002030000500300d5607000381608021000358410900e0318425070b80c403840020000502c0c082c0c0c20444048045000441083d100741406e0340d0100d9540d10104660340407001001400b0302c242c0c40c0a02c3c41c0c80340c0c010059060030800d91806000101e0310fa951000c0106a0b05082059000c55031401c00031902c130101c1d03231500c20050b45817030a40740700104100440400810780c007005500c40094580c141d0740b404140c015100c4000d0104403a02d4000c1d00203403070003106031001c600c410740035007040e0410001010079408000d82e02c02140e00603040030b401a04024410800940c0401800000d4903847c940f50703815030b00d1590040d41d240507500c006418004880300003414819600d008024042214090302c0c00345c58502503140003403071075002c06c030085200fa0003c52075007080080c014007560000340c0200380d06402c0804000721241c0020078605690f034a283e10704942080c000e481402000000000c1c210184084000b400b5007080d0f83d113480401a0078010040c080b540011006100180403000003402e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 503816978 1250 503815728 503815771
    0x150a15080d0302120604060302010e090423060f09031303060c03090804030501050601020d030b030a03140d02220603050c0301060e0f03010204080d080c070803071d0301110a030c110303 81
    0x4451203038415003180c040d9880c090151600b5030000c0119001c2c0c0d452100c85035031404100b00c2118072500003c0d00188840c82c5540c07490030300881c481d4026001d1401604031041c2000000c54107422803900040c40d4112500340950710043c40640c03038100c440303403002c1c506103c000d8141c14101d0078a8440580804d841d044062042d6001e0303402503160a40007c1501e0392580c4038280720780a400140c80603801886a0400302e00c48501c00d105040100c10010080d2540c4032003a20100d50b00e0400758001c0da113402e0b0400c545403280102c0d1008010816510181d841c1c2c2c0c610b10900c40c02d816586603c01d0085c9400c085c2002032401d910030480e41581c0301418070640c0c044500010510b40c41704009503980540c4001400308256000149400c3d00b41d1460b80d40c03400550307a50340402e40d68054028014581c0c00240302041d29680610b520b0418000b0685c130070300c09510745500084c01d54140710a90a0082c43c0014420a4070360700d401140440215420072a40420a1a0005503680303c000c0106089400482e01541c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 503818228 1250 503816978 503817011
    0x21e040f050610051b0319020f06220305040f0f05030f0a050316030507050a060f0c0e0a0e0c1303030e041404030804021003020706020f0309210a0e040902040c0305041202150a 77
    0x55042c03021007160b4451844540a4290464140c9004050700c100d20300401c5000e030022b80544607044140c161343c84070305100c43c0b0303036020004203000b1410f100c020701010076848001d07002d520040c0f00450b442c080032841c200a060901948505171002030704054000808604004100d2700e0710001d21000030020241c42c00d01b1582d50040040040032402901e4000f0180101e94200c1c0c01d00002080d01084140340742001550552066900e9541200c4143d400b0491400030310402e80c2e00c04401071000c2d01d82030b403000744910b8810281e00210081209003e2065003400c00d449a8203400940421412841c180364401a000000040000703203c0d0826440c40c03901c81c0c0c42501681c42146c0d20542c15074541241e4041085240c02c00c4680100c1407150292408940446142901040300340720042882c25050f00c030304032101180310210a070030649907e509801030316507100d0802400d01366a400a040c0c20316291001c502c080182c9440c0855000090105c1c210b00241c0e0610340091030014001a612054040002d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 503819478 1250 503818228 503818267
    0x8090d0c0f0c03150e06090f1002130807030b09070603020906030f040510060e1503060c12040602090a0b0d1a10110a02100f0906080f06100309021e040f05061005 71
    0x1000507400159603050400c0a4115400700407455080d100d09607904041641d0306c20004403012500d034410009e01104418541c0103100c101074440d492034200ba164650030340352001c0c1e07038021541c01800034100301d2020703c1404094003806203480c0079840d00160030b00280c080c0c040500b14200c01c1645a012030104402004041c100d104140002d00003142e442c0303e010103030131382181c1440e044061041044407600c4c0104100b40314241c00360a15041007800ea4034140c880780001d0007156095800c100001032540c1c0e981d01c8400414800d41090744d00d0706c820120a080d51000c0c11250502d4204070000d00c030030364904e0311810741140c0d030f8500103041c00d480071362462401c2c01224010703400507622402c0106003075200c0c0e00400ba8100d00d4a9006403180c4d2900c04580300401143c01c174080340c01c0000070070103510b1701c2c034501645248107140200300c59a40d1340010f0440225035a050f00740324440001540a42002e0195811102c0c401008000e82c0c82c0642c041030841c424228880c042140001d6100f040450220021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 503820728 1250 503819478 503819483
    0xc06020a030f06140102010501090527030435070303080112020a0e010e01060f0203070203070e061f0206150a0b030703091a0403080a061205070303051b1c08090d0c0f0c03 75
    0x50200d113907149a0b074416015440a040c5c0154240320000c02c0d401c40500a560040480e41100c001100c40c0d0b904400c00e0400124880c21180400c0000040f901c1d40d01c8001c3c0301d0014464440d0100d00304840100d004400f208820b40301300d0300015801c201003074001034010304452454600701003400103440081d84450041e00100440c0c00280c0001c41c851010900b05416074004ea1110312030038802200036a81c070b01441e440294140d1007240705224a86002040750381109000d0404e1141d90000c00180034080c100601d03400059004c60100f0a00041407c0c00e038043d06010703143c0d001c07442c0c10501c032403001d44001840c2c8814151074120001c100407181040b91a80e400c0071000081d0390400b0f01c0c000f4820007064803149001401c1c10000316044000b082e021041c41c1e4003600030301c140c5166541c151015040490f000480c940d0701841a02a24024404030030800baa810008141198680c4050801c0501609182d09648039907540090303240c0065170385038116001076403060000080d03d4032018030325264000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 503821978 1250 503820728 503820731
    0x71b080706020d0506060c030702010c0807080307110c01091a0309150901050a0516020a02040c031506050c06090613060f0213090509010b06030915041e050a0c05040b010c06020a030f 80
    0xc2000d100803039000e4854907140312800d20042e01d407002003000d40e00a503248454550420070100340158001c580382100c90344900303c0603081080944030691160030845821740812201001100c8100e81440107a0700f94409080240c207072414002c02060034540c4078050b05d071406000000c01d10050080010903103240020800340b815140041805010b046c0685451610702d0403c3c000c41c144e41c680c4140003c11000581c014600c11a442d000c001c042c00d07500021400b419a184d605000501a183c40600907105c10380702c6540e44e40c0010015403038407900821400d07264108009015603507907003c02825026400400126200481c2c900020080c4951000c5180304200340800044084194101c903104900140080006403105010301075603200803600d200350b07134102e00c4208850344e42c0c1c150380c2600070b805202031001141d40c256050741c00fa280c0c00421b60302540302c049140108002803402c540504000c0d5028000540140000b802c203220302c0d2401044242c010595040c142d04c030381d002d88c18407102c1410 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 503823228 1250 503821978 503821987
    0x1a040e0a020406060215090a030806010c02010306090c0e12060403020604240c0c05101a1e03010204120c0f0b0a03110c0a060b040c03050c040302060703090b120115080708071b08 78
    0x1001c0e40e1600e0101015511b902c0160000c0c400040101e1085910303034040c0c81c1c50340141d865030011194205080802c071305046e5500307000314460302544210f039000d1025466000c0340d02d6019040040345408040540510380c08de0007000000b03a80499075503042a4018250a20410300d80c038414080b1000300c0355504414134104100b00b507540d025008a2001c4d0280007611503202c600580381c010382e07041d20301101d111052018a14003900700791982007960030305908603400c3c0d483d030703080000c0c2607038402c0d400700d002410f441b0826414803c80c5e40d10000241030720036013440100d14080c1c1d080303da800340c8514681455039846c24440d544414004803030b42107440701c003a81c001f00401d10380003004260a00c6e01d28060f81c5850801c69020b03000e0710502d401061302500b84c0d400e05155508000320303680003034401c0f8100040003800003110303080c41000e05060032542045142d19030514101076840701d0300865000403c040d245c01d1014454201c65a80c0d003000880c600b51402c59500c0040c0c985509080000030b107046070004 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 503824478 1250 503823228 503823239
    0xa0b0a1116050a0e040b01140402070203100f05010506040f06080601120504052b1202090301020f04030b09010f0b1f03060f08060108061501120b01030914030c010f1a040e0a020406 79
    0x1c00d8030281c8a00700c1d46120742e0340c0c40300707141c003070458040f00c00034490f54502005101c81115030040c001c1c14800140003501e04501a80800c0c10501101590711495403101c504042424a50182c580540b909644c1c80342810302d01000c1d01a8404184580350500408a000c2240d6920031000c1c0c802401e1009402d00c03041c2081c0c035155036a000c41080444003465245032400300c0460a18a508078030650b40d03592800e074052a20464004d600c514501c980c550f50800100507804c0852010340015402207031351154620b000b0780c6250a5a20150903810101c0c41d28400303180aa440260465419010074045960b40440502c10b400800803604400310700f80f903100c00003da60000203107075810307107078048103440b101e0303da0028034044066041805400704000c1e1015041c0842d00354058104c80d507052401044610b0380703455000e003c1c101c4005080060b0000103446074a52424011410f10b903a03150b60800c030320303900c0c60104074040300c0030003000b0702c0785850380100100ca100c10022003000ca03800400410800341d84030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 503825728 1250 503824478 503824513
    0xc090a0e0702060906060604081e1510090b0604050a0b031810020a091403070b0d18030f0f020d080a1e150602060718030b0910091b0f050a0b0a11 64
    0x45030b0810b018801c0400190f2070381030181c207640480d844800100ac0d0302081e0b159107040040455402c0142c0d04c02e0410890400104140740b40c001c49807100c80301c0946060911403019a81058503290040904000400c1a034465910001c203c0301200203147d02c946803da4030405c00401c61b43d81c68076034031a0003042c0c9560300707407a03004240140098031400072140c4d99014042811119600c410ba26030000a030800c48103030290004c1c9080c40000000180c1e0041401504083c900740c41000e500154110381ea15403042c0c0c1000c0604007507030581c0020001400d41c510b00804448000f031804402035110070345401400900a2100c0c14011f81580c103000300b029883c2420350820040c4101c40051084030042589140a0481c0b00495000a01c0400141d0700719100d068031034a01800c0b00185200d65102500f061a030382c07054034030641c400c1c515000944158102d14040d1002c58100d501e14045841e400c000315911500341000312042901a82e86607082075109490b144140200c00c1c0b818025600c203003400f100030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 503826978 1250 503825728 503825731
    0xc060c08060f0f030a1b03050105150406091b1b02040f0207062706090f0506040c06030b121e01140c0403020109120b060123130e09030a080c090a0e070206 68
    0xd07900b0703504007a44101004142600c0e460b0311a0035400003011040400d0143c1841000c141540b58100702d000d64941c3c541f0708494003241e98881605071440d40703848034585809038030020310315034001384203160340007400b50480031442501d4804e2050800301c07820030254200000e055550001c00810107050300b404004c2c082e500c85401101d0851806040750b004e10780420380039207800e4104c040c89605404039640c00008140e9240705550020041410200041040050501c00c0c2c9c4640f00c1c180005203882c4000e4161410030000500c60324543c09166908130740020004481c0751580d90000304681030415190040040e151a64054602c1c5001c01c004000490005c3c021a8403c0c1c0e01c6082241d0361b8402461030040300303100200b000070540003203000c03984100190884210038400e071070b50102c82101c1080455119030b0b82d038501c034070351460100001c001030340714140d1021a0002070740c40d082d1070002c01001d01e50002d001024942e8081906200b58490381c1c0100f025040652a104080c00c1082019507114030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 503828228 1250 503826978 503826991
    0x11100908070e160c050d1112040303051b120901140409020406050c060705030c3007020a170301030203030403080d09020a030809100e3a0b0402090f0717070c060c08 72
    0x5226103d01d0425101e408074040403038101e4082c000309191035400f1540304004103100004c6d442694807401c10407030110010401984651100707542c85200000c944480c1c0914085001c1035045600500c40044444048502e40d590901c2c003101030320310200080401c3d000750b40003022030310f201207808220750303030040c00030600241620100c3e0059524407008885d03c7c401100d44c000180c005100c9441c0224450580234542c0114030788003c0050040e5868050a00040301c00200591203290000c0a01948010344c980100d01022a18039560664000c40e689114510000340242030018002e4100007603540304610b03499000b001d178660260f40b401c0250b66500508580f502c1083e010f18242e460900520206c0200d03040900b44102058a141d035501a201c4500103032034000104074005500234806002c000031652144419440c9402e0900500c452800d0080a942c2508500000c1c00142904550760011600440782c15589941c2c0e0541c08542c0c1c10001e50009100d00d040081891005402454080c480c84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 503829478 1250 503828228 503828251
    0x30c020f0f2508030d0216051002031602070302091f080a05030d14100501030b0d2f06030f16200c090a0207110f0103020c030703030b1c11100908070e 66
    0x704094001d61505081c1d1041d5074180d0300410a103045d2503c5500a0700e070032620601c03030107995966500c8480c20a900c2d601c03107041540c2d000041060505901c04030b20f000707150620081c83c00d241594003249030300002030030810043c82000004680644d4002544028006036800d8600060940c5007140c1e0f00d421194414034981d003424803000040b0421405c00e40b09502000303503190b0180c980300c01580100340000415810141c0f0300031140100300000c2d800240311700501205000724040105051900c004490902e104071410803e00070f10018031a071603a000b80318903929603c03050a03081d0946401010700e9014295a406038890541c00c080070a000e440103100344d80c0081d07560b40b52a40d8104071321401c94001c00b0a220100c2d807040c2030900382c3c9041c071600018100103181c80f40c211441403458002c040c040b1f0000b51180c140c20107504050325590060068424040c2c01801c155075030544070f41d02e0211007802820701c1c980542d0101e1140607031000400030a0706480100f502d980808920341000c5611a0021 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 503830728 1250 503829478 503829523
    0x30804140102240a090503090a140f040603020a0b181503061203030603030f490b0607021003090b070e010215070f080c0d02030c12060906060901030c020f0f 69
    0x503480f00c06400854451696514110f99903140310303c00600020b80c083e035442c4807c0c881d4034104d4032030b444004094a0b0b4400540f4805d0888020842034080848103580620705181e02000140c50740202042952000c8440e1611614809009044485604403c0e40d000111050b00c5103038100d000011801054156074411001803080d071003c0ea6488240d45594259004105040c0300d0703c401405000c080c204040c802c20020003803088810350001a0204c83d212002005c1e02c003000c0e9203e500002c00345403901c038007481400d900b1030003d8103a0180302e5002e8087c0c0c0c0044004042c0c01d110303503c01d040031a440f0040000c51305020070020032810041090501510a101e803201d01030351f445098a11405640d034507514142c3c10808101d81c820409003181505100602440076503403481d0018510540400a80c240ca0b84040140b80a075000301401040c0a908400305020617a00c1d080201c41c400301c020700b000b007180503621000302c1c0b42800708604082e05000c2d54407260829980803a90050074032042c888501003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 503831978 1250 503830728 503830753
    0x804080f070b09040221041406090a020d030c02010e0a14010914130c0c0c0326070b060415080106080d030e03031014040f0e010902030f010b06070813030804140102 72
    0x1950030324002d001c00d440041c050310046140c075800802d903a00b54907690030180725201d1800c1c980b0510a6504460103012041c1c0c45280c1c0310304010346580081c2d0400200411856500402c41c620b040c008041e0412940006900569000f01064000d01001600c130200e055a201c413000052120b000003180024681900003403056080c6442d0960a0001498072041c40303d6440400028143c4032940b2041c4034070701c00e22501003404114031100450041c0241d510500c2c600101010550090010080400e01031200704080b40403034085039032041050303a001401c08040203085450700d210303610400e40c0d50300700031002c031743c0003804910140080300544050280b0303c0c0c4444016140d00045603094103131590607104214060501c542c40c542110082c01c00a00c480c2c10900d00c6c410745407400c64202651391a0020001141000c00a403448155600003c0040032000341c0000d400c1c1c440c004000e07000000201e60650007556080b840002154058030180d80d460762881c0e00b4134800c60b5001c0403030150181d090745958 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 503833228 1250 503831978 503831983
    0x501050a08150a05030a0b060103110412060b0103060b0d0f0605180403122304110603011a0c0c0a031208060613030b100e01120203011a031c02190804080f 68
    0xc180580d5281e00d0915540c0c840750066000520088952000c445180020303640c81c14020000054082e9403801d4132880d0003c0098103807400c1200c800d100103030820003000344d03081d409004503ea076401340c0701085084403040120302620b11074100d0101c900c400529003000031840c0d0700020408409640c03c6c0041e60780c441c10401d0001e642c1d03e44035071000706400007600180c0b05520f407140352800b4100015030140182885070084601884001a40c40f0000601003884442001c20058030401c131340e164955030500b00f10403810701100545528003400418402c04d640da05010047c03a52102900f4410705c50b540e03081a50007002800f425030041020400840d085041610450301c4880d035140c140e860031850350ba15800b040c00001e000d800d00c41440c0381d0201d4040b00c1420030394000d222400c40362074103030b000780109800c4503d400c03000d81b810314180b040748100b07403000329a00742d1140001001186500c42c1d8201a401c0812070b01d5070a42242229181a041105410203002a100e041044937400f0620001207a07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 503834478 1250 503833228 503833237
    0x108030405030c1023040501020f0f100c0c0812063318040e01060911130b0307120204090519020c2802040504050d0f080403050301051e090403020d09050105 69
    0x50b05a00010015609401d0070203004103100795910700928900081c005a18000403020b0030310110100002e401c000540c0e040101910700d40300c40b000b50444041a0943c55910034940d0310480c210303a220307403425403c0f40c000d28038143c680e80c201c0c3c1d146a48800d094840b4001c41401c0710440e01c5482440c07581d6051507508141100102d200000d04402d021884810710095084800a4503024079514507803141038840d801810541018100041030007428086401d0075504034001e4850444418084041c59038402d08541040b91a0b404880d0750740c2e1102d00c41240c2032031865041c0801140005000200d40c030030759002c2e6210300b103141951003548080e29009003ea110724400d45486038080690301d01c000031800e031500d9050010b0240418810341d26030104040d1602160300780e07042d4001c010002000c941000c0c480c0d102f28800d180108091a141c0c0e07015046003c180503480c001c0203111010140d0040040c251500041c00402020107850a071038002d680f841c524034550002411140d000645501820555 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 503835728 1250 503834478 503834489
    0xf180405070c3203131809080702040209060906030907080610320301090305030f0603120406033b151b0c07211e030804022e090e01080304 61
    0x14801c0d1a03240a103e4012039100004407881142c0700b140800ca40c000300001e11403000f030002040079051514010360440404240d01c02c520b80c0c10300504c1000549160700b21081c2c60303811900142c0f150440c101080b10390040d4001e560300b01400200b4011400703c0001c0440171565030310100c488070354451100311100312480c428010010b200981b600034030f0440c00c074040794081921323142c82110700a0100182c2510015002900400d90000502c02c1244c0d03503030030356030740711000341c0040c070116a0309030343d007500e51103030340300300e0f020540d890140c003451a81d2442c00070090340941c041100c00c4800079041c241100250100c1c02c0e242e1144e01070784070844c01d0b001c0e55144503082801c2d8400161441c04c004020750340c0101c001242e1070141d40b4000c9104c8141440e001c0b0100006902c100303083d9100c0c507003883e40218041700c1c80c64100080d1b140b000065806100c40780d01960617a50092003040700014000740c03085020011240d44200c0305441c1409a1002c3ca00003140c0050015407890399031103403000e07100e2059000701d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 503836978 1250 503835728 503835743
    0x5090303251704050c03010c0f02010f0b09042306010b0301090b0901140d08130905010f12120e030a020d0303020a0e150d2c1005090c09150103020f180405070c 70
    0x15191002e10050b00c254090700500565400d6014113001a084aa001031408085600d11211840c0994244100000360031603840400074800e8210001d1076030200100000d095904003201030360700b5604520b40e2400c040c4850106d46195840780f41042c5036400034022051a1850410006180e28150000358100c5a0714648032910008510a1000d66002c0d480187ea40c0401000324944865400e0202d80c020201e4060016407941040c003030000d030703040c10751055048102c12600803021450f070894000c02020716081c452031100d103071b80c0801d041c15031910010b54040324401001d010b01d60950001c0c0140b01d0150b442e0440074000c80100802d94401c1c1d10050315000b020b001d5480c4401c5542d00000402d07aa40200101319481441032400041e40030080310340703d070090300c04401c4515031303402080d03000ba615034003038221211000045001e4100043c6180402a42003034404041c1c2d0180d8100c41c02220380341209669940140c0316911400d400c045210f0080f86414005115144520400d4100a07808403c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 503838228 1250 503836978 503836997
    0x5130209041e0803010e010509010f0b03060103051012030c1b080613050102040f03050f060a0c32041d0c0403020d0f02010201060b03010602010e0d0e0a05040510090509030325 77
    0x58803400800740b203000e550032242e40b222640104441c40c000e0f50080155040040043d81481c0034010fa030f04042c2d00c2440c83d84200703502803000420f1a42503d5121400b032070300240039070b5004000380350884a036004528001c0000303040000d05a0010002045038081d000300703e258000b6802d486444140340c460880281c00020124001180b11002010010700560000d420151241221074200d035465004645942c00b400101c0081201071000b181d01a25400c000c000c82c001d2114080c00b0004801c40f451001070001ba622041d12418021001d29130700c2a803001d90315035490321214640c002607498049050f05d006030000701903491000454050780c0d4007404620b8120a2540c4002c1c20402844081f03040d0354aa9030007141c00c01c070300c0300918000e01e1580d00100e50300d0800c6040500300722000100504000c65109a0300842e00e450391440100c0d84143c1e80008c0c240d84102e81e4031100e44c040d8225041d69402c100c1840415400000070354001c8210410050f255446414010005000d440c0990089501c1c8107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 503839478 1250 503838228 503838233
    0x915270a090f0e0609060106030b040902011403070c170703030f050403050a08042108070809070501080c1b030c030901021902010c060b031903020106060311040b0f03070207180507030513020904 85
    0x2c00400354001501c0c0c012a50703c0807030156504046040f0b4818069a01c0780e40108001035150140fa4800c01e030551301000f0b180c13400d400080100803d0720004c07168040000104007070500c1075003004401138001d0b0541c21804510000015150702046041d0000b90401c544202a082d45216481c0110741c1512414a018151b51060b203c3c99801081030f6496050000203581e401152100c01c0c050740c0440e955240b007031400d1305c005440f00202030500d07602035000070401e02c0640d802406140d04220802c00c03094482c030784002d07000c80c9a40380c0c13403049041d80401f241b00074003210000b014265142c001d030280d031200000c3c540d505006512900002e4005500800d4000200350168081004a49c015042d905480707517000300302034000d06080045005079900c0300200130003541440ad000802a03403010241c44c2c94039025140380b45002c0c250207218807130000008910214020080140140030f444c4204050506081e44d040087c038085521a000c68201070010351550200100c211025a0003043c284c519100c1c2e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 503840728 1250 503839478 503839481
    0x22020d1b0e190506011215030c1211041a21072403021c2f07410a061103040f030e0f1e1002010e060106030504080915270a09 55
    0x41c0c50075050140718480f918240314103000300c7c81c42c601450080c5901c2c61642c42c00c0c070700030191648400368501916044000082410031084401441140c02040f2032004c400003e11101d420000c59078030500003061124032804100801109428a0050f200050342e03808050300d0013520114001001c0079041e0f8a6041c06000398090900f00610401e251b1107080510412001c80301c03030340003150520500307035062420001407282c4000204400100a42005c0b01580d0b0301d0f101030030809295100f440031580c2d65032100d600d4030b5207016656180c6540c4400290301c00c0c02d6929445012030030f44006003840c8544400c0d90705002207a010760f60103080c00b48412801d807400c4540700302d440101503114410142000442d41c886000004040903660400301404124080108041780c17003e041c400d5904003140100340704800b16015044507450304010a080d5114540209a0701c030302a0030503800900c00c10703032000b6845420094000c820000507446c5030032844d40c8049030030b6084040c4003544818920b8013808105942d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 503841978 1250 503840728 503840731
    0x614030d110d081914061f02120f12040f050f010605060409021b241302091f05040207030309050c0901050603160203040308040b1c02040b0322020d1b0e1905 69
    0x1660900c4c00240100c0c15141305890b0701c1103c02c5001c1d02c482040c003c2ea40351940300d8814030325580c81c00f6481e50340a40c83c0607454030a8202d03602e442d00d90104285070168268000c881080c101c80e0381010700f5240500d4440343c51050075800b5240340c03181d807804044101b0148943e2041e5a0024082c506203480c12904c44041c0d0320003901103e500c007005031000030300e807400c2040d41103180d02901e000c000c006c51403015002918006001c0d4000402012400c000b50300d50015042d04888c52036032440b0400380030303850054031610b940e0000c0d40142c0300044a405059040d0700502c8007900c107506442c0c00c031030443c3c10850f4441080c05030030340c031510410208151520201048081c1a03040c0140d03070415a036a2501c1c3d6190b04240d101d9403031480009a01c5451049002101c60000351040007141054101542d10382c4078000106500b40f40007a0112411111f0110a807056503142e004080242d410070901d003030907082100b41c402c07003050040e9510103d000000c040101d40300341c2030340c20005d021001640748003001c0c150 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 503843228 1250 503841978 503841991
    0x903030c010507051b01050105060a05090109081b090112030e06090d020901031a0105060a020a06051e16030515090604090f02090403231216050d0614030d110d08 71
    0x1041180d03000c20a42030082c1d5100d1020b07a00c0b800e0700c03400c44002c44054041c0c1608141c407a64941401803002d556030070103449544003107161181d11081c07802c005a5100c051500428094405c441301204282814480010100019a24031202d6641c40d400e100608071501401004100783c0c00d0f18102600f860300240c00400c00040c5688255030075500800c41e07030a402e81055886100d0100820702403070840c0c45e12801864140c601d40d00e80888050002e44840c08884020301e41510380000c140d8042204840260a0b243c240c2c10320841c1c1423409404401b2110122654042828180003900040360f100119000340d0004d018065195070304c0c0200401400020821660040801801c8000d0f0b10b980301c0983c400d40c0310b038446010440a200b02c0007040d03050307601c0c0d540a43c1d4040144482d0002ca0240480d0020f28810007042c00500047c000e03078041c007481480851452409000040c003584106202c1d00040082e4140c8805004d8000100c80303156070011001c05a1f440a500c08002e6031207500c8042e4401d5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 503844478 1250 503843228 503843233
    0x100c0f110301180311070609081002031005090c0d0b0102010b062505060c0304030201060f03031e0905060d020918162001051303200c210102030c0310290903 69
    0xd0040020801083d24543c250b0004e100096800030130107017040f200340500300c1410f0100000f494583e021b540c0d030000700007240e00d06e0380102c046202120071000c2940a000c00614440891800031504401c071b401103c0250580e504042401506c1d50061003500705030b52300a40340314500b010041d200d154040e00041844685c2d1513120000c2d000c00c03803e000d0a4007030b0300d141d0740059a0381401e081c000d0035103907281c07c0640700b5120114100000303a046101c0c00880c442218098080400745481078840040343d40c000b42d0450350000e50120340200d664010f0050030000c5541032843c0036032811405045804403007040000c4152444100701c64000d418040c00c41541500c1c500384028800301880c29180d05540d2040341c0078011140804040d0844c14003a134401100600c914424001c140c580d80c1c40e07504407840340c01519803c04a810000407110005c00b0149040300a5603603003000b1101110351341c400c0720124034030100004085000c042440004c41001c01c0f4580c1c0c03040003a40505a0240b542c09046070341e6251 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 503845728 1250 503844478 503844491
    0x160503070503041d010e011202270901050717060f1c0c0305070603050105030a050d03110c010203010b0414030f060118090519050d050909010b09010c0818100c0f110301 74
    0x101d04200900c090a81241c0643e0514031000b9a910030f0070042c0c0041c1100300302080140601440e092004281e150100c5480b940c81514649881031154102041039546a40200f084180a41500854050b842c3c958803078038622100d07249101c0d80c2030117941b0251701078044811100580b900c1c0e98840c0c00285006956101c02089075280d003601c007455801103034190030842d010029641c143c0309080c014601600074004000e150b40d04c2c00e4598032900c15540030f0503910412140d200719407500f0390303a400012030003c45d43c1f561900d100b4595504544240c0303440c90070500400d042424040303541c100d9a8841d4009040d02d07400c1603090306018a0f0301e03a6150046c0c2d50b81d603d00b0041541080f1b0102285e225108c001000501414a1400e015a400164050000822105082d62502410241100c0807080c00940790341010740103c402005609000d40003444c0862030700b5180203122001600b84400311004045050b4441341600d50320100322000e0f1580308121072a401007240c0319100780c9403400040000545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 503846978 1250 503845728 503845733
    0x5040512030a06030203150c09040510090c050415050405031506010e10080402010f030e19050a020604031202060603240910020f04090509060127090c0b120f0c16050307 74
    0x550412103244480640f6140100158141800100c011a001045072512868803640384a502d219200e542d41c0a260b40318002107204840d0791000c0050041c032182405144031500307000304550424040c9208459404480002941c01203085404840b0068054260f0740094030a98111410051099042c4200c41c2468002e50b46c4082e11940c000e00c007900d800085091038000102040e00d110700c01c805061812a20446000c0005044002e44075820181800c0e02c020f40341440c00d0404c00007000390408008100030041001d41c01c0074402001e0b00b0780c204d54040d03030744030105552411030140000c0a62280c0711350005d180821050150b2100305103044075005505810b800c0700720303030000d01c19909000c0003080034080c02205000d040d4000341400001c24155050031522500e152001131400a0154400220860002d4603046001091741100c2c3d0030041da03aa41d56110010744c812203c8071a03441128001607040d1060780d03150f5000d071205003082401c00103030805100400340716007401c0c0d910313100a205a100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 503848228 1250 503846978 503847013
    0x141c050a08030106080f0a0e1c0c020d050c011e0e0d1110210905100216050a030c0209160f050906270a061d0d38070918050405 56
    0x7414a540c440c0446d1901c845842c0c04910b020b0000c1900c64105140c01141900000d8400c24001c1000356008600c1103129047d502c45036100c8009402c240e1150000d003e001011582d80403100081c0c0b540c00042c54580080c95010703003100f00204c041003007c10000458100a20003c290500c2040c04445103804240015502a0013048600019401c0c602442d88800d01c2082410b00c941200014072120205945840c1c4601d0080140781000360702042c1080303c1c071881fa03604843d0b1504170f0103803041c030411410018801d81a001044c0d000352000300205d1401c40076071643c028100b00668a101c0e6450b214801211300f640415811b540c003103418000001e0503e08814a4214210405580030f0703110005020702269101da540100700313200c404a9503072011403640c5200100c0b007038200c81e8007166420341d1803e42003840c240e00648050040361425600022051b1002148c2d0b0100b00002904a40c1d03007840807120842680181200202c2c4800e583c50b2002040d0001038210344a04180c407130007400e4010040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 503849478 1250 503848228 503848231
    0x3031326030901091103070b030c030606070c03050304060f08040503070204050603160603060510080903180a170a0b0a110703080603010f0c0203120a060f14030703020a060e0a141c050a0803 83
    0x2c21596445104a080141104110207841c0003a0041c0c184c4514091070428140002400e90124090010014000b0b5a800c0308444429a024455440e265103038100035550303030460301031007000c2903082d50074104035030181c039056120340e900c500114600209503003400040c12026000c07540522a14001d036110f1505005204042e08050b6800201d16141c807042210036180c0488010a020f4080c041c03003100c44004c4111030282c41b0006030204a4850040482c5480d6000d500120020551a80040c1c195201041e510840350199581e20400c0c0c440085200486200d82c000010884c02084002c00181c060380102e5032040d00103000184040b1902000c506036141c0e000658016000094090030000c0c5041909800c0001e0707120400c04981005400c00e0030400718060740c076285008490f0007409a070200f00c0d0802846c0d01401d00c0404a58840d8064030b0071010011084c4140050340c00401d070483d0070030140b1011000106102c0b000c1c004110f40010309c40b0100f00503a054061229007402041d440c00065 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 503850728 1250 503849478 503849491
    0xd02040204120308060f0306010e091c030b0f03011518020f030103120215160507080714010506030f0a02030309010503090304030606121208161115010f03140303132603 74
    0x280c0002c10b00d0014240080207003076900c82c080d940a0b6401684000629505480701d00301801583d80f0381c0900c45251802000e400080c1e084000c0c002c1811a5058116980400c0207031440c0c42c081c0c074244100b40c2a20385624811004035030100040004800106003205a507003030182c0146800e142c00c4020780340742e0003604181d5001c0424644600030560400c000050368203101010503050501141c8004685203004010b801c000e0082000801d10010200700c52150340e1080d414950b461032986030703a01030403084510b58840c0c00303810860b1032045000f2607840c50007580107014600d003c0b8584010f4030364ae0805401071307c00d0b20003484040300082c81840741d403018044c050810950588a4645400300c14003908c0b00004005090302401400e96281441140031402403c00040c1044181030b00d42c6400c8000c000f1104c01c000a000001d48130008551510940740207501100302c003070a4440c450350300c0c8400d882120502c2c0b114a0010041100c40150307004d01c00000c4a0076054088040301d015050f00141c400c2e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 503851978 1250 503850728 503850749
    0xd03140a090503100209030c091014060c1b09090f0c1009150203030406050c0f030a09031101060e01030c0807080303011e0306050c0310060e060f070c0e0f070e010306050604030201030207020d02040204 88
    0x1001c6d000d207410441076006160850700074610b0715002c0ba032070821403424440c41600d0061440e200743d0550b1440c003600c17030000c980c0040f5602c0c0c400090a1140a42031440618003448809010070a4100b0203c0c25040724000e0200501ca001c1d14003003842034403072640d5400c070208143c400b00894980c070800c4403018900c1c40ae41c0216104d0405080507003c8440140444569020070041c1c803407000080700980b43d200751280b000060707a580300d00341a40e100c4800c1d0000a02075280040108580034034a81d01e6040e03d008000b200121511141c086a94802901030000329500c18001080310720100c028115200300d0008040c08a10340d45d50340d44080e1b513800e541c1d84070507882c0030040014806081190100800e4540f03000c2000007100b4001c80d8040c841c413003404462040c009864801e0042401c1c0383c100820880b418800c2c9842c01810403001c448c03054030350748001000010b52103000e602c00e009400688500415a80c54545558011b4000b50700544080ba0000c0100007190090ba0380e03480900000c0441e0041e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 503853228 1250 503851978 503851987
    0xa0507140705030609070f080c0108040803060d06050c04032d0f0309150e01020c10090504151203021e0d0e12160906090635071e03020f0d03140a0905031002 69
    0x207c1d4104042c280e04060102d5100d0420550a83c0e4401c280f542c0141d08150595503980303031440030551310300080801401031400c001c1031180764842d0100420499000d4101e20004880c102ca01c44440c401e40f80c0030100d1600c8020120b0080340c0080f001c1c401c1e0501c20b051046544d640d800c0c2900b001c40b4090071003c0451007482c0140b0321541c060100321f8a806040300d00700752410080c84068103c007401e005441c041e41e81ea500c600d12043e0021254000f414545403950700340905850002c0d900d0038041c03c5010f04541181e1003c8448200080d05002e00c0c0560b140c1e0503800d0003a0007880701c1c1000350411000284101a4108081e80e981c42040c006010340c0d01d00031a049040c02c8400095941c3c503031224001074120fa22103c070784842404140c0c15107007100744107040d00202c078221924101680e00400c7c0116841c60007210804800000c00d0100c91003607030741031103d40c0c02504201d800f842e100c00260100c0d2007801851003010000c0000c043c40b46003403d02d06105900c5002092400010152140c01c1e10f03030018 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 503854478 1250 503853228 503853239
    0xc1815080105060717161502130807030b2d0f06091014151911010b2e090f030606080f0c010f080a0209130c0807050a050714070503060907 61
    0x600003030140c10305a0300245804c13072039500c00c44500c010885250058002003124440200410082c2d8091038000c1c4c9000a0340c4010110302009520a50700022004080500007580000200d1660100c0f50040e00882d9595166510305140600c00e01c0c07150107440b0340507107075100002a4440309009441c0c1400002403403a00300705010303450b240035003005d129001c400c4080081c603210f80c1c4000000e030410b9502107160340c0c030100c0000d610b001d180581c64035201c1120f0b1141c0900e40c41402e030014103a540c402032106038104000d008903568100104409040c1d50044142440b100600ca40344404240ca0080e44036943d500c094003108285070030846406441c0c99080040b401c0411142d03181c4140603000c0c01e2122003960020386001d40b003050f42418007200c000080d41080003a4155415508090285400440c800900a0042060841d01d0010030000c602050400b07214078140c40c207805070b645405141103119241c0390700321281d50398844214480c0800101c1d00d501d00384581802801e8000041c0412400e00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 503855728 1250 503854478 503854487
    0xf0d022b05150f040e0712060c050310060e030f03030a0f0f06050f10020c100e01030e01090c0b09041d0303040309060e03070614090409050706030f1e0c1815 69
    0x99098400c608020501c1054420803000000d004002c03030f4001c2c44006040d000c41d002d040820306034481c1d0b00800b40c002030700c0b00801c050241000d10408007041103002c046026180c1d0b01040c1d9185261200c01c0d00d0a01040340074107031030381c40200001c040703464040b040da03041450340e4000ca59080c5441d4442c801da86c0d00300e0302c03800764047d160f1103154103214403420440804c266414603012103110b9005104480c80850082c4404013a00b00040c01e41511034440c600050008902d5000941c002443d0142d150f80030b00c0d0602c036146085900400f10b000031468040307040c0803600142441031303000e03a407a0038001c081c103d5800b9020603101c6030000f40d41c81c1c1c900f50501030f00300410b991102e03051040888400886540c0810b4000644e0901d04210003140303401e601c01100307030040c4000581c1091034a510350060100011781c002c00c07901c160f502448103001805018082c0d90445890240d1165443c0e105012505950407a5054008915050750391050880b0a64100c1480d07511082c0c0318004007203058a440d500 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 503856978 1250 503855728 503855797
    0x20d060801060b070602070317040b01240801150210180501230f0a0603121107050402042105030909040f0201120b090a0504050c060706020904051b0304080f0d02 71
    0x45802000682d140444910311440f50401c0101066070000d50300c81054010008031070480c09054441403246000d01cbc2c0746c813200340c003030040d211509a818000e01411a04003a01002c0402c07030b555005059191041030340000d45080c403000700398000c00d00c15102e50002480740e219481100b014400480b100c90408900719159400d036065503200f40c1c03540010100600101030307000000000000342c940e4501c0c070807200400f815080104240102811019002c0c1d01c11410210640c40e1015203000301d5a1724108400c070311861041380c541343c07620464464401e00601c1c0030507250380288156032400743c00c2000210304d82412a012940c0740c140c140c00e401076517801803c5090303174032110108100c0c0c0d00c62000002d00c21400140401c500545500001c0c007046000d21805400c4440608a9902c6105518168019412040c0190701581c5031200090354911848560b0740072000342820140355803129290b40101d68080701140f001200108058000f030606c0d4030003043c40c0c1040400401c40d03e0f00031074000c8180040d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 503858228 1250 503856978 503856989
    0xb180f01110d1b0605010b03100501030c14072109030b0a0923010f050705090f0d0f120e0a09090506061801060302070f0b09150c180f1f03020d06 64
    0xc0040c0000304800070380364007142e00c9824454074142071040305281e00003000d03100402c224200000000c41c003101c2d40195002e001c0381c0c8a68200103890310300440c11154124100c3d00098002074426031601000c800405c6942d0007807610b038040c501e610485402086114560344002a5140c10030003e1191050b151a0070207400039043c0010b600740c2c0c90314005081c0e803088950304c03410300c00ca05a030710750400d40c0b00d00e800d20300c0031006106a1810380409084d98000e2091107001e0540f000300d48d181858003e8404614a0703000481409084568540c84441c07450300e1f1a030340038440d0f20914280559265246e840003400702d80d0020540701401d1410a04142018080b82c1c000c41d070040c21644004540e0004c941541d4a91030010303214036103800d020010811040d406031064081c1018400829804640003084421400f004610750b21107800d00300c2144a4000c82481081c5601c00c0004240f41480c800c0c6a00d803802400b0b400989214003a000c0703110401d003511404290700140510b800199401800010507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 503859478 1250 503858228 503858237
    0x3020a0b09010c050a030f090f14190b070e01210504061a01090302010f02010b0a080c03123105041d01061203051c0e030403060203251b0c0b180f01 65
    0x1020500050018010796001c9001e141d100c03580402c820159501644545410001040c8000c105044c2b40e006000d13840503140840c000c900e090b10b11000303460b035003045035944850140d032140d6840c10201c42510085080d0742c10880c0c50f0310f8179840c0104615103c1c0314408000c00004041c01c052401d101210f0070701d140c02000002c11143c400660781c11804402c21a602800c00008103000301c1401c138010000900450f80c0008058130201e0201c000140d8913a84410980458003400301a1020401c40d015078018244402d012812360004001098032020850119007010402c03a42c4070000142583c881c1c03003074450005252000315020f00424056440240407038049581d6100d510303280102a841824181001114031000c50304250101d584030782d229204040550381c90326280c0c03a081019500c00c2c0c844011040c00748500742e03401c80d01d0360182e8890b1a1070380c4070394842d030518412064051b4031044083d24295402203002441c10408001003041c01e0040c40410300c03041e092401c100c1459144000d490400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 503860728 1250 503859478 503859491
    0x405010b010306061409040507120c0921150b040f0e160e100905090309061903050a150e070e062a01050705091e03011503020117061518040903020a0b0901 68
    0x800d4031700100d40e1011001e5801017003540da000000e55000b0b00354400100c00e903280c0441440c6591b44404100203a8880449202011042d103c0501084910301c1000d4584e10042802c01b01c1e004d8968041184440b002c0d01c04140102000000800c5684842d98072149811642e4034040321071507554808081d000048085145041003148110300304028021441c000350b669000c41c114038030070029608225401041a41e44440a0021000c0700c143c0c86008030100b800c00c1e021400c00b5405010b424092030081070a0000d840c500028280c0249000e4554010704c0030300c440748d0940e40c41c0c50000340a02561120035240984d51031030130051164241c0e1403000c0607450907060013907d542c04011034141c00c0703080341d1003030308002940b00c00100b06917400c1c6155455841d010080300591940150700c01140e000740c9a414041b8204480300c980940c048480f40d0788000da00843d24031a241c5180607003022071685034107141402911001c141103c0d00000306502580c03010080d03200f0021100071740c6510503c2c0c1b1009101c070307 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 503861978 1250 503860728 503860757
    0xd0203041b0b03160c120504060f08010602120702010536040e03180303040b120a0b011b0b07050909040c030b091b010503070309120e01030e03090d081605060405010b01030606 77
    0x80c0d01028000c0e400708884c0312541c00785030340300348081000550809210441d841c14190050005d0b8400d11131107010803102100348a116005000350790490709aa000307007200581c2c4204080d07042c1e120880407414400c00f485200510140e4405135000b11b028044141c80a00c400c501800203012070f0a9854802c03410083c0300d841d4020017206450b00030482a0032402080070079030009085020f25004400b208801080344080f42c0c1c2d950843c01c3c00760509010400c000b840c104011508501040314a07227403605070f003d02c680055100c003005a40842d180c0b07401402c018402d00025410301c41660140ca220b038042c030061082c0300c00080320617080300418000f410b20300c0d1015403100c0007500740344015062000100028864074000e4211202480d07100d9078607501c3c464102c0014000060050903240002d20303100308602440c03000001c84001850040c000000c4924941d2072a80b02c1e4481812045490408102980090310030004140900c3c4a54008038858142800044c121881c076441902048000d140c001709 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 503863228 1250 503861978 503861999
    0x51819030e09040203071205030a0306140d030e030106080d110d09080a08180a1d060405090c0d110405010605031e04020a03030c061d0c0307080c0303030c1b030d0203041b 75
    0x500c01c4151140c2c00c0d01d9a65000090501440b584841500078103002104100040030000702030031401f648007044001d0700c3c0d10040502d4001114440d03000200240390801090145e0136292050800030008681340d503c0c1d20002e414042e0322040c0360045808041e107040110828030108130201d049150a640303042c60000c1e0349554901d0040050030030480043c81d001b00f0303100c11805800722500904051200f80e0b4a510403514180a90031402e4408441400b00ea45440d02d0300640c0c1c012040c00000303280c60301d111002c01c00c3c230502c0800101c0e64041c0000c0711205540f1940a00c50003000c0704c1e16244d40328a040c030203109001190410b1802d40102c04401c1000596400301d02c901925050310340050807201900e0b141c0c1c01420300d5901c602c100b86502e902405820b10005d1034213036481007030b000d40d44102c0d604ca9006a80345001000103500d6003083c03001030001c0c102207018203144050304e940810300080443c042404c5038096103880324800d07000001c210901105850340507010798103045101e846403030b0111101 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 503864478 1250 503863228 503863247
    0x10608030a021e0a08040e090c011e210f0c1808070e18100e011a030604030507051612021c0f020616050106090906140f0112080d05181903 61
    0x600c415440641201c140340402c80703c91019448085951b0f10b030349619100340540f03000c4403110610321400600b0308070742d40b00e4156400c403100b404241c02044044000103440402000d0042e80d11400382c61403a080c80c540d140110b50800006a50019100070514001854202c51240a24040380720440c1000050b90000f1100200d440a10310030040b13485010301000b181c1012202c0107200e219400c9191000c0301103070f00000b1040030050082200c204d41c090032812034842c5046a5038141c01070000200441d015a006201162082081d1050b040581c54128004c0072030f0b8006160940d8a10401011401c00e419514032000040b207505d8000051903444050b00210310350000e0040e980413402d9071801c1c3c7c042c010302c11010350080007444802e460300c00d05e1000304403000f0242d510f942400e5251070b8001c4003101060160008074130806090b0b007804007482101c000e18000f111100f07010003141c440e80d10349124550040391000e80e900920304040403094640000c64080007c40038006550800180c0c2124005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 503865728 1250 503864478 503864503
    0x80403080f071b05010506040b0a0b25080310210b16091208031012031b03020705100f020f0313030f0c08160306060605040e0c070606031b0305010608030a02 69
    0x14100c03959440412034407080309030003443c00c0301508410b50741080010741009224240a80e801c02c1484a040c081102810181c0b180178004c480801c003054420303030904400140c1c4079081c3c40315480c0d0b800c60f0340c41c000d075540221030040c107070205510207111408080f00368403010b0700242c0250292003616240c0d1800d000e0b0251601070385028454070704507410300078240c18005141ca200b18403041d0105090103090796000f16100c5012603c540c0000c10100d0f10741c400481d405801d503807501031004078492080c05404101c0c80940c1544910a0009501c4e50307030b200b0b020030011296980c07080750801c5080c0649040140001042c8942090006100301c249030000700c0f048941000c1c00c000550140e080c008070303140b500e8200c034510380180c0b8030101d0b64145444483d0204d0303104038020407240e81d036000100d80c40e014900642000c0c0803002e010826004001d806407680b90301944000582e1603499a5070082c2c4003107440300145c1c640714100f041061200c28800d11008100200245180c0a650325000352210b0f5203060310b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 503866978 1250 503865728 503865751
    0x203040308150a0317090906030a03050306190506160506070c02030c010f2a02010f020f0a0228140406090b0d02060a02030415030f0e0c010c080d2702030d08040308 72
    0x41902d5035070310b4110001990040e40100024029072070344007440d8003031410603001d029000f01103601030030300091030007406030196201421500c540c3c042108200440c00314042c0803e907000041455620900100b00c00041c1c000c800305041901e151450500c2001411181800b034000541d00140c0c5011030b070091303801e0342441c1518140070303000015180b5080c40b04641c111604d2804040707103242c00d618412600c0034006d0300c4000d21003441d458101d0362802405000d05803500a1501000141041c07001c0da030000c08661a400440300f80045030424209085d8008600b01803118401d1000d070400d0720a1401070101314209208920032007011455a0307031352403c0280681400a46601040d10900c103907406460824096403044c1c5803110000c0c00303800d003031a041005038036000d1180028800003401032040101a1100d030400582504c138002c554000c551140213658854024454040c41c1503954454941d61031000665035000d4010306280120000e458001e110041042c0030200c1d820501d52940401500103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 503868228 1250 503866978 503867011
    0x170705040c140301090e0f03040b0a140906072019031424070305180d0f0909060306091a0714160b0a05040b091f090c031703040c050102010203040308 66
    0x241203075020042d200c2401c20180101c004210300c405034200d104d100c041b520803549106181c0030695240e2060384150b0000d440100950009580a043c014180403d007043c10303801c040104000c1200c4e940290811941101c015913034602a0000100d54441b60700182e80c034081e5040308070b08082c12a030240c080a054500030b18003407456500d0810071b40081c01d40805e200c54401c6900590076480940a61709140440d04180004640321340b40e03001d941c1c03038401d00f500420504822190540e0030040002c500801c00c0355101020030760305881d000e11401140f1454000544600301e0030010256260203840404284003241401001548034203001191907200c840707140d50301105208102c40400e80341d40142005500d004100003100c150b4403c91040380540b04240300b0f6924008015111003601508951448441e618030000f070788681e002415091080341025280d80d00ca4072040055022038016000d4400c1c00400c100400041d40d02402c0106401c0c0025811030400d923802500280300188100d125a50052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 503869478 1250 503868228 503868251
    0x12030806040e070e0703141513060306053306040e0c0c0601060804051c021c020705040e0a0c060507020a0308070620030a0c050309102c061017070504 66
    0x1400381d012100038804407103c542d0354020100c1280000c0b680d4402003072820318800642035a00000910a90f03030203025103002a480801c1141c1d08040801c2d041059554000c0417002650501c501400b1304807200306000c4404605484101c480031902c071161814503111a18001a160071041c2e409480c16000307102402e0b070300d190304042c2c940540a0543c1c440c0c8502000014400d0300021018042d034001d20548225400681403800d41d40ca03102c10040041c1d01c101000750000c155101083d90920280c810f45500566440000e03098a1001101c5a00f0b03400404428082040c07210416000340745a0401b82d00300400c5400003004041a40700262041030001160420096030741d03c4410140401012049100fa60810000c0e1540040300c1c00c1c205680303003011444080d07000c1e00507244104034047c01410b50b10340341500c03d4042e0068114548080030805224800c03c401d04180120600d200001000039140c24070307602001c07000740d5000d810340034201502a45166800b15041d401da403015140820400c4408 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 503870728 1250 503869478 503869481
    0xf070f061b060f0603030809151506070b010b030a1b0801061d06030a0504060605030a0b06040f1506020312130201051206190902070b0f07090e040c050a0603020903161203080604 78
    0x71407000b00075610b440c01603e44183d06034402020349010703030b403003008503600c540140baa140584804030803240045400290303a210707428064030114602806203070038213041d03581e002c800385002e8014900140b000302c05c01c0300f0080f45101e00d64602c00c0c103500065051001140117004810b06008000422141c214a14070b180c1d444000a525541c000d81007030703681e1070107240031001000252011141141082400103041c81d0010325a07110303e42000b180c1e82d45803140410040100b5401c0103025075540c0f50302030100c0003001c800d1241c2c01040b243d0081c540d02c90181e15804800c0f58018140750001880c6400c28015036800030690f100c0d00d0310501c40d02a40d03240c100003c0c6039164114000301110b400600081200c213010707000707002d4503449150f604405031248541c0c0c6070100b204480f840c000a12081e803c22402008542d91a0014001c88002d40119181c0707006c00c0501c41550020360101340c000945e504182010451003000b0040510b90031a41390408245140b0202103120190412201202003480f607a00e6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 503871978 1250 503870728 503870777
    0x30219081e070f0314013501020304050f1c05041e08100b0a230603181603031b0201020d03020912010c0806030d0c020a0509070e03100e0f070f06 64
    0x609000301200e140602c001001c80408860300d100007070074803100c051000d8034a840c0c1411b891a048904900d800001c20100c40c403080000e80200c940850030840404007c203100039400b540c000d030040c288442c2c0d418601c80c0343c410b01005817528482c405603c6007045900c04142c40035a0603500881e41140300240c10380849015a07004017080b03010b28452032580301803550000b03a50034410303100000310690381e56108d0500f0420070210260b03155058400c81d01841c1080055900c5240801e0000d0b05107841350000345481c5003841000d4201c24001030500525402c00045c2e0348410701c408900d00103001c0340d40000d4032030305540c484409054000c20740300429517951004000f11f40b00640200510004508003c140203020741d46c8501034021160007001141c07090481081c07150700a03110820b901d24000903c4030204000b8068800c101c924840b0315001c1d41c0030b201040b444c4a40300390204403101001801400e1a034603880b04035256000500401110000c1e194140c110f03801400c0102460030581e1040711010706 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 503873228 1250 503871978 503872021
    0x60c0f05031207120c050c0304060507140703110a05030c180601030e100c14070c18060b031e010602010b01020a02090702120424030209010e21010606050c01050703021908 75
    0x1201c1c2c0400031640d6002001224000c20501c0c24014440180700543d07183c45803071002040c58008101c240040390041c0000d14031144035000e41c90301c0e01400b8130302d0b0381091150f401c06c8510030300b5070043c09141c0c40c12000c6500584411405050340d00c0c01040090200c081c0c3c000741e0b41064030043c0000707465078001c4e40300341c0f182da4100040d00c003203e1520340b0181c0240f00d100025400309080c1325146088020180590320010f5202003d02121401d2410080c4502c4103103500c0203816456000100302002038101441c0501400050f04010b504c0ba0070707104141400507000041103a140102c007003c01ea900003002003000ba0103403052009900d45400803810642420000045003c0001c0d002490034240302c045144546039480f46501040d0040b0106c0c183c0c4a0426500d00081c0c501021620510300140080d11510411442840901b010154a400e692043d800040894400704400501e8007081c018998003400d1840c2c01c502d40174600c1001c0c80040702c5c42e52444200600d400020306040c22501c01c1054212 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 503874478 1250 503873228 503873257
    0x30c0c300f0f0a06060911040608090106170c03010b0105031905040206040504050c0c0606010c08030a0f150801060905011d071b05031305280b090a0e1e0f01060c0f0503 74
    0x14800e02c10300b9030720f08a11000b190750610b401000624400310784210b140c0764205498461a0030b1600e00d00b00c2d00ca080c054119601c5541c0c8500010790031003d40131569000e1100f40141503a940e5070820142110856120141400303c10001c0084154000c080c0441c0f04003403e9002070641c0300d0380003060641c060790b004160090314280501200342c0088010703103200c0081600f140e03416a20280116250400343c0c0e0010410300381413001c24404600381d000000050500840085d030f100300400b602802043c0303036100d0313000d6965401c3c042c4020a4079020350790150403038a02113244486503902411040e600280a0402c100030b0b8078000a484010366115021607405c502225250100203e01c012001e120340b140354452401d0104400a8860306240114400d00035100402c605141c0480c008540e03005143c4d056200d40d10a83c042604000703c0d481d0303801707100042c480112000390b01f54010032041c0054000102c01c1d002c0c3d0010064160700106411032030f0351100c07041341e044040c0e1502c3d510b1802204c03066112007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 503875728 1250 503874478 503874493
    0xd0503070c080f130810180303180213020c0106080303010807060f1209060c11012306030f0a050c040b030334020d03030e060a09020a12080f0a02030c0c300f 69
    0x1484c0c0c0b035140c15101c0d45406d80c1d404c1e00e20600344004584030740b0700e071101118440c0d5070440428001d91042540764884400548030200582c00241e840c0d01c0c5482080310b45e030340404c24807520703407007407241002820566004510315414003030031070350f201c40f80e02c505000c1151400140ca007062144500381c4600c0d448100070b01c88042146010307030240000948a100140030381300505800740050003050192694a00384010003031100e030410512020090030319070144162450790064200810400c2203ca0260300075003449944501048142c0da900012035101794400c1c0b04044085c400000000c91600c01150a03c4640026903006207a90700b01960195104502008043c00d05415401c42071403038062401341c4401d580c2c0d0350701c40401c8542101d00a5044140301d9010300203480b0050548a22900840c6407a041091030302d050440d40d40649510700050300003152240c02c01c40d0401c140c0c08100c3e012902a09020300322904201c015a1042d8125500c50140f001000903280034403500d102582c03107105440c0716 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 503876978 1250 503875728 503875747
    0x5030c130807061d090c090405070e1e0405101a0307030603060c0e13060819020f0303042c07120507120c090609050a030201080c0f090405040f140d0503070c080f 71
    0x300084840382100130400076207007566403030100060340c401c0041d507100d02d05010701c05060000409005020f1810f108454158a42c0c40d0b440b40071030607142c0701101d0b00501d102c2e801d0b014881a550043c05500001d45218014007685404c804010b0400314840340d804e03140d590760403089015000c16400604910f1420480c002480e5212810300f840c1103007511000c2c3c543c0c81150f60b03031041301e400d0302c2031a00c50b4001d2407011000c46036080d580101d0380d00040081c5d4100440a00080c19a0710582c0b00c0c004210b080004201440400c042c5800110106c640030002480d0030301e000383c07203e110403100203001c66886001408d2540685841418203180d1031381004022039070301c00501a403009010300d40201d60144000100c602e000301c0001c0541e030f17069592445686681740c0211181c0c022181015401b041030100c2030030340d01d4034403803e44124051111500002540d09103e44d4401004d5a5200141c0100001e0005d103900501202d4019905140424841c81c803401c0c10203141c021164032180a040c00a5105074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 503878228 1250 503876978 503876987
    0xd050c0c19080f07081c0c080c03030612010b010c11011b080a0201060b04030515070c0f050105010e060607021e0a031401060801150f0306020d230f130305030c13080706 74
    0x544409070b00b210120300304020340d280d42e001d00d4881c03c5200c0e4030120044228801c132850211507400d19040510f900685076030b07510100c2e000740c13400050550000c000c2080034a40744403213480c8000050000c100310001d03c00024490300e01c1c40030190003c1e040c0000c1040c641d100341c00c684603031554900c0075070702d8556500e44811aa44590420f40041d8200100400d000d001417007220200c2c0d50200c001e001103144c103030360740410a800405103400c4c00a8040f00602040c500030b030b0749466900c00c00c000901c035030400656230000140a0007a42c082d540031701412006807180c2a000300054407109a01c036014060b00000b451401e07141d0001040e22016441c0d0714400c07501500450140d07103d070b078000d000100c4000000d51000c0440e00c1943c10181001e24104040348642d4001e101801e803440e00820850181c110b400c108114910190030b1b007a0348041023000448a07050119040310642c0501e60321810b041e00e000300140806010080e040000042c018102101e0700241d8005000500036107102c0790751050040c2 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 503879478 1250 503878228 503878279
    0xd0e0604021f0c171c140c070b060409061b03090b07081006120b040903020a03080124050d0204050a080d020d1803120e090c2104050d050c0c 62
    0x2405640c21810901001e201c80301200c1c8500c1003035031950702940458680e08011282c00d41404020b0700c04028510b43c2c420080d28280090001c201c0109a6030b510640391007001c100141f60b0b541c81d5405114100008a2100c40207070449000c0302c000ca00d20001c3e041c88402015104040d40c080d031148690021000c0c0c068001c0320485004000c000d003141c0d11045c080d540920103c800940a102e44d80003440320b98001c151ba2404049034040010b0300600c101c010408807903501d101900981e000c01c500c8000c042c1c0c4050f9850140031030020000740c20416075000200d050503104190f0901401040c49410072a06a05a030001d003002030003c3c200c2c80d603481d0070680781c02049603c44014081e2101c0c80481c0e82c054801107954050b0342d072003c1c10003459038580c0c0902da001c10351408100100090010301c1c681d60512194041c96000302007640e107400240107080645004031080e5034080d5181c04100200e00e010484072900c03816410126503c10b4948605401c1c032480c0c105c1550f0000c4180c1d02d160000080c8a07041 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 503880728 1250 503879478 503879483
    0x747030a0b180403091703040b0403081215030309060702271603020306031c020a0b0a020d06120203070b09190b032d1f050618030127170d0e0604 64
    0x15008501c545055010b240854002d40818480b0000704040700001414556040c00ca000740c0e42031948410308110240d1142d07109460000c40410700c900318100d06040581c11060658110320900b1024004c40c0d2240260800c4501c01c080204001095486144070707a80c0c40d940c4d95005590100020351444141e04c03007034031b040f458440381c28400583c1d02e001e44210383c09290000c00400141303c0e00c2206841c2c40080c007212400b1030140360b40b08000074598903401401240900c1c00540c0762014444513400300d80309a030104000d031098030380000143c0c6011680c1c070140d6480d906669902c00070384d00801d0b040360081544101403104034100290f2400414040c42c0103035408014194450081100c80c2c0d49805000407004101840101003400701c200041e02c02484880c1d040740200d12640c0340f00080d40740e04154103503884480c13201d11088081c036081c840c075800c149055800400c10360a104501d4400750b00b280f030040036038401d299158107003614002071703842a01102e54144061091908659203484007610308 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 503881978 1250 503880728 503880739
    0x918012307020118110402091503090606011803031403041109010e010519031101030c021e0c1305090a030f180303170c0406050924030103050d020747030a0b 69
    0x2950150281e00c0d14403442160001d0b5500301704192074007008002d60007501781c141e0154800c41c50100c991744d5000914400c3c0039100160180d49801c00003d80b001b56010b100c4c0f00524018441880020b420503440207111403000c0a541e103a0f640e41c03420190701000714521a620000b56000040e4400d280d66425069034801d4950513810040303c0060201d0f41054040100749019042c40c0b0310343e43d440b03036110b03010311a018030403100b594000a00c038800364110702d9407030401d6801a100f55942810848448141c00075980b808010074134240c40c0058903005043d80043c10041c0a1441a205500c03803500540c0c2140c49135070429000340c1c0c0c2d00d0007401200e81c0307200c4030145070946000070781d0108096040e6412110141c44107840c5c440e200301040000c0fa401c10b4000c1c601245440e03c8001c2c010480040c5019602c0303000101000105030901903d0507a5a510041da00103101c0b50910302d0403200581089450210313031680601ca007070003d04051030ba1140c110041c512602200308403103504182c02454921609465 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 503883228 1250 503881978 503881991
    0xc0a090f050906010305060d062c03030f0103120c0602032509050a0623030a020c0708010e0d0804140d0207061101050609160c1b06030605030c09180123070201 70
    0xd1001414440e0711070a0707800092000041d5495010303810056016400408407060035101b0f580384000c4560100e06591008a5070720002d4107003a501c0f110400030f0003e40015401e603c0c1200b0042070809050000078855000c410702d0580ca10b00800c0c45004550b400001075480f46800002ca809042c441490b035456011960481c011442c01080d41005841010704800801418a132040c0c07094042c080c00a1040f2980003860f5007545074005c05903004204203040565500740b4030071481e1428003e0340007814243d140c5507008042da0300000354010180d40c0da00300080782d0740c0c450500012070350104c81682c0d5075004040121842c540c0c08202c54080d074000c0d4449000c0a040703000d505088a900311810342d00312480c240420200c1000d110924600b04107403a020011111903681c180414907002c01807019030003a0082800569014000c40000d4101940144001c1290100084420340c000d4022042400001c0d18404030007003e4000703903000d08082c08002c0480c01c1500d0228025071b8110b5042005501c1c221 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 503884478 1250 503883228 503883239
    0x20a051206010509060102031e0a11070807150c0204051e0a0c08130206040b0a32031807050307120b150a0311180c0703120c0f03050c0405090c0a09 65
    0x24040508034003880003004903030300f460180070800c0713800f42010341980300a0001c1da08130154555078004410403c410070b0349031001240302800c142403294000c070701034210107000d21014100185103000c64070490414580a140820181c56880303a541c1d019401a080004000d400303200c00c3c408101c0e8a0f0408114401550b58030010b0341215004402440010b00240100701d804289030100701049000400035031802d9030382d25070749640754800c40c031020111703503c0402070783d1415281c21007020600d15448201808960b40f00800f98906c00100303802c000c1c00c68070f0343e01030055038100114805464090100c503240380c1c4aa14480010f5224681100c403000305000003254507403e00f401c03441c11440075001750700b02402c55441c15603000d64140241d400a40300c012500740700c644070800501401801180e15a9034050303040081002680c000f0000006091291820301c0c150301c4442200c0000300c9250011b0301e600c2c0d010500b0b51a103e213a004940c000703041024800c41d260b00c48000c00d104002512843c29555480 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 503885728 1250 503884478 503884489
    0x403061e020a0212070212031c060806070c06021b07081513030c020d0503090d0311160303140702060d02070524070507030518040e010204050310050f01030303020f0f0c0604020a05 79
    0x40c50080c0050300004090b20f0340d41c0004014001d0184010705c7c85504034450f032179240c5141c000c8003040d010a18843d0300011120900d01c640406407110402501c181d28140602a010f079208440c001d0065a00096015000042c89020903c40e03030520140c5201c50b65030104144d64540b9413040320000d40000d404542c08110310342d8010b90003645034855080c02d01283d000c111029400c5a401d55540c00200268003440c1c0d81d56499550051081c1c4803014001811101c4174a4040e0140030b040074082120828404203421564a101c5035040c0030400303540e0400ba2011550038003501c181041c0071800803c810041050100e1640325102c3c04690303510f21400301c2008620340300010366150003c6402003100701d021900c51401041c4642103e006445041c00420200d401c0344c50500f03000813203950100d41400741e40707401d005843c0e40c102c42d800103000074105800d0311143c1b188184001403e065001a156142d03968600544069a0241009903103851000180c036844034012a012445440106030103e90361414 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 503886978 1250 503885728 503885737
    0x905030d230f070203130f060921151104120b061c0618020306070801090b010525051203150a062c060c011a0f0102070503100218060403061e02 63
    0x1e4a801e089a45890180c02c40c5903001801c410218001044418185540502404000c215000304880001d00e01034004182401a03081115030078061004c800107c04a070512203a019045001e9030900e01c800c2c0e0200004045e00c0d910f0365030248001c1000509034034130042c07141c40980110b081c82065030300c241c20800603024900f0046241d0700c8019051010908a90100c00c4407a212811103200030182c5e000640740078030841d41d44e4002001000140800c654601411400410a0804a0501511040c40450214004d403100071070140781080e4428403504101441c1a0b00a20300801d9407814100620440940c640503024025030310ba0700e001070700922801d0102c280c8038046012009600601a4510340e1590031240c09a00c14000d001b00d10040350b0038072401d0036800c0d600c2c1d0104110780000042c8031550800c0e4100a0642d04002000c0005480105032415224120080142d4803120851340504410000d800d1540207040441c02104002d0303554842d5001d0418100c814400007003402e100c42c1039214 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 503888228 1250 503886978 503887031
    0xc0332010e0a0906090b04050c1f182607080604021e0a0e0910110a0c08030a09050a06020301180b03120705010b040222090c0207050607020d060905030d 67
    0x948004101101e640c92041d600025251004101d40c840c40d1502d0043e03e6004c1030560b81d400301a000d2008100040140f182900000e56213200490b14409100323085006c41820340003132201ca61101341c0c040014030b07007035000352540c4c03e0000c40011107100240052400c40160110034801d452012660600c009616886640d000703250104131046403429002d21040f410305942c020310038800128030480c0c51021240f0403c24100200703040d00f0b0b1010314506403100940c81490540040003850b903842e9000c00710602c5a070304a010039540c1d4031001003880050507289406481d50044845140030045240c00031070403101c6020f0b1410080789443c004400b122141e80400b90725622160010b035665032410041c10b2242d00540000a0504415022405076841500d1001d80700c030200807144110000968180054003581604000301c1c180441c2c003954030045406020320440e0040f0b0010210760318808014003207580036405206072115440e0031035480d08528811442c840c1880b1002d0501c1d0143c0524680415 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 503889478 1250 503888228 503888321
    0x8030712080123120d030b27040602090d080a1d01020c010c0201110c120c1503161b02030d030f061e090c050c0304060503060117070c021002030d0c03 66
    0x5000010700c1031203c2076902516001105079060720502d00040c0520398100c04144c6000c61100c0d0a002048661944d0a41e402d00d44421100d030900e440c44c503a8000c8da48668081c40050f501d684180c0010400c80c85002d00800010b0005144501268050071010780600c6402091002c141c0c0100103903150945450f0050000b061655050701544c40740411041d0381941c0e2055504101c0c0d92070100d00288071010704c0c594030ba071100d1807444a600304402424114070001c28414154140f040f01c0c1000c078685010008108a04504a040340f400e003144e20003000c6500801321041d000790100068060160100d05030455031030b00c00d0000d01c4000b08141e03103e1144511182060103420b09829100803c064102402000710034009100030b0300c0200010006080305454590703c0f440d101000400e00360700e00300350b0311314408800d0a004209070032a003140c0c40c50340d044039410407500c00004220b155000e5004c6a8500c641003040c0181050f8140d402100b140d031004401031120010b600d43c502c401e9103400340000404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 503890728 1250 503889478 503889509
    0x190905041e050a02130308090a120317040611030f0403080c09032817071106192006162c150d05240a0f0b070804050a080307120801 58
    0x2070380242d2120b035001d032888200500700000d0440d1031580300c1140d04211a10b10000402450354649002c0d80801880303880030a0051001d5640d0050900c030903828071340c0800056a020a0800c42250881520f00000030a50b50720385c5021010600344000a446c181d010035800c03408180d8502041003200c00004000d00280350076110380c1039940300500c1098000390404134918060300000c50031844507061212040b40345843e5000380c100715040b12800110240328070002c100007240e4401c503541003e900c01d180c0c10691044080f034505522940b460107074800203030040d501040048070a00c6407000503030401e59210019900200c10303601103410880b026100105100c401d81890340f6040e50030a6505a414022a04201740c10202000795a401d564055501f4600003100c4030b0003507200c81910001104540007080145446428904030a450042115403a00059020103218865045a000342000b40041d03c0303050340d884600b9140d400c006c0d011030b40010404030f00380031148039001c1c0740d05030b51908040c40780c0c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 503891978 1250 503890728 503890781
    0x71403070e180f01170604020f0d0203010b0a030b0a0f150e0c04030c03111003090f0204051b03040b06030105061002060c13080d02010c09090c0801051c02030319090504 74
    0x11500c0c4050040e8004040d401a20558042d002035078010314207003070ba4065550602283c1502889a22030301c0e589503004600304009030743e8400d08449400400d440c0200f04400c14008030380988400440c0a070030580c0103500004000400036000d10a01100004000300c1d10244807001c107440e105500700320070010005040c0405400c0c04052604815140009440c00747d032a50340700b1a016a0b58000c0e941d44401c1c2e5039907400350400c07a40075480001c2a150410842605580fa8038101e0b40480010b400b555403000007440964483d081004c003203600800842d128607051034a22480c0904a907c40c2c0a54207240101d0b006060011415100c052244c01030101540c52840c4420b181e080410003940450028100090440c01446052050525a030011514202240f400741c203c021660140102070300e0300020130403c5a1100e000c0d815030b2022250300c4551410440695a1400c140d0707400395040c007000904404664440300c3c81c1c80b6034626502c408444964850405c0101e070301d0192002c0104000050070310b00c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 503893228 1250 503891978 503891987
    0x5010311070222061e031a0105060307180512070302180f0103110f1e190f090506040e030f1206100c08090d0501060f1a030105011e030204030f1a07140307 68
    0x8841d100954002000c960705d00f080040f008106000c480308010120b41031040c4401c2c41408140307000c000c44442001d5240c0380101e2000d120003070807907040054100041e99000c80196400300100320040c03c25041e003a0500500b070b119959480300702d210b001d02464130700841c0502c11301d04d40708154a98074a07046a1039601c0b00d003040201c41100b20f600042c0d09241c44000c4e500c1201240329808404a465001040041031100a0b210684140142a04460100901040c0c009100c0c00d44440d20b00104054541d000814040e00d0002c1d05c1d103a65000c0458460007208440024000740482010304001989501d024821800150104040010b500d000444042200300b001842600c50142a110700c040b40f5407640c600719200b98218412070582120100a1100c404070358500159030700d25440d2031540740c140043e02c0071100d01514006a401c40340c10301c0e00103000740d05440007503421440c64542c240040c0b034400c207c0e00040410b25210a6014040b82e03486115024a10514401002c50351070341c1c4640e80c0544e03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 503894478 1250 503893228 503893279
    0x130c050121091a061203090d0804050a060e010f110c0607080d0c051c0e06040f0c1e090e19081309020c1e06090a02010f030609020310050103110702 65
    0x1034074004401c0c00501d0140345110700c20b081c602941c1414a560460b107003c500e01c0d0005801280304401c8025030800c400030100840e113810f2022143c0c4040600c83e46044d031803a005580c0916448424484c0c00182182c001c464814154026a140a044803102501756210181201006010b51042d41c1c410714500781000200740d501d02404800d0704042c4042105820b450f0003c2041c0002170b008550341401201b8810410342c0c480c4501c8050104641450080e03075a13000c0248003074452010a054401030191300c02403040500500510401c0c0d0040407030b104020150a4411100f0007071401a800354aa44089044600c410b000b0005101400090321418a1074002c20741d410202200d0110000304091244001c0003031468400c00707468448802481036600001400003070243d600640204242000d0204980712200c2e82400d101c0790411040108a0040a55811450030035200009114068ac4080d0403c0b0454409a07001e0084420204104506004000000390010305d400e081000c0d4422860345c0c40d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 503895728 1250 503894478 503894507
    0x2312120f100f0b0a1209060603020102100e0c040b011701030f03170403080612120408011e0b0105251a0f011a04060e03190b09190308040303020702040603020307080114130c0501 78
    0x4141c40742180b291001114030204081f600760356121000c104558040c401104680f48510701002000f000d5208241c0f2089482c04a40c400c075581c920b6110141e000d82801c2e40140800034840105607120b1611100492648000342e0204503800314100e2404480300307400e84100d50558601c05c00d07403034080a01040c800a100030807180d0041304400c031440c14010000c0c200030804080046003900400080609134800007214a891504111815a0b666045070850340101004000f0250000034280100e440c00d0b400c9600400d0074919035005003850105220b40e600070404110700d40c20590360356030450080c0d44828107100002c3c200348001c0102c03a0059420022604025041c2c822000e02141210913584160f20b007118841140c8081c408072043c02c00541003461b100c0302900141c4001c0e91009051920020001020103800040c18000c548454000c5801581c0c05070840707030440c2d100c05401e4080c1c02034401d10f808284010000a452a56425920024903004003840c106a420603004540d2400c100090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 503896978 1250 503895728 503895737
    0x80904090f05010507021b1206010519241e0206070f020312010e070207080604050c1507020d03120c0201090210030c020312160f0206042312120f100f0b0a 68
    0x6041c04250b0a010b40362007282c259024140c02c0b102112000002100744500c0c601810203a1003c905400000134441c0c1551030445090040c9a0880000c628402c16600150011a40500286c0d4010204c007000701103a109a111850f00c0301c0c42e003441101070b000840c48900140d20000200b0b40050003910001c460340082d03c1500d10700030403070409503420700080e405020078078100d1003041140f40d8188044806410b0341c02c040e004506054031050340ea40e60906109205602a0891900d041487c0045603044c07580601030426070b201c542800780c502d15480f8413100c811070610010000e83d0384180f048000c01a4010a030207107011250300210010710300b406581c0c06601c410031500300f442e00715030b0381d80d841030203140c4001c8003290f4086c5000385040058811a13080d94490800e0000003107841040c0c0c3c64600080c00c20312008104a41c00514248100c1d0810010480c0010403524110880540714441d0f00040b0020042c0e80300c217a80701e60b0403c03192052080c3c4828607402401100011802844c46075440d141 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 503898228 1250 503896978 503897003
    0x1803190e0405010b130b0c2a011103040e1f05130515030f0a0609030c170a231c061211040b01050306030a0b15060c1507050910030f060f08030711030a08090409 70
    0x1040000b0360303c0d01c1c0d80c07642c20002d523020607049581d1010940400c075112070302a5041138902400362070500e8015142c001002e41020081c60305001141c3d00a0080c00c00a02c852145003c900e00b61b40102026140007820106002d500d0b4003600300003680744070802e8804002d11002a458072000014421400101d04000880d983c04010413080c02000002c1203c0302d10203a40c510030414080c1003040e03c04030100d4205008041d0061714002c80c0b05035400314159075800a540c10101020000400d256041041044240341204003402000b41611402010640b070400484c600c280041d07641d800111465580341c0e1291030801c0020742c0c00c4140380e8101d803040c0840f0006111040009a1542040b01e1010310303a40401480c0b182106405000c1c0c1d00516142400f41c0f41c0050540450079488030742d0244424136845000c500b10308405580004d004204030020752601d584c41700340050326039000c480242c54000c0f40e8401e403003543c6008103c11071131691001e0342a107401c040303900b444041c0400b1401078403208020721 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 503899478 1250 503898228 503898253
    0x5010e1507060b030a03020d18050f0d0204151403070801020408030a0c080705150601031a060904020f04050402030405010905160501080402040506030a05010f0605190302091803190e0405010b130b0c 87
    0x29017025144240c01810000300108402484480c04114a8400d040030b44410011a200c500c10000005800d40345114140300a0012a0203488492100c40980409440005100c1c690600e24804102c0845c190b840540c0d592951a0070b0340281c1c080c000840e001005a100224013941c501070001e0710035880603052441c036450350350400f00d034039000b482c40c91885010000d4569140c490b03540c3c0038035545103241081d03800ca0302003a040e00405109074040daa000451584804001f402c1c3d1740100001082550340303291a00e0218068005000100c906100b451200ca280200c0c40c41d81d00281d0b030040e502d40303030184e403250204800b400300584019058011400c1090200d6070a000c1c4c000e116030401d2010a01524100c140000501d405040d6007180d5030440301400140c0e03900038000e030441d03403030000510661940140a8114412607880480704500315048a25058000d80d075080c040398100d6080155a0740c45410b11142d11800080310345240c1440810700030305c40c000001d0329800100004480c224903442 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 503900728 1250 503899478 503899483
    0xe0114030703060911160204052205030a03151a13030f0c0e010605160b04020f060d0905010b0418060507090b13051e0102070306090213020d0f0605010e1507060b03 72
    0x54840e500007a80343e2609015506260043c241241c015604440c5040100f9203200300381c03a030100d40244156100c4e4085000318007408142e004220a401c50f282c445142071400745e980f503101005201c00b090900000f110010f105240e100b049a103d0b90041c20b0071800319003540c48503405102d400354040c00004d03012000c90100e44a514a0f10701c21003140e615941004104440b900e0705900030f508120042285114440708010345441095024400801b641c6076840000c6070541680c0f420754000d48040340b220301d02e6005400c884c900034000c030000c00484c140352060000341d4540c0541e54005003c03c1c100390001074000d500c000e50100c83c52911102054843d120070301541d1040174510701e0040c3c0c201040c821494044552242c100008400b81071141d03c2e00c00103510f4105520002d4202907440c5000e1065483e101c05041000844c03110856454107024040340040c42d4549201061501c1d0030b40c040b440c2d500400d103402081c10010403410442900101d031011035404407104a0721607465841c10720fa2074504 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 503901978 1250 503900728 503900731
    0x7050f0406020307050705040b010c02120705091905010f0b03190b0a141e010c1502091f0f0e031c0c0204091a0c090d14151f050102030c030a0e011403 66
    0x5640695902c00017820414a80041c2d038124520503850524240080d0380c101c3c3d83c041301950705031028009036200c41110703401d04d80680d11554104181d002041802e80d0118006160902088000c00c42a6290880c400840b03409018202c154101040850708540c0849011061500803d001244c211501d50204180421540c0921000c1000c440010001e00e08852500710780310b07242c20441902c1c4101c1d00020034804924002815000c1507081c44600780500c2e40464651000140180b004e02400d42841440004400351100002e1181180e2109a0348514540d000f9000010010086419620180f04d0385c9510042d552040c0040c1c220003400680b100e0040380c0b43c250140b48008420f0702020101980407400405094800400304440c8040c0d07a00e60003003044441d0009040c500c0442101419403911a0116981192203412400c1004801000d2003000528242c4c4151240c0c0c60390310030040e65640070b00c9d000702c100c0750000e000581d0201d109480d88900c03060149040e0070480303613100212680d50300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 503903228 1250 503901978 503901989
    0x804080d140703060605090306060d0f05120d05011203120b0f0a12030f1103070807152a0c05030d0b1801030602120c041503050c040b120f07170f07050f04 68
    0x801c8000c0096a40c0c01d03104060081013182425490201d5210000c6c0d01ca410080a01c0d11601d0003018600034801d600741c900d408954480104c860b4200e4042c5403a05607007080540008103810700f000410482118007110902e0f5a0540300c41c2000031000402e00003a004020083d904204400c402e030040703546490307000004228441c00745e00e585d042030a00800350403880501400f03115200c4c2090304c10000000848002c41e07088060305848044a10701070100c075642811600840b0709114030742c0004400004020b0507540340358010079500c03180c020151307080600703008040c1c155041800040009009a0416202d800c8000d001c4420101c0c1e4200d1080740000c00c1e00160350903a804110380450300b2119038440e40004070403040a0420f854043c000d8011644603190800b05074072030000c2290060001d09407405001c520056603120107802c00464142c400481e8292061210940480c2159019045044c864507003042900034a503241c1d00c055101903006000001000003c104101190311042d016102510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 503904478 1250 503903228 503903261
    0x10020606010c050f240105030d05041223031b0601060c1709060a050c1203061e011806030e010f06120f1704030c14100516020f030607030519020f0a0804080d 69
    0x45505201703941e01c9205801c035071701030b60000360700308400c0d900704094030111280403800350212038140c9401c4400d04013482d80e2120b103505d015880100864044050500d0b14004140c12001e400d00c004081c0d941c079420301c07800d000312710001d2184021a080c81d14034010303103c401d0380b403a25188101001c0b0b0000c0c0d010740d0802d03000400c007181c1380c1c50454007440540b030007440c0d00755483c7c00c504200700051452108811030010100700742c105603032aa4040d4600b0420706115011504906035a040003402038018034080780710039442c00144e44c0714400244a0a800d9901e00f007400c80c00740d1346654907010201400320082d80c000010b01040302c5504015001480903522402703001481500d1b00e8036140c40200c80348441480780f120100803c02c0141e204050b5060703107051800f0800d0055650000c2072640070550355035500b50050104018603180c141c1c00c45030151045c0582516031560002082e001c80c054941050307041c010800802440d24810700190b5005800344151900d001d40b240480d00c02c503028460a2901d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 503905728 1250 503904478 503904523
    0x712030903022d010c05010b130f0606180509060a03080c100c0e0d021909050405030a23040e07050405121f140606070302070305191110020606010c050f 67
    0x41c00c0c60030b6030407101075003000140d500958054a0f6040400140412030410030740d030380e2000500c1025003002c41403860207010981116403000c2c618003c0c161000401401038200100041c41303d208801001c0700c01501c001018400381800d08100b448000a004260700401c0b042010000c5004040201502d00000001703020905800b24a6001d9850034400c00c800e2050b00b590803180c0d0340300c2a0442c0c00c01c0e68111144480c4802c1152600380d01c00d8507030403002e003441c500b030100810004008020f00d141ea0641d21035450b00d080f10700b40ae0350414a00340b04442000b80500c810418074120f0814590040c1d440d0800302d0900303488001240204044000c00007840c0d008640324640f101507244613400901c0e1300d04051107644030802001240707030009031040e8002d0784000340c04c40a151003884510302070359201040c1c0380d2032003a94104020382c0925500c1956005d40030480101186000031041c980c1e030380035402030034048c1d844100560362003290401c240c6041c040d400c4501c401039002d0004508411091200a02a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 503906978 1250 503905728 503905733
    0x9010b0a0902120f071b0c1806050307140307091e0e030a1d0d0f02190f060e0a06090902071b090906110c0a15231f24020712030903 58
    0xc07001800c0e658140b5103110511030090b92007036603141c0326011840304110f0500c1d10700d0864100e4486510100c82145400c050348c11040c020b030004001c551044003182c2d000e948440c56000280804501c0d1581755005520400c010000e640106111340ca1142d600c2640107841040d200c2540e000c101c80b031b00944c200058192116030031142401c503009124041c11016400300011400d6100412806490003690000340c4045643e0312018004500300304006100300c0b503035551880703c1074000d030143c48003007170801c41e030060641005148001154050354401c400f1614020410000794045402643c0b04071907070710008041d41c0d04080d190700901d03a02c4000258917490b4100401150441c202100c80c0100400001c0b11110300040d480702e034160040650b41f80007841025000017014140083c0c0045681401c0300ca03400e61152400d40e00c548402013249a4229810106216844050181c0c1c6484030b012441c1c0980d001c01400c80b4104050726004031100c50ba102c090003003030030720420000c400280d03507413809108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 503908228 1250 503906978 503907007
    0x3020607030f0201142a1c0504020111010504020d140a0204240f050604031b080f0601061704120e0a080f07240c0605100e0420010f02031209010b0a0902 67
    0x4000d14540207017151814041003421040307032480601a80000307541e419a41d070010000c00c40310900105d0b948810354019100c1e042020346011141680400c040c00020040c181060040601ca544d0050101d11301c9d441c82d695040141c48014000b0111b889100a02e1005881d20b12503c4100744048124070441010801034050005c0c031500101411245800200901e0329200107a405480d4000b4004484039849003c0f48803441300360740a8550f5100300341481a4081010800b9810380c1c041d40c0e1184203012130040b007003861340d0042d100103000c8844600c120308510710074444580f6809000740700040b0030343d45180301894410403450020b030b507070800c100c00c001c80202021400440030555401c00945015550301801141103800d020b02a00d85650000c2c4007001e840000700c000d030074a014040c1d2207040c141060100305081e960090902d034228104041d1a6000d0f11500050010b594001e51030203900760900001454064043c4095640f07410700014540c0d10b422814014001103100161105c0c801c004415 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 503909478 1250 503908228 503908241
    0x1206060a0602030903120a0c05030414030d080402100c03050d06080615090103030909020a183c170c0d050a0c090b010804080a0c080a0e040b030f0c0d050703020607030f0201 76
    0x656000700201402c981700071a8030b41c001595a04000c1d01c44ca2040c0042c2c0342c4004009000348640000070307001c506280f601c0303401e5114440a5040b2030307812046010564050605035000b84d07104600c0054050824490007600c1c560a1080c68028140b041030400c1c142580d0f09030700200481d03008102007120a0481d40b081c0c00000c44100c0e02007a0035499520003805542003805040b810a40004400390f085000b0521507800c1500b14840c1c0c402c1035a503003803030007110205042003000e101c448445c5210000711002241c030750895110030541c40c4c43c0341480307040b20f07401c0701c14801503d40940c0d116600c003030b1f80d0b25103802e54943c0104041c2c034802c0d05526103003075646019040114507625000d1020003e9910080d03035980503520140f401e95030598030b1000c1d0307407040405c6c00050243c08001501c0d50003950010043e2074042064a05001248501042586507181008400b419500c030240600d03051400035440c00c1ea0a00400549181035201c0e0040f075020b6100100640c0070465030404001c0c0507509101e00c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 503910728 1250 503909478 503909489
    0x2160807210f0b0408120c270a090b120303011d0c0a080610020f070b09191a07021909050f0a1404060c09050d060b1009060c0807080403021206060a 65
    0x1034041d100c26030360700d03410502115405415a8250030005040141e824111410880161a0081203181007a60030901c0d900c00e040b0124014245030300d483c01070140180351400d60400134411180d0702d040102c00b500034403c54024542c00351605504002c4500140021130280810100c400c00c0e140c0c03045040300c008500039000303007201d81c0d0170025980b50a5000780c08a03013100d01210311a4020454030012860210202c1d051012801900c20029601d00f582c2d0041c032801c1d00c191500345a20a00c009020100c080754032551800e0500c21290310a1841030000070001c880c030081c4110700320082244140c0d0500750715044424541d41c3d03142070100c010009035a80e9071185128000380b000160140c41d1003d6030101920003001e542c0c582075183c414500422401c0050640035000032000071281c246100030346036640400e802155440d0003034403201c1c0304815210540d07003d5110207488080c0ca54070300006a010610aa440d11010702003c001640c1e408070800d00783c96001c0003007129040840070040b46058a0f0f100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 503911978 1250 503910728 503910779
    0xd020f040807170d0f05091c0201320921010b040609050402100c33050c0405060a1103090d0807150b10030906060e1e060406050a0b0a02160807 63
    0x952441e1500040604d800f5802d0716041c803050000c80c90030313103050007584031040d400b10214910f090342940a803420340d0418005da0342c04100048440703109024840d40c1503084141c82091060640740391404004240301440903340c000500d404030901d00c5000408a0003241030394407501c48094900d02800b940e00078089209041100341485c1e40010b20a0190521002c05c0c01840014001401030701140c54501d00c11110326100700d45144c4140e042442c508070b04015000b8a08000f050381c9102500c21740e41520406000c407481d008004000391010842e1403402c2c0785600c8100321700e5105484000b440488a40300715091511070105261001d01101080d007803211091800503030850603500c4214050a482c0281000940a03080341048400ba0003142c201d058051a810180f000c1c4090a000c0308800da10141d84001c040e440703035000c20064442c0b62207000d038096040c50b8103010090100001340550796150044030803210060f80c4207220b8144992242e01550090745d0200074908204201059036289100d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 503913228 1250 503911978 503912009
    0xa0c09120605130b2a160b130c090911041518090f0f15050103030f0807030f0903050901111522060f0f0b030c011e050d020f040807 58
    0xe04001221440090189034642c00811080ca403078a900340c41035904000c03418503602e0803403405070b40d05c0c0740c5003201407411039403200c15450368010406a031005013104010141700381c0d06445400603080040d15411030300140d44200000502d0341c0e801c01e0024800314002156112503404c0c006150008855110702170390400004c0c080c006d0f12805640300781c9203521205030280d055030368140002c01600350003e1860f0041d000d00c03414001038207003e40200344520303542c40d034420703140803680183c80c401e00c80180030525800c6641c8811380164482c96100d025440c000078031030100000001901d914020070340101d880000c0c551900c0d40c1c0311703886010300714000000b403031001d541c4112045501d00092041d0001c0010036121016229400e202c0d0041c65048482400f600710700c0b00c176400040c0001210040d02c0c1e450900303403403400d040114540300b80c180146c50301607415012545002c0b501020365280010000e040108042c000c0c00c1d44081c0a104101c0c02d0b9041c0c07220305200c04e10749003075803035045080590b0700e415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 503914478 1250 503913228 503913239
    0x2101020304031d10200a0206030a15050612070f0e0907090305060a11070f050c03100b04060e010602301201171603031103040902071a06060c03040e1510080a0c09 71
    0x201140d210061385c0c042054114410503118107014800304000e41c00903002041c0081e4584680010304068102c0f28001c50041ea1601042114840d08951200e41000741000139401c07401240036621365070b00d81c1080202e000c1548000b030100307081200d49101180d1540014005d002c003c000042e4400785c400c80c00c000c0321070300d03c11030705d400d008040008109690303c0da002401c114051004c540007040140444440c4052440c569020380a80100c540c0618505070000440441c5840000c0c12914070ba0013800c00c040e00d10051080750110540c540401750040446111085140c1008040d003010100c3d490569504114081d205480b99140b0b0310401e034050700080e015114509003210849a0604001501c0c001c502c4015007103000b241c0c004e0703804900c040340b45400d00040801010b0404a0300078403103060350b5080100b02072802030300c0d100c00080d801880309012041111074000d8004000311003a401d00c141c80d0001030f111761b000310a0034000910b1042030008690003402188400341e42414100800c42c00c10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 503915728 1250 503914478 503914487
    0x4020301050d020f0604090204241e1808030307020d02061b031303020c030303010b0415030603170a090305011b0212030606031b16030207061713022101020304031d10 73
    0x1182c0180c440e0121820070810356940000726002041700c81001d540b40ca40d20710440103101002c0c0040d004800c13036443c038110140e101e1003040e55120034280e200260210a507004460b0b20300240d21241001104c25004902c0d1581000590310032071075980109002d40f0808002030405401620b4400102811991804074080500030381e90300000f202003524400209050480c0351550b41d1081a070580000400403030300e405244000c00c143e4400d121101283c40741003200320122607040c84042d1650003d0710140c8000d0740f81800801c502070b6580b404508190722511071900711505100b002c0d5182c001091b80064032501400b01c80200b900c03165419042d0701d0644041912484024406c10050034440c0d0110a2000340744250390303140d4030110502080352864074010303503104060b0203100003041c0d10081840c4064080b440c0240b00381004446001003c50b2582489039400c0d034524103c40d12151034031040c3c80f8040c24805907101300d001759940e40011189000640c1e16840305102c2c00d026030710300b0102940ea00d410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 503916978 1250 503915728 503915749
    0x15181703070c06051302210d050c0a15020309070f030506150a030506040c0f08010605030c060a030b13050f161b030e040f050603060a14010b07110a08030304060b0402030105 76
    0x400042696640c0c1c51000716510044080010b150f20300e00400c1c00380b40c0403000480c0080a10a4629100e001804400308142040b2072070301d01c049070300036520155214400c00150800c07a445800b1034040345400d580d070810b0500c1c2c1d070190b0742001d0750202c1004607118080100d90010840c034103940b40d8032030860f20350ba502d83d52300610740300500c013108807007031a2900c8000c2d0783c400558112043c0c070400d050614280c1c209120034421003008000c4007a01095806040c41510115140200107102040f903200138804c840d0400409a0249a51640c041e1015101d1040b40c65410524440c0040d5a19200300780300d94244020b013885a103002a014070703855003a0011100a0301401c20b8101811222403460304030783e0549404210746d0441d0a003889201543c025822082c0284401c070142c43c1d1950318901c00004940444440480000411004100800c000801011800d005030400d07118540b07030f480481e0400010740c0c01184180c0c07001040005200f403a02c101440c4a0f0304413815841c40d45000002180c04c4d90 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 503918228 1250 503916978 503917013
    0x10090608060406180f111003062607270f05070c0615150e01080610050a0f051e03091e100c0302090315090f071503020904090f1518 58
    0x140c078115132083d8010a9041208241e100005003500c1c0002c4c40c1c041800c8070313440364450040c592105c0e518603050003801028191f920010024041190b5030a000e840210b0300a8031070b041e801032110100c0d04100c0900340300c81c3c884404803401b9035800800344840071509039215510a56140a0034804929441001030a1300350300400040b52107408142d8170660b21866610054040b03a070101c0228405d5001000c44451900036280c0c1101d540c0e070300c2c2c00e00c2174898500340c10100007a41084120181d900540920072080820b10f0110b0400150400b8005825100306155626220101c2000344402e000c10100601907001034241c240110414401c61f42c1d0f011303000301d241940f911255802c119600c40d41c1138070090700e002011900c4d468111051948901c00685014a840c0a101199903000c00f000512030100c403507651907208024844001100203410259140e40d0098480c10442e011170340d020f0707000380403a0080807404a1315104019420803103028070445d41a681c40d02400102060300707c003000c2049507 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 503919478 1250 503918228 503918231
    0x40311040b0901060e0301060b0408030706050403090b0708030103120c0507060503070302090405160912081801110303090114010f03050712020d021002030409050604020304020f1519020610090608060406 89
    0x20615800140034291041000341c20280c03034000025401c1d0310a050b59840e010603002002450744510b850300e82c512590181d08040d92081048100049141d403055502c14005d01c1d0108110341c880001d60032691110f04203a980781804401070040c820411382d60002e0080d0b41c100180210440e50302d80303440304210300ca00303c28000044009002070b40290100c803041240103004101c103280004a00d061640d6500784500000e02c2d5030000310308058038010707014156401503005030a0108007428007009000d08560381e410480c01c81c20041c080381c0200080c42c0181d01d9003001207103d0f10344000e03200c50000c050f485070300c052110710b008102280e0086008810784983c10b08603c2e1280150021845024001d40300039000340405102211003980800034000760348030740e64180110b13262403081000fa400f054402940c8401b04000200451030084a8a0000b1021040030b504040280d0600014038041c4001240503801440c10480481c2c9205101e1000d0603014104200960502206c603541c0e20004000601c00c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 503920728 1250 503919478 503919503
    0x40b041b05010804150e010c05071101090b0d0b0607200f19090506030712050f060a02190806040905070f0f0f030c0e070519030b040b090f0c0901091e060f0f02030403 73
    0x42c110344d0880d92031b9203800b00c0244117203055010b00418a602900003600d450b21084c1003c04258811402d08044919450a13076003800001c1c20f100e0000c0250900f11548000300b0441c200c0003845d2081076900c51450140403000c2586443d092042803c5412001c611440103e03201c0c072a03140700c1d90700e00004d0700c0356900f0024244d941c1c0000701c1c1c40d01c50039800064401e503c1ca00c007a01040000956900402041e10944800340c032171100c0c520030b038042c902410007258a944440f095031481200450740c000801000450480e032261200d0b0304005468010031120804550140004a800c1c00c03098014200d41c8030714103504d4038540b2203015802290150142c3c00000101084c4d4141c4101c0568800c140c0040f405040c0c1042d008000d0300810100d0030fa28012070800a42600c185004000e072440303100164804000c1e139650130b4a07040503038400d03081c0764140038a03118042096000201d1450240801c0e0200241290400300c01411300200c0c3c40602080015a11241003a141d0210651b030450707030300c080f014254 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 503921978 1250 503920728 503920763
    0x207150f0b1f0f0c02032b0813020f18010314010b031c0c03020a050303100f0902160305090607080d0504060b060a02070509040212030a0c03032f03040602090603040b041b05010804 79
    0x1304100c00081c1d414410032000c000140d1522030b911019080c41071205a00c40c50b510000d5a040745e04940344940003031031800e01409030409048004000c0c1000b41255500e404401c01204680820380051307428415100d100961201d00744550301000d88200c00800c50301030110041e1522805040004082107070320700640003090300070080743c80c02c154020700303480e1a4075000c000c11044d8100c602c41d00c030030140751410004a030a403034401c41d100e0002e41c20820000b021180c400b0344943c0e02c014451a003140003000200f010860342406400d481c07800740c0000c1000c0c00c0c5400c0c4103080ea03018001c62440754000b0098103c115400090344001c4a40540c1d20310400c0e5070b43d0001940d104a11540c100040c040040c040c001c00e40d100c150220400d219440400441c070290754444900707428032101d15102400300343c4054080c03c6030b20265034082d01c10b1001510300310403030001c0b4600d07800a0394202c4403100814288003c1090520310540e400684202c03600340345180900082c0301e404090805000e580f40c3c0e2a10245 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 503923228 1250 503921978 503921987
    0xe0103020613050303180301051303021b0f0307030602030f0c04050913020609130b01020d08190e030c0a1a0a1103040210030b15071a090a080d0207150f0b1f0f 70
    0xc0030b0007005d694482c445003400e040f0243c0c1e4424a00d21035440d00000500866038504000802a0180d005061071740c2024094804903100c041e0869101e0140140480f007a50200011805144100c901513100e041000c881503c0bc14042c03c01100100288000e006030340301e1240c4254040d2003451103001ca4542c60000ca052841118140d5070082c4142c8152024080c041d0800d0401c84003e81c07c42d04c00350b220b05011114082d05451000200b125200c2c44041070b01c003031700203400901c01c9109891500c449c0046062a0040110088802c0b450004407004940544444a503000d2200302e01407129178403111f6044d0309480010b00092042650402c29140c55101e030740014610000500784000c0703040c19140405281d080040201c5200d540d00b41c0e54407020b80112903075401003400714020b28034601e060b61400b003590441c1e034005090650074804c90012074031905840c0c0409000074400151211499445003c0c0d51032004444c2c01505096540d002d4400c0a00c003443c030492151500048130341e10044200c0c1d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 503924478 1250 503923228 503923267
    0x10807030906021201050f0d02010801090b030f030a030b090c0c07030f080d0504080c0c06090306180a0c0f06030e0a030801031b0f08160e1603020307030f09031106100e01030206 78
    0x3400302d0310224512100742c0c610155681614000c40d0308494101c420001c003e01032030105c40090015002200400ca00d41050b001003900400050555a80d5401d1005040c81c58100141000000780c54460502d007c0c00d180b8034007504a01c0e4000810310f403a00d91800c441d51105107104c014282c881c41a1140103000c680d03011350349600399407403040c05a8103003414140c80179081505208058000d40c0584503003458040100e56601101401805880d0b0741c09880741c440021140d42e5065900404505000003403003c05454050502540450341d0682070046c000c0803100c0041e0001d955510501005002c203411041d490b04590b40910010341049001415030852030250340014440d90000350045242d1402055105400c881c2c80741e080c2015a03140d00c21101c0034015030f034850b12228484c2841c0301c114401c0d0005c550001d9581004105091450100710442e05030010950008400344000c084101c1c05001a5030080d08103080c1c0036000b420b06418250301c03c010b10000748207180018400c500340c415a003544 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 503925728 1250 503924478 503924483
    0x3031d0d0e04110d27110904060b03150103050c0d05031222060f050615070f1a1305150601140d090203060c0c0106090c0c02090907080d03061e060e0108070309 70
    0x116114600000e90501800a2a21101102c0040d4052070300c0504017140000340729400c807203180e20312000d001c10f2140d59100036005803016a103c01030a81251001c02180b5400d00544010710b01540c518104035061049450701244035078040768200700403400c00429140d982d42940703068900c03600c170091094810589003400f00b24080708089403405005d425804107207110001c2d0002c0c8040e40d200ba0401c28140103403110800099010300440000c11156448618820b01c80c2207580828190040004400c0008480800814840d100301c0410010103101c944050f040074207440c0307000c2c00c0040018000c802270540311143e0b8200030800c01d211036450f80002c0503540d00642a92414180500c8081041c2c0c40855161000e40c20034000003503540552003940d55071441591104c02000040c0c0c02c0099042e4054102d030510304c035242000c41c50700401e005a0140380d0098070005101d42c50519403501c0104d882a0741e01e42902c940c4420441c09030011090040c41d44246804e12031030341c400350154020008500007 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 503926978 1250 503925728 503925761
    0x31e03092301500703050304080a05120103060507020d110615030a06020412210912060b090906100906031203020304050712153c0b03160303031d0d0e04 67
    0x980d88500030440c0510a810b400c00b03440002440d0100f94034460b403081c010700500150003080000c0205404030042c003e50100b501d42a440d0450b9008528a0b403c000c1e003040e035415543d41c003800030b100d8040011008042d0381d82090000300c0000f039081900c90340300034a640407080b40540324008980d4140701608030207602c1141103440356100c0c4004106200402400c030355421b5050801c0a41c00190900c109009090f60785400145051000d401c04420100030101c41c110b45440c054080b90b40d810b07800034451030007840208110303c1d0941034903690814580c888421145440414004100e0403503808a04421074280075a880c3c0b282e180c49450701c00c0580c041070590468081000801c0104440150320000318881400480d242040d0000030241e68460301501070160075503000d0180d2407a82c841a00b540442e000200c107503155000c01c1c1820a2064000b031003062501f0180704040d0144500110044030481c1c48044403603500d40d450395009019103a40a00c610034449814aa460303800414405080b40300 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 503928228 1250 503926978 503927057
    0x3080a14070c08070509010e01090902010c051b01030f060302010804080705031e07150c231e07051e032d070b0906090d020a03030b0a031e03092301 65
    0x100078035005110f02400003140101d0300d0000da6131a1581e2018140c82c43c0078984690b6034a083e4440e030041264000c22414041c2c024800030108a05005040707184000207040b01e134410380d11000604643c02e05043c420070500c0e092050000d130343c0c825551940203034071000a595071440c9003021071440c00b410f40700b004002011040310f1058004140a1b000c0a0300c0b07031810611145d1900581800d0307902e14140c0347c1c001000740381c11071483c11441f91088580c9030306d4400c01f803400035080c00500c0c078040c5e114003291501e000000c600d4200942001100c1ca012402c02d41903a00c9200300d00d034651680306260900e00c0754130300040010303034000100100d0343c51010048040c640d00c1600d45401e280c290000c0320103d50740c1c0944030014100c0350001c144100307821700c1903010705004803142d50140c006256080c282078100c02ca4507400b10000311018440540380800e0340b2406070b40142450010100c01c0e26800956044690103000402004450a8040d0081e000d0038000c00140d080410719040503c1c031015400c04c000780a4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 503929478 1250 503928228 503928233
    0x1a07060b06042709020d2a230a05011b0501020d2309070803160c05100302090a0b0f030a0203070c120905030d050f03042a03030e0f0d0c03080a1407 65
    0x3c00403032100307040c503081d040c02c001c002103490407036044510194001c07645401c01030000b1868000020104402550350500c0c901c92000d8602074002c0c1e402072469080c801000f118900403540100d000020226543e949043c10003000915888e203030710f000462a0301e03000407a03080007000e4041c0d4094108070f100c200a0451140781c0315049194402000701400001804180300e04008200042680d410b000214a8a14000308100020105d801d00340e500310041d0002290359030310001808681c204558002da1505140b030100070400105c0c1e441030b182031904000b030300c921010700015203503c42c110340c1c00140c695581c1c2c60262040413207004003e1005a0f0040982c0195810140c80d005890041e8100e810303070124040141c0c3c540c2326685000304140e00c1400060005034041c0d102d046102c1407252010207000f200d04c10440d0854103500124042148001da500c0c4c6420701090865080034229804100c40e007070b41c0c44811062419010207001702200240a0300880d029200c0c0c4082c18a1541c007540e9503000c1030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 503930728 1250 503929478 503929499
    0x1502030403150c170c0412110424091a04050a0f0e01020c0309060c0a0b04030c060b090112060f060f080105060a14091305100c0f0e01091a07060b0604 66
    0x140030440c2d001500c8541c03260015141d1243e1030100107030ba1613421180c402075200c070300d00c26002081d41551180411010a1100101d04142c0c0c42900c120090480448000c0030002a2040f404800c144211140749950007107e40483c0501150030007840001d070000b810a5601c1c1080040304926005407c0000740060000d296021600d11207056004000200c0c0e16003d0500342d00c02c0d10301d9000b5690050110704528a0841e00902d18440c2500440e144203182c1c0d074a134100c050301140c055004c196003003052814010f032802030700b810900c220b07540d8219604089058401c0000d5074005001c0340e94485411710700b440550321180207880301d0000c590b0101e82d03c8605074003030082240c2442c019214580002841d40303600d2404280c969005182030781641d0341c1c04019618800b011000d80300e600c40e148105440b00c00d01c0c8510090799070560381d4111720080b21030001d00240c00c3c800721b1070704010072400104600c1c090300e030b0000650010000000e58540141c2001e4029020ae404455888100040d00003100344d000b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 503931978 1250 503930728 503930737
    0xf0f12030604020f030c1305060309070e06030705040e030703080f070c06020c010b03030d06030c150905060a05090d03030902030f0a0803010902090a0f0909030f14040b070501020d050702010c020709090822150203 93
    0x2545503007d40551520180030f00c1c0c0c0030a95000c180c60f800b441302408004808082c0c0d03039100c9000780895803a2a5520005000e850740b0b1800c140240d040001c0364030606600000140c0e02c1500d8042e24036060802e180d004280654100003d80300c0c80c1e0109000040039000e40104010817030060440b6150058640e411008140902c001c42c0c89011030b00c03000980d00d490184200007002075403505801d0b0f61070308040c800d00c0e82c000c00d001c40c1001000c112509003540c030501003401d000c0c000c1e80e001494604503c18107161201229030001d45600211510001491503012a815180101000b40e100c001c1c00000c03480e9a210b50300700149a0542070b1011991580c1540400c0d2800e019542c0d07080444001031080d00c6c01c60b00d81480d000f50850402c410b00810b00d6801c0103001e001d20420005290002c00500c500880d40165998001070b51076004500003540d04109680c00740200040c20464100b499443c98400d10409100000120601101041c01c0200383c000e8802881c00141000d40c9501ca24402503da901 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 503933228 1250 503931978 503931997
    0x210060329010b09010c140724050304200102070305060c03040c06091404090201090302130c0306050f210a0c140a0b1c0506120a0c080f0f12030604020f030c 69
    0x4080c40308521200354075070038504840d006072109141c0102c860045a0684c4180401c0c1d83d50303001b094a9403040ba60402c46000101095000313031010454694464041c51442d4032324604000e02070003440082640503511342c00c24861003c01600400c1c4800040c0e0a2648603880a4014090a0100141c50060900031442079210f04442e1009940342c100035265052603000e100300444d09440d140d41a4203181c4d1200507a00d005040041e801a62a8006188081842d5405009a0b04c0340c2989000e00d4044c09000003a240885515003401040000300c0e8029040076000c5022000390310030303004084814801032200c19000091801c0031525116030313008174598904403178062a0344500000345032212000b598004c4001070800b0491001d000000f40181c6805000242d01c841c85d4200c2e000d40c04010420104a1440383c0c41ea100300d245854461380c2800005c00c100036498204045554503c0c8001c6000c0020044041c010360f00c90303c6c1e0601041c02030040703028091030000c0000c244242c41030058003502d001c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 503934478 1250 503933228 503933273
    0x110d060911030d020d0807051204030302122d041109040302030301140a0b04060e1302042714060112090209070c210801050d1a0c030118051009050702100603 69
    0x1a9580180b55030340340c070704050200581200e80e2203031032917215404541e007000d56071a0580c140b413910302903941c7c1001d065030200c001c80c3d030024190024065801c0410380c04a030903c81c80d02d6085101d200c0701510304502c8403480e842d2403840c000400b0090042d20000724140003814002c607a2800c0d1501070b560390310038060201600f200b0800c1c4800d501e4502400810b60714980341007401c0924218060b42c03414608030f0754640c04070281215079040754062010f84020003003201111010109110f0300c102084000c490010414101000101510012518580c206100780382284c468105504820000d0240307010003540042c00c007080c00201030744410251040fa005c1d070440c1003070b0102d8001c1c103402d0320f00c0d10315410040b50a0b60010080c0d03203030004085a005000e00410010036001e9200e8070445001210a4011098044014051500040c1070001c411140000803c250b0a21400400c0c540a041c4205d00c0c2e00ca03115070000341024400d0108010300361510f541846401d0300c3c0d00c0d20008030700380c0000080140 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 503935728 1250 503934478 503934503
    0x4060501081b0d020d140a080d060503010209030a02090c1e25032a0b0c0a0e15030a05131e0204150f03020603250203030106020c0108010b09010c110d0609 68
    0x30140c4075641e40303110702c008100c9405600302e9400e010b4044113401058030008070007140352010680600c002454684100c800c03503920501e1181a900302d03480c54101d68000d80c81485401d50f1a2000243e01300f0042c1c0443d030902060361004440b82151054080300e0500142d60844520b0f80041e04000e0000030615070040c88203009200152602048421405400111035801d03c074604206040075003001381d4105143c1640b0900d6884d1640003100c1610070619030400050a02c0110341d209030403004210080b2040200800c6184030180e803070001420203c0582e580d0704c0480c100c281c41c600b80c50078295000005050583c6001504078036090201c0c0c0607402a4107100301c2440901c00003080e031098801a4402907459401c64090099a070802000c00300001007081d1704105401c03204890f5120782400d540155600d42c10a8402070807c040c3c01d0229051001d0300005010700d95101060345e4030301a00f031a00310364140c071074102440584801004290048002d030119001d000440e0417042d079150060307140002c82c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 503936978 1250 503935728 503935753
    0x10050c0f22060c2105090409050606033310170c0103140112031101020c2b02010207151505060d02130509010305060105010804030207031e0b071103031f0b030406050108 74
    0x1003c5410030061400210142541102c800c0b41090712400055150050803c0c02d50300c0071a04a07540040c080d00c440e03001d9001c20010741b8041000c1b040c0c091200c8040b0010910006030400b01e458803005000c18401004001190b4080c4503529900500200d03d0090034008024001912100a195050300203824601c40b42c85400c00c18a00b036040340e05032442000815082d403821a800714440701000e1555400700004650302d0002c1220300174854010815940000701001c8860354400d043e4601c400b564014802d000100b48189044100340b0f0046c10003240990b5071050483c20b0904541210758003280c080b030040c8508045501070310f02840e40e60320703251805480d5401c001d4015000d10004020f5030003040140f0042d446400a243c110f803003801201d04082d103c0d41c400c040d52440303030210312200c01c0c000c103600d060152002110f50450303601d041c009804084050040d4491100400381c840c071741d481400100c052003030080385100801d0110401c0e6161f0401d4680078001d80390a104806040c031030000d90001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 503938228 1250 503936978 503936987
    0x20d0f06030302031b03120a05010806220209060111010e010c091208030c1c050f0a0c0507050703030806060c0f0f1501060507032d080405160810050c0f2206 69
    0x1525019001942400042e5030103907400d499030170710b000860000f80081c210000010101c14041c4903a41d102040540c1005c2240f072038001c1c010900b207420788a0062004801a03802502d0107110b405444c03100441d41d4040044e00d903035011840c004095860b10740144c000714810f41c0300010800071641c80010301c9965016010320841c2295015100010070004a4050a0500b0040101c41c444054a90400b6081900e40d001c0f1407085038601c154000b50410442400080e10585124101d2420103d0921a82d5154180e40d118180401801d128085001c40e2250343c8010541d02001e41d8681260b00043c0ba00f400651245000704c1c217504140310703450a00f940090440411410707104a551442c0c1414001e450403101c0c03040011a080d4260b00c207038101181c0e41e04c2010702c0400b00e5100d07190710005081600d4290b1510b5054035545500113200740c81400f116602050748520542d134681c0c0880c5580364020728100c03038400d000c01e90b01d214500041d007201038a10105100c0400b0544250310301d215564400c140da = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 503939478 1250 503938228 503938241
    0x305060c130e0601030902030a0c29031314101505040c0f180504090614010e01050f01050f0c06090a1703060d0201031802040c0903021f0c2d06020d0f 66
    0x11180e40010140b00d88024048120b501180500d000714032092070380c01081c24a0300502c2d0136241018120020302168181d4659030132012440300c180c00070b40c40d46c4080000c040c00301410756089a6000c901c51010f124101480e6041100c0300c10239581d0310762122040c0c0f00100900b04004d62029110744000a172458948074801c2c20386243d80b1241d41d00400040210b5504918907510020810661004141c5440b103115140c02613104400000d98040082d80307041039240147c0c000340b201e2000e200103204039198174010029a1034282400340e101c20000d8052015401110f80c00b10b09442190100050400001002480b081c010b003211403641d480211124020f00c000c5809035000b403008625100194072aa01030b181125140401c1d2a020400e41d000600b0b856002040381c0c002450340c0c3c3c040c01546000b40d0509000201c101d2400b01c003001122018003840e07069000a0f00d5483c076601448890300c00182a41e803a01050707100070403101c2041c504a8001c1d04080a05518203207080015401418241b1551 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 503940728 1250 503939478 503939497
    0x1814090304120309080607080712060612020a0507060203040503030415050405120a0c0c0b1803030306030c01050702030703080f1207020c0901090510091109090c070b0112080f130305060c 82
    0x2146070a041602c0030001000c0200c0850801494070000140c4400074400340b0b0007110790f0b5035a16030368100310000420007107503a00d10941082c54140c0811020360459110302141c02c0380440540c95100300041600d072802001c0300a0151400003080000304200800198801e0b849810652541d1082d0110b0714100c4200300d078014080e40c0003180220090240001400808245180c80c07000b461059071101904107143c4d000100d80c090228180503010315181500c02c6114003907009605619000000a41d110b2002c10903905004000078084290348050000901864201d50203d5071010b0702609440250300c00e9504170f9407035460002181d07800d132001c601b010b54001e000308000183e034240500c440c0100f070064503091040c81603180000e80c043c514083c2040101d100000d50740c68904190520400b400010200000400d080241c1d80002d000c4030161380c15145182405412210350b0310f410b800500c6180300030b40032000b0106031310030052108a2503070140c920850070b9910f952105030a01005000d8040c82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 503941978 1250 503940728 503940733
    0x1704050604240c0f023c0c1c11102f07080303162309010903060204031113050601020c04330906060827120301181409 52
    0x11801081150b545000000c80144105032520015094070003211411101d54001c26070010904c0e0040342c0600084000e8015880c07541c80130901200340c1c4c03000140c020001d00820000e0360440d4201c3c1020030032410011805001c400349100e01e103601811030001081e045920980880c0c0d040c10314241203101c507070311031000e4590350b14480310300c00008002100000c0d0002c0409001c000590174040410000c0024a0000003456490500d11410302502c40041c150344140180c01c1030074070101440c6034100303116601d00b50407247c0b240040e5004030f0b8100b1069002804003070003c1008014019900510103c800c81102c110541000c03068140e4152071040b0b4a04d0302681100e844600c00d81400d4003d8030a6064052080f0514901240700d0f02403842c5428098850b20765240c002e00540109101c0d9201070304003802c094021349404500303000070b2040300500c101790311041850421401c8080100000100b540400c1d03541f2582c4800340700c4a098074000200c5592410088400c40d03c40004040e5402116008003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 503943228 1250 503941978 503941981
    0x9030c010c03181511040f050102160608010b07031106070f0e102c031b01021009020a1701021b1b06030f0a0902130212010603060503061006030e0703050a060b0117040506 75
    0x21080c6024143e4003006042c6500c403100c051001560342c0040c406402510701c4110208d080200080c0f900340c03a240d200c40c60360340d140000d002c1c3e542c100326218110381c401c0a95564680003454100c52281d440c180062040c070900782884102600802801ca1035840c03a5140c1a28200c1c002c204405070220520940101e54003542900302c0300d05a540d140d00002d1a03003003654141d00d50001080c03a04076180c0468007a42d030000c504030303500d6078180000c4014001c440c90034030041300c0c0d80d00081d41402851041c072444845950075444800000e4050310700c0700340c1c1d03560220b04c415020390381d07151110200007003029505074442c4200650320b8484141c9000312030401e01c5240c2a03540200f45d00c010145003406a1b0710010b030390101c00c0c401c00c10f0b0008103002d0b01000d5400086500d07203038025041d18100d401c29417103600050200074114018661880031a289403074007040c0480c0c03d4412604104c00f40d0806071007030280b85011003e0192a8104040f20034080c0e903030341c6864118071502e544500c41954010070744e821950 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 503944478 1250 503943228 503943233
    0xc080c121501031d060601110d020c301606091a0f09100e0307050906030a110f0a08210702030307030e0a0906090e06061c031803060509030c010c0318 66
    0x255003800072501030600007581c10a011202c04c40c12000070308860258000c0d401c008035540e001020800c40d4079034030000c2c1503d042c2c80001a48803c0da8280c1140516060204050003883c80002050742559081301528081c021000a03134940001400b0408086548000000c07068441c02d0ac00c011550004106208a00b0400c2c212005910180108460b844144030b00c0846540e00b04c21440c0d080c4032500c0710155803007202e0070300d410a44254010b80c8509401c4007000180c2e00d021644403c002d9000b020351740d652100d00d0025030451030800d881900035400c0c80700411000400140074002d0100c0040b00e500007642031409010340d2050500094058005205d81000203009040340100000700620040f420b80d290480c2004499080d88420485500c1e40100600c00c001444617640002c000e640840d40720800e6040f040000c510881c008080241401e000c082e030f29400621840a154001802d0082e81001030320195250844c21080d17807194038081d074044055000c3c0c030030708611043d01c803c60b2812004a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 503945728 1250 503944478 503944501
    0x1113090308160f14041502030406020c030a0b04031b061d060a050411060309100f09110103200d020c0d080403110c010c0b0c09040e01020409150b0706050403020a08030a0c080c12 78
    0x10002d07840c111010300c004106e141030041411202000782c1e005607101e9280a400924211540d005a8007039001100b00c0f0700400c3e86640200d44c46500360078040786001d460341206121040000002e4403103850310058440c01180203d0041f1786000c15021a4510748890681408407070098400170700c000818a070388084ca00700306028662059641054071000b20800382440c0a07283c001400500392a5200074050800000003840105040c081c601040f40d4100710b02c114505100d6400b9042140c0c0000c10000c3d00e2142da074045608809403a019034111801040700030b4080d007800c0d9800c901040040e4a00388003140f00207842165600145e68607011140d2986499243c094054640c041d5250208091015915203001c1c1c405034005603c00142d5552a101488080700c7c040070048101c254070080070009041c1c184180d1301415000b003000075594640745420f80c60002c100d000208050804803c20061f44402d501c880c0c5842500c0d00c3ea0034959451520040e21803183d42840c0d40301c4000c00000c9032159112 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 503946978 1250 503945728 503945747
    0x90b031f09020310090b0f010603021309020c0f1605030c010516060906090203030703021615020a021005120f0417191107050604080f0c0607020306010e041113090308160f 75
    0x64240c4a4055044d83c0c4e0310213941d002002a1000c920400a10058110700701039a401031010b440e0031810407280740741c10690803c02e0311071359494640100e4400c07041c040c144400100ea141c0c0030202c2d405440320001d0400c0d00340380c6204a510a0103a480c102026500540031200c846914a00000a800d46917035000010f011550080d40d03070b603a40d42030540040e24100010300d0316a000c7c0d001000f0500d00d555403180e54040c0358005036201046118210702d00c0360001140d00c0b032591304696600120450080451346401054900c1d0343c42e0352003505001c5035035804e4002d280118001c000f180d00c011200e42d003c020a1045443e44900300e04c029010505441c0b0a5421448400c501c40554000b545c1d200009a2560001c1d08100ca250b00820382c0600c2c0c86808001c00c080000040c0e0b401800c002e0160002502da41c8144108172101e49081d001404200c0d100c5928a540803000380300d0769207410200c03110401081e090008034081450000070414640c141d081120121140356680d10710907060785002c0300c80102 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 503948228 1250 503946978 503946983
    0x3060c0c07091a040c0207080703030c110a06050d061d0c070f080d0204090e0d02070b0c030f07081c09050309060f09090906040201200303070309020303070c0f090b031f09 75
    0x5401c8001c141a12103014062000a41000c141c1c152200c500401084422006001c029540581c804010043c00401c0700d50840e60581030602c00c0c2d0000d8100012036010000c4010b600503001c06010440c0781c0c100780a0310210942440800005444400c2c83c510b0110f0304040d5452002d40d000003a07503450700907000301708161140d90140f0b54580b0a950700c1c00203801c801c0300302c00409d03000f043c1444508035034410721100001c03c400511201808041c003039120409806000c0c184003000072403107604c100400840c0c1c03094500800c2c0a035104c5032410489020340043e990880e081500403803408030340c0401c0c010301003100d800c4000355140111450030000f4680c043e0f0351080c3c00030b206000c02d045958074050014898022440a03003001d14040c8001010298620308254100310721407100090b01e80000140c9901c40342908000a41d00410b000013495806117050040c44941440c80108561740c00c01c2a0504a591422042c0f20410140e402c05032100907912541d41c201c13030000d000ba441c0502030781200700c2c00350 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 503949478 1250 503948228 503948233
    0x2601080c100c060c05030117011107060b12030a020d30020307091208030f06010c0c060e0a05101d220c09080a11030607081e0613021605010f090203060c0c 68
    0xe825030f4800302500c0c001c40324207001c21004001004581c90542800502a841800810001e452055602034500400501801c1503644900d03c00482d198001c000d8144000d0700b080307948840d07210000950307400204540f580092424004100000100c0300180d06500c1074100800300c0a03c1e503d8660001d401c000e20440412603c000e000a001054640c0300c0c003074a009200c603d9891810b240c450100c002c4c0900039a0400c40e6224003807011400c40c80d000e505031001403506040e81c1c004c220010f210200f0301c0d0842c9a00c0400c41040100c1d85800407109071141e142d209100d24400740c660308110012240c0b20f0b184007820381507a0328a03006241940286025021428001034040e180c00d4154030702500a5400c9903160303e90204521a840c0c10440316a0001c0705180c0801149400710202d0740181c03090030380b00e043e0540d660114000d9655020500380560243c8030031519040318196203011554112003d0312594a801e00d103400100243c001c91042540280060406444581c6442e903d40d105c05140d820a0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 503950728 1250 503949478 503949497
    0xe040c021f090b07050310170102270103062103140c03071217100603050403020a1b060e1207050d050a050102040b071b081b06120103032601080c10 65
    0x101c5100380030460101001100207040b4140d45000070820380c003c1c101000340702d028802c014034982c4000e2001c1c1035070030000b81042200c10b040245030280c0105d142152680241c84c4400390b441900c4035030040d01250903a000d111456944186d11000690200781c007404000e50760703403800420b01642e200c08003102c404c2c8103140f6015200702c0850031500074035801c0b2007844211000014280d806034003410109018510700016041c070b04ea80d6a034000c028402c003804d0588036400201403600900c42240e1058011701640c2c06560742800c4490550303460300070b41c004140c103005402418100844c44500d45040000117000082c106010080c100d51101700c02c41c0c00780f03d24001480040c00a00282000709004441e0310f1f1540348524059641108003039031b00c04841c600840070002000005050090342e0341300007044200c4001c04021465600c41c510ba03100e05108010300010425a10800c4c403030700716101600c00345c0900440d90fa555203141082c0f2400d000ca07408418024403d180070034004003040300c80e00700103402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 503951978 1250 503950728 503950753
    0x9050d0c0c03020a0b07300e060d060821070209012d030b220c03320a06110304030915050c1504060e070521030405090c031e04030e040c02 61
    0x10300d207036038115030700c08100030425404106a40b001102403040982c2039407c1003c1c03a038002c0341d07883c280d60300700700030880c140c4002411605c410b400c603102e05d10000c2091204030b0b03e61a099540714014840b00c14095270950103a0007140b03000064400465000300800c2c0755900e0801034462500310041910030b901c0070007544900e01482d650309035005502c141104a028541b90b00540308203040c1d140308501c409411070368a000100c80d507000e8400d5030351190b0350285006884010030307044050311000c83c14509031080004e5083c1000142482960f100720400d0120300c0d00c0000e030403010300040d500180071401d000424807403022540c40d94a0000c0c03440c601681880300a0000a183c0310040000c0e0317550030702d03900503c41481050700071a4003004007540148074042c07a000115411480c500708242d500c01d03505994000060f03040c01140d00415004150840600341485002503540c400d07111410008629902c0240701d11550107464441c60300b6485004841a40704240005049400245401c500800008449 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 503953228 1250 503951978 503951989
    0x1a0106020703081b2a0102190b0412020316031211130b031906090b030c0108091213241206050105120603011d030d0608070e01180e01020a1d0409050d0c0c0302 70
    0x2010412000a0700041c5c45801c0064188200c54045120465494030610301013429001c80301c1d002540641140701440d81400105d055014101c039174504413072031000381410301d03902c0b0f004002295403c050410107038070300c41e4005160340704e100380080c201003020800304400c0c0a1070380a103501c614009a04840b00750030f025028100c0f101900b0041d042c80d0780d02289099401c041064290320002820280d1860500006032580c68403d01d00241200100003040e81004405903403810084c5844c2200368a519081000e40d42d4100700070559500182021000085505042c02820112003041c0c40355482c0c4000f81c00040b4819400902140e095074880422041e03072100d400144c6429540b1401442d10303034080081030307020343d1a107a04c00901680440b8050005840103001d51f811241880100c02c00308210a0038140074200b1010040c0d1503510115014000f0340d0085e14a110380800714151203d0310b0759160030001202c6150070060401e51143c0e14680394940903141002e00f42e07010f6040846034036501e0340002c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 503954478 1250 503953228 503953273
    0x2030d110109061e0b2b03050c01060608180a0c0626190c03050603060c0304050703050613020109090509151e041203061505070201120b0405041a0106020703081b 71
    0x1003440350250242c00d01010340e4842c0c0f41000c1811a05100c0c81c44503071400030350301e24109180b01101241b040d808410540644121800540454001d0010a6803140058501301c0c0c21561010944910450740240d018041652426540d010000422040c10070350229450343d1401c100c842520900c00003240d54074001f05500d841000301860410842c1d05c84001d540071b030b581c41810603081c9810481030050a54021490561104941c2c4559489580d6418128541200c0342d0029005000f1b01c030078802803640390080d014541e0f000382c07558000c8540c0d4801043c01c6610480780940c443d0008c0c010050040c26071031001da000781d43d0400304148074044000d2022001c4054904546428180541c0c20005825018510092241d0074103500362008003400901144282301000b410170884108482c1700e03a55503030042620042c003034000c10440c9024030300980c12a10308007004080700c0741c001c00094840e10004030501030300d510001e1281080d41c64400180008040c2c0d4081d001d0f0b000d10b19805028414842901 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 503955728 1250 503954478 503954501
    0x3051b100e0c0406030b0a020c0115060207081e0c010c031404090b09100302090f0613050114040e0f032b111305030304060f0c06060302030322050303040302030d11010906 75
    0x72080e105100142c5084040c9008901071410a00200045072642d40b4150b0f0203030b200100585c1d140c3c041c80890340104014404203445810464011408503130000da0f07d0199440d410440b849818425050340403007811007089803056100b285038880c2d5501c155581d000851281c2031903e0360100302d40c1c0e0684107401c15003004c040b0560720700d616000c5213815000309401c01c0d0080e01c0c49202c1c41c25600030521071980140f182c0b5060300b510340403c10a8a480300e030b030307029103468840402907561031322195003141701d030207199034400c50030803005030340310300c00400c140c84450030500c011480c003042c240809040d100400e81c038480c0001c400c0c0140d909200039000c0e44010b01d201404580c2e85a144165100c410381594004500a034004c1c0414042d294104040100c580b189003800d94405556240ca0000343c60a9000290036010104101c0403e01c1d100c1d440181310283d1091084520352580c080c95941d000d02d01c0041d605500c00b04100b010a0b01030405200718100503800400d02c0302640c0c5408050340c5c03c0e00c030704 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 503956834 1106 503955728 503955731
    0x314010b0f19181203020c01090e06010e03010f0213061e081b2106130905060a0903020717031801031a0f130515010306080706080403051b10 62
    0x410800e4614221004002034036003040c2071550b11104e8080700540300d003100e41d8800b58060003203002618507007040740714a90741e11001100d84c142e204041d00d8040d541e0314098000c0720b895000400c00c11150700c2050b450a071800c00c00a1451003030811280015252400100035503a1040c011030300600900d2509103024400c09a0305070318407860a0140003850b451780c8003a242910140d0a9215802c120f403e181e6100d1180c81d54020396500f86030090058100e40c000070466049075002c011800c0c024270496040e01d03268444040581204280244198400300b503085110103641100108443d0a290601451030110080d84081020700c445a100b842e20180c9042e00b625980301d07201140303c17602414012400c02000051325404002c4210303000a04180c13000c41d80010014000c07080300c0b043e0340e0303400303840d540c0e070320100c5085d040000310303c400740700344125031036030200070401066002000d440 = true := by decide +kernel

theorem cover : BRFrame.Cov 503776978 503956834 := by
  have h0 := BRFrame.cov_init 503776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 503776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 503776978 ≤ n) (h2 : n < 503956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
