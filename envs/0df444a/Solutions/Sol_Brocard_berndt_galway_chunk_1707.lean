-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1707
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:22:49.257006+00:00
-- url     : https://prove2.me/submissions/61525d37-74e9-497b-8d07-e0974cea415b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 306834532 ≤ n < 307014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 306835782 1250 306834532 306834557
    0xc05011e031a0414011d01030c0303080402041517070e0c0703120f0606080a0c09032a1502030a020d08070207030201030509100e0303010906080309090a3810 69
    0x805000344150405040e42e03202110900611107600d041801c038010300811805480207450104080c0030f0141075400000050242c1c00940d4020089040c0e80d000b043d10403a9038a0350390708640b900b8008000700c3c1c0040e00c030000600f003200ba01071201d0107031202884035800940d0f24000c06140c0001584108503d10040040c00440d1005404a820207030b014541000882c2c10040c054003c2c0c0030700c40b0b5603481c043c07400c1c1d000522242d00550050017003603c01820711140707010079000c90f10700700c06010140260f00c074803440a94240300b0162000c28080b11030100f0a665603181032802041c0d4801e0584005070308005422425944e040c4602c540000c0a41051900ca040c5001c00039a01d1f40f40b404024180769035403000c103503100c000301b01c018408801100103004003d502c00d040354694200303210342c8500340c1c2003d4020440725008030540e440020042e2071098695214940100984000e02d440c488a0030885070344150391000404102150b540c0d0040c2c00001f01144051140d0030144070b5411040210350744084 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 306837032 1250 306835782 306835817
    0x260c060c0706020904090819091a130315050406060e04030e1c02060c0a050c011b02210a0311070b0f09040504020f030f010222050102031e04120b06090f0c071e0204020a03090c0501 79
    0x14ac020702e800d01d0035540b500d00640d104022185541c1000d070420b0f000c02c0e103010042c12560080b0b8032076440b50805102c8680e035048541455482628004c011514003502e40381207080868070180661440e40c0003080131800760300130030103d510041032090380b0340140d00d500e000d0160400443c05500c90a28005090610300301c41c00c40c09101d83c81c0002d10820000001d18010b040c0c001106202607982020703900140c10915014002ca41001c1140b11540680303400000d0400080d0151a45203003290f5a0741e140c0110f060400c402080020000c0b644940344416542c40e03514200104030031a071900e0300060b5200c4508148051541880c4680c040c1c038a0020001c0c01141d88c08019a240f019043c12068503481500b420340249018603044540440700807100142800243d003071765030003424140c0340600c1c1034560341c0c0e441503410b42c1211185880707942048000002603c201d07494518003040000343d1740700d5980c0d50005040e680440340c074400207a110121031082c8101e5442660080c80c090922040d00d04030451003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 306838282 1250 306837032 306837059
    0x4050c0a050d111e0909070216090b0a09020a0503010311041b0503181204091406030a0f0501060506030f06010e011d040b060f0403260c060c070602090409081909 71
    0x580a0b0a89920142d00152014010b0303c1000312080c2580000c030450f0780b4803150a400024110303101d0407100c40031500950010a200e4502000c03080341c000640d0403c10f010740a0400081c07a0742c1c21510b080f200040e0381800344060403801405940b0740b81d50354903504002c9103000a05488511551034904d6500341945503c00e0302d41b1041841c00c2094aa9075113140c020301109902000319414003400500b0141c02000c000203005540203510200040b94502414079074030901180c00c2c64140d0322641034003000c94001122030050390312550012441c1511a404542560000c0e00c101c462000f25a05100c0c90790703000000a030901e00c0070700e00a40b0b5590b41d42641c0c07452a020031140c82c051a5221301621580c0c4034441103610316821061495079540c1e491520000001d10501c1c4888048540c0103040140400082121001c2003020020304454031151500010b60340101c2d012104107031700300410011901e030707801076040090140c241c030350712649060300118500314410316403001c00035452000e00118500c1e501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 306839532 1250 306838282 306838297
    0x617030a020a02090901022b0e0604080d0e0f0a03020106030b0601020c0f120c0402030f01090605030601180c0504031a0604060f0f09020703020a0f052107080a08040c090e060604050c0a05 82
    0xd41d0136903921560300b910300a00c54204050f1408001d129008403080d0800c0c0182c1d1000929002085403d045900542d12800c043e0f03801403800d4410014103841c0082034010340c000300c0b00e0300195403980c800000100e2510b020010300314003603515240100207000c03500440c0d40c2d0109081c0040d11400a8000020b61000e0000c0300d2588140c24029020400480402c13a1003118070b0701600c21566800d00f503c1500e11380b8000d101c0c04c0b01060070090003040c01d05000c01e03868125404004111448242c042000025000122080d01041070600000021600c07111108a024210b01d07090245401d0042c02d11081d80d40a8208101c1c10729004000c11090302005a0381c4101c604e499401070b125003051404a040540841001d44000c440b140340605104011070b000b103000009810300c003400785400c522400c1502501402034401d4006200300100c0710700a03102540e100c0d00c6040304456590b00c07507820000300c4903c0c0d2540c0ca100d074448010031480f400c10f4480d254104102c4030b0b0443c10041c4000000386071b40704658 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 306840782 1250 306839532 306839539
    0x150406141510050d09030c052b050315062d0301081902031509030d0b09060d02010c0c0305060a0606030b04020403020604061b0b161709300a030617030a020a02 70
    0x2c442018801c0080c1c4030b032020020010b12911400d401c00400c8400004070940d890b001d4203030303030450f00703066003a000c0340e505c0c00c2074480090b14000c0d00c030580c0e031500003d118180036842d00f644144c5907a12180184100300c54512100c000d0306008081c5001000142c0e0346128440c410001071102d002d0008007190345048100c50400003601a1000c00e081c0340c50f0300d8104000d40d101070144500410003102620b2a000c540000308034009961080044100c801d4501c2d0307400c10b0203180d243c0095403054074200040f6024200c2c40c0f0300c0d1640d990310383d46846400c403613103001e4036074903501400410351601030188040c1040700c09508050950300011810b109074480c01c82030100c0c2d4a00a0044408121220700c51900b0884200b114a8401b84610b140303160b0078800350005000c0c21490000c8000d1100c580d009485243c020980101750a00051a80300700c4099010380070001307114007941c1d1400400800080c0135030359021070b10610305441034049441303640950f00650414072403010700c1940080d8054048d47c049 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 306842032 1250 306840782 306840799
    0x2010806190b0d021b0724050c0604030207080c091915170102210438010f1703030705030f0601030e1c08010b0408060a1d1504061415 59
    0x12020800014465010307611190010401d4090b95000c0e13405071490300006401d6104146010302010b440e031b905d50080e4130b0078809101206c081e81d5548500d060316a01c040c00d21a103403000034a01c20b85490b00407602140182d00c070b1202405485418040e10910074005d07140b1038414113000045032800408504004000d80e914521940c007c640440d51030020103640c1d982108081c4483c480314080c2d030280241200744130008009031505407000c90280d00c155001220b072140030358052603400c42d02c102c003850303241c0d500041202c10b540803800c026468000c00c141442c0400c198600001540c44c15030010100541da0414400c00a1041c0c0007803c4030343c0080000d8913500c05960307070310040c0d00400c031a49015489101d410f030701d1409034040c3c5040741407500140d1640700c600da9035069581610301c1a03001e5180590800000f20705c41a590b604596401403160404901d0703545500c13401c0b450036080042b4016105000402c0c8020f005580c46500e0312100c12904007151858440085003000d002580020b01a02d00b8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 306843282 1250 306842032 306842059
    0xc0f06020c030a1b0302120601030302010c0c05100e010f02130905090303190b0a09020301090507031b020706080414060c030703150f060e0d05011118060a0e0603090309030d080915010302010806 85
    0x1000600005981c6c006c081d00645040b08005c41e68032142400210003540c40c0c000c0c444c0304503004506100c94164840018110300c114480148080e000c800d03082807456407a80440d0201907000d0010f071403290032100851002601d0315600d50107a82018214101c550800c2050003041c00080003008061000c105020809139480d001082c604121a8407140481d4400700000c20359152036000716005d031a01d56001d00110440700b030400001c01e5503040340d1015a0010342d08100480c095003501d50301600031800d055940c4d50f21840340e400d01c0710840315100300850000070010440d40610406255110440070400d42500340301c100f490301402da0040c88184420204d40103004d64a03020442c040310f034040002d00c16084a02c03e01030070380d00000c5083c00c91440d03c080c1c59150781072410964000398106d50380c0d143d04240d64001e201003580003401005060104001c20030080e2130412900ba401e84940e80d452040e85840c0c00c101d41005d640d050a60010310b800001040580c0c0e01c0b020030340e04100c0485050915882 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 306844532 1250 306843282 306843323
    0x50930030c1c0903030605120706050d1d070b07170c030306060f0c0f070f05030f061506040f06080403120504030e0405060f0409050a12181503180c0f06020c030a 71
    0x55100c1c02d001c550b050800072020558950014070071684165003841360402e8859a0783d0701c45e10580a103100042040c018603400004541201c82c101c01050300d030440100c40051030350300304040c513000102404070000c1c0c039000701f00300242c08000440c0c5500f0110304002c40981b6a5031a81306c01350455100702e0011400006c80c42c174410450349212018412100200b880d103700715295211480f80c882003000040c0000b03a03604010807118070100040d07000e41110307a14001000e20540405078100d802c80424000820010307240c448000140820b41c0b00c20945280c50718000708401c4044802c04845070501c020f21000913040b0703900394cc59290898010500790b51b00c0d00420b40089803620308035070045c240b002040c14400042506103c1b08d004181040350450182c800f600c0040310312825064030001204100704148007040426140c000c039140100f100030400350124a601d508100076181c0080c01d01c020000340d0b8000640c4c6000701440e002070b050007103620000036168143c6007406800c00924509119030000d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 306845782 1250 306844532 306844567
    0x605070218180105060d0506010911090d080903010b1206043306080d031401030803060612090c0a140a060302030a02040510080703060f05062a01050930030c 69
    0x81d81c6200340554507104400d1204498040400816075180c031010480340e081c14119903440b42c3e0000d000301402e0340b03011001e000034514820b10b41282c200c203000e003c046580c0c071091880d2050140880c1d545491043c030815003103401ca65081841040b0060f01f2114540300820800d52043d004001c21440c0c09090102c1e0344a403001e01c0b841e01c154100c0341582407400c04180c4c401c000740c0e030f0700d1821601c40e0000c2010607011079904180041c031900c0c020004000248404000316404203001d4003c40c01c0c222011a540501c08042e1003008664201507030550141c100070202c80d0090001d0581c0c2016180d4460200303410340030500800d804c05030000000390812485804442c01420f028003c0e140c20540e122004154031015141307940003038100300000800d5010b0919910581d1302c010121460140b268030074454101d02d0b103103104403110101700803501d203103002e11585100b60030510146c4060101c40c80140f807110845905541042d0011040043c070180d550142c9070f2115102c46d56a07a110011010048002d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 306847032 1250 306845782 306845809
    0x3060e01092411030105030304030b09031204060501080c09070e011b081801080f090316061b050c010c0908192f0f1008040213060b0d021201050904080406050702 71
    0x902c90718040162240c0c62455100381c00000b01070030044058007400d560b550b44002c0c455154142e006020500c003140c48214001d810a903298204d80c5000483d215201d0844412601038034102d07507540040200080600020060300c4044030140445e180c00140075010720300140c1c00c141042484000c00d45030001070100f60b85110740040c00d65858903c1c103215000400310082000d40043c4440001c00d01040440444030b0180284001075810308481110180840b07030082810f441c0c0e16140d4142041c59031103d551700340c10310b08641d269965035590401d85130a5138039000001d000c01282e03403c1000200000314805001784d01808101c14403030360798245a15001020400030403a000b0303051400c1650704e071203052402d085a00351a140c408007184c070100a1000016203480300030454050000d4014540900e85001e1501c5002001499944070b223010001170f00011103600080b42d0000340400c4801c1c1380307940c1c18010901241d4141842c509552500064000e80c400c00c0e00340400840e00c001190350301e4201d074110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 306848282 1250 306847032 306847043
    0x90b010608070e090f15010c0f0b04080910020105010614070521070b0702030301060906030b010c14010f020c031209161701060527090105130b0603030c1501030b090307020a03060e0109 81
    0xe07083c41da084401160f41642d1b5264550034818804916501558240300207a030083ca4106001d0001c7d203070040180001041102c401108005a00782651840203d001503290780e40000380d158145040a030484d4044004464585003d024850005034000345510500d84c910802c082d040090484540c4903014406005040d030181c44100220558000095812243d40e0f5468200c0b169480d00150219042980c8627400600401c010700b0104007204519031541c804a0000184024080804030480c0c0202c40c89080580000411264a001051400d44c20417081000b41890300100001200c0003031987c0701e2084005051170301104810f50a501010003400003030005c4c8a4045041d0190440e0407160103c42202c45001c008216110310521845200e20058201c0e41c3c54000182c40d00c0755110360040c1a16494401006404800a405c2c8aa801d00b651340380018280c55045260840388a00001c00000c4a03a000340700c22070159442c1c10010040325084040001c000d0450b641030780c05031032a900040c11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 306849532 1250 306848282 306848299
    0x520809100c0c050103020f0d0b0a0f0f091d070501080405190804150f0807030e0a05010c05070203060901050f04030e040e062404020405241309020d050703090b010608070e 75
    0x1032035004000036248030312629494001944800041d000c0f40200425030300090028005204010000c0d441413480045c002c1a49608580e610070800d1040d00300e8100e440c0d10b4800d250104112416801444007251a240c41602c1c2e8140c4901815503480b00f80c8201410486d03040c0c003141c18020240600380c4403080540e0540c0301c66455040410090780607214402d00d1540c89100455010720402a1507403296982c2c2e280b036456140e054040b0040c08141c0c0b508060b034010181c0103000900f0034412151094150b4803107648030b40c040e004240c213101000b03001c20b40590400f02040380910050090980c0700390716081614451070800c01190040c0000308050b4000d01c144010b008600c000040300e4503201004c0d400110000085900748002d03400b461280507000012921850450a204449225a40c41c0b034000c2d14200171030b1206140101d4010340c840b000441d40054510850804d40c02542c1d80720106050038004402076960380705c00590148034400802080101040080f4842d03001e041030703038030018160704 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 306850782 1250 306849532 306849559
    0x90b0307030b241b030c0d080a240906060807090e040804210b0a0c0905040c03020f07030e030606010f0e0d0c090f0506092203031808520809 62
    0x705154420040e403c4902528004031410303013800804c84521072000d90141801c0308a010040d29401c4024101030003058481c0e170100400c198060640c01c008040100c0554694a031440d007104507400c80d0008030400c9000c5003000344d01600f11615200300c4070908901c4400d90b446040091442c0219084210846001ca10b0481038a0003050186051401080c0e004483c2e211405820119001d007820080810180e0104005510b010341c418020f900450a0161a020440ea60182c440d401008201c01051011801d059141000c1058aa00000c01e0030018600078161501038400d0003000c074014400c4d0300c0700c000801000164410100100503180c01440964003200c6101e000c0c02d41100c038940a400c6800004102c200156400d61560500d98004461216035072070840c00340020402046c00500300198410001e0310000040c082c04c41994024052400c000010386943c014071a10311510f6440500440494224810310224028800c040c800d032414192030000e03c1c5000c3c40400f154003c10010601 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 306852032 1250 306850782 306850849
    0xc03070311030106032306030a08070615081006081207080a0903060218040f0606080610020a0503040e010306050a09210e090a0501051003090804060c0f0c06120c090b0307030b 77
    0x1b140c000c02c06c04140040c007211402c00c40070003048a0300b55041c0c0c02140240042192a070040c80094050700340030880041418081b5500900c07035101645552000ca40e14040ea80c4078880e02024000f044050014101840316007041c5004800d0045d10308040055601291401003503001e0065a00110541d25922030f1003d4031600d15041885600881c106407002400d1420380c03182c24150b441c02d44a9034116103a00050002010154202e90107500c121039018001c41c0b41000607000402d2001840c140c55811450501c0c10344d80d01a008003965400c10f01514001495121200e041c0b070704c0f0718001800d12a5050080342c0d0102070481c1650028580c0041c041090036540000381629800e8450803008802d00800710201c410752032000c0c0c48980d045c082071141074840c000104000e4011460611041c10f40d4594590118a5178040d001044000341c02000130b08c59805005001901c5051a10049182000074001031000505510400d40d540e500c3c880c00303542d00502d00300020000d00c20b00e2210700103034441 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 306853282 1250 306852032 306852041
    0xc03080c1308160e0c07140708070b090f0d050d180f030f050115060909050a0b0907020c0f010504030302060a0509011503240e100b06090d0609110103050f0c0307031103010603 77
    0x91004480c02842c0c041060320074008118064085111280c4c86c021242d2030b07101d40458082000607090049a6002408d92001c020f0040500048141140e45084000c10846581603070491580580c0116000b500811000300320700c81c01e8042405e00d00c0d50820802d11091f04841c054002400c440024030010007032001c148100340c0014450030003017103d02c44054a5505040086c03043c01c0026a040c401400030360004d03040f09412030a400404070b41c0203080c100080541c0000c0b2070603401640005031400c41e0b403400000303002400300f007030805614280c20364900a403141d8004080d10029520b90000c1101c50b0425482004114044902c00c1403141d12803406004c0c3d44c100942030b2011004030501c41e105c00d00300b03100e40c080c194000e100509011a403200030b94082d100b0040c2003940a5000d1000300d01642302d0288640039680b04140025024096242a00c06004004c610340e040503c0d00c8200442e503290030804a404c10b214284075130b1079907541c00e0300318041c04018940e000384083c04000041c2140c1c25400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 306854532 1250 306853282 306853303
    0x2010e101707030e0a03030c020a0b040f05070e0c0f0c070b040807170313030b04030201110315011707090e090f1005062d04020f0904090f02011704030c03080c1308 72
    0x801100c42d15290800c9007a070344244000005a004000a407001078003e078004141e07184180107032904c407856a203441407202c2c4100c505031a4183da0300c050204028051240c240035142d4461400b00d2418030340083d00060040e6480380c80c140c2000a4030300d1030f00004000320307402010422492075440b0388400d03100740c9401c554446c40101c14182010310403000408010f41e640428250184c07c0c1192940d02c40001460010b4020b4040d07541c2c58101e81d501c49006802036128840c4210910103000c0c4000005184080c02c44091034103610308005d006000ba031041e0b0400443d0080c08840300183c454030100382c181000d03050788845a1181c00c440701c400e000070307030802c5218104c11208220f0042142c65107042182203c40d1b014802d40c010048401d042c0f0b031580c00303130602061405001d17060001000114003201c00c032220984241c40c0d10180b0204560707105000d814084031550145141e130600b5a405465104401001810b002d5030100056420744058203035500b10120108440c0180e0760340b900603407505100c21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 306855782 1250 306854532 306854567
    0x120a0203070603020921031e1204030203040510020115030b06130c120c020604051c12021b0d05190c080d2f0703120203130203120301050f0a05060304030c02010e10 72
    0x182050343c410740c100d5490130031800400590700d0000701000f640b880d502c6145031072300d100d6820f01c449500071200401d40e51281e44650021a5143d08081c104074103140750f4113101085a041201c0c45400d07008080d50f013400c4942c09600503d081d1180c1000407031a60b80e48003200e280e14548554004c903a03502c9000818500c00c1820208108080c010303089031246800c41d005002540301c1b51038850b0104091a800d01009002e103001c2c070601d00741d188030304160780c0405424a00e4030340300401c240311180c007484408010b00e46400c02d5460000544c035a1882c003a071849414060100d1030a1a4082c80b000a048480d184100e1004002c80c80401045d00140384101140002c4a50180031510300c082140c000c0399030040c1c1585030075007a40c1d420803900e8081d42c0020104c414007188281e0510040e00e0810019040d0760103550b0b400d07240c0d0705041c2403001959000d0b4202d4426080f2040810441d01d9220840b504550540340c40110310b00d090005945000c102c1e100150059411000101d411fa40500016070424112 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 306857032 1250 306855782 306855799
    0x1a070605071d0d02030f0a0303050a1a0a060507051608011a060f04030204051f060906030b10050306040b041d030d0b0f090f09120d06060e01020703050705120a02030706030209 77
    0x54001c0b034945101444a0b01440e41c202c03810b15080c81c0400c405419030740300400711030050f825001c029040140700300c0b046001c03940302c01c1800750385140c5000d5028115030202da1580e21050340000a0440c0b5242c0c8190014060006401024404144240d01d0f180c1001c0034510449941d03100c2c0c40d4000d1000b401200400c8840c070300003000d01e280c802e04490f03000c41c246101700e0a0074103503002c0000500001c0c20401d42c44240c80034810400901103039502c0117020360380743e0007210303440c203840a4280d403403591039188a030b01c000519a40450f00036043d030703400002c10740740040d0426000f000709004100c003443d0441c00d40b40700c201c1c0c04c103004070000051043c0221303c2018000c4011100c1072010104030741c644940d00105601c001003984076417140d615480100710701201d03c031000811248031aa8040005c03410341a403598014050320b03400c520b001d00841801e200800c8800e1031526071903101ca60368081c01e071181c860915a60381100080201059845c1c0080561381050703a101030144c02544100f01c00b070b0094090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 306858282 1250 306857032 306857041
    0x20111010504020f1009090e030c060f0403020a061107150e0c010302090303041a071401061a0a09140a1d070e090f0c030402130510091a060f070c1a070605 68
    0x602596000c2c80d40580794481361000da104008040004820007010000c4502001504000a0207511003031488c80c4007841e07823070003002c80c0c25041100052070507003410714001c24000040d90004841580c035400000004040010b0043d1080c580700b00400604541c42845844203480916440500c84100c1c220031951f10b208880e0054003640659840c0c640c2c55002400f0421a14600c80c041e5100129030000c020b1801c0c41c00d540d1700700c10100940c0c0c402c00d141e640f00002e001c4c84004061010003440102c100720700302500c4c844014249811802505404034003026100e0854540c1c5403c10003400044c10044101c0c0d40c641c1c0c45c1b08051204440e444c0000300c10303081d04003070f505240703c186000f0a01c02e03055010541d01c02800030955400607000703d80000d0041b244001020321031080078000c141031602c401c034131407811005605488012009800640a0f8003881900380d179a0412039844003950007409072210445d0910f140d240000f0b80c0010f0111410100c0801c002200c40c004015541c41400c003002251607 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 306859532 1250 306858282 306858317
    0xe0420070b0106080702010c0507020f310605011b020f030708030c060a050718150e04020a0507050f071409100b03010e011806051c061b05070203060121120201061a04030201 76
    0x42c88052303070114004100702005800c1040506040c9107018200000401d1080506500d152021015181541004021301c0d440c0c6503502900004210901c0c00d8030120a40c441c03600b10211003150001c0c400d1540440d43d99098406000c00c20081500005030b07500c8a1944203400c0c0c50316021180d44124901d4540041c0407680110781201d032550540701000941400c00c400ca120b52441d043c5440240801500d10642503034490009240e41c46056803131948408451614070310300070813807111071484d800240701405a614906290107180c03200303c4465410b42c0b00c1001c594490f90003600010b40041c400400812060ad204c0c0d40c59049030307030812600600c890030702201d034121840c0f070146503448030028816880c81012400c81d800228095040020700c1400900808038400c0c902c0c0090022071004100c1c271003945000c0c411540100001000d41d6170b0301c03600381104a907044038004000d0412000641c1c15000034030135400403000d04104440100045050204c0118a0300300344402c80c00540d4040e201c82010740d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 306860782 1250 306859532 306859541
    0x50d0f080c04031208091006120302062811090301020301060c03080f012301050c010603050106170102040b0a0f0c1b15020c09010504020d0b1327030e0420070b010608070201 76
    0x780c115603802c2c0c210070302101c00c40d20028080d01c200600d21403407c01c0d042140842c411440200050040b81030256020302e001b0341000c2c1c0c000c180954021480c954114585040c101d1031034032a075404400214000ca03651424200d0140881080c1c156101000101da40c2c1d0300a03441201c071038000c1e281c00e017280e591a5240800c1803024014030f1100c04003103107408203074441b0000001d40580141005801e10881c080c0180c2101e215038015540f0b0b80d114007040055824101e40d201c261000000250b10b005c0c180307002c1d90b07240d228045000081049441c1c54020162140322040940c070784c403100c005040782119407400030074a540e01840c4084241c4211a10fa928000281c4807a200c41c041e008540c5a03180c8401c100007904003000b05440c26444206040060303481607001c21020f0002400040e0072440c881c804030408515000140c0380400e0000c01c00040303a009900000c15078022240491090b641130010310640e401007400000145003c2181d4003081811007015050b41c0f90b980d103014041c0d1350103104a0985 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 306862032 1250 306860782 306860789
    0x4120b09120715110904050a0c0f0f2c060c2503050a140717010603050d02120d0b0d020616021201050601120e070503070f060813020a21050d0f080c04 66
    0x81440c03980a41143c80030750007040f800e60320070380030905202c1c2c81d4020400340e400445209968583e1540c4a4000c00d0708003400e0100c0011900c0c0011002061200c050000c4488201d02d191a135000c101195455810312403600c400b000140040d91102401801241e270341a000e8022071a0404018656802c5030f035104040c0120380c0c1150013403801c501c4580701d400448a04074040081800382500205003195080c4000b940c0c032400c5000000c4140c950704009081202d1b0303490400444d00700581006164400d00c0a0303801d4186800300000ba03041c20180064011106214020f400110120b500c04c0e51078a41015a41158000da0741000790800f107920781801c840c02280c03114041120351b001d00d83d126140303502228a2480b04801c890115440303100091600c111a0f11000c140303480454240700700c03603004030f0042e0864400b010b00c060345071103580010743d910003e0203a49500480b04039421b4400144c031134100e041c26044030986410710036050005003080030074202100894a000c0200d550b0050400444045 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 306863282 1250 306862032 306862043
    0x123040b150a0306231003051c05040e090a0506012d1503020a26090d0215070e0f0d060f06050901030503090d020a03331505060a0504120b091207 64
    0x142c0303040d6a6100000c12500440c07480003103000e145181002d490402070f0340580050069034003410300e5842c0c62850518800b40c40c0e1044012039203a00c440c0383d00101a201501d908858207181070fa50070000c903181c84403d00e4060b145110b213000005a24141416010501400303a1a100f0014900400d41c08002e4580c0300e00100b65413241c0020403080d210340d0280544600502d8003110080d2810900408100841d03005d440d500e01080030f100300103404008040e080491800603140303404c10340c403400170035840c018060410f00603040c2a1082075a00d54021aa00c50402401c16114900504110009000c185c0f00c51813403030b10308680410075103009000c450403240d1000c0114942546001406200045c040302240c011200140100c00192031603c030800b0a04500280b440d81c540c0c0b0040200c92001c600e441005d02807804d1803c3c6c0d0b00390200c900c2401602c1c804e48265588105036141160284102c0c1e01055a0b05e80e00c046180400c19010b8186000e81200340444280168404080c0514031807032400424 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 306864532 1250 306863282 306863299
    0x30d02100203061201050a0605010305060a031a0406020f032a040e010b1e070b090106090501210507090c03150905071b02010e1002060403030c0912080c0123040b15 72
    0x50a4000307030011075100e1400b41000800014600f0707113a0079500113503000301c0c040b43c5540c0c0038029942c1c9440f0311907015504603650140149143c460030044111101800c0d030401c4034070001002d00031640c045034401914100070b90b540e071904200729004620384541807140c650603003c11aa0a550300c4041c0c1e07007914000060444c1c00d034039049001005901c01882c44031014403040400e0403510001020713086840c0180310896042c134141980a08450658208442d00c0d46450014008c1c401410b808820700d9401c002100c0102c001402d100380750800d658481214541400d01551a20754150001818070082c81a0075000310b44866925080e07940444000c800500400d0340000f03400b50354003000c0d0815006040030501d030146140461114648441d0845c0035074094401e0001b0113034148541108200300d407a08401440c14200d0120320070800640c082e0a0791030205103001030140179400303071030403113202240500082004032002e0282c2204440a41d506010000010302c2d616030a28440c1c440c1c02c0041c80d071807 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 306865782 1250 306864532 306864553
    0x60a14060f161703070f180e010303021f060b0a0c032703020406080f030a0507060f0c08010e07082404060806040c0314030c3315030d17040609051204140f030d02 71
    0x3a19501e581f0800300034007003441c3c80068100300052680307000e980aa4041d010a000548107444001d58136044a1142850a0400c0108a0b0705105942d0011001e1034480d07400c08040c141118502c02d0283c52007c0300440c00705c2c0c94070302d044000020741241d00c25101405425030b5582255100c101e402c80d000c43d290003c101440d01f86101e003009203d2244600700011301c900c0410340c0300b807c9840d0003102801060740c0c3d40042c029410140341c05071f071099041c81c0520407840d1078031851031404403000c0d0341248180004181201682c1da41c0066001d0007a8804940a505d4035080a480c00c1105220a40700490072080740b440c8000007104440300000701c507000b0041240d050848440c59104070b0101d6603002d0340d01c021410010102e407481c41c003411000c620f071910500c1440c2050304004801031070307000f40041c100381a0342c03808580841c5039100d60815800a021411810040e003006002042e100c034011001a0116101c600180c07030084c0e41c00b003034465075001001401850355030b0450308140307c0560320410030326 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 306867032 1250 306865782 306865787
    0xa330b0705030712081b09010905150d05040f0c05190501050a0e13360602090a03170a03050106080f161101060803091008060a14060f161703070f 64
    0xe18015106104030303881c10440b500c1d10b90050380d2202c0c4590000702050b0900c10303102c400911048200902842d60b1380b408880d00c00191a1030824480c1c140106c0e110010502d440c1080b00c242c81952030080f0042c0440c2c60302c0d145c036071285001103078100ca9410321281e0204040c00c0061440d02e20048041b4060348240c04c2800644003500424403060400491520030f50041c1c41d16507490f4032000d140130011424201403800300011884c0c90880303180c0c20003072141c0240b86c51030b4080a50070303a80c2c004070300582d40d00714003021400d80c07505030f00702900c103442c4c00900310340000d04600244205046980e0070000307039032030b0041180c1c14402918800c1c110503000f4007090110310058403d6251500c40d042c50803401d07158404e07490940303099a0110039240c101041707a03041800d062440402801251421900030728080c0001425001c080c000d000c507000200100100503150002191195031040d580346072100743d444bc81500c100300085044816044146212040034243c40c240ca0023100325403901050208882000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 306868282 1250 306867032 306867037
    0x27010e330708090102090a080a030f0516030302071a01030b150109150f030b0910030c0807031a1b03010b040314060c181f09050907020a03090303030b0f03060a330b 72
    0xf101c190303560800000c034140e80c481005000424150003c1c0004100a06001d0815458000c9031000d104080208041710640d8011072480154103060041e15100c07141000046510b031501e2114a1020f440008011704c00502421480344055503401c2e1016030352500110344641280c46901018503e42800f00800340c05041c44c5040484e05290010300a03040308002130113050192241030350102c004005105214a240950380901000001448034501c0c44c2d503010f968082140003112050411320224981a00fa14103143c98005203040668495858990000302c9610070712089408070003d0100c15413000f0080380682c81050651030103400c1c1140d81c40340d000301100b03c07031703805034170803c501100056114010380000d030008c095603d514510b401e00d014004d64400141a250030355000504000000f648400ea607030550f03034140b4004c1061440340c0c0100d0100c10f0250710095050081804010458a01d60b2160800078510491010000c4481407920030340740070303900d442d2840300c042001070000c100070500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 306869532 1250 306868282 306868291
    0xc0703022206091512080904110c010c05040f120b040206030615270d05060106180503010c0c031b020d110f060a1e110627010e330708 59
    0x1201c0c0701440149064048512641002100c940d03540355450307124256048401c040c0122050307088245000361074a00c002d00034410814440c07a100d191255a20140c2001d0b10300409000c4024040c040e0b20010140182c0c2007405440040d90110a00181001e07000b0401030506400c1070048d01141c0325a000d100f11035200400c040c4c0c11581c1c40c1452505008810010a2103842a10a240c221a40f800400300b03000f415a484138070581020050001280d03000c542c550460b655810b00100703070140f44010100174640c85d400070340d16510301003408402682100c03401203c1482aa1500e07050386000703030b07400c00031004003034007075040640000c44c000014012000c0071503480f002800303409850f400b400014560f510561201000900e291306540c00c841d96031100881e42c0340f00342080490301100828995507004002c2100014041401c0122008804000e580300c07904100030082c071940706244140c9548454103480500d06480c6440c600601440100040d0f0040c1d41d500c1e205211922129022100d0483c00342 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 306870782 1250 306869532 306869569
    0x51602010e1003020702040c02030405010f05031005150a020717030403020114040e241512060a0803430305070311010219031505030d180e0108060402030f030c070302 73
    0x71141c410303545040074641c50809981e405603840c0307824070501003603903a6070100e54255070043c44103010382da81100d0443c1c2e034105075203400d40d12039881007506217403410301d5444503800005250f981000480c017000141640300c0030b034089070281d80e03484020168244d05007454102039002400240019803145803051030600b2035482042c280703615248020310010080d241c9007c2011030075410044005050103503811041c0c01c43c0d410350b004040901500c454400d90420164103449800012071075030341c0c081200050a49442100c0d241c2c1490016007640d200d4110041c3c014800180c9226040b40451a0a0b105481c42c10341d280c0c48103480d42c0e0140c03201d4010880403014072000c18490700c1054001d00c05840e040542e800f54101030740d20721801404855072a405502040c200314130512281e107000940d21030b21030300c034a045402c04800762540741440c503050f04803264a10788207000060918000030002d0150740200d081e01e0140112001147da20712498402c80c15175080a0313000c00152030400100c000c1c584550 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 306872032 1250 306870782 306870797
    0x1090905120f0408160e01090207140f010e210d02030c160303090c06110a0803090f010e011a0a060909050a09060e01090b060d080306040b0d020a29040605160201 71
    0x300500c00c0c81c0c00c0341d101d0168105021600b004194402c00480c0c40d40d44541005c154900d08088001000e54414000c0507a11078000844030200101303800120311402d90b140035980c0781840c1c148814060502001095a10700c69203400c400844018a00380c030000c070884059a2410048140100103500000c00e0b000588600b84a100b9090741d10b0710501a440c0e00c42d9600090380c0c00c42c0e00d014070700c0c1549500080c0c1000089503105c010a100043d0304440780c0c0c0c010406079242e41d41c9070005840c101c1205075030045942444410007190f001504009074400c8070144802c41204a2401d00084014502c81d42d03002800850007040810815409503821410744403000c10301180d191100030940d802030105c00d8042e95035224100903c03000d054040d400040c11118554406070301c0e100e402c450702024110501c11035564000e540c035661054050f1644641c05445511066038500b1402c80890480c0405940c4680b1851340a0080302c004c8100c3c0d05480850316003d050008403480f800d18903408010417410f00c030f0384 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 306873282 1250 306872032 306872053
    0xc012f03030103150c05030103020d02190902040b090f0607050706080408040306060303051207020705060a0302030a020c060c03040b060d0210110703050709020c070905070c022407060207030806030c0901090905 92
    0x14030046028601075060362040c0d450b8142814211591001d9500410809200500059540e1510b8140c49501198240d540300030b003a9982c0d02406880e031042030110320005002841e8072114001c0c01d103081c0700700c0f42c0f5111500301c41e060010368401c0c00340041c0103400ca4401030120ba401404003e4009000d5840b1608181d00c961f2080b0444000c1d803c143d02060b400b00c1c1d21304100c2c40000409078428064406001180e25100c0031803087d011300c0d000982131680110024110045690607540003103d18000c032406414084101c8419900a4409850382200780c0f000441e9030801c40181000e00307501504090320340105460444084490a104030040c3c0200040080422020400c20000e045107680040e40d5250214606103044c1140d440b070551103040c0402c0101841d00030001c40c4804d501503130f600240e1b04c816070315101505c80f450300a44040001150410500070142c1c06042000c0c0f10f920340741c1ca071b9102c0342c040507500c02010b0381c1c09611000317000c01803050f22480e4100d181864801d0382210480b001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 306874532 1250 306873282 306873377
    0x406050928110d0c11030a05090118141005040b12091015060e03010603111002120301060804110405040f1103070302330a0503011217210106020c01 65
    0x241e00c140c1c501d032050045070481c166440d40c4a1340000081174100140030703a19000d0615220302640800710103104000c14007810507402180081400c011701070007400c03400d80f0b8582c9a800182c4a08007903015500808242082e0382c094012201521040c07050182013000c1a1001c260104009200b148180904164610182c01c50f00034141040b42c002000403041c0d08008004081e80e030307115011031003603041403c108081400900a5920b582081e1400542444801c60a81c90003c0801c0c030701e021220000000581c0940c404c1d03074a03024510545188508601440c01c2106880055401906504100e1042c00c0002c1300c04070b040b0401d44014003a944040e81c1d0b82c0018200c1000502140254a28850304801810621102a024078100742c0968182010514000c055000500980c1164a042d4006000f84003000c102c0e1105000c0d12001c40e9a1101f4285103840600309180303041d0702d00c00d842800400c20740d001081c10502060107a40c0c6680c81e2001800502242c2403110f40b400103416420310103101d144 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 306875782 1250 306874532 306874541
    0x9030206030a060e1b160203070506071121150406060803040303080103060c230c070e070c050c0102010b010f030b0a080601120c050d02090106030915061e050406050928 74
    0x1061800b0004181c0d20348000140f0940008144441070f49164145844040c25102501c80602c084144900f40500d40d1010074070b003d0058001e03a0f4800c4002c181101045100b0503041034092043e02c072209680803940c015804c481d0101d40101c0c1540041c0c15203141d060308100c400b0740c0305006200224043d507840d406541103074420b400a0f03000603003c00062040c4071850003513a04060702071503c0c500103001030444160b0b2240c0210070340d41d81040010391068031007040040501400085840103210b060000003e03100d1007940b4422106405010750005079580184203110340d0034010303100d01801c0c00c0103a800b2401010b018542c1e640c0300454040c04240140c00f000f51343d000c2c050141c542c86040141e4140860303070203600da02052003a014072810f10016122044070700d046030007905003c00c40031043e207040c00c8800098818403004901c0c00c03c0c0007c07812031640041c051416540c2c48020030710f480d2000e002c140d41003170183ca0380040c08140414440d10781002002505284000040c0d40c80c4500b1040c1820349 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 306877032 1250 306875782 306875791
    0x80c0c041104060813020a0608090c040f0b01020c090f06041d0a0302030301180218010311071403090a090501050d120c06092001080f16090e13060b0901030809100903020603 76
    0xc1074080390030310816410034041504004d0f05803400040150746d90008013a400c85004807010401d04c40c020858843e0300700140d40c0f6900c0028000d0181481454100d8010040012130038010300c209200d40c551424050440d03801150041c0360024590395030703c203000151129840309541d030840b03100070300210401131044a180f03510a601075640e170b52400038450000c113010502101640d00c1000740d99580121036501c4c41d407a100a08021543d494540991040d0740500c50700a0030b5036030095500e20f03650740302100401c00c21200321407201d8102c1e161094001111402d0041c1b54010180b05070b10000300f2b2034207058104401540c234002c5109080d5507210001d858882000722070704000c500750720707900080608000f02004000c0c60f208940303140c1900e195100210141203a1030000c1c060441e0440180300b0300382c00000d00302d00744030b00c1700508040240d080440390707404c41621511302d040c40c90421441c11004c42c40c1201d41103080681418800401c0000384001000c602007400610b0800000603115031014502c107 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 306878282 1250 306877032 306877061
    0x2119060e061e032d0705060f0909060f0310060806160c02060f04081504150507020d0309020a0b0c0303150a030503071202010f060605070b0121060902040b06070804210c03080c0c04 79
    0xb13034030b24600d5107191001c03540203940b040009010440d080071015065901c0c1d034804803000303582500e529022070808150080415058042e210440389032050300d030804012545542d044801a640341a107060f04460346c28803020000b0303111041a13001d40742840c05850741c808040c03001480c081e921100245410140350b501d023818103110301000140001c44603071441040071003201303000c54a0a140c0003902c43d031134910001305065842ca02002951590000d000c00b07848610705141d40d07096008156030740d0360000c0703840400a10346008980910b06012a0b03e5040740d03800001142000320654a03250020b410050013004c41d0342e03800c0310003010a04d9001e080001e14040d100c2c66903500e840d007080d11003044140c22212050b175501d00441c0410080b0f0887c0c41c04141c20002c00101c1502c180300280181c603210304101d07440140030506600f400302d804000c10466401c6070246031a080d6031f0310400e100c1001a40041c1c88090100303020000b04035803c00411406030001d06548031940c1050000b0200c44a04814101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 306879532 1250 306878282 306878353
    0x10f080c151b0a051507080106120605030f01061e260a0f0f0605070e0109090b012601080601060c03020a140109020a03080a020717122119060e061e03 66
    0x6115040c48100038441640d00c91742854a0918400b40803100107102d40400c11040707100443d030303452090303100d03401800d40101034444c40011080d21a0103803071b003400340d804552540d154610032450003a840900326040c4081000201c907a00d26102d00d0240042c2c1500c140d40195041880090302440c00c0d0070752144a9501d401084602c2e0030620110384009082c142071004101500507603070b070486400c00c11a6100c103400309410b03807207200480301c914a15100c801c2c1030000503500500360071a0f81c1500d050760304100407a0b0281c1c0c0e07119002c550810307400c3e1010340940c204012540100e1100980ba00c0700ea41110004104cac182c055000c02e5100e03a040e84103071010080450801e40040d4140901001803d954064806a841007422540c46000003480c15007468030010305145040c2c020351102000c1e440f01c00350038001e0710f016200c02e20381c50151a20303420f05510f020b02c0426403400c00c1144601502015220304500304807002c4180030408908201076043c400c460003c41c04c201031140600c0140303242d00310303c0e2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 306880782 1250 306879532 306879553
    0x601120908190f0914010201060e2712090f0d02030a060912020c0102100518060103150c081509070302090d0516050105030f07030203060d080c01050f010f080c151b 72
    0x1241c002c44407018020401c840820302c0c10a9809444441a41c502c00c4104032443c1c04a00141d006044c1d170792251038506000e508000c4044440d400c0001c14219688d005100d4041c0241004c2c3ca902000c61b00c1a02c9400504c50900b150910042d003007200740c00541540d44200c155000070b490400d202c0701c21640980c4800303d51082011020105100e6407107400104411803040d00082d44646850100001c07995690000403a920244403082d10040a00c0c030913a4403558490822415900c103501c0d1546600d810840200034992080c10098400c0d240c0e9564060741421503410401c074458081c2c10b0908040c0c09111a200340e543c2e00100001d00c0c0e00c00c10060030b1110030b4a25507424034400da402181401420b0040085004c4002c502541c0400c062074016a0783e80c0b00300005a0220f10000090881c40e07000c5900e0740c0110055000034007400031a03480600f40c0e80c1c0c620701c03480c514915009550b0340350032212064110781000048a5024031a039074a55003024a4414292510300700004040501d51042e01d100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 306882032 1250 306880782 306880807
    0x40203011d160e090706050c03071a010e0c030c0a1d1e1201050c090d140703080406080a0e070902070c1d061014090906030f060c090a060e0f090601120908 68
    0xc8010042601803030b40134681080b146407940c907180310325824484e000450b507600070418801ca842d09644644989045515204190b0b90b000c801d00411741c61032682008100340000c101e0640b0b01c0345a4160400d80781001d06a021590700b05c29105030300c60b40e1404485001203607141d800503030100b282d8007051840f0301b488104120040d40d00d80004500b0b84d24007c2800160030744242290400c2e10184c50106a80c522071419000340b044000c02034001d802045004010052208010011038940d80e07a91000c903154110003904841540032507607203c3c0d110050401c80e4480320340142500500464010700e0032607551070f110b2915078440b19100c400c00c0c20130381007000c6407802c4454038175006401d18020120141030340d4110321510070350b058907100766002c2c40061f4669800b0400240401003032415509141001e1944003031a810880c05c1307e01c22241804040351042c8075958007207092100515005140d080701041c0009400d000e000725042000071203000c1c01d4a07035a030158000d21071040c0155a50740190301c200 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 306883282 1250 306882032 306882073
    0x30c020111010f0b040b0a080a080c031207080f090105060a061101020d020708041d0408040e0a0f2f090102060c0306010c08071101090506030f0414011b09050f0103060f0e040203011d 80
    0x80c240b0900001e00184544234001640f5407120340e204405035600d9115031851451806400c00348401e100b0200208008170307038000c00e900c0c011402d003100c1601540715400c0d010309a1f1011996140c105507224800c00c0128802d0100750701600d06180010318201403402e4a00580c4c1c0303c90b07030503511032500090411482d120041345105062495012072803e00b000d41d6020b80520480c812140307a120f119020034201403030342e4010a4000c104030810800c5000c4074500080300036041803606d085585980396000b122011710101d4660f000168054031443c2d0f1040d14041075a0000743c03484c2c0c100640080d0860000b54098010600a4003178000807105141a50005005100c2500841c1c050601401817041010041d0f200a0700660b200050500c40013001d810680100944486c02d04019108401e04070400d4205441c401500c0c82034a01d8501c010b444801034007912614801e204d564454100e04000d49006070788816002440180003051422401160081c180d00c4403012803815005041144141c00715101c2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 306884532 1250 306883282 306883301
    0x503061f06121b1106161b060b030f0313080d0c020607032d02061509011a040902040b19030b060906160606030b1e0f04030c020111010f0b04 62
    0x180003640c01004424160506851040406100c4003035045604a90700d9000000000d518400c2101e003e540028010011001d03490142094000d0b0b0011500c0b000310060030328010340c11501e40800b245582c5070884011100142d050320b090b580c42280b0340301c0355018040c840346071515000643d294080702c03c042d8106421a0700c172192b1903118040d00403149421482d1080f280740c04669030381d00c501d42403c0035600118550140080b96a04072a010500400c074401501c00c5217203075007154a682c3d2116040008c80d0000c4180c568440d00c07203401004092420724034030340105031140c0030701d080c15030340c4410100341d8210b908220011000407400d40850340c2c0d4180b0502454409180a01a03003000030301040c03e521501516500611000440302c040031280c085001e00c4952028007044415a40d0520b0120038009903002e803043c0700032880c07111b20051003003034079401600c407580450f03007a482e60340d4107a13401020320300f0890600c074680403603e01c1404c0a1203910450362107500c0c0032884109d068104001c8a2400c907 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 306885782 1250 306884532 306884551
    0x10311010206011707090c020c0301092f090c0a02030c0a050303060913020108040b220515010b070803010e1329090d09090b03070f06031a0406050607111315050306 72
    0x3800d100311404d0019441085038005c51001820203002c503c1241070000d80300b04c0130342642c2040090010810382d16200804850104500c5000301e844503810360307401c101c82c10001c1c0c0c0007000001003892800707035400402039854180116490950300481031800c00301c2c5918180c030b042e00080200321060505103a00c540c08800300f0080d100c0c50640d540003800da280054405811091042d002074424100b2030349040b600500024000d182080d0b46c90320035621041c440c142c414681c0304100018581000109590b10300d640f107002d0500b103038207040c0800410360000f4120180d440c1d1124000020810011111f0700081181100605c150f5103400110705200c0c028003940d01c107501c040414078403180d000709038206503a184080816030440101c0001c0c90400780f07030000840c2003c0c802000803165015030120079030b20410401355500b02c080764208411128948141034011104000510000c2c1c184203101244d0308008004400c01008400d5450880300e150200c90019180e011050005203803c005240d802542034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 306887032 1250 306885782 306885809
    0x50c040501020a030c020123070c0b0306130b0414011203020106140607110a0305120d0c1b0b041505090705010305090f0a080f1c050a140f01120c030b01031101020601 73
    0xc00007565003641c00c00140c10008010f8080c021684103001e604c07071008485c2102603111044008441c01c5500070301c0100d4003581640b00c0025404001c000356441014020285d00e149014000f40001914040a1070380e40b00303546070703940e844420030220480e02038034510101c1d05400c02c441c9000780c00c481107a004a030f128000d40010040961700c1d06c00700c0d080c503540603030034082c01c07028000482d54418540e000100940901c0001d60540c21040300500555441c1850602c034401c0040380c01d480303090b00344406085100c1c03106080c50101e00100380750b0743c00c1232007001040341d4000f80702c2005081301d406440011b456040503408005039030781400b5480d041030396000544021411092019514a00300f81e008000d030801060030907600f500750040c0e840c909901c3ca0040102c14219982d10001c0c8030882d9030308659803030441c0d440f0003241c403403d0842c031a11401d2500c200300d90800c0ba540700c03900128501150518215403002c000201c10994986c003c511543c010240300092200182c20008140c2086000701c081 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 306888282 1250 306887032 306887039
    0xa0312021006032001030e0307050a020118050a03060e0f1b0307050603060604270f060f23060c070902040b07110907140d020c0105040f050d090b1c060e07080109050c04 74
    0xc60300c1380300700c50703844584d8442284c2400e005a003d00903140e01926103000c08503146007808808140ca1003102c0c400d0342c403200403910740350022025400c20b015054001d900e0420520014030154030231890b0070300004c00c995a0700955000c251400d0134003100b00703128041281c0c0340b414600313041104101a03c003c44202d402c501d0910042003142c09144100d981a4041e8031594500070481080700c3d000b9240800b0500109111407402400307803626100e1071400c4100d544001030598a46d044205034441c0c9498503600c114600c00c2007000e540c11140c9850902d0085060011388017000b44000c00042c41d030803503810740701e01c02806c0214080e02601c48540c05211101c0400a00c15400f1413100360550503010341a85940810100c68002c0c007803c02c10003030643c0380c101403000b0f00c070481c0d2a030034445201d0411110030040401080310000e04901c03404418000900c80214040da0031420155000744500d00083c0d900e5590700d500a00d0138064800002184082c4014007225541d8044c155200c0102861203240a18 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 306889532 1250 306888282 306888293
    0x70609051e0307061a06120402030c04050c09010810150e0907050a020a0b070c1401021209030414010c02120d080406061509030b040c15110c091308180a031202100603 73
    0x6220350013852556601c00640059a500c08420440003010340314503210140001d50811010059030305911a10231031103401c2862030305014461141d0901000300303080080e0f240041d00c8405002e00300e2041210314134800b0401c0c000040440510840668402150180c0401480030301c2401800f200c0410800300104e1040c1c68000132480c0e0a02d61200710301c642540d03496030454400c031000b00002c10b412503800f1002003000c41500a003144084081d8901c1403519150308903a524403d038030429280d0842981928003c1d07001d165a162b4950015003400483e2292088913802d085014099001240c504010301c002c1c000d903445610041c1403100c1189071003103000440500324008600c00142900d1140e4006000c0091000340a80288650080900c26254005001e0203a00315001a884141326501c0c1010f601c0c40c250159a0042c2e0040d03200251002484c2c0750060140d1084803145030801200500c040c0c1501d92031070b181c0c02103029140400724200c1015000303080005a0b4a1038205905255050001c42d5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 306890782 1250 306889532 306889537
    0x6050a1d0303010302010203120a0624020d2c0f0301140115091a071b1511010209060301090c051b031b010b0f01200102040f090b151914070609051e03 66
    0x1441d080c0c002c0315036a2261840c5028084c03541141c0040c91200750751082d004810078251214010f03c0d005c0c1e0700c3b142c001d11340464003540604071650280c245004040098104405914050702010309004010500300700401d0070343c1e120401d0003508004000041122500813070003004118503510300601e00e58900201d0310030b92003007044940c480c11000a0a0300402ca110042003e50900c2c0300000c0071440d5075041c0483c01c085041c0348041c04202891000043d201061003203541041004003c1425070b400c2031171200050848400701000d00c202045804842e802c884445034000c0b40c08401103a4030000d1024181180076602c03d00c908507810b00402480981c0d5114041900e01000e280004101c070903285005420340c4c0b40c110b6927440f035100150100d405840500c404007610390b940302c10312102900c1c606100091421154034090881c042c484190441207858020400304400e1a02c003601d80190000102a6400ba0000b140d550340c0d5003d04008010302801808000b0760482c030692480c2c1304040c8015140e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 306892032 1250 306890782 306890797
    0x1d030403061823010e2a0103020c1920010e1210060605070c060503040c06050f090603072705061c11030103030c030215010302060d020d0906050a1d0303010302010203 73
    0x119140c10b40c800d80d00b141c030007004600680001d1419400b0810450b007444140c4140350407601e9500b000c03030941010000003550303400e68482d85c02a00d00510724440160174000c0e032401243c10540c00f040004a0300750208415180844070203c0412514400c0c0782031a0079078140743d6200022031262500d03181d02d84e002002440408400e40341e002c804040c110440d41000b844810402c0301c0d0303240010106007903901070041c01700300b4850400015240d440c0c14059074180801c440007401c5e140702c058184402486440a00f105c1c03040654aa81003108903000101c464000b100e0290008078100104218450309034841c8203030400d0001c50a002c142880c010810740c0c828080309021801041c4506003e80d002c551100c20f0060421400d44c0d200d5840e89001000c20304014000e0300184070705920f08001c010503a00c0d0a0407640e000b001030380341604180400c406034100040e047c4403585e449110070003046c0b403405028443c0311030800004003085001c003280c40803c8100090004da40c000c0c001400180d8000080b1100e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 306893282 1250 306892032 306892043
    0x1031104060318020307080a02120f1e120d02030a1a03070915080109030e03120a080412020307020a0b0306031504171e040b0415030915270b040201031d030403 70
    0x310107803c00303401c4082203109009406100d03d07200043c40304404200c40d00c5451084a0090341040312510803a950826210030100907000030f81d044607ca0300b400c06280c4800000070a85200130014038a000158001803149210260004104144091507105940c6060310074002c664a07601e901c030100f5030716045409a40200c1e42d95000c440d26000e03408580e00c008101e031000902c420a100d28008020701171080c0843e02134842c070041c2e50501d04092055841e01c1c5601e540f0910560b60303339200c414020b00d1090319081503000c00c008400c0540c503401d02030030240400d0b80081d41c0e00d013008030605180054001c50070070744220841c180300014107000740b001410852f205209403182c0d00406580c002e0740e074110401c4211a0300050018074400440040c004842c01007407041051000180f05800340d4448101c01070100251502c1e007614459140d001c04001e0b9849103460200e0a400c504000304007410035000e45004c03080d1820403046680c14011500444440c1d10610300c0300c4560030700150340303000d60b010082c0f4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 306894532 1250 306893282 306893291
    0x30507030809040b180a0c0c02030102132105060f13140c0a050307030305030c09060c0708010f0501170604020112020d0213030c060201140a110f1b060c03060a0611030c0d1d010311040603 82
    0x200d944507140640d42250003e000315560302014070f004a208105104d030848ee5141110810103c00e07203504049003c81e04800a00000d42c0c8403442003103291001040d10b500782c6e0352880340001250ba120741c0c5c0104011810018504d00c2849400c200c0400e070b07280d00562283e8001481480043d5115040ea0b801c0610400d07015160410040003c2c490b008800c4079100c2441240000107900b20150083c02086072651420803075030f44c0780c0c0c2c07a0494505013244409081d51181002ca00194881e2248010000301c03041d005090000c0c065003001a60301203034081f02d85810326003003403040c0014170f2a0500104a5400200001e2040864110141c4801842c0c4140c4a9460090300004444030301214601e03400300040640e5240700d030102060400104112880d40c0c0300f204002220700c56510b044900130b8000034001e0398110300c0c100c0c0c11528009840c2059103240014400d80400d9002000704010034581070f100c0c88040b1a014102c1080460000740f00380c1090b0521401001a100f00c808482c140d030345501c0c0105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 306895782 1250 306894532 306894551
    0xf091203040c1e0314060403080c0c150702031e040f0612060b0a030e0d0f14090f0303040303031e05010b0a0804020d020d08040f0e150d020109030507030809040b180a 73
    0xa03901d009038452101d001e43d02080909051515403003d0940c0c1c4100d1202e0b8407008034503442580c0700011240200031034664001f04822620040107032240c0161101110a0f440100d0008201d007a026126100540e1010403510b20f030003814400d000014948450035410b02d0319021980300191030701d218800a103c4680745000b00501d684e08003402400e050178843c0d643d0600d4242c0200180840c04000c4124022031030602d2055101e210500984001755a4000d1101c040ea00081d01550020060907401041d00d08502d40c0707a142480540015402a00c0005a0001030010320081400d4810340f0000c0b03920301401440901242800d54128a461303180c0482c25590360301c04100300c8041490060f5001c0ca452406030208403034000100142d40717543c502c00d0649a51b0368212046d40c0c60940d10b81d50b80080740d18030011582090071400315801e0051400a8106680340c444070b0a0040035003050300c00d14400651008581003900468584038020380d805409100107040d550b0140d0805000d00c106291180544c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 306897032 1250 306895782 306895793
    0x106080702070308030115030c17360d0305070c0308042d060905070911090d0203070b0309070518010e04060b01050c010c020102070c050405160503071e02060f0f09120304 75
    0x42c0003950344070010554030f50310b0340724010007070110002da2800242414408042c5a119007255100561000c8c5000c885445569000b500c4204041c601c2c0c05488440282c07580e00070111103410050b130313079080c058010745404207801420b84400820160134000362188180003e54048807195000745c0085199203100e41740300701032041c0710304030065200d0120420002c20601c10b02d640302105083c40381049800d06640e481c1c62000351115403258060b0b09106201880190138a562692074841c4000e05854001e6100d0480c002950416a075464071a403000109100b941818040d5200c240581b1800300e46961500780da4078000c900c0200020009034840303207030606990050302907451002d003140c0248140f4542600c024000c0d00010f0f42030798a00341c152000222400c1031b03c2820301501401c620724082c1e00c69070400340d9403580090038850412191500088a460f5041d00303040f0008170681c00380031031f414551034458080038090311a04860240b2403c0c418500000a400500800c1a613203081e00e80c0c1d11070030300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 306898282 1250 306897032 306897043
    0x11202150307170408030601030501080d120b0607050a0c080c0607020f010318020901150815150a1701090b0f1f21051608070c030509041109030f011b08040203060106080702 76
    0x183c80606104050000700880b0402444c03141c0005c0c0d8003042240c0e030303441c1400d903160400118800807801d16214812805610380011602503006410245012115603c0b03a00e42005035038240d8103140307002c80a0041000a008066204800b02d80203424000a900041c50b8a031082c459039050582d0b443c4410070740c0200002c0b1030b80d8590000c0104080e03684d030b00250000d2034020724050380098100800902c0f1304489901310b0f0040320010304000201d40f60b8110020007948510403c100b031129020342445d1a590840c155806080d40803000f060000402f02131001c200c5040c5815849480401503000300e609448408214011032446c2801007040100404244141e40c22001032034113040c041045810507041841e031001c0c0440fa540e201e01903076003030f50071202c01100f4400100043c408000701a50352510b9080342d101c1c1a2075070b007010329101c074070130009181945401030642a40d442d1207034100189d602c0d6000d42900a4542416001807030590300103510740d801400707200203005d080008110f42c05d01c204032 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 306899532 1250 306898282 306898307
    0x60a0201020c03180307321f020607260714161118071706060706090c150203040308120604181b051c02040515030318030d410a0314011202150307 64
    0x3402005900034000351500011201d040c0480e10300a2680c0c0c428000341c4004123300d0003091140456250b0880840d2001c00340d403c04a8480305c20700c44050180c10300354110541a2203111288100c45204051200e00a22650102650058030741004080d58012040a40d03507620285419403a82e520b10000b42103000c0d000010b0f1065180549003400c1045e40c1d11761405030340c400e0f0959444000c400d4000ca90302e100301c0c000144140c00c1030000744000f1160103e00d68204000820100704000744049070880d115003990203841500f080c6200c202517041300c02c04003010389000d4070045403d4520300c220280404078a0300081c0107039038400014030818621500c100d501c0788001c00762944c0d404c8620503100b1030030810030140d119005412000a03014000c140410003100302140d45c40030b600502810504080c0d060710300700d0b65046254840c401c1a41071a0081001c5145038900054100d0700b05038003070720908141c002d0300040d116030198401584e01c019905003d109000610f0f585e0356030f24842110060030566 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 306900782 1250 306899532 306899569
    0xf020901230d090b060a0f050607060203060a1505180103051006050f041e03050706020c0a030210170a0c080c04080c060d110406090501020f060f0105060a0201020c0318030732 77
    0x502d120404c2a00540e0a00940048640c550040d0f25410351400100191046c130b6400301c0100102d40003d480c9402451f40904014241441c082c0d881c855018200f00b03010000d0000740380002c40c0107000201a000710341c80c01003840d00b00818649103052060b800d010b03000d6107040c040046900b02070304c41445c084402070544080c04401400556900c806840001d000454680c01091004180d2620000e00c00001c10001410078054600e10707001e00c400225a0714559040107045c16260050801d90030106028001110340026003040303a600007080c030140940400c3e5404002c0108105e4814001100e070282038045070610340d5001070302500001802c00c101c481c21203003000310300000d0013a04800d1070803c0311001e03000e603586803034003801c4170f42c07580f2040322031400d5160940014031441c02d105001d441d4400450000504d040321150641d49107801440c0040c0420004003652080e038201030011030003c0007964042281d08000b0000d065044d4142e2010081c0a1080c0d90b160341c2c50342c0c030b2400c07000d880e06280 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 306902032 1250 306900782 306900791
    0xc0f03030203120f04030813112218020d1101110106030b060411031006050d0e0f07060f08040b15040207022701080c030615030a02030f0307060f020901230d 69
    0x28a40030b9203942082d800302d03003442201000188503040801410b0b1140e94150f843c181c0e00c0d507407503603a255010603100040e100041501c3c49500e031500d4082d840ba400c69503d191480901e00c24000030825501615903910592418003807210061301e41486401c1030b5a440980088050740c3c03400103d0f001d054008119a60350309049000007800002445203000710300a03201400b401d98403070302d03a000901c41039460340c83c0081d00a01c108100d61145019018500c140c200c049181d1110741e03801e51604170204079103400c5802c1103004004032a003052022105e05194101918145019181c02c0045103008005900401c4502410b43c865035503641100d172003e41c018140b1088411141c2041c0d0310280c2e00000c10003212040c4000300c2c548000040354120306100400400d5195034101040e0201c0c1840c0c00d42a80600c58104403200598080c0f00e025200d100d0380000f181c40740342074100301c0140e0305c1024001040074810000302100b664041ea145558100f07548924980030301c4181c2c10f5503907104090904911070b10f070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 306903282 1250 306902032 306902039
    0x30301030305040e0a022a03040b0417101107030c1505090f010e0309060924040303050304051006050a0620120702180702030306130212010b030402030d091a070c0f 72
    0x714010f4070035110b286107404455170ba40e0a00c2d000300d10481942d0900c000010400c1c510210450002104290007901078a003040c0d40c6008440b4250080d4101c081034620f601200740c034210042200c0100301907050401e001c4c4641ca0803d101d51440369480140030030813846040424491341d1402c1c604603a5211404008a01d0086200c9031240c82c408030700c00e243e5090403101c3c2c1402c04d0002c140d030a00d33103000340f00c03a142011100400603044134248050080302032000c0209080782220010700011400b9842d141c1e980d1500786801070400313400c03070440b0904500c1c1900500094a0f00481c08043e12140d080a94091881001ea6081018018451400d80c803441151610008000d406040918820740701c03c00900103181c404900c414085584000584c82400010b4580c50403001e505110142d0190040c0360100d0300034000c480380f40c00d070040030a07000c001051000310b04041151081100d0246050b200040c100000040c4003400e221704824000d81c0810000c0911503da0350b500000d020040c00760951654 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 306904532 1250 306903282 306903287
    0x30206041206021c05090d0c0302031c0e0f01060f0e0f04060b03100c0e010e0108161812030e0a050405040c1401171e0106110c01030207170a0e09160215040f050303010303 75
    0x101211b410707107140502102c084501d406444000303802c992540181d03040c09103503110204601c00d0f61807208192625078803203482000c001d00c035460541c45ca6200200c8c801c0d00740319a90084e207070142d1050158050030b80401c0351800d500320590b078106500a0010030005130450000f840c10a00d800d406c014a07241c58104a0b0039608607010034904142030300d541c0d40700309252005480c40201124400707034018050038004102031190481110744c0d001084403011035515500410011508000c0440c0071541b50917a901c0180360140d00d8400800084034103100500d0160b03100218004a0f20460f21f00d2603009903041c0580c1e0007681e00d4480c410300c0c02c5c2c0c038110a10f8210b5009007140d2445d994042918403550020920a104420018141041c2402041001c980c88011002075201140c252825141183c121076800351100040c4030780e05256071203000452070141000100c2c400941800000688010303500c3e0007075000f080000c0c1c4010704c04568090b0f9915420100c0c11130f0002d0380000c00030f00000001208054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 306905782 1250 306904532 306904541
    0x8030a0902030706050901050403060b03031e0a1d061801120207031709010903080c07081e030405010f0501050a0e0a060e1303030b0f0f06030a0b040e03091306030206041206021c 78
    0x500071070031590032668600c019185c610690300c101d07000840800090010030790390f411220640c907025003240d103002d2071030b03030b00c9004111035811041c40d080c000504a9503aa0340904007031090985545000400e601d200c0004055110b241041c04040d00501d41c03001d882d80c010503820241e602c100d0f03400e565a850514000b05190019803500305000c0c2c25201241500c0014410201c080e68103844145050300c0314211280b1a4004000480d408142000314041c10525014004101200c00145c1a01c0f820a031400da804d40703642101106085280c50010001c65032190005002c4845482218410361502210350001e4800c5411490040d1401d2040c0154075482c41d02c854840c0f400380d6010080b80307103c1810042100b08003941c50f41e0040710062007580d103103823000046400218141002901e11403280c0410242e030b803a204a1900c035040800c401d1b1040c01d01140601c00154217070340800950703045a000032940d00460040c13440040d0361850100400005038100c99072060344040035401100d5200e000700140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 306907032 1250 306905782 306905801
    0x60506190602101d0606011407021f08091c0c0303020708070503040f09290d0b0c09040f0605091803070602120a0f09020102060610140c06010e0f09120f040308030a 72
    0x1460444c28401d02d440c0074281d10301d483d0014026004c203868030001110701c6581c0c41d010b141d0409080011000503a11071203410350b49210469010306d040455540600810401840c0c4940b41d04070024039403042c14174140c80300c43c02013035003045801e8800c142000c400a01a410004015200005001040c024000040c0044440b9203000a18158a64034100240c072600300701913014005202d030800071002c3c440ca0203500c1100142150b0741e55a659200d044107504283d881840c50f0702c002035054441c0c20f10340115070302407085900501c9103528050200d100c00000a020210300720b680c0701d0f080c900c04002d00851301a150041c070255113540c0700d00c1e8554801c40c402e6403102071692604a180d080b06110380218121550160003a066650f50142441039054007690050100002d180810450405040c0501107203030103600200601d42c100070b032120f0344100103400702034001000420418a6040080c0035000e60344904030311500c1c2d1900c0f501706c103242c0c003403500010001d00c0003000300a003400c2282e00c161280d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 306908282 1250 306907032 306907063
    0x90e1507210902150d051902070b0103021c150501050102010c090308031803040812090a0801050112060e15010603090302010b06030709030f0f0501090311010b030d0903060506190602 80
    0x36200c00303006941240244500c80d075030480c1c103800800056220b500c0300b01001d002030302c0003000700304190020050741d0014001c0c0c00e0403a40d840c02d200c12030740007a640c5100959401c2d41145800c0203a00c17401106c010501c4028842c1c3d455102c031503c400c6142c0c100700201580800c1012803030380c7d04c130b000c6409061309004141c019840d00c1c0040004074841c50003181103075000001545552188011540720f00e1030045400c0d12480304000000340e0881c00c00c59541003003800d004013904c503500c010030440c008807a503001c0a045c0c2c0c100710050121890030309440d00b513660300402c000703100c0c0904a80c070386c18505806050100ca80c000707400010120781503041414203a00c0f907402000f0000d034190402c602404203440c0c1c44001812510f0500001c0c08001d40a03110764081c00c14aa00c003810343d51440d0940303d89440840001c0c0c0903103009040721800f40600d0710107034811005001000001200100800014803014140546800204140761600001011071500306e8410180c21078490401035038460888a40040 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 306909532 1250 306908282 306908323
    0x9180803091c091e030b070302070302011b021006050607030e0618031506010824010507020d0512120108030a0516030e091f060509100804030216080a02090702060f1f090e 75
    0x1c81e00044c519031025a80c1c80010a003060b00c1b030041c101d0003508260400c805642d0f898509040200c4104400404052603900502c80c100c464480340055034000d6001071f02030001031045500003500102c10b0406504141c07040c903100c00f81c0404100038851482c0d0031507010700525900400d51082c0b920000c4c41400e0a8895000325111102c0b0a100c8001030000258003403400010000b156120303100030300400d030000b0204803d18005441324ad08001903070b100d01d00200000180c044240c40030500c441e0042401c50301031401c200c00000c019050703104001b195040144050b008004150145401039601c2c100548040d500f460719802c00c3c105803450b08000c1460b0740307494400084ca10300c04e00845000b41c0002d051118021783c03544003501c4000d005001103040d13000303000081810034030b070b42e000c000100409401002c1500070741c0180401c80d00040c00b0507085400407010400f4200c8402d031890f4000e41c00b4288112030b141c401294501364001c1d030308285080b50400c802001200f8000030600d00d18000c3d10503480 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 306910782 1250 306909532 306909569
    0xc030c0b0406030e0609070b030603070b04090509010c090e062704030305040201080a0908090904141b010f0f0503340509090601050c07170c060a0f020709180803091c09 74
    0xa5503101708860103e001c1d84025418072001c0200c030060768100d80094110350b481a01ca0042d0b4007a904030740c0100c030109588004000744001700b40a0340001900605054080e1030a20f4480079081d40010240c1d402040c0309015000c410030101844403404120704600b403a641050f01d0000c1c0601000d84c0c051340012160340c082642a03071140b080c0c2802c41d81c4032407840d152070709160610a11460040050740c0180941c51580c0c01b114040c414090050703414500564865407560000d402d030301c42c0c0c0300e01c0c0d000c01c01100300412000e9004400c807501304010386030002001c154825013492844030046010070780095007040b04c0305150400007034004aa81104c0e1494280e80b008011112401100c003e00e0440c0e10012040105002800c0203075102c000107801c4c0c942440b42039010900c59441600c0074800205145e00c15658658140a428050070455002348803520507803c2e10210b54aa030900600408000400b04401c26001c0005c59021702d4101c030104d0041042400141a00c1a107101e22a001203201e00d420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 306912032 1250 306910782 306910811
    0x3360303160b0406060e041a101401052d0d1a0619020c100c050f06010f06141608090a060f17090f0a0c15020f06060d0c030c0b040603 59
    0x8901e1489803544000d0403039103980b20390014020140060300c9060380c0d400701285010350b80c200544154001c201101c1c1c0300404141402072440d00502d00790400e04050070500c5010f640c8020525045030900e002901c41c1c002180075503802021a61420303480c040722003a07542e42c50101020f018021803400c410003030f500b00c450b003c100c0c100300c10440540c0200c003041040c5000c60868036034504071000d441118182c0c1008800705640001200502c030100e0022200c0a0411070100320048180d624075010b0f064039403501a40c00040802c1e80100c106001600c2c8103101c4403c031401c00d40b103c1c842c2846602100d142582402502944008442809120110b40c0421854045e13030b502202c44e4074030740c3d4041d60840c1603800c10000450107824100d4500906902814103103041080399081030081100800d0103103008080701c51003143c82d040d0000d6400480c1640034818000c900e5030b901003800e4514000c20343d40c51601514a8206400040c40c44209a0000c1072010001c0c0260082d0313003950b00c042020091000c0340 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 306913282 1250 306912032 306912037
    0x130219090f05060f0703210501030f0c08211e130302031c1e030608010507030c08011a120601020106170d17010302060304020d140703051609020c190503360303 70
    0x70004c42004100d0354001900c110310004c0360943c090001c0f440e0b440808136441c16a2070a0740155410f01580c00118140110440b0f400002d1203428014241800306c11005100d100100581da0304441010480070014900700840c061712455000d5940e941d04808030034445c1000e003a0009a010384110300148000c28110424580019600d446950208180c80940181e501c400e101030b1080503210100041e00100900516004500703a840201300614404001452017805074010855090071188004800503400200d8604402d030321901d030300e25559100181d025003040c1e80a080c6070300790003211200701540031640071006803166660068080c6a5500e0003940c040c00e000203940701508101240043c0f80001b20b2444540c800c10060040025144043c3c4c184040c7c0e0340f05642681181d0396201c0080540c14980f00982807407901141008980085550b4500b40020540c04483c8104d20300d1091200400942d030302040c20308025001c0f4015040003001c01d00744140e04040c1560360001c90300b000c0c5400b10a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 306914532 1250 306913282 306913297
    0x1d0717060c0706150509070509040f1802060904060b040e01080105010b040f09020a0c0602130503070e1302010f020304051005190306031e020d14060108190f02130219090f0506 77
    0x1240ca0508040341c46040041c00d140d401c0f0700c2c03e07001c4c004000800ba2104001c040c030a40c20f5490340c1d1303126402307c0103000580f0400944100c4462404080203440342405110307001c250b4043d241241c4501032040403400400c90b82e005040d000501040000706848001e00890507682407900038401070f43d80d154040e549000c2d502500f04102040b402c140000a0301790b001d424070400918001510300e03038540783c2d44201e9101c41c544003150301c04503e0a01c0641800c118502c0100720031110300100f4034003030040c5201800310b07a50003810401035252409443e8420030075100900300003818104501414a00940198071011618000150030440000c4203800380c0b10342e03803c503600500d401d40d0350030760502070f00090400144204d0303020303403003040400100766001d16880d5001000300c020161941044081c6e0f00c0c0c080030500107101161804481000144003c42c0e5100c034560540748070001c0b9040e262150081e0140540072001916140810304039541c4c040e4402d0101c0d15001c06241ba800e44540521005214209 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 306915782 1250 306914532 306914551
    0xf040b0408010b210d030f141008161208030402060f120403090b16030f2003030103050613080904050703090515040311010e0327060a0c0c0e061806041d071706 70
    0x20740c00b90fa01d4003c0d00450341c0c030681020002240c4071a4900001c0c148c0080c0e4184640c0300c1481424041d417031041088840d40c3d030000c12010603292904081d08040c011550b07008210303002c00b10100d42151204404c1c2e6071800c0350880100d444900410607014103850882d400e40c00600ea50710002102c0c0d000c00c00300c82c50006141c591f031240700325503202504c0d41104082000c003046003140c40501c10704400d0704031b0000840400c1c00346590303501d0750038038510f40300d40a4803040458103c045600700044010040b40c0300c00c2d005440100740369a40180c20350003440d88400251050065408181085c407190507498441c40c40f03a103c42c09401902185642256810210140d0301d0f8400c2200c28280070448540040c0c08484135004004181400003103112500140c180c0d0003c6051600413404201e00501000d01030501c003102c280c0d01c0e181501c009145075580818603450344400001007601a1602e80003580000c03002454918179001c4941403507541c800c680b20301d0100d43c100c2400844580d2020503290f00801c001c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 306917032 1250 306915782 306915793
    0x11401060206040228030b090105090309061b0106030f0503070311010c1b050309030321060d0807080304150608030904050c0304030906110a0b0a0203150f0112020f040b0408010b21 79
    0x55017840101403d0740d5003000342c01c00070611440000540d07601d0394042e40c494003100c500744c10840042070a4940151a100d01c0e07800c20700481000d900e8040580301e2030403809000e4a1f0200384035004900404064002800303d1703400d00601024850b00000401440e440f035903500500d2010059058200d03800c030420400001c0480d00280515140302c081450741a000d84140c0e0310705010200000e246030310425000403464051403d07085030081510b0f6065202c00140d03a00341005420f170b81c40301c86a1061820003032850002101050a200e03200d5400091180451001c00c01d403500c5601060380c0340c010a0026215508200000d094a40c286042c2c90049515454014015080c00c03400d56128444104290291141e42007410101d0001031005020303050b13030702005907203007040b51429a103000301401c42802455412115400f59a100300c010a585d078000c075005071640c1010224602903c2131740e00007030250b680030034007180078603041d400054012411100001014404140383c034046c6030324049407a168015 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 306918282 1250 306917032 306917041
    0x1d0606150412031704050703050d0503040f08280e041107050c010e060c010504060c0e0d150515040609020405190e0106050708040504090c032a05060f041d0603011401060206 76
    0x1aa10520b111034402e0510b44025144018054502003046405541640c4100000c0090290902900910420f02d1030094594035003074403483e80b0800380044c010006180024119090074018040203100056019440a41c510544004000102c40740030b0510451801c408462401c007002c1c12545560350100103021080c5442e001074031040102003043d0f0304003100308403000e1054800c1c46043c0c070992041c00005900b84145000038004211010464094422420ba0f94017003a842408074040c24807464021815130389411100b40030303c0c48241801e8005080c5800030802d800315070054026245d098485010000051171401106162071290342400ca81c1000144402031141000302012405012007900d0140e4442c080f90807504a8002902e5507950760200b80200310b41a0390740c0b4441e007807944c00700308412021407010b64602d425200705442000000740f4081a00d1030101514001c0c001f43c0e1210411305054070851400c0d40e0126002c80c400c0d480c01d5242c08070b83c404603e640d4181d4602c0ea0050216986 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 306919532 1250 306918282 306918299
    0x2d040b070f021b0118030501090c09050411120c030d0e040513030512060105070c0e190e071e0306020307091712041701061502030d0b03060105180a0f1d06061504 71
    0x1e09002c3c2c241007012030942130a42912070580702c4002c62103603000054250341030400e41c241c2002d540105105030304190a000100301a070b0310b0900c1038002150015040c80c074009a117440c1480101803903406000d50f120172441c603038002058507120001503605004039951148202c0100d50311b25802008500d0a2110010103c901d50003070781d0042040c140b407403401540382c583d1034400e1220342c08030304403413031002c10440d5100c9690400c007400d4500749814000720080d5603c15884101c05e0140c0c184150b41c0310026211100803035407410065410007021582d1f4140039800500d10300341d80c001c507400c408010340b0342404500001603011410314001103050401303007090030030600c5101240d1161865920703100081540100d03001203100d1012103030000c5a81d070943d0100a81503682d00c0490602c40d4000c00700400060700d480440c031005842c1041d42c0c142e941c1d50440303c0c1004220340038207400030514045041c0705411481c0f80d2402000d0140d02211416034524007007048503010001c00c20030013032090104210008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 306920782 1250 306919532 306919573
    0x15350c01022b050a0c021819050103110409020301020904020307170c0a02031b0a051b010e04050405070905041a0405030706050c0913020f04080312061008011d2d040b070f02 76
    0x7000c1d840c2c0064001050340001e071610050607045040b1081c41d00508c00090701c07104070301002d401ca4100a200541c9140c881300c0d801011380340ea03607000b0b50f02c0c0d071021411503030300b175040b5129003100410842d200d081a4500415043c8044030705000704280c6000300b411094442c0a642007103c650f8002d5107000ae0076220302283c0080100120b04900c00e00c045074000940174842000581c803080207030200000e000c2c00040c03003e40200c10241c040d0b4580302c103020110b88045482c0041d00c404c20008903041d26140380c40103c000d00c2c01444249000620700303000402c84040000c1a0700c41c01080c0902880d21508050343c0c3c20b03c0380342c0080ea413080500c961002000e04d2a0003418034044500c1007682440e688203203850a50b8000e0030001100900c040c10450a80741449003440e244505103820281503060404022104a03e01d604044c40a400320000e070303022509148000701100302c03440c03050808242064488074000c1c1504c04580600300c05001400c0141300b003100126002d03803940184642c404090500700420b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 306922032 1250 306920782 306920797
    0x909060a1a0d1101023703090b07031d04050609073005040c080109080706110918060a060f210e01060f030506010915350c01022b05 58
    0x4044002001c20698522075200b803000d02030b03c1e007250082c004000080c11b00305200340702200c440d0b60b210742400c090114078007401c0c401c0140031000051041800d041c0d81d10303907590380710803210750001695404240e482480b0a002c55605a08074100c80c0b0250300b00004e98000300c502d603402c20000070006030814800c4440c214810181c4a00501d0344038082c12617003c081003041c40c844004d44a8003407204000000c2c4240c6d00510700700c0c2c003c200891160740e80300603e20440034003410850b2a400480400b1841c80100d90742150300818544040311021126030140d0000c4414070310940121000017140c80c01030b80030b070000820a030785584c404020010b82c80085c00580e240c01802c0d540d035103c41031201c6401d20554001e030078840d40c09000b0710b103140340561504005030030815000382005842d0300e94030300c051111400d580e011113811048640c00c0020040c1000c0c414030a075a03203000e441041451810100300b040d0784180030790903510702641d0044092140500061040e140c2c0d104469040c0e99513124a000d005003 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 306923282 1250 306922032 306922061
    0x270b040201030f0608010b090108032b060e0f0103020414060604121b1d0106020d05090105210f01050a240e0a080d0206010f050108041515030b1303030b0909060a 71
    0x703d00c00425003220550b401c03209460395603c00407181c5150140c20540140020802140342c00e41096400e490810f000c200c08100c015401d0344440c0c10701440d0483c00c090000c00d0101005032801d1b46041640340f5003071009902540c038000181c8204c12483e00f1061241d080030740128a485d00e0300d4000004900c00b01402c0d20344060803000307d20150305000d4038900405602103608800c280300c00e00e0321f0140c8410f030b06c0350342554484002c0008090300315040e28200381d0242070071901d4070002c0401c100c005540414010714050b50904016520f080c5084040c16558240e030000092900d0f40d192001c84144072903003d92401044c40340038942d41c440c07080011011005406da442150b5955142840c144800302880c016030442c0005105e6000b0310328010000b85000d18010fa0305040c1900d54219003003111120039400c1391a108601c800c4c6c0e042642c014000c42d40040b4483c020715044842307812841c07c070003081300041d0418032180340520f00001482d02a51022000e024152201c03064031009041c000242c140 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 306924532 1250 306923282 306923291
    0x6091802090c07140a030206060d03080103020d080d0e0106140a0e19020f1c0b040c201f02190c02060d0b0d060f0b0f3003191101270b04020103 63
    0x3a58080d01003080f000414005c1c40c480400d07140c085d041a02c0288850b0103400c2d040400408650301080f000d0440380c0540302c2c47c420409070b041c02d115911607442e0305c040c0c081c24034482e2000d17984154410021207401c403050000c2c81c0c0c80f86080000c138810500c11044215600350100b5903d402c090703202c40ca40e00c03107058010300d44034102c403041c607407038001211440181c5580c9a990b011070039140250490050b04440802407404c42500140041ca090f42140300c5514058801d0350001c0340400580800700144200b00403005400e24500005e580130302d185120755808201d0022000d8001c0121408031a030041c41c141c00c0c80001503105004042141c1c0c1254414180d65080011541d544203d0405202074400420120085014410114050101980912070346a1504124401c1302c4800107010000c5c4501d02075400d081811a00e540242c0e55114035990343c0104000303060781c00944140010341d0840c001d1004403016604080c40911401c214142e40d5801e10281d000104404c1c0600d5000344141800103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 306925782 1250 306924532 306924547
    0x2702180f0310110403060f060f1226070201091d0403050f04180501170a03020303160e13022104150203060414090c010201060b09100c030512040605060406091802090c 73
    0x3003c2d690b840c14240703685440003034180213012a1340108042400c06010603c031103403070401740c602e483d4041d2281030031010703007008070074200814062017205c8210302c6d0603109204041c45240000c5540303c0002213021510034440001c03500b0343d0000440110282042e041c146589a44040da16940400c501c0a1004810440031030207000d0b0f146122600c850b20980002c0c1903041107003070710080100e11807804183d0b1000c4044000a40c0c000120f81d40141c8001b400c51007500198000e42e20895210409580802243c0d6980c90100d5564050520401e071000c1c040408100e0080c001c880d0042918081d06210f08500d51500c41e503030f950021500000060030018a6403203d20280da2000d10036900e00111f5000050f46031031a684c2401568060400741c09003514000f01c5c54001240306d204009000240130400800c00e00b81070040d800d0703500c00740034041e220b140c17450140b40813001000100c81583c07081d480c102c408241d5007400d1144040e45420003e041c4400c80d83c6800304a4021402042200386000402400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 306927032 1250 306925782 306925813
    0x20a1e0806010807060f023405060f071218030b0415020a020a0210180909140d050304030201050f090d120e070e0402040b0d08041a070602042702180f03 67
    0x1c070700a15400018004c040d041590080205034541c03454800c6512040c2d50360445110100e02403c00010a0301e920380500111418040506090b80043d510030004614941410003400041c00400d11901501d01100d10180c4103545c840511041c004e4000f000460904c00510460052a04207010300480740344018a140040140c0c0d10400c40000140c020041140460801a00c80859000b09080c0503650344000507007030701d114500f88940000a80c94401c2ca00502140b11b9203041151842801d80340c41003900312001e0903c0e442901d04074010b46c0f82000080080c100e43c0c00340c500500c4014040d1684460480048070310401e0b51b007411918659843c00c445200d00c0800604008028018400082c0c0c9814010802140c16045da00c0740103070010700c010000554007904079020749006000212086090280c007102e9402040d1006000c00d100040200700110b50030f1040c060711200342d1901d010a800c2071841c506034090303304030900800c1c144814911500c6c2c112984d990340c40004e0304440c040c4862038000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 306928282 1250 306927032 306927043
    0x14060303121b0904050c120a1107110d1208010e01060203070b04031d1f030b04021806030405160b0721020c041806020f0406090906060f08220303050603010c030603020a1e08 76
    0x28011b0000d80002c401580d40400107107258030122024003081500c0c80160080041d100d240c1c0010300207100000c4c200310550300d007802101c1282d0030216400e900856031030083c100b20020b024442c040302c0107000000b541480001111180b5034080c80140540c1c940380d4041e15062080014a201e09002030003030102d640b035621b51700c85141d156400e04844440000350180484d404100040d006900400c560310801d40d040c400040035a4003a107c00b55a41e840d0701b020381c101a01801900819008218000350b40b5911901522100d802908043d16000300710b221944050024040700d405604040364840c1c0034039081e030002508078001c00000703c4040459544a040368010808440e0308200411b0138807100741d001c480440504100c0e036040214900f40762001e07011141f8104030200b080707580000900001008030120541207031000d01c11014605901d40a800780c04202c0707926003c1d6181c650641603051103406003000303c9401606034164a410310b0705400b000f02417520101d490200042000908201c10413a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 306929532 1250 306928282 306928291
    0x160309050309040c26090604170c030703120501060512010510050408030d0606030c08010b19110a0506010503100908090d031b030305040b010e01060f0c05070b0d14060303121b090405 80
    0x580107240891086403c2c0b05c01010305042403200c0c40442000943c040001c0e40d16000358203c40f40c010f5a10b04d540605c0308030320030054607143d5404041000e004240d0402c1d50b03110b0700c1207040c800f0720081c1c0e295907003280c250140c3d101c5d584c651040c0301d004102030300f402d091142045c005480c00d18941919028840c0c5185d002c4d0368000360241d6151000c00295a140c8100800b0750010718007050315514008051040d0300076218201031101c0d0b501d10740c101040c01f07041c0004e03c81a010f03080c2c8525901c03504240e5140d07042449521300070f02500794825030b200311901c100c280c0e1550000c40d541c1002c104200f880070034030b042c1c0e80403800d00c4206880d4612400a60b1004014680f0a0360301190310700d01450100c201040c10b80c4100403000290005008154014407130b42c480a600346403c2c1218011410b20524002c1c1642c01604090f400003800a0b09240f69042409100c101a0054101e0b49808050507500d10480100019202204010490420a50900c1c2d845800c101e10400e0600400700000b5007214810b0380c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 306930782 1250 306929532 306929537
    0x9030203040825050a0e1603060f151101151403070902190201060b070b010909030c060515040b0d0302120f0c07140112060302032107061107150203160309050309040c 73
    0x55042c52100b00c0540000041c0c0400d07641745032210b242c100c0040e4985c034081d040c105004203c100740300c0c42611a82c4428003c2071104850b150060f44e40d5690400700d8902e80c3c4d00300c00162401000d00c4003180c14060213030303944220b10700c0104007860f20f400701e51803c0d4280599641030041400c0000c0444442c0060300207030040a420311000c500701da00c0030f80bc540c2c050303101100340d21050002101050046042d64110f6054540c0460100600c0c5011600e01c0c84c414002001c0919003814800100c00f003c50703050030030304140c404000d151040e00400003c0340000b600100141d1101042c43e100c004400301422814100c0c15400f801c1c602012915401c00b900c44d044071040c452030b03555103049503a101c5540c1d08602d8440c542004440d04540110341c0b00e41054841340044d481503010b501d00001d512040790b2156030850810098040031000c2c485441e032203580700f516100301da0030002e14849080c0c4212402140d078080040ca40100442c4158003500510301d0035a02408103015a00c6c07261158000d24120543c0703503 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 306932032 1250 306930782 306930823
    0x91809060f0f02040e13030c02060703021f05060114120412020a05010c0e01080601081501080c09181b030106020c0d080702040f0914010c02031c02130e06031b0102060604090302030408 81
    0x1403001c5c01591006183da04c603070f0700450b03040011941181040e602641c068400c556641003c3c102640742c0300c5a080346180100004d000310300724801903809580100b000740e0710040303142d0035403030005500c0c018408040900c007056400708001038050380401c0d1911800340199608800f0540343e45003140d00150044011407014240c0c0d40996903c0028164030440900301000103041410210100705014610141841601e9000c24990101001500d0703034148000d118207040a01c90503224411a020307156080303400c1403001c50303079a0390f42c1c0c805c1624141e0b2907030f40c010305002400c50100445107801007404e50300444c04001c4940980c40728011482c076014100004101d40101d0315103505184c00c41c1014035840e0340b400c07150008071603000c01110910f404401c50120000c814a010300000c0c40348802d9900200d130603100024018100f040200d1040c0c0c0c0840540e8041500074116202010400b86101e0041e08044000384462806a2105a07801d0180c41140d0410b07403582043e5107001d01103010191030741040c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 306933282 1250 306932032 306932039
    0x21801090218040207031d04060b040906080d020312070807051e0a020708010e0c091005030a120201241203021c1809020a0203030708130204021612091809060f0f0204 73
    0x400381100d102c0c0c00507507085261000c40e0f20020300c2c0c0a0a03e900e40b994004510580718143d030745401120180400c00340360742d605da90340c01c44080108124460a10240915075410303005038004010b84510084104c41d8281950741c44100300d8068000804c00c00c1845403e0080d83d00702d032641d040c00f030340300054032030710f140c1d55540e40300080d01e400010b9201107010f80c1803044021002c0c40114105505280039a00346d070607a1a00ca0780c00780d02d6001a04056094418111414148150880c442c1150f559a8008100704056580c10481c030b280e04803030442c0550810002000700c0d85c0948503998681d4004e105480016150504c00c140b8252000b02080c0020400c401c91800c2d1845184000010701c2c204c40210b02c0c218038404040e443e400020a11014055507500280d400b80a10000741480ca500810842d40c407401494900c03400703160b02c1010307031700c9107440480195520701451010064540c0c5a101d0228040e1765040c500c041c0900040442c1c03001d4035a100400940404c0c0100324181c103d503840561920b00703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 306934532 1250 306933282 306933307
    0x4030807020c12071401090302042307080402030d050903100903020601080709020408070e04140d02030d1a0114030709080a0b010801140c03011a0403052a040b0312070218010902 78
    0x2051060340c0304485100c2e48032401100044c800040715060780000b000003484a00590b8100c075940e202035000f90400c441ea0380181a140170420300c1503080b084c504869162518101e4001c081298000e401d5805400d0208916000354080d1003184001011074914014114110050310034046089016034010801440100010302414020300421001141130500c0c01c000d1a544410740d1058210400300340001c81c0600810601d50500328008504448441c81480b00003982c80d8098480441554500542441d001c7c2d050418103030041d505035191703582c0d4841c0e02021360180c0d20140901040c45081c01d0002503041080c0001181c5500481c4038001c203615242c50b040c203440240c440c40a80e41a80c60070058030001000583c0e0644200c07038828550300c500c240c00b2095a22450308043d149106414290038a4603109190a03040e002c90803003101c1540344103003408160783e04402010307816000101e040304802160300c081c000b910300040c07007101260002640464900d00a03001800c000746c0001c1c3c58054280c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 306935782 1250 306934532 306934543
    0x908220e010b07020a03060504020a05150c16030f060c12060e090f01060e15010909110919060e060310051f02061515070611040803120114061c0609050403080702 71
    0x303031800c1483c038002e0290f0015040244500000780303196600e6000c00c0944d12100e4644002d440301402c0c00c4e030802c00b8024400c6c404c0e00b003600110182e10400c2a5011402582d103402011290711001081c484140c0d56982d070040c040d00c290b80c40401c2a413410443c8013031854041c0c03200a1100b10580300241c00c1401c111401e004080041c1619a810100d042107a8003030511115032022010304091241142003004031400c3c00c065120308170f0755043c004114808505d040c001d00b000c1c00c04980c40c07503103c01101c00903412550700d4442c003004104191808043c070f0408000460340305c0407440b41d03418040e40781c0e070010745a80c400d054000d100d83e020f546c460301e48940412500b070700304401d03901840c02254600e00146058410b00403640c442600414508100a215000886507110f161401034440e41c95182d400c1d034940020000703400300b880003000091140b00a2201e40c122240142696280c4101e48a510000c071080c02520025a6a01d4400140f1607049106103030080d84a6035860f4424180700000a01c0d05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 306937032 1250 306935782 306935789
    0x2e2d020601090b0603061c06090c150215010504020d270c08030f040312020a2003070906050a21050303010b120a050708042901090c08071b03030908220e01 68
    0xb00d2800180c90941d41d1110142c96210000729120058080d16440110407130004620003031240b801c03d0806d07001c0000b100e41c013400b90f9028040c100d03440a00c40c03000700d980d50481e1302101641000080144000c2c00c0c541c0051560480e41c82c0e010826200102ea8a80b20f4401301d4021880342c1038a040d684100807001c1120f0009119600045040c5440318080b1159403103907100040c064600d5080d01c01145000380010b9901940001c150641c5403c2001c00d031300c5020752614018802c0c0207002c0086000101481360005850000e054032083ca800e00e524090309105060b007003200c6510010070382e400103800f0801103000c0c0404101458907440c0005000c41c0740e0350081c1000520508000400000a84c030940d10740d07000790000385000c24a10030032801024a80c4a060402c401a20040040358000554014144070350143d03503040f0442d654501c1c00c0300c210542e0a540d084203c2c8a003903040200380300f6045201c074180a1165640b401500d6001c80c0803004211082156209903903004210b800552094031780103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 306938282 1250 306937032 306937049
    0x4030e03330c04180507030e151807060207030b07030e030a021b09010311130b0d1103100501030c030b1e0403030b01030509010c1b170309030c0c2e2d020601 69
    0x501e4140081e16241800c07203004d601c00ca0307546900088995100c1d070072a240041980051300d64044083c0000c45051404079546d420f030402c0c20008284d000800654602200c12640c081c080d801d0a5a94a008034400504258105512054034090b0315000b40020134540310180c0042000303001040c035807044c00c8d10030a64070b4400c5159a0040000c100078804078020b100e012503910069803181d110341c3c0001c14070083c000740c02c400082000c10811071020b00f82120581c0071400c40c1c2d90180080c010209a50003404010403032000300008100049502c00b00c0d41d00b025280c620040c0c079100c08440350b84540b5048505500080e00c41300079401550301441107680203502d0070f0003031041841c4004042c00b0400044004119488802842010702020790f0110300c1800c2801443c81d541e050282c0c22669036085141000c41d28090701c0c4c590050780c0b80440c4117800700c4e00880c200320701d201841044400d100b102174030600203100c5030700790380f10103240c0031407110300e03410b200c4d08505c01d8101810b40002e00d450030503080b4010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 306939532 1250 306938282 306938287
    0xf0e03040806150d12080712110417010c0507241503140606011d0301020d1503021801030f06050a0e120c070e01030503190c1401020304030f1704030e03330c 69
    0x4100c5c240750752401103480c1d003045681c5840f10103003204c43c0e040200516420314604566010649a114010421200d039000040000901802a6400c1b00d01e51090704000c100100308880008044069015101d41000500710b00c1600e06110740301a03c40c81e00340000c4409483c9401c8c010817011030340e0b02d1050701424005041c1e030b280820020301002501488000000110200f0000c0303540c00750100e5424002c01002403080c2d0000483daa0180d4896010803841000c41075201104030000b2441d1a0490b42c002007100c030328800070b0f15130b40b00911018111075402c46d16040f108d045681c003008410602e0709003030f0784103690714804840a4105078040d00505040c0340c00c00c00400c00328600000303440c044031529400000f02210b103d000e59008880703030402402a51a014070312a0100c1c1076010f144514001d071520525081c02d04ca040b030f010b407903a4041c6405059150702041c0464030600800e1800503000d0200c420741000c0311155554030422261030113504821044c500c078030389034050642e80c00101c0e13010542d0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 306940782 1250 306939532 306939559
    0xd14060c04030311010911091f08060406180312020304060204080a0f030815010203090613050901090f150302130c030b0613050a140d060e03090a120c06210f0e0304080615 75
    0x520121507500c0242306905101c0440c6a4041c14042421240e0041d80d074849200da4603030b03030300d9200e03403040310141c0300d1920305248010504030350407007015400da042c1d03107a0180701c01c0c80e0219002900090006c0e11820b50a120105075402c1c00c011418506009140410703503a26285001040064020480300d213181c50720450384440d0340c0000a90300c43d80c204039480746d1101c90742803604401040643c4929030012540c4000a0901501e80c0402c040c0c1113944410f000c6500082944111882035200c029044000e181c1004140e040690068401c00d0b018500403605640801c0000d9050f0071000e10f018104844240c20415441c181366034200414159034201c1c01400030310001825210001000b40c03c03d901c5218010002c1c40034011641e0301c0c40000d200742c242a844200e01c0ba4142c10606040320728004568010900c2409500e01d03039101008003000340c10010703821541d83c000d859030751030501d0310a44545003184041e100b403016202611107070000b486140741085010100042c0c00098038044c400180c5900e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 306942032 1250 306940782 306940793
    0xc320604090522120207081f020c0708060c040509090105060114160c06030906050f150f0112020403060b100302090607120e03060114130b0306060d14060c040303110109 74
    0x150100c0e2052a0700042c0341c0e0b512294182c410600c4403440352000c103d03454450070030031140707401d1546100c1507084843e45a101c0d2a82640c03081c140190400709580c24032038075110380543e0000c01038954500d0584151070390b90580c007440c1c003c1c10303125405040c402003818819410003a06031648814410004e1080742882c000281540780f0310348407035400080008030300711400c0411895070700d00c0d41c0c4104244030040e5503040080040c0606001210708509281c0840c6640c2100c03040a030045110007240e81500d440c41c03041201e0783c008268840c0c140060760b290200e4520760351014000035809021301081d00c20740041042041303c40384060000303040c0305000412698441e00190f49c200d583c0705900700e142050b4a00161000703040d40180ba0352504c156400880c4d074081c26510703062041015185d11a048882d9a203e00c242d4506428142c0c040e03203e0000034649240c510765504056002d50941d03150500030000399814940f01b156810111480090200708069005e03102000740711525001b04043d61041d5241c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 306943282 1250 306942032 306942037
    0x30c0c03030f030c0717031918020a050922060b0f030307110904060608010c0c060b0102030a020a0803060613090c0e0906060a0809010f1812030c0f0f0c0c3206 70
    0x214222050205d442c60070070582810180c440080c24000c1030303c03803800440e50034000c000c8000b03c5128a0818003500034240400105c00c0742294010841800340f4204070510a07408802441d0140c43c0a5080484122813410079034914910300a42020920401c08010301c881a1803c03100540a0b5000300608004605240003050107102c044415042c0d035100c45c1080c03009451a03030080c0800d94038200340a40aa0780040a031040240304a50034408010201c00580e1207015049030f502c090b80003000a0070003d40c0d20001594042001007aa6081000e4000110059505500309008940d07885943c007030429040025106d500004640301030461510001250342800f403d04e0304006d02544102003a0b01c4d880a4020000102c00a00d0422035041c40024502408031038010541c0c103542ca0000220703989110307000740001c80c0d48507283d8184401052030100c030224208942d01040180071880d0314001030100350000000c102e481900034511680601d2003078181c002c0443c000700900800442c0040d912100d05 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 306944532 1250 306943282 306943291
    0xc1008070801230a060509030f0601140d05120f0c07090504150902032b030b040b0108070c08070512120604060f060e040204090e0a0b100e061302070b09030c0c03030f03 74
    0x754042800c01e0402c4092003c2001a15910640050380072030030980c02000742048500c11002c8911021038a80c0d190b84800080c0202007807040b404a40050604048100c10305151041c811100038030290203064900750041180f003100b0041c0001c40360340103041085100701803c26060100080d007420368500d92070100c0061908a525120094403040d545d05101502000d150804a5003590100c8102d0b01180300100c1d0407500802d1400c421107107582000d1055503005507040c3c644501940b51803a00f03903000c4d18041411120350b6004c10001c1700061052212030880d880038942242c850016001400351290700408160145150080801201e40003140e06000c81e02725040c64542e01c00000d011801074819a08041c4280b4200071150744000300c00107805c0c001c0d5014152041d00c0da00c4881800398000b44510603804500c03e600086a12854914581101201650030040c9081740c3c0d80e81d58244e41004543c900403641001c40c41d20020f4806011b210341c8548114095031a0403031080c2071004500002e403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 306945782 1250 306944532 306944549
    0x6091e0d1103130b0405010f020c0d0b0415020d020d06050607030c120311040b12011d04230f0601150c031e02070803030f1f0608150f040c020c1008070801 68
    0x251880c44500d09000f100c02c0d00c154840d4840d0600d8890303560140c0c44c0d00174410507000074000300107000b000303102040381d0455000060400032000070b0f980352440051000380c001d0f42c0c11400341200d2494140c15100804200d0ba10000140c5c4440f00000300408451103a0701c80340c0150000c03c001c03000654021440065954001043c2d0b42c643c403039050071802400d40007068800040c00080108089070040003034a403080125103440413a130b8a854981e9030715404400718180c0f01c104400840d0000d45014410200e6008061542c070002c00b0640703100385005a45603981e0065004040180040210b01c20303159580001e41c142484841403a680041804407241c54030a8030380790718003260264600c00c0c0114401070003c03100716030f164240040203120301071003602d00702d0343c0c840000c01c422404120303030b40500e0031202e50307403540c130516a03d01c0b4258200d11000d41c1002da01008404e2159041c0d6194419007145800650090048a9a0100341308005100c801b0540504c0410000c1204059011403150b06545211 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 306947032 1250 306945782 306945797
    0x60a0b03010c031112220501060e06011418041503260901050915130b040f080d050405060702040f0c0905031605030a03050a0201090b0106080402280504090f060204060206091e0d 78
    0x201c4006c00c100002c1103d402c44644201802414080b054020005840214544011b152140c0c2c0054402001071301a80049800911a4441b0071443c641c4096400501401c08144039140f8408105103044a0700204d42d248456030861a90400420035403d8007069103101d00e152280c0b810010700b0324040c03811145c0c0f08254103030895501c04c05540c191282e50a0140d0907250325516652410741c2c50308a801002505040020001002680082c07002440b01150b11124601420f01040c8641a803208005030303003081c0c9800d00741c8103d28282c400c0c0700180810340e907190781d100c2c02c100406003003d2032207099120f00320001c0d0007804039603400f00301807e90a602d82015a079402210100782e000d80134a08010780a9100c61000040050f0020b80c80341c404d42c400c0301d5070422810482440311048900741060451100142c8046c08542081e510540301140258110f81294000ea640c0710240d9121350071100068000d1418014000820050390709045080024400004950280d859403407000c1c0003030b581049440c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 306948282 1250 306947032 306947041
    0xb010813140d02030702010f1b120c02030708030a0e0904050c0405040f080a090608070528020a050105010803070b090607080a02070c0e0f0f22020d0c0503060a0b03010c031112 77
    0x300c9441500070000d4020350394009448140079403a07800071030b01a408170392035207841c1400d24483c044c4001c6020001d041035030085095251701c02c410810344441c10500503110800000f581d02085000010001a001550b071440c0984009104010300c582060141c3c44040610000132000700381c0d5400700f0000d43d0002003603036407400c02d001c0004c04c0800240043c030b000510068030701c1c3d100100748291403158441c00c0a90703ca00c2c208444038400c0382c1c03043ca0100b9480400e0f51210148407000c24100200c0d1049072881d18113078450307a003107980a901800300399100103009800c00400685490780300c828240034001c40d06d0003036805014608000d00340c10110303a000444900b04900001914003502c44a02c000000c1c0c80c2c003010f40b000d811000c0e5105c0c00b4100d0010f0020380c4c080007030b04101000d81a02e02c18100c29040541c28010f40d040c10840403070744100c00c1e541c0400d0740c1e1010440310388280c0866074045201114201810700310748860310300c40109420071710030304a4043e80300211803001c9101340448a00d5541c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 306949532 1250 306948282 306948293
    0x2003070f09020901050417030403030e220c020f0f0102031501020d090b0d0603080a020606011409010f080c0f03090d2d0e030a060c11060f010f05090c0c0307140d030b010813 76
    0x10701d420804005a4a47c201c0e0700002d000000707001a244a6100c105100d075105041120401000440c5c1c0307030b85003100000020600742e90300a001460240c4c01101d070a0031450000707905100c407612401003503030360100402c0007000b4500b0a84400d03003402e001500c072a85410500809081c1c41e8040c44160314400244d10500000f1759101a0003507400040b0f00b030300d0b013501450081d01d40b5010b4aa13240022150b882d04404112a441140c10f5081e05856002441d500c08000351138003038005042480500c1c043c8010780080c0c1c405070045104500020150060501c203a4010301902c11224203103607c401c401e9802a5a0341c0b05072100024403d041c00c00c03a80452850000910740005c10100800d08d5040c100c1c4500e540742c000c0341e050010322042c410340380c00d0317966440d00c5024244244900381322103400e041d04014604182c0c4100f80c1008801c41400c3c41c0401741d00070390345154090308080305c0d841070f000480e01280c0d9052106900c1c00e159480c047c0040d440160000b050070700c02a1040c4540c03103520b445582000b6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 306950782 1250 306949532 306949537
    0x1f14010509280207150b010e0a0909050f060a150e01080718090f050601210b0105010804030c0b0c03010302130b0f120309030a080c0708190b060103182003070f0902090105 75
    0x50305502559900000e15040c060310505805c0001d00c1c609100071405198007a100c0048505006803500303031624034105d1818050b1030048016a0f15010f0b0070303a03204507040248121481485954404106500d403806c0526242800d0b5102440d035841560040c003d125010564034201c4454032500e40340c0140030312842c0024001038200404000710100354004000700400e825040b6420000d03840c50281d80d102c15440c800031307a000010f10038070840005004079801500040d4200b406883d1040390060503941d180304801c000d8030100c148800c0403004204600e8108124030029004150a0080700c01c503801080307541d80b0382e52125100c0c4804103001c10b481c200c00c00a42d00c1001c0300408640c50803102c2d00300307195194014010200940144c41b004580300900054201c0ca801e0200c80d040401d404031b4032540549000035100c2c80c10183c50f0116141d1441017440b0500f480c5004070800b44010380e55201c82d03510181d504c2240380c02078000100c20026130211121940803619980805680d910051004803401e1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 306952032 1250 306950782 306950851
    0x819050c0709230406060e010807030201021f15030501091709030a0b07140d0b0f0a05010f140904020c061501030c05070201210921090521010e1f14010509 68
    0x1400020003080c000c11b500300d10100d42e200b08011402c0d0740c03201945900c5e02418000a400759001720707004200f2889100b0100e24000e03007500b00040aa0000907400c07100007140d8400c1d0303126034442c035220042c403800b9168864410600d00e0f1403440c2c01103141c08a522121201c0002e0300003084c500c00118841c0c00765100004542c9030480c01030703543c203c0c5229400144480e0b24024050110300c0445034943c14000d0301981550016110010034010388441100c2c400b8483c100c0a20040d010310881d40305854500144c04030101e42c40152047e0300e8100405904040800d02143c10107040525007110250414121a003854081c41c02c4044200d40400c4910404240d0000c40405843c0121600c18008202c00038441d848882d5203181d5440103682d0b08455400351030280325031207020040d0241900030160035814204800c03000100d004140d0050081c1042c052500c6040d647c1c0c2085218451181e441c41a10b0710142521841c507540e50422000c41c240210007800841c840d06000301c100c2e40d0b98448050601c40 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 306953282 1250 306952032 306952091
    0x50f0d0201110115030c091103060d03050c0d0f0813030905060723060609070908100b030a1a090f0102070b0a240b12060f012c06070819050c0709 64
    0x14000308880c542202c544c91005031640205c40c140860340c24072a0080040c54000d00030070340d0454446a0070040401901e0204400b0300c141005075040030344042c014080d1140d9152200c83d451a89040301030002d0b20001e00c01c0c1207884440100c080041e03049048401910300907500140c61b08000c1c03420001c42101d804040700c40800c01d00a0300c6007214001601481848160f5006d02c2c0764413201c105907050b20090045c100a5000542d801e6183c02c107070f51002c807440c00020704642c3c0d51680c64940c2d0003808069000c55600c0d241090401001d440d003000024241854038000714a0590390f41c031214108000a0440e40d085a10390100200c00c030800746407000c0c5041d485462007000c0e541c0740c800058582c0f040b4001d105002c042e000180240c40d200c500c207080d42070181c490043c0d8218102c2004a00e0b034000701d640c6905002c55041006a850b09030161111070311441020fa80c82d041100c45001080701031914408100c01000150801440400c10604944440001060b00b1201500b0840008400f030500d040c2e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 306954532 1250 306953282 306953291
    0xd030216080318010b0618010f090b160201020c060408060105060c01090b0702030703030609050c07121b030e03120306010c0f0213020d0c08010608010b07140c060a05030708060901050f0d02011101 86
    0x300700c403c544060700c2c050f02c9040208080d5070040e061101d80d000701d84070302410b104869060301080d4020444069000c000f0320340042990f84410318202280c00540c050f42c174506001c51401b08650301080001c0643e00c040701c60fa800c06140c841d03107907954501400742c1070103260301107030302c00c0310380003d40203201d1243c0e01452201c1a4074020400030341d660421141034000034200000094007400c03a1003668016819403d80510b0001c07a520342e05284441d100101040217400481120114200708210305114407035550081c15a0109081500d80308a000528072a0f031802c200380f14039603800c031030702d469030f15404400780410b9103007400001c4140f0451403410404500025a4a196442a600024686103039489209a0b642c039a44c04482441c02401290051034040002c140030075804140c15a005142c0401c4402c0078140b24080399031500039101c050007107440032050003021034210a050f90700000645510303100b90701d8076000520211030b40c824240140c03000074280c01035921400ca8180c6000727540f0020311 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 306955782 1250 306954532 306954541
    0x30d2703080a1404020604140a08010c0e041d0616020111030103060b030d0201091106180d03050c0d031a0913060509060a0e0a120806030304030f05060123030d0302160803 75
    0xc0058034115410342c9078078503003540f6000a45401c4061405a030300a46518101800d04070843c2e10360000c2600c0300c1c1d00c24103003980098045403d0140b40c015010565480007045d03c19030502084e80c03002c02c4032440c110100202036a020388006885540702e46010010010f000c0200010381c01003404621142c0c0c8071400000200500c0010303081051003420580803940042d404140481c04c03034002d04001821401c45600300c603103030320742800030741030031a1080d2460158940344000600052440d0404802107880401c071410807510a200e28449140541001d210304061002d00308140c49544581e640300e200340e000852a2140800b0f0203059240e84100308000d82d0910100503903070b59000315100840d050801d2440204064040b4129003050740c0250768040d2098170000545034451300800070798141c0700600c030000105a102c1c8440e0911070081b000b0741507650500d5082140081142c50300e8042044411581c2c05584000481c1c0d11040c401d490300603180c0302514208441c00740c5105025004132000700511 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 306957032 1250 306955782 306955787
    0x2060c06010920070c0e0603030903150603162114010e01090203010501080313141f0305040516081f02040506281b0b07031b020d0e0909030d2703 64
    0x8004071680c40b50024000420014115030a1040c4c0c40020301250850004014142108413225003050004041c0d9040054083c082880d0200d600800b020058400e8244207a505051040100040c1c980325043c030700314204004040f46002e40e10066000040c014200010320007105907001c0c080702400000d0040400100003a8042c0c20304640030303482540f0305400043d480750004210b0318130020300e41805003030300c1c1307080341d08140c1d250340025060300110311256452515042120313901c494511070320b0010b024202402c1c4036141604030302c4030703900f00d001180040c000c42c01c0019105681c04201c04e09600c10045904140020b8020f50b48800c0d00414045400c25500f2400c400b07501082d07410364160780308074103580001c4800c5c014207405030b10f103241ca040c000c4d00070031f627106000b075840f840074200490300100b81c0000169410400d644140160484801121183d0340100c07103620200b8104d8040c640d90030302200c081e4803485440300b000b0249036100c419081c803206656111180c40d90a003c0030601c02d6032030601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 306958282 1250 306957032 306957041
    0x320409050d03050c040f03020f060706060b121b1812031b0c0603041a07020307020d06020910080c03011e15021501080a0b0703020a21020a020f01052202060c060109 72
    0x40c080400c0c20000080d84c3c0c40c0750760041c0c40171903050883d220b50a9186800b80019107403203107045078000ea020000701004c1030790350103040000e00700f00d81b640f60b81d035040d900100310141d4094820301c0c403c200c40140401c40b228483c15100084005c49804185400010000d8188800b5070f50b0480f0030b010110f03d01c03007803800701d480e500c1d11080c1540035141420f4044042100510084a00928000403200701105400e07600201c0e03640f01ca50f0b80103ca250182d030740c00181d040307210b1400480380355400240010160a000d8102c96050401d0b0a20b44005d04140300b003c1042e000c140549440911041103180c50361030480d5800d0b00810013030403100b507a0800d40000030b44858820802070b6910101d10000100c040000034801c4005800c507141d485640c070340a030110003961007681c0c441d01300300c0c2c401074950f00e11944980320a0a04000c2100503600c080c03c01000c0c0c01c0c5040d07241c0c6540640d24000c10800c41d020303428084540703441d82c1e51070303124510001e10025141d806113039180d040e9881030400114038100290300 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 306959532 1250 306958282 306958303
    0xf02120a0227030a0b0c0f03250c030e1003090f0c3308101d150103020f09150705030c07030c0b2a210d0605060432040905 54
    0x210b4110012400d00300412516050032250590701c10b40028010500014185420400092100b840d03c011302c0b4001d10290001d4448200141007411020080b4141d490012a03804880c100041035076125140075042400c1408524041d54840801280c164400c0d40b143d00c1442d0f100d203030441440414100107090288a010b40000b800300404110840071082100b0028208000d040c0424645141401c40b05040041d01c01d240c4000d00480200e15040d00060720440c43d254403503105800c2c50b0540c429124044441100d42c1070605c100216201c000341c810071203c950382c0a0760811516031002c42402924840e07050050401d00000c42c001c1c1703035440040b4504003124003c0c6001e100326921012074218511565074580b9035920b044a0102448401d078541c07030401040c8000b91422140d030050002c9030300110403c4c448403482c0c0062280d402101912130500070b807005444880c142030400b112101c1000100c03041c400c0c0c3c0c03040713500105890420202072050750080908107100c4881303e4a041641e64000e00c2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 306960782 1250 306959532 306959557
    0x90607060b0a060c170c070e010803070c05010f0905150912060405060901231005061902060c0f03040209040813091e0504171e04060903120302041203030f02120a02 72
    0x6100151103441078071380c481d08540203100c03403000c000c2501801400e07034400341401646005101002824002034201c0a00920140014660700c224500e00b4164004460700b00038103111600c040c40319a96884400d00781910426518454171080543c140001c0e40034441905a1042c200c0f0350001c03d48001183c40b501480c070403004c6491540f51401c4090aa80a1440c4400c06150141010700c01d402c450b1304564110496a5881c1d02c02601e0702e000c901c4941c4012150903126211078625a20154100019030740b05032441c2040e41807000940000e4003d220251001c1c6c0300e03d0f2a54042801d0040340c8048030024042a08442e401d03640c3d50605002a0015640c502c6071000681c0060090031458001d66104550203c0d40244000b4609d0000c1e96036005041a58000042004494540502100104041c091644440140c00c1c550718000c990225001a00c42c1018018042006100b03141109003540710340c5404d0108416a4004a0400038003a022940d03214800c0c00c02032160311241580205030f12500341c1d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 306962032 1250 306960782 306960799
    0x18011103040302010c060f090f08130f23011101020d050f0105121c020c0d061d0f0d20012409111801050405030706080108100b010503060f0402090607060b 68
    0x28088280c036805103110103804a500328103010b00182e0a64420703040315a2a10002641b1882d81c1c4840d4450454010b0031070707140d040014860003521000c240c000082000301b1010300014106046010741580111304031000701010400c9000e282e000301120350a0766407080086454034035451504024010031380d16030a6840282c0c00200d20360a01d9803540ba44e09031010014800d040c1200600c04d202c401c0c60400740118011940918490790768541ca0f41051402100041b908054511b00a00c06c00a00450740007a40d207c1452020325040c0401d10350599074030b034100602c0c078642260700002403240701030281d40c45520300303114000c804051110094003076040f032900300b982580310f81d1031904039800d040c0800d103510340030302c044c0f0910403d44620280d24401854000d042030358a0300400d14007030041d005540880c20030001400760b841c003040041d00742803c1e918184108000304001911511010300041e0041d0080d03055038500d0303102c6404840c101c150241c0b102e583e0b200141060801009410202846003414 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 306963282 1250 306962032 306962057
    0x40306110711220f06050f0103050603150c070204020a030519060b04140406030b0705041a03040f08070201090e0a09170f2d0a120c090b0d0f0f021801 66
    0x3810140c0d194141e00545000d40031150104000410510041188651124a00240441c1c1d400d01904900f4101d0f10070106a1a040c681000017088100880c1d5041624150070403c40d45c0c0d0014070718807075010340070780200e082e244c1090b804072600c5284000f80d00a030001580d18540c40e890b60040c4e01c00d400c0ca06500b10141440307160348040ea4114818104a40001d010034060b4245d204000607000c40014400034205550b07984001c950241210107102189000c90100412506100c1c030071506541910b0081c42d42c5000d03940e0701c40c030103000403019064401c007017088402c590003004034502821030048020214501840e44101401c1c94120407100d030443c804100544902c94000d44a1500380e511000f801c001c51152500800d061080c3d600d0804062856038507038a0007600010042c9c1c40789560382000d055400b031605802c2d6106061130760101300c0346010400c40201801c080d85d1041c03146c010003190840e014440c041c05040c908050510151001035181c040008642303090300804001c5e02d170f0110a403403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 306964532 1250 306963282 306963311
    0xb06010807080a020a0302090a120201090b0c0a06020c0f0a2102060420030a060c0504050a080a0210030f1514030f0f030304110d052a0a050d0f02180c040306 69
    0x60030340e481c4001c41c00c02404110b0070f202580260500c803c0c82d141c01414005450005140c41107031368020300000d00b030040084159603109c400440030b4460840c0c850304d003440309003919079540c0f51490050300342e59020031101007411052110f0980c90744007504480c6031901e181807003061071860510f442400804140310007102c50000c950244100c1d001074a48540d5031103401c00400a0303140007a4150b050280c1c69141000440c02c2c400c0408a003620f685080d15242404248520540d050304284071130b510101144005070381c1c0202007015030030f5070714011131029400d0041c207025200c5c0186260b050110180081050141a58604e1000800710219038004c0d0b061404c05031112114104040300b900f04000040c00302e14400c1c50841a10300245c1040d411007415142c603800c20b42c0c0310700c052850b074049202d2001e010ba5002007010070094200da5081201d0700d04000640050748100005150428181c005019565089603410f80300d0450701c2c0c1c1171200c1c0340186494181b5885400103c2d00c0503d40010811400d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 306965782 1250 306964532 306964547
    0x16150b030714090a1808120f06040207080d0902061b03070614010e160512090303070905010203030c0405010819050f070801090501150305090f030c030c10020a1e0c020315040b0601 79
    0xa0000d45030b003c0c2500ca1003240740141c2581c044400000c1414541d80c0c00040d881c0e0000e110b0b42c1a000d0104080382041c1c58501c41d40700010700039501c0b80340180003200c0802c0c8603804988684140e40030000c1c03404040d10200f43c00e4043e003180242c41884a068905089501000030090203110b80c000b0030003005141030f88001401c081c0107c0082c1e61b0004d00181c2e090120080d004100c1c03005041c0a420202ea1426405680c1021541c0c16210340022003030010094004040c140603000900144d801c6103484039400307e0310b00651254504018100340441d40a500516443e10200c5080c4000e0003245030811003d01c1c80101641c0c1440040c80c4e5200014598180740f09070ba0503906596020001e11284510443c0580300140280d00c0034051610b008051140400c01040705521400c042c1d0f4480c010648500e040c01e49402001508500400682c50701990009107440c0c1c074000a061400e06002c448001c490988500c480203405100381c0c84880342c500c50301e10410388503502c00d04140004c1d41c0c1d004011207940703 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 306967032 1250 306965782 306965819
    0x60f010b0406050c0307020d11010f03091203020a050408030a18080a0b0612190308060415080a120c1502041a19112803020f2116150b0307 61
    0x4901404280809842400108080000740040301e06003046c0e030300001ca122605e43c20031110540840c0000c003240d60400745506460301d0741d04040000d4040d94540244000202c84841c0426500180000711107000300240c1e0098062002100d40707c221400018002c08550700460f5002c05407682c00143da1280003030080c0c3e40130350004481a0700d807588024406101c3c10070460070307020700540c0c1ca9543d40d480303408040c25125000350b0b105200c50074560140011507941244081c500c60848800b48010340000402501d0315900c1414203850b40c0485104031920820108010710007504811500000102c640140056840ca46503083c400108100c1c464a00d21680c000a4035940201e11020040d40c019604401c0040343d2106444500d055100c0500c0e00c846140040c2c12a07101d12002001419810001c0041c80b441100c010311801541c07150900f002210503110002c0b40200164408110100c00842000d29500024600740c0e07018001c218000b611007411600d001340320744030b4002481340b4400c4510105 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 306968282 1250 306967032 306967049
    0x6140a060c0303050c120a06030201030f090f02090618100f06260411030d050d060e130b04030302090a15030b030607140702030a122a03052203020a06090305060f01 72
    0x18000d4542e42600a464010a1455020b4003800040c00708252103440a1040704d069000013030903829480050700311000000700b100d001c0d10f46201c1c00f000800e0582c0d03421101c1e0b0110303001e605a566020001d19115170301a4104001d5a440040c04000010149020203440d4020b41d007050580d1148421166401e4150480722500c0030504000c4801b81510543c0da0028017a040d00c5818401c031030013003858501c920740035100082e00000c0c3c0d011020514441c100180c80c40f081e030103000c1d05104448842e8156482c0020301000b801c40045406c150003036044030351700200540003950499a03024000e82c144080e04040c0d021a081c40c0c030b489003a18021610512401c000d4442c02078070720101c0c03041034250b004080c080340c052140001c602c1c0400c00d0001841c0302d5080a07a6000403141c0c5201e180006030750700d14803070040c2c0c1800d12500c000103038100c0140c490004048144161b18400d90912041c0c1d002c607640b001c0d40003030700d0200108005d41e000c0428029a80103c040b5443ca84a1964241d5881d40905c0340f4000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 306969532 1250 306968282 306968297
    0x2060c03040c1203090b0327010e0726070f0914070807030c050c010906020301050a0b04080604080a0e130509070f0b040e0403050d0f0506090906040b010603050c0d0501080106140a06 80
    0xd00d01d0000f1928140603180c00d03100380352140e401c1002940b0548041610114040c844402150b06402c07120022104800034405120850510342e5190414011400061580400803200c00b4400340c0980b1481100400c881c0075958446091111006a00510740783e1420410381c800700341d100b400e841d8014060780c4d540c41810f45c1c82402c12402041034092220800c901000b8501d0031880034000c0b1550703203004100044c1e50f5450082084501c00140e840401d03092020b2104000e0300e0008642c0a90007904100340c1540e8040580088840b121002280e41e807049402040c8840403040303610080c4600da032001119040d68075000e400b02c1650241c4240702a50001700000d0101a00c18100560000c1c4a802d0150914130f810680390300352002003009180840d6102c040000c940360040340e072134225642c44007816950400b0340b2204010385050048806142d119000316007981003078000c803004001c5c005010000343d6100c2e001d0b41d01a1540d445040038944154603401c0700c5240540c000402c031103080d103a210 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 306970782 1250 306969532 306969539
    0x807051204030f090305011b020d1e0305220b06030c1806060d060b03130b0106080106120507021c0e03121216090f0602010c0201060f051c0203010e0102160302060c03040c 75
    0x40c2c240c01d100e04483c08104403e440000090000d00842414038040d00e05594100f80441d8001d15046440310100304020940d00315460600017103401c62081c1506281c0451180e440110f0081c4180306541401032070008084c2d66400e00002c00b0005014803001c0342542c141d0680401004040302c1d1100e129400d4818950114400b841c280005003075000c0c1c2404040b0780780782e584000b090b068008941681800032513040380303000c01c008101d40398003421142c02d0080195040000040000c005050000d000590b9400480c24090081120320591007050002c810000c00d4950004c21501d0303024001d42c048e00c603101c5403190300b1f984078050b10102c03c0781c20880c803481c0c0c0c0c803158440f04e06c1294161035014400340f8200410104000c0782034402038001a00003148408007458000c0c211081c0e644010005002000305104a81d102c0c190440c08810240c182d0f1481682c030300000b0300610300c400d007011302c540c03002802d8010010f40520014015000e9000e4480c01e17030301d03000c20201d90300c4200d40c01800d801c048001807 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 306972032 1250 306970782 306970787
    0x70c09060f05040506040e16090c020102030c040312020c0303030703140a050402100f0e03030406050301080606030d02030a05130f0f03020109150c0b0411030607030209041503170f0c07090606080705120403 90
    0x403540840001c03c046030069824607100e05040880c0c41c1b8410b0107802ca4400c1c451002703a4001c0c606d00b02d103540f00031032840c5490051089280542c2c0001042c4007200b02c5c05464243c402c004141c2c001c00010141e0b41d072400c1002c400340003490040d005210030b82048001901c6000305104051080740c000d040030b000a04c0d6035108458415200c42c0d401c040c46600d5103440d2a40d1002c00241000d0419034640690300d5040c800207030301d0200010b04142c070a0b800110f0104525070b000c4103940c1a110346090a03911517088441c070145256140d0000003600300d141c20f0000d050102090030108807070007a20381120068407100c1c6410311840c1d44041c0c1d008034805d41c0104000903180d112455200703000e290840780500304000003d003004010740e540400603401090f55000f9141500c01d01182c00550403112414500d56501c41c45140c81d5003441c2a2000004150409071402a4044a0108084205131500c071a01e920000004111a0141c0d01c001407000700012040d500a40407522200c5060081c00b9113569260b404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 306973282 1250 306972032 306972041
    0xa080711180a0b04050108060405150a022529010509130602070507080c03030403051011090a12060b010c020607021e03010212250503130816030302070c09060f0504 72
    0x165004000c000c210220303410000010750158a8450012504602190821040d2030781030b084000c1c0340c1c101e1424440000d000051980c540400100c2e0700b0744a545862004000b0700428400b03902021698041c2140010808150301c500d45c41401c0c00c5c9007603e183c2881000401b01d40a2540030550345c6001400b1902e02000e803107601107456407140345450307001d941d00d03410798000c100204c600d42e1200c0018409200c06104075200d141050b0015410586140c403412756400c172065000403030b51355901d0088030154050342215003080e4080d00a058065a8011504a102e114003081c0e030035600c0c0c604d007044998802caa4552000c0e8004001504003800e507001c22803160644800d03010080060b200c1c10130151402e00180c0405000489165102e1401915201304070480c440090034010703011a4044416070440103490b042305801110111200e1b4518208a65106404c0d94403c1002d42540d00020180e25030002c04070789101e00804101c2c2c0b40c0c0d600c2003509a5800e8081c4410f4070039002e0040c051414560710 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 306974532 1250 306973282 306973313
    0xa1410090b0d061802031509100203130b04050a050105070302030601050702090a060e090c030c0f0306041e0f060506130b0a270203010b09190305060103081c0f0204060306080a0807 79
    0x2c0410321075a03600d4600300c420141418010742d000f0b91054040d46000c3c0150700406040350000100c82c039021010315103504d1884411920143e000c0080780a44101d074036404c9946038009850741d0281841e05205980701d1010354101c40a40c2400002502c403482802540e002d0300044e12810300b010290740c00c00107480310041080d14102c0da034000c0081d000801c903c056000c3c0c850307100a440d100007110305041c100807a0114160180440012590064a000030141d6019410403100c1d100e40085410800c900608803a002d07280d680c48131100c0302488000e501040c090071084440c00d03066114094540255241c1446407039101e00406002c02c01c620880c2800c0d1602c1b101c40360b90380413803002410b04030308071b8200fa00041401e21001c00e2445850030803019440014a1081010a0070f510310350321540d4074071050200800c0010040789000050100182c070032144810848144036284542079010003c0d00980701e500300190a0800005081d00c022403004c82c003d40000115107000c5054882411054440c030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 306975782 1250 306974532 306974539
    0x62f03090d03050c0c0d0b15010c06110a08010e19020904111c11070c060e01030902040f0525050d0b0f03070f0e060f0906010f110a0302060a1410090b 66
    0x1000c10800d03924a455020314510a4403000e40304c0c401501480d190982c0100c64601401a0640c1d1074086070000f6a600c0e88225868088000741c0080c00041700d464445000c01011036052103910218092000043c04490850f40d44004060303a84901907001c0600c1a00c0c01c0f4100c0ca445003610900f40300f42d0f0020403030b1403400382000c5640c0c3c0a4060041c1c00740d000d50580300a44560000d13000e0080b6050003429090f00d015503505003452215180c0340710351000c0e40306003030038429811582c2040340d01a0300001e840d190018010890b8141003c2031802900e42240e22a200400501c0030510707010030080d18401108107a174a490401c40781c1c0d24410020034213000610391043e010410225555030400c02c610150400081c40c60a203860300c1410202c480003c0c1c4024450024400765011640300c01e9455603003d002442d1000c115a16481d0075070301c020703011031440d12038054031084000780b41d0001407060190005d40410840c8101030040350243d4141920b041e2400040d1100800901015802404c1c4c9a00700a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 306977032 1250 306975782 306975787
    0x13091a0f0415050a0308031b0310061805041b03050106020d121d0f160501030605010e04020d0908130e0c090306040209100e1303030f111b01091a040b01062f03 70
    0x248001010b403c1c06500c2146c12107000000c214110031005004e40d11003210220302c5040d402d040b102e80791451310307074081c0e001002000f081c074003031f0b03524445011801844050000c01000c00c1889900020a11200c0000d02107400c050002070042c0c070010f480b14400800c1d03a202c07400043d074102400e0142601c120040117405040400e0040340b0f030306001c030051400a690041a0201129421a2003207803e03a020724107052800c0805c000e581d81281e0713220051501114016551358203044208010b0509190103400b0450119815103450780f013844c1002680c2501049028554620000300464810740e0309080d090b400c5440810011f05204032056003007200e00c009046c2c0d0b25100c500d140e00c003590441c6d1003001c105110740034000781605413040d6031000c110110705110008000748464424483c0325000188500c00107500c5a840100b0341c4034405d0a035002101101a40c101c04007480c1c1c0031404c3c5d4050790185407000c0005055070003031890144000d600a41065440345800c141c03076205003403800c2d101050008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 306978282 1250 306977032 306977039
    0x80f1b0409151d120310140402070c0e19150b0c0a0f050c0108090604170f070c0b0301030b06180103081303050a0b0f01080f0601050d0606050613091a0f0415 69
    0x20303000c0c125445030344004141d034640f0b031100f9680c41e0400140408481060800c18440001060251403054807643e1004040301d03015580418000c0c0310702c00014200c04801000401e140b50155401130160402c5c04460300170310000706000040b00c04580003148880003919081000d0b2110b200502030354101081138880828950722070301c2d1414040700c1d040b40d80d50000071411800d5a005549a03400c000c0c00d40040400d46010342c0d404840e142c42d02030700010100042410440031035010100c440090b803100e07060102c190fa6030f420110540080c00111070180d6020000340080c100309548850440c04581111441d074650b0b242c3c08c001e68004084440183d0190601101040c01001100300c0706114001000c80d92038000480481d402040e00032206c160810901c802105000252445c155038040300d04801c10340042ca41540188130690245400000100d41d40b10a032001d0728000781219025042030003290290360424030185203544540b54404005400da05807400d080e0300c13032111f00c1100440d010b0712548 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 306979532 1250 306978282 306978323
    0x40302120106030b131208060d020f420c071202010302040e0103080705010b0301021603052a0d1d06030c0702130204090e0714010903020105031005090709080f1b0409 73
    0x504481903a28921700a54580820654880c06a0844040e00e01710315141806000682c5451402601030b2065a002c011a40e45999600352120110702d11141c1114403440740c0300041e0092803094000400d08040751134020f259400508446507404504040c100301403d20040280b4601d01d82c809070b042660a0101066052450701e140c0e001e14010800980c80f50514900f060035030f20002440e0340070341d0050100f05482582c6e000c2e12042a681410400c0c2c031003e90385480b03840c140c60001d00c0d01807440c600e0200c0009540106400300c0c00c1c2041d03642d415180c0032a00e5003448940c202c505030707900010704000103601000000054405103100900e40c8241820698451050b60003c0c3c0200035580d503241c2804c00300540810000d80100340d82c40c403480e00c869030440040c0a040b9688030182c180318002000814008600c643c030005440c2c000e1044016007002d03000202110711038002d4100c40d208648006014080028030f888d210750070441c034904010502c205100140911200c106d8000d0300311014080c4240c03 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 306980782 1250 306979532 306979553
    0x203030d0203090c0a150309020102030c010c0f09081507050702040906050901020a0e090603060f040f173007030f180803151002060a021308030c010c081b04030212010603 75
    0x800d0410150300e9090002e0f595040c0200501c80d40d2081041140c200581d80c603d040c0c803008010301b400c00084040440c00140d080d449110928011940f07490080c2040b60f07000648000000060303940c02c500503403034070b040c2039640c04a10320090030303405c58500140c03025120b90000d00060b403025101207402c1400d42d40e0041035420540d0341d003c0e42e03500802c0041005a1142403441e030348904403604406405c000012907203e07840034201310038950b283c03400682840084075024803401d82c8041452104078110a440c401e0f5000764108000112500301e0240c619407002030030386040d9281d0113440b641d42c0c0315620241c0081034a400c210319000e40318034000b00704600c0c5400d030020850080c5c0c2580d981c0d2403c011b648403900103490180d072080c55082c0c0141d0885a00046541d070024200c5401603541078440d008209040441d407240c3c08900c0000380009103031406400c41d080101345034032030400640b110104e07118512214404482020410b00c01000135103004884c0300302d21703880c1600006000c0d45a031980300c04031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 306982032 1250 306980782 306980797
    0xd0c050412050f1204060801030f02040e0706080601080a140f0403020f1e0d02010603120311040905040f030314010614070c050613030308130308011e24091d071b020303 74
    0x5411040380021415820301001c0120309030343d074005240506101007d4038624040c040a090701003103141c00c070704546031640300e1580749aa0701c00700c400655541030003c04e50300e0101c402e02c1c0019040d03400709140200310701458080b07070904a110384040e5120b200207524210011710503000c600c205014502c454406100e5440540b01c07400300c1d40300180b082040c0ca89002110410300c411a85001c004002007240810103c06d4140319140c04540d031100c0d25880d078005d0041d6004901c2d03144c5410706020070001c00340c03207080e40c82e842501c050091081401d4030044600091080d8000f0031203104200500482c100e000b403070f00358441c002c0c1c2980d55455030007007640342d0030040d0103491100040300c0c2071040c55003010742d02c1c5d40100c0e81148040c84040c05d80c0c00400d120740c180710741c1c540322141c000740300e4181400034a03100182c6805004055a0402a04c0001e60143c0030403801001c124415804215040080800711010701404444441c64544402c2165403858002000c2c40004400408c8001645c0600040c81071 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 306983282 1250 306982032 306982043
    0x30210030f0902061809010509071b03020106031a18010506031b0111010912080c0c1c12050c0d060b031b0703021e0a060c08090706081e0f1005150d0c050412 69
    0x102a170300c02402400b10060304005e10900c0f045c4100072110354030088030381c1800c814403d42c6e0301281103842c050740581500d4000901c91080285402002228080d050384560703a220504050801070100b0325017201c10a1f10001d030945c00010008100c9417503448110159003061411001e4880740b819021700b121400c0d00304a50036107500c0044000b05a119400c60f40201151080e640b40c6112451115503410165600c0e103e102100314004010700d0085c80c0d2451081c4d9810401e01c8145028000c1840c582d00c06640d0328005c524000c0c1c00324a440b5005c1c08e4034460f80000490500d00b50b01c0002c0c01c20a030b00100c5044085203c0c80600060388811418030402c05070780c0030000c02d035080b000c0c50988150f5201050580802c0b8002003003010296001885d4011111181030514032a2120401102da40d0300b0003504540c03400e8130605012030186010a543d100b404031428031a5110317100c4007005203c044080d81414203180501c040102815180d00080d110021810280e1501790b0b5039101407585040760304141c86 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 306984532 1250 306983282 306983317
    0x3050c0706051510080f150a09020d050402030d03110304080313080403030f03050f070215250e0405070c15020f04030f060203040620040b031305030c03040f050a030210030f090206 79
    0x52905101e4541013030760b512400c0409442ca40b40528043c011002001522801e01390020f00100341c6411500310080c2c141c000c010b65440d00707100c429001030101900d00300c3c0a40714000c46000b24602c01d1007800c010014402c803207031550710740361030b15940c0e40c0019000c1541c4142d0164860002148000107100440c840d40340c0700f044c1d050815000d8205c0d0001030803e1903290808041040b12a40071401c59420401410441c41d43c1d02e50b00b11040c0a1001c410094490088410140141c69041036200d48154030885040c01155650b4104441805c21504020103080044c00c000b40e040c462034025100d004c9001d40150308280c1d507a100c0c01d400e84915101600c0e01e5500108cc030052060380e000d005200b80d4154018040c00c012500c0c02e01d0244201c5c0300308038082c40b02002103100802111011f0010b141c003d02200c0d02d07140480d0302c480e103d0b4490310908180d0740d820f0300c00141c1e40c1011881e0500703d98004003102d88c0d0704100d41c0300303a014020704407411604e2503890f6078003070050703407000c014100c450741c241e0b442c41 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 306985782 1250 306984532 306984571
    0x301020406260714030901060e132a0b0a0507020402160203010b030a20030106181e09110108130209040b091209060711030709060e0a0506100207050103050c070605 72
    0x400707145102000e00b6107070840b0030402c01e015400c00b41d1000d8074040c0c500300341e580e40d0307659640724014000398002081e48403220041c070220704102e50001c410309000d800b01001025488040c90b0002044c0110f03514400440342d03040000c0d00540700074180e0003038541041803620740c40b903000904984c400210302c41154055030000e0150b04091084000d9a1400c1c8d00400e92550f5503114852600001c0c1140001c0c182ca000340701030281c0b030a4010070000e00d1050040030003c00020300c1032001d842000688042c0c43c5080035038540d800c1141c05070f81100c2da0171171100081c0104c0100110344e84540140000ba11040b01c443c5100161a841c110601c00c0b0301594182480b42804506641058440d80a0040d005014020740c0307540c0e5104800c884045a01034040249010312502013400e000c1c003540483c20103458540b001986045202c40c9900c40e1500000030025a5980400c010041e030124958100590210f401448070394001d52199030000e114a41060601c400356039140e0584008840282d6503911070385106 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 306987032 1250 306985782 306985817
    0x1080606061c0509160e06030a1403040b03091b0904030e060a030608031902071509140103200702030d05030c033402070504061703180d0f0506070801051203040b07050304050301020406 81
    0x4005012001c610140b1b03820f051002a0380d441071b00e000980079111038200007050a0341007007120000e040d003110040d1a40740c014182c680b2000061f511044240070b82c050340103e440c1c0010518841c9a040c0c40d0040a4200306c030500000d034225842040506903a10000304000100f0005010070103080c0140c0001c0000070907000b4145101a4002c01c01d10060a1125902e00c0c1c001c41b2040c00d07102122902d1010081e0700300100c0180c51035808040d014090002500303000801d40001b00320b050700990440352202c42590084801d403200b02c0d045c1100e00d4041c000f082c206e00060702c01c40c0743d4039400540303086d280070711682000b1118000c000c0c2201690162004001c507060900521004100c00700c490340320018101e900580b60301c0364003800d40403145000c405402030740d641049910b501d500011080c0c000c1d42d85180c040c2e0349001c182c80b010301142c0c50740d000250614182c40c1120001e20705501a50600e0324001c0c1010341908441d000300c0b558001403101040e80d4400344054001420141c0e038407840001c4002c41ca = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 306988282 1250 306987032 306987073
    0x90604050708010b060d0e030f041e051c030806181311060304080717040f1502010e0c0f0f1206070206160314040b04020402070c060207060e060301080606061c0509 72
    0xb242c01641498500d03241a42c41d481130350400594440301151540301c2d074044500b5031280106d0200c40601c049000b291800b91a0140c000301d4403201c0c1d60205840d11081084070084000c05c0e0417010b00318011218001a100b40c2d04150001c5020700841402d80f41d1140740210f20200b101c541c2040e4500075081400c0c051310b60720944000e8001e0b10030a1075402d00c1d85070509103115514014001c44002c0c0801600d0403a1b0340100c0e00241140e01c078001001c2d4942104821000c064801c1c1ca00541c2015112254021f010030742a070103150081c0701c621440343c440c0512950704580b5094950003003900c6102e243d5418140002071103000c2c5039010306010300e0901e000750924001d0301030b05810149009101111860f517444000d8200d80c000714024807555071440024080e21070810010030351030011500040c85900041c50b08241c81c83e9455a451800c2c0840510050b408240702d000d031241e103d4000320342c03603080210041c54100b401c50f001d040d00900300c0707110b030003504c20658203803c40798081034240302c820858806 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 306989532 1250 306988282 306988289
    0x10315060611060103060e070806070e010e0303090a0512010b0310091e0c091a03150a0f0218060a1404030f0b0c0f09090603100606200c1e030c090906040507 69
    0x1400340400507401c0b2041d81e00e0205010007481075651b0410700055a008000400090102108460f0149031400c1c1c020140b1081c00c0015000c222888018010740c0743c044281c1c0d42810000e02150700c10b80c44c0408000c2088100f00c0601625580e03209403181d2a101130000420181d885980810034206d585402d0704035000c212003091a10851050440020f006800d421003282c1005030302140c00000b003011800c070003442c1c07050150300d4850214a07a0b1004406588c3c0c034030685000404002c405458011030069100301105652411100760340c00086150002c007401070b21500380f8210140c0003500c0110041a44590015540c00a00300e4018007040300c40384c0c00642c4072120200590070040f80c510074482a00408811178803547d0120001a1140c030100f140d1220002e1809061001d44e540b00405022001d002040384d80c100c66501d0f0340d440c1000c0000d000703c100c0102402900f1100c00d03219020310784440c000b514561600608982095a9031240034050141004001828140c203003864a1490314807941e1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 306990782 1250 306989532 306989537
    0x10110114160c08190e0604061e050414011821060f0c050d0e1c09061d01050301051003020c03070809040e010504171e0f0c151902090301140103150606 66
    0x32030b40001200c2000344e810000824150050030001300c0c40545850000302e101e43e411500218001500d503030701001c00020400343d5028422010441e05003210180308901a0305a44034446410042d107511804403180703250074003200d440d849620786034a0705e0301c20095507940804011580c900c50500c0b109104184801d1a0404100117074203140102800724083c14106080c0e0541c0c0d1a0041c1c5488014025008034020102e44210302c8440110040c00704821400b03103c1c006a280b503e407005040c0030302001d1300351500584400d030650386840108103d42078040302d0380d01090f80920003c00c1c96034040000d04155803154054035203903801a424001241d41c1c0302c3c039000240e030404040c4404a84011030b043c1d560302035010815502c600401c6d1440742c10a0001c0b194071410b1001940ea030300e81c0800d4001d4001c0b02400c0d03007920350492404c1244114150250780e250356440c040000c181e8407580380c0c0d000f404884009800820f0102e00a12001c04c008803d034400e446090a0320700c9031035041524492032020701460b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 306992032 1250 306990782 306990797
    0x1204111c030801180b0409050d030e070803040b0307091d0103120e0d1502070b090606100c33020705010f290d03020c0306010b13090c0203091011011416 67
    0x381c600070074954040c401c40d05051411410600c803541c0c290170850007082c01a0040c000750516161142c1e5810100300c08800092030a40740d1540007201142900031100110001d41c141030a20b040c181c6682e102610b01004d10130441070000b04411031516948440c0594121600d680d131460800c05482e080b103811113402c210302c50012641036a2000210000a42c0001260642d50750003c0010003e10603450040d141c414500100684101e00080e0340b84900000e40b121a01d02c0003100080d2900d00c860ba00003080440d0240f81d01c01605c5902d00d0f001802da0115040c0c2415442c1c42041c030040b1b174003280058600d03075102c2e100555042c0a074001c002e1402058151500c2c00030311103203141003002d88180350602c1031a5100c070100906100301321002c15540d00500b510501c0d60756203981101c0c1d80c0b040c000240c00700e2255400141403803d0340314891081901d40c02a40ca40fa200201300000060000d03030501c00e01a92150101004000344244074074600303841c070000304509054030100c6900e40c400d9003640401c43c45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 306993282 1250 306992032 306992089
    0x20703121b0c05070b1b0c0d02030607030b01090b0a120507050412080319051602061f050906120106080d020712230705030a08180904050c15120411 65
    0x24500300300d01d45025441c100095180d986400350804241d64003c268035100400c004100700480c80090000c0d0f40180308079031080540e0b400b0711916048031b10000c0d60581004000a6006000342c020015280051420385105626107a07084030310742001140038001380da20f003480c1c51281c8213407040903007000c40c60405c1c900709071501221404240614000800302040440413402e1100c030400d4020b01c09a001ea8140030500d0840003682c56100365011040040c0324040200310310b5021048022840213011885000301420042031069585000d841180c02010304081d0941d43d800c02e102d85c5000d40030303100240940060b210030007440d000351900800303040d01060410350006900e22503141c0a92070000a8441003420604009040c1100703a03000c243c041c003410b1500380800c94103c1c010003400c25520a440811603000051020004040b640100954040145e148451901c0044030115181c4c0b0707000780d854100d0b45445000001d009075400c072043c0304020303001c030314914140442440f446c3c40000c418805114 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 306994532 1250 306993282 306993311
    0x1e0b1c050601321c0203070207090204050f0402070f0605090d0e0a08061b1605030703090e040b040204020903070f08060a0e2b1205150f0301060e041416080102070312 73
    0x20f802003140350b22031000648014100d00020382e07040760b06035013040c6665401d428050010354003c4403004014020f5035404604003a007842a942500c1c0c001e84205031143c1caa5007071100951101c4000d80e002c103141c000b4440010f010303000f40c6214000e01400b504000740c070034601610366005881c015100d014001014071480724001465584000a51001d4001145003101c1c007540c0e200c1d41c0001250034290b030310048280b040c00401480c00300d100303580364012a5514440302588280c1a94001e1101e04800c001c00c0142c6031a40141103504801810b40d44000c4d52112200c0c03010555a1080c800f68010303004005140500b40710302e03d000f0810f84003502008007c048213042895000f025505c009120803901c2d88150700c40d007140c82504400e10000c000d14142031400100140a141d240741c8070f60f02d03110303001103141018040c5500b101c08140008615850b16500e020423598804012200c91041c805017058042a20301d8410003407044d04001a0380e4046070500070092b45001c20591540c60804551011544 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 306995782 1250 306994532 306994577
    0x903020c09251707090e0601120213060201050f06010c050d050c0a0614090d1107141305071d0a03030f180506030106020c03010510030c1e0b1c050601 66
    0x200c111455001540c03100540c5480340040300e880e031080d4680101c50240030303801c810b803d0f10341034074030842031202c3c1d4030620211501ca080340100103210b030010010079000d500030f070101149024409000b5081602c00f000718803c240ea03c0d803080300140c1d19a0140501e41860b03a4000b07030000000c3c0b820180340c02454644d43e6813501a460340c2d00030003000041140100c941444950102940400144104002031110400686041d01c07854407034001c18000600c502c0c040c41420101d5144040908065850300b540500040c401c4220182c1244006040820700342207446202d200c0d003070584445050307200e881c62501550400c40c6015014802401d010700200e60010315060302010a803806220000000b2025000d032101903215a8001d072004c8008a0042e80204001c01c07003e070140c0c000c00c080e9450420000035000c0d10b200243c056113581c04240980000c1c150040764807402e0f02200c140b141c0e51600c00220550181500d441145241212100d103c07207103000e16a045802440d04030014502d25905600c4d06 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 306997032 1250 306995782 306995803
    0x11070c050603040f0b0403030b0102160602060a020c030403050304260307020604050409050a0b010308190302030c160c1814010608070f030203060f09040807060e0303041109060432070201090302 85
    0x381e0002c00040c0c2081091154100c42c2940b01200b15100d0070f25240150113042400702d51800350040a4522182c0c041400c47c0317000701e48665000f0040e0351510000c6000960100340b4420702804208004400705a0810040008011142009928032503031510030000e880c02200341a040d030000c0115002681c0da500c152010f5034000c4800007980700340d5141048c980029414000d041c001d0b4032000100780440726000d01681400060302e46c45600c2d007800110300324031080360324550301541404400c10072040c040b003854640f0b2082a00185071910b882204092076020100c0341103681d200d0706e49059008502c1e41c241d0042c404c1d414528a5800c1851024105011300080cbe4400c056011002449517600c090070300e5003a80010380b03004424186820b1070141903100f910b0a5404505103401c518802c2000022240703d181c10a00b0164213074420390400c1420300024001d0b991140e2031f01210151b0b00c41da01504078150340343c8031481120281141b032240a40c40010054825640b40132070040c080b0740c001c41c010115 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 306998282 1250 306997032 306997039
    0xa0203040e0a0e0f0604020913170307030204030803010f06020c0603060108190227030c010807020a03050a121a04110a052d0c030c07080601180e0c040e07030611070c05 74
    0xa948400592005000415070410248103a84e200c01484502180c0c4500690080e500d00e402c2d55a180380c4080c100f4110b22005140c1c0c8404c541507004180004082d6070860744d41e00d00549000c4d9680c0350001c05400a800c44c8900900b070090801299070100f04a80390340d1401d0b96087d0071340c82d201002a101102c014002e5400341034086031040d604030668126082d10800c990340304013050350210550301444665401074003c0c8a490800c3c52998000c01500e403041c0015402802082d22554044030181c1010401500340400d490390151003049500030407401a00c00c8032032012500d84a801c02c400d4034503002200c04002c00411004c41c0c5164418121500290407044800c085443d90450314001e00c0c60510b681c03240c03040422003000404000c80108500caa41408807000c0076109d9501d943c9903c020b00c03400f40c001c0000f883c0104050800d4202900300c40414007034035480c80e80c000200e01520a040ea800d0210b0308840c5e400d00401c00b551003034a140e5480c4584680c1070503038a580303442d1400500d0141610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 306999532 1250 306998282 306998309
    0x9080a03020705070915050108010f0b1b1014040308180601050f060d0203070306030506010f0605090913050706030c0f09031104050c0706230f06090114010c050105010f050103110a020304 82
    0x20301c0720802580c001003966174001c228800c0700c0c000d02c1c1d041050314001d032400181000000128000e10b1054030b426a4020f100940c503144550300d0323288800c2c2c0d2080030644d4a0140713840130440c240d030b640b04000300c03880d401b00000d02501c0c01c0d01d00102205401400d9429103000e82018074030807003002803800c0c15503206507914031542900c0f00010701070703010358541e940c1558000402c1104050340742d0003250480340310b8011603a0a9813202110300e00b28402c1d00404002800900442c0142d10b4034128081e04610200c5c40004003495644880c3d003031103095008540405c0c1c84030282100507501c080c007403600c1c88143c540700c10810f056a0343c104940da440d0003514842c0b034881c8003185414034810100c7d540d459010008005908250243c0b0f00c14403000f9100411802081000868405031003c2840c4100c40052003594160f080405440e004a000d01006040020f1040c071000082d80034481c2d00d000e000810042d0348080d01d010001401c1d0360803003402c00d000801c18044078003c0c540010644040d150010301c21b61 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307000782 1250 306999532 306999547
    0xe1e0708070908060907090605180a0510051309020118050d151805010c1d060d05100b270312070303050702030f0d1b09120822030c170109080a0302 65
    0x90b0b002a06070082c403400d0207220300780040b4400000301c0c801103904a24050101c5960b8501700050f61300d100c0c0703042002c003a203a0300041d00c0c2c40145d0b03c003d5214044140f03801c0000e0b01c4001141c400b103682c10701580c8682e40c45103040195078000040031604c200e1056040880ba0a0001041090380190302c020003561203550050310f141c00b203402a001e41c40104006103400080d50500314080c0c916a030f070140214814009200000c0e03084181480c9490001c0d20442c81d204240c81120700800000b0148555600c1440300410b04800c410005c00701d5604c20f11071007107101c0400580b01c618510000c400e510944c45158040078aa41c1030382542c012640600780090150340e030507410303400d5100e83d0a8400c140c0314001185001090709078008800c83d000f6010f00d801008200805035510b81d002c2c01900440c4d90403074400e200084003000104010103001041e00c40d040000d030a441604405504101c403610038920040c0020010103c280b034410030003500911106402c1c1d117600c00c01e4850b401000041540018518 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307002032 1250 307000782 307000787
    0x11120d0e030f151603050c090d05011506180e0708060d0c0f0e09010f090309120f1a04020102060c07020616050c090a0b010f0c050d03090c1e0e1e070807 67
    0x41c040080410252840d40d2090751203070700254400c0740c56000070f0300c2c00e00f08a03404c00e1003032040780d10641c1c0c100b01c3c06290008000401c9a10000301c03600322410340d02c0d40d400b9207010103c4c0c04044004d00d000d444001c10480d080001c1c854002541c0c001d0f0380b2103103415080140c9103900c2a8031540202c8180c8605140c18400d00305082e903145650481a8009e10100000600320340d00c1a40710700c03507000080200206110707001c0300c0c0c0c00e981880c5000b80004060210030700c01d5400c11041001c840344905040c0d40d0a81c0c16030364100c02602c40d0180790312200900001c010039940c05201182d03101c18198810b901e04142d41e40000c4050095400400c650700c00344003400c081001c200001c01c0310f88001880712580e843c0c1440e0745000780c0303141e40c84c41d030020b040c250002ca070003405110030525043d804030203484040b03210311085005001e031410680e0203500401002503030001030035020444100c2a96121062401e194070307a803018a0103072400004010307600c1002d500000b12608150005600e00c1c040c43c10b070701da40108 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307003282 1250 307002032 307002043
    0x80309030d02070305030711011404030503090f0106031a01050a0317160510060915030302070308300106080618040605060103020c030a0305010503070609080d21021611120d0e03 78
    0x8100510000d282d800b0b145c0c004002c2c0d84549001d0f511981c0881c0b841c3c40d56130a8603254a0ada02d0031481a50204002a0066005c1c40d80101c83c54200c1d0b40d5117a000041500351020356000341c40e0700b00760200c102c1c0e101c0380c0d02c21040d024140c181c500c50300d00e0745195540d90300e40c00c2689a0b001d2400000c20a44406114024070018158226080387d450200c10207228000f044144100c942141c5020580700c1c0c8091000e014008880c0c064000c0c184407441c50300c400c681c0358000862002c020317030341c840c0801765a0040b03d6a0501c2c88001c0021148660400601501154002c0e1803031b413141d548076101d54005ca60601d012036000303511600106c4c031521610700590290003603960400140c00301085030a1440e500d41d201038101d4104500b10740f4481d9440000307071044501d03801604c004d0b0300032041c1e01c46540c8c0540d5210081d07680032000c1112140e07c2c2c0c1e500702d04070317000850200f4030703014908140800c0c4440c200b41c49050050444040028101000f8001d41e2061101008000d00450f0106807606a409200 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307004532 1250 307003282 307003297
    0x1090b07020607021809010b0102010b0607030e180408040810020f04060e0d0209161409091b070b040b0712151206140a06150801050f220c030605010905010e0d08030903 74
    0x5004917508456828080800c00c65401449629221980300298414015843e0020004c1e05492a000442d00c040f9228450003a410317800c0004050382400007580481d026100d14098490340d80c0b91820300c046203040c5600b20288014140c01030010302108043c203011982212803a00703107581544c408101188281d0088807001c0d52010701c040800c0004440b08440c1d500f01c1b402d9940d6500704040b4000140014000d40c01c20300c4e0402c2d8080001030b00500d55550064100c000e0345a07035410b09240b9910b40071101e40c21642103d003104900144800f958001c0100900c1d2001c0c4e00c802c0c4031814012070384a40354005840769a60031036241e4000f00034000140d010604036164011018010b00c1e040850b880079128a1040c070f414416004882d400c0c031485a035005040e02e2005105a0301f40310340f6401c000b001e641141002c1e10030b103424002c10103e00c4041c4a070f0401c04069482c0424140d240c100050040ca5055000c641446100075480f6101e564130b01540323041c560b002c50350584035110032104501c0c6005016 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307005782 1250 307004532 307004539
    0x306010e2a0409060f1a030c042301140703081f030507090e0c0d08030c0d0e01020a020f1e03030105041505090106080a110406020c0907020f010911150901090b0702060702 75
    0x21a1000c90710140401082070301c102c100180111607981510740c401000c01d206036484491401040352400980c00000c580201214003018109601c3e01441d00c0080050300080c250240c001e842c174091960003c96103105040348041203400c084031910042c040010040904041d10100782420440503041c2100384c0103503401070115596981c40c1c081d94030080c0300c2c03041503c00381d2043c1c3c107280040340340811648110035070008160f803d6440e01c220303002c5160000d18115581036111042d0310740c8c0b21400d01c06030608660341d034000c01000101105690602034640e501c420380400b07400d50000400c80000841c0c1c11250241c0d00081c2c00322103508441c04030344268010a03800001c01c800000d915902c11003044c084c010800c42080500c00c070000d2400588035074411100941c00007030341943d85183c21841c641d48050103006466000b945810072500312901c00004541c41d0300302c50318900f098103003109107000303000c0d441c14828500300d0a0000030700080d03020310070183c5404000802504644681c1c1c01d44500c1075014 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307007032 1250 307005782 307005841
    0xc0e01060e0f04060b0403050a050106121a090a0609050615100e011b0609080307110a030e04051005120304033c0609120801031119140301020408240901050103020306010e 75
    0x8d2408544921003080103841c25030a01c803010920304042c841c040341c0994068080702d0060b1002c80d030b203900040c0c0100f4285d124061984200041100ca000c0d123907072148500054546841c2080c1c02c03458100c101e0000fa4045e5400b1a041d2900ca80c000ba14080303158002d080078071034055042050603d503c103c0d500100000c9c1400000410012140b000c0d40c02030301c40ea04c400082034110020f490b41c0d1100a80007400168001944207011b080030f600403600301802c01825219513466901042d0b5081443c0440003040c2d00015041003440540c800500004104d4110f00c0c240190103244020240030b1800350720001480b44800404002c0c6613800710001c1343d44150206a102141540981035683c01d100030340b00d940500c0104001440c2003c0b41c1c0e10181e05d00154800c0b441e0a202e04520040084001c19801d0f660070030010482540030080c0c03a0710103050941e402d900620101c10180c0d502c402400e07200c41d50781460010b20050380c000c2011415507007506880003456030b68a18510306ca01340d0341100c043c8400308 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307008282 1250 307007032 307007039
    0xf0702040f0207060c1d01090311030a050f0313060c0206040306050601110604110a05030f060a0f110408030702010e0303030906130c0312020c120c0603150f090709030c0e01060e0f04060b04 83
    0x69000040f41c03032116215030b041c6091040411b07800002c0c00300100e0029096410510009035800300c444950300d0064207c450565207030b65014500200800e0b2058158404620360007100103484100300503022900d050078a4030126800304800b4015408004c003c903071070f203000518903407041444103801060b82041340c5003802d050800c1f1004141c140e400901911000c0d4001c509414005a2002000502001094160b41b00245c480003000c10003e2f582c0425190a1860300b240740c070202910280034518091992888030b44005800420304c032500900039041071040ac032000c4000f2a4840d81321a4146441240c5402803500d031044242c143c00c001c007006080400ca03121640d001480c12203da40607945844602c40582a056079034410040042d03018408000146081090041d103001030b160152150b40c419141600194485404440040005030000c00030420b205880306800c000304411761440d00b00d035040040050a040c00140031034020014806590072945503980150f00034506102c0f15900d5945 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307009532 1250 307008282 307008293
    0x181b03040b0121050d1d03030c0622020619030b060301031202060c340c0e07030f020405060304020f0d02040615030b0406050306011203110601030321110f0702040f0207 74
    0x40a02544000804581c4821411290341e00ba2080f103a803c900100110f0041507403c0b1180d2064514401404180316040403e80e201000540300728403500015107054a08000c482c90a0010119200d507501c41e41040d4001580302c55003142c4003000c55040c541d0341e2942052003035000d0010f0000058001d400040000240422081c0c000c40c107201e15801c4c0c0c0c10383d4451005180c0107015010700001d5582c5000c91320a03c10803801d000541040d40c2540810200300c00e6145c6030500c0c840795210b5482c0420400402110590512411002180082007182080e0a00c00401c07000d001c02040280100e20340309041000d42c1d64005082c500d107034018010701055465142840c0c0d46000301c8a03040100c2d00340b02c001d01c40303441c140c000c0c082940d40c041c004210a1f0320b4204066400b0032410401c0d030a014428035440d94020301400b0180c0130f140281c65081c1018004080050908004030858200c2450148088599001c2c4400c5070b681503103400c0e803d501c3d80d1041c000034006010800009440c0c03403000071000c04000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307010782 1250 307009532 307009553
    0x1103090316050310051b09010201140a050108121318020c0a0302070501090801020418022d031b0c0c04020a020f011401030203010c0c030e04150b28020705181b0304 72
    0x2d0702507050380e840102c50100c2c0d000380d410550380ca40201c084208001400140f0001510990307905100102d0040c040d03000c0021005000d944805607035480e0f900602041500700140e990304180c007151540751014000280800c80d540f8024801c51440c012a140c100c0c0038203805170b440040c0d0100a48809091900c1e01a590300344a114541c00300d407100400103a844010310070b80e02141c00103410b0f040a41c0541c1da2800081d489180c0340c20a241060160384c80b90390501e20100031400b01000c0851b40c0303003492403030587c1c000c60348a001c0c4900c003c1080301d000030080110307200601d810700781e80c096140c01c1100f4083c1c1c2400d0030072400304010741c44c20b0721104e6441034422030941220b000358000c021804c400c0728202c174441e04805001d004115062101c1346281442c0d8040244001c242c40e451500c10b03291220400700c1c4d40420b0881110302c22030440e03600ca0103000c2086210304c041c1e0340008c10b2014508404200980b4036550340618400b042400540d013141041c071801c1c1d4074100320a98a0f0303039182c6443c00441c8c52 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307012032 1250 307010782 307010789
    0x1e0503010c0e0d0f03030e0f0106031109070c0f03200a06060504050610080907180507080f090a03050f0d0c020a0b100b030412090b1b0105060616031103090316 70
    0x35800d20a24040341e50041048100d02030340030f0b10310380d010195074407801054000440100d041660796400c440600c2c005101c2c051490f1041c80002c00d801c0d2460504e407281c0315500c0c900c648508015428040855000130b0b4002c0b003650710050005000391181020383d05004c42024040070f241244801c170b6000380c1c000c514140c0d240c1c80b070b078030030041c2644a400f480100c800c101c40031038200120040281c1c8150080035001e41c080b452208031040b51351078160944003801c12120380003030140c8600511200b2500085250307404a0742200403c2c0519003103002c0d03666a41945030207030600c84000b902d003c42c28100411150502910340c81440880c40301d00c0001e40e206082003065480c6200800850030b11203d44842c00202c4240605150458841e9110400e503c0240c041030b80501984800004881e0000d00c0035041950440b0400c074000805a40000c0c00e40b80010040c620440c02044210242030f00c13040d1200a0030b400d07140103a90041d00c0100340e465032044225155162252860706d00b20490035244070800d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307013282 1250 307012032 307012039
    0x10e0708010c200f0106030b060f18131e0503030108070605040f0308210a0501090c110316021804060218030a0c050f040f021308190305031b041e05 65
    0x2840d92201918200d070722008101001a0b41d012889410680014902800070541025615140302e61081d1a0840b10a68001c0f103941c69a030040001c40c0c900138080001094003510b89a5917000e00d51945258103c0040c030541c05440c0f0a0382550510043c1203044681d421020000f2340c3c05411810310719940e420034410a1818810081c01041c0c480c4030390309580403682c00607125a9494215520b001d00e6030069080206407188440780c0404400204064a015102c4050005015410f24000d20300361200c4404020030700c034440c4d00c403030101c1e5800011560b6484007200e0000f44042c1c1440003c0b070440c0f840c5a0700d2280c0d80c101c004d000501c056039004203550242820200d8000000c1c00c02d01d070f11401840005808540580d908008908000442000c200c00c01000010058030440c00a002c03a0080200640350918084041c00350070010400b00e0140031141c41090368900351683c005090b803100800c5419100d0b280005141e80140c2c00017070300c015011006165064a001ea0545c2204160504c240c80c071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307014388 1106 307013282 307013293
    0x516060507080603010e0708120c010e03030c030609010e040b070305070219030513080a08070f05120a0807030525080c040306090309140f1e150408010e 67
    0x10409181c1c9a002c41d50510070203242c00c5844140385d604043d882560240010781d00002d1005002c04505000c941d12030b600c0302e0550240202065441c0648404428003030100c04400166205003000e440d58111a0f9880b50004600301d800e0720701034000b00005010640440c070070303002590701800c1c50044074540c1036071101000c4224801c0909030300154020800d00606549071481c0c0c4001c2420030010030702000382e81c56032003040c851040014040800c006800c1c0400c4002c0c44400001c00c03405804549034054504040d00c2104101c60750000689400c00052100004034001036030800745c0081d100c625402910305990f524006804401140c2c010312001000448502560441921076569851403074507100d00502401c112110740c81c4038121006801403551209a60840c41c03016032074a10541c03422880204d0f41115011a0111407680c00090104440c88150418026a0102c200b102c5 = true := by decide +kernel

theorem cover : BRFrame.Cov 306834532 307014388 := by
  have h0 := BRFrame.cov_init 306834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 306834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 306834532 ≤ n) (h2 : n < 307014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
