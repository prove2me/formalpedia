-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3166
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:51:40.382457+00:00
-- url     : https://prove2.me/submissions/eebb189b-4621-49bc-9ad7-fd72ee43a4cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 569244604 ≤ n < 569424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 569245854 1250 569244604 569244629
    0x13050405040302150604140405060603060f09031903021912050c040b0d0903092d170a06050a11040906050f04020307050714150a02090306071b020420070b01031506030b01 75
    0x10b20321b507101c1e000401500048110844103081605080d9195001102c11900034032400000c0b1f90300c00c00020f55903110790b16500c05141007000810313240100300c0310918280105a000d004250b040c4454812403d01000c0a86400100501c0a084141a200700030041c500c0d080d0280003c004240b40c0404640345070201c040d00083c1003085240a82c1c0740e441a411174903501407011940d17035015035128862900510780308194880260354a10030b24009400d01064401d54010000c0c060002c1c03065000180c001588050118035607180345420301840d0451b0703211600d443d49500e001c100c00c1c01c12280038050911b05440c2986140303070001002d085449000401410341400d0b040304100c0c450144200e00c005100c503d107252650402141c3da2010b90071031001281700e8000c1c074001c0746003180034221501c1c0c023480300d1b081c2e14002e510a408000080c44200921080e0902150f8442c1a00204a0080105510034110740d9220350440c02e003030b170710035240d01c2e00890340c3e903c0c04d0002e1002c00c9100f03000c24111a04040e521 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 569247104 1250 569245854 569245861
    0x703052106190f1e080a0302151303050708280216050904080405100302070f061a01080405120f1b060108120c030702040b0607060e0c3a030c0b0c1305040504030215 72
    0x811821617540100028007820680c501010b0380852050420000e0345030206664a40d403051041842d4100001030105400700032210000705048098040740e0307070b0305880b0920000c0e4a410140541035482503c401a0424800d940060b43c2190090020300301c00d40d000441c0345031036540c4013060703c81e03800f1303940c810810120704000ca14440c1e0105d444c466071002c6107074504011840c141020701044c02000c0c51160101c4226810b651040c0304841c801c0d90002c000b8415810031203482a1594800110184083c0c0208280b903100c00c041c2589500720560764004111139850301403243c4c141521010501c2c4d100c4000c01a00016401c004160340c07110341c04890010b01822003600085061003850b000810301400c00e08018061b040110310403000040565010300843c1e000c1c0c158a03413005116214859003402090b10b05c0c0d908904000b099038a43c824100103100b0074842c0c0b15030000c12800c0b03d1801805000103100c03601e0540d440070120003040162024071243c101994065100e41c00f158100e01c42400c00c4000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 569248354 1250 569247104 569247149
    0x133c140106030c1707200102070305030a0e01050f0c300f06060315270412020606040b06070f0807080f0309070b0702010c06150b18030615150703052106190f 69
    0x414040e454008000c645e5510f050ae0040e01a0f082255103458051034140c6c0c038040543c060098038410000c10340800382aa50b400d407001c10300e070019210b4501e80450401003c0364110b40652a000c2a0a0035020b61550310f000d0001c4009910010502401241c0500a120308070441d02c90803c51200100c402110541030741e0080e114114441500030915444407007804244008812042c1c80d02c04582c1c2603c030541d4806c0c0a010940e2043c4a0381743c3c008078100500c4020404074280c14142901c01d030107481c50415662600c04186d000701110f03c054800000501100c00f8041014000800300300c204e05050044580010f0001c214200340600b50b6601e4a040b20724224813001803501418100c10059100d0f0140030349002840c1d0ba101035903009111b1400400c00b000710703180031400b100e18000e10103090650300030142541504045011410b01405212031001c4201341d01e102d8034103034031010b1800c207a45894810400c00d1a07050783c44c3d01c0e00000050040c000103041141080c01d4410040b030701120303040319014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 569249604 1250 569248354 569248397
    0x3080909074104170f0c220b1f0f02060c0703050310090c020102041a030c0301060507050a02100e012006010b0a090905010e0402133c140106030c1707 66
    0x60442c000000042c003c540c4504c00d07140c0900c0c1807060411208986091620250713501c81d000449a030000558201500e204510510034052250754480071841440070400f0a00c0141e4180b5003102e05000c010700007000c5540310a028210031220f1000303140c0c60600c118502440c2c41121809410040c0010010302010407101c05100101540c0c9020024410f005200070f00035006401580c0c008407210001c0d48900500d901500c1c001c40000303072640d01d90f910389402602c41d5800620f04540390f000b922040740c09030b0389040156030320340c05607210480ba910144c0300040c110300c14281c040765003940341050311800c00400600d036410b480081d19850340e00c000080080c1c841c0d1489903c0320030071908000012a4001045000074040c610a440e4003030015030b00b44d031010039070708500f0401c034240e1042940f034540b500f10301907410403d40e4503480c2490355480191090040d1805012809020103200e0700412446605201d0400004002d18100503d0404d800301c0340420034003c2c08100800603400000b000101e201107 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 569250854 1250 569249604 569249717
    0x1106030411151306030902030d030506030a0f1112030a09031416090e0609030f03040210052106030c010207060206060d2901060e0913150b04060308090907 68
    0x1d00b18003419400c94210740d5140e100c140d0040c1403100500000540c40d0081c003603081c4056000300a1b0080c921030000031030040800030035003030b80351142100d02408215400146441c144c05540384c80341e014a0f901c280030000d056240340081d55032003005840794007170388107008206580d4040482800303c48a001091700d014404002c04160802841000902c2d40441d40b1400100f813103202614040d0303460044194407401002c50b20841c1800c204000303001440d09030f0000e034411400d41889400c000d07914004a807a4242240c8085010003410103101152504010050598009100801c405030038560001d40366030b0040c0070f0a0107411120588010408003d1003d2480b2050750032030464a4540e0b544840881000e1145002080e04185481c8640c00d202101c14880e68924590050300007290351003103003801000c202e000b2041d56590b50403605540c1c3d4042e50740110702a00ca5280c5450f03100080100495020300f00c4010310403611001480c8202080e00e00c000483c8041e800845414803100c1801c5009111 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 569252104 1250 569250854 569250859
    0x50c010e01050a1406010915180902090112020910120906021207080108031908040f0b2715070c08070204060e09061e060609060d09032a1106030411 65
    0x1521044184030540c000e80c0300d501103c00600500500702400702c41d804007911500d00144014200b8401d0702280d0380c044801651514091200180400304807035114101e80066070540c5d0001014a0190f90280c074800480204d00720031480c00401e41e0004441c1c521500c00c850510007480d51898030300816a10220100c2d4004034255600c005461158005590860703d07180410505400828501c000105075040201c41401e413200040c810a026210320b50024021a6a405003450890000701d140200c1400703800000c02c007404801e001d4002c42c401501c100a0800290b07c01c0d005007542c21000c803046030300b01c0c1c5c10703041421014029041c4405144514000a034206080040000e0000804820b40303120700f071948280e50294840c0c0c0100c441000c0d91003003001c005600e6070089409458140700510100c0001044145811101c458a20079140400030580c04034444000b10b4400b8001401000e490000c01201380011001c0d50f0b85000341102100720f040c1c06803501000040c200204251948142c5500 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 569253354 1250 569252104 569252111
    0x411090405040c06140a1d06070c06030204090c030e0a0b041a0f0103020f090f0103020f0102150c0c0d050c060432010c030b04090201140c120409060302010e0a051f050c01 75
    0x509110b10b501e800c910859000841c140c0d540c4c48410003245c26241c0b044415a54411240d0170708400480b85416070071115404a0204080b00014615182c103c008011a45001da12249402d80d001d044526684400040c51700b41618441200b0b008206503c4403607000350119601c2d2283d04000170816103008149120705554002e0140814012440b07074100c920840e41900c0c01e0f0340c94000c0c4a84140c06035411403284254900610041c0390000707804500b201c040c07046405000503001c40c00400c3c034050f546440c2461000030480c8402800b030000030311007d410300b0458a041c18040c9242c1c1c3d548401880070301810072405105030b000c503001b03030100e519006180b0f42e21110b1149809090007003400b4054007010928003205801c90f804c003800b0308101290140c541d0703481d41c100660000702d20b0f406014814414000c0d407170b4403e84401840040c0002d8118940b000858608503c00542400c86100c06580304480440c0100810742d64001900303401c01c4201c51804000151010035540c0340600c0c0c0a0024039402d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 569254604 1250 569253354 569253361
    0x604080a140f03073c020904060b060409051009021e0d0207081c0e01060602031b010b0d1401060b12161e0e030c0a03081909030b01030f14011a0411090405 68
    0x481c800426007007540d45c144140030b0f0641c0c500808503524038100004001c107a090000c0162410680c4140e1240c0150000300304d054103400000c440d540107400180b1172581d2081030045109840001d64040c00fa508000c515040d940f1140c0788040e0701c848070240401100190391822204a070301900c0706c8503130002d40d02c0e440358281c84c104a409202c18071607a41061810403c080310500500407907044441e5500a585403040d2200301562860f82003011071503a43d00e4105146072600c0340700da00700b10180507940703801101c2407132a903241c00d480b916031202543e01400c2c4a0020004000e92000e44c000414400ca802d2996440c1c04c140c1c1c4e0601080c40c2c240306402202207071000720750068160407104000f01c080d5045c920807a001c20414500900000e05114010f00280e03030b100b40f140f030000b009400c0b0382c18040d948642c1c980e500c06010000740c01c200d030300c0d5210000c00001c000c42540d500c5032011140e002031084821070910082201c07044d04c080d41c8101d44800b00c44000000d0341045611020026109201516 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 569255854 1250 569254604 569254613
    0x30e10030203061002280201030e0d050301150f080105010509040905120301050f0406030b060103050c04030609080a0809061b1b060c0406020d020316021e10090905060604080a140f0307 81
    0x10003c4501c2030041d80000100c4850ba8404120400200c14088910100e402c450702c480f403403d000c25408a05250340c410440c2d40300c05003007041e140c5070042d0f5a5001d0f507940c1041c00b004c80510400203210203020084514441c01e5410040850556400f8a81991100b2120f4001400f40058040c042e14a0144122030140780a200d40194103039071081e285d032140d0380c030a5000e1004413031480c440a0540c1d0103140204049602c241c22864000582d5088941025180d0b1034000850b81e50003403c80b190680011201d000507089005c1e9944001c80034007500da54a00000c80080400900c10800c0c1c0103040050094281000d039194004810125821203215280c0a0381344005a0700a0241c00050312071402e040b60601d10001c12038421400301502c0e45000c140690a00c07254295000c800c9540640304040ca20150b1a0714440030102c900a6a40c009030390710f0074914600304c3e00e000e082d403030141108020900a0b04800119146003c0d8006c0100ca00350f00342c0d510a40c18070720041707421892808001048030501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 569257104 1250 569255854 569255857
    0x9060203160e15031f08060f0403030b090609070e0102010204090608060415020a020a11010201060510030b09010b033105030703050c070503010213120f0b28050c04050d030e100302 79
    0x50510344442c44007540403010420602c03450041140f10010400c00210900101070311040c0480b410f40b07106400301c0d140d248441c10040d084555032000200034041100381681030117600300e905000d446c58035031403c1550118802c1c9000411440600c0705040078160340717074400d5045030018041c80f50304128050301c5c0c2100c41e40703600090b28240c4200c80082c0b1805000d9856200311030b0801459002020240125918807010300703c0c046800c0d045d03559903e000103590712020f808102d8480d0a80d80011f41d41c0d01d44040040190042c1c00c0b007142400107208018039002c1d41c1e081c00140d0440a40b05c1820800300b00541114104403480090640c08089120010560030201800c3c032001000705480c4d115442d4011b040c200d002e0480c4444d049440c00c00c04102c6100e0304540c841045005c0c0394811041d0f2425268907981103010345419000520000d112241d41d070a46102f681304001d03503036040c80107080101640302117014600403035100390000034891003010b00a1110b00c02d10100940078650000d08014050000d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 569258354 1250 569257104 569257141
    0x20a0807050324070809011e0209030f01060315090206071205070b010e040506010e0c16111e0607021c1e02040e030a120218041509060605210a09060203 67
    0x3d100301c0003201100111005824603100360002480b1031a40c4000c012076014002510300360265590b2905c4c8503000a901200d020302444135000583d5520000042c145440642c210a40702c0d645040010700000d100000c898074010300004002c29000c1d860f000003402c61141400040101459015511044d074000003d450300310b0040e0508a556a40c40c1824400007004079001031580c0c1081d0300512022a2014081ea000600d410300b160400c88140c0302b4461410710201c0030364490030317040380f1400a0318085c0c5008241f0007040b01030403d9a403190000c1062401804030007441000c032041c2181d01020084140409940c00c4440b01c0f558402d20a10320714a02d0780c4030005d030300440c142040d0001d14000041200c030342080c03a41e58030950041d4403004200a4100f02c441c0b03800c200580e040119141e4590096881200c0a01801240e440c90007400d101254421341c400c8050100611840d82c02c3c1c0a007580c240c003110940d421802c441c0c0e0385c500314000180202980200340c0c2d0b01c0407090000034465480ca0854 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 569259604 1250 569258354 569258359
    0x504140f0714160b13030e0907050c06151009081b0102280501060e040f0647090c0f0304020f0a14100810030f02060c1203150109050607030813020a080705 68
    0x41502c600034106405202118084c0107e941f5905480b19400c105440f10752050051606508080d80d0000c05070620b102510b007032818504100ba03d142510348a400c1032140005814001019442c3c0410303140c031005410070300c042c0f02c5511124007070180d009004502c440c5010500501040d549122410721440001506580380d61800d140454100b070b11400f40742c0210382100c185a500e805a540b00340240841000440e0645071054038620383c0f482c0340e1203907241c280c208801c2c02c8a03140c00380c1c000354603c1200b0082510800f500c0060081c0480c180c1d088482c0034041d86e22244e600d03a582c4c0040b85007412042240c9810074001540050302c1c65480d2219965594110b40111086021403000c8590300419200c226886410f800200005034003060203000135803015000a081015012a103400c24030300301d81c00c42d84d1040010811050026100741061903020074248201c1c018180380115a203400352801c01000e002c1200003180211a07400480010640d0051224548940b50060161240b2480c0320f03450 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 569260854 1250 569259604 569259623
    0x13260f07060b040903080c03040512181804080306090406020c03040f180b130b040e10060f0e0115030513120504050a0f0503030d0b18100e010504140f071416 69
    0x10b024078150195001140c2c02d40d954a140d0b0301c407403140180c0c03684040c0c0200c2c0d8174410f9003985400e044040c400b42c602012401c40d035103202800ca400b40040c40361010b030014034110440c4104800a140e040075207400280a0303640c901d0540d00c1e840e124000380300350080000103100c0444d001030401410f02c603907000d941c04141805030244100014000340d07010051402c2e80146d210f00100c0b18900329600c80ba4843c40c00230300100c0c541d06080c1d00182030111425038040402d86981c0180202a8518503810082610307070346074412503140041540c11000c0101840f420145c0721000300b11150868088001c020390172600000c81458a504060880e60080c8070741c40c090144d006000800c1c1c5018100c81e02151030107400b4600d05119a0180b4004058000045a00c195400b13400b0b200855150502171042a0511846a09908001100320b2928050b44614412401c200f29440368001c0341007003582054151104420302e48503048143c0385110548451a410040482c0c0b11107002520f0000302c1c00c880c095103154 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 569262104 1250 569260854 569260871
    0x13141b010f03051501030b0301020d0f020702120d321204050f0f0c0910180f0b060702030307020f03030c150a0e030a020607261311040513260f0706 65
    0xd8003900c81c2204c00c08141240048a281c0703d50094014002c10f92008000500d0200f401d0410011102c0100b40c1010455003c50001d046041c2901d064480200a100078a6040d48e0f00c1c1e402000c0710144001d008918110900355025000c03034607401240f4241d01740e205502ca114202d1540c251a408507400d8605104401040010040106502c502d03400c04034094001c0b103c1c0c01d0240009410050302c1a80701015107140042c3c8100300c080c00700c0b103e403041c48000c078032002d80601002c02c0d5403042481c64817400d020086c1c0d400681c1c1c0002102c1820303034140e40c5100700041060009095008803041618940182e10303800b0340340c10741c3c107003428440c402a640402c4031503404182c1590741d01400d650080075a11078400f08887c14080c001c44080505401d030300c003528580e0f2030003440002c00240e07200500d031441c80d00a86e081041045440e02c0c1d9010a0382e04200c94a4941c01c1c104070754200020143c080c07210742d40300880e800c401c0c054029140281c20201c0303503030f58801d0002018991108409441d01d07441c1c840b20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 569263354 1250 569262104 569262107
    0x61d01090606020d0513051f0e0906060d0c030603061d0f0304030305041e0902040b0d05131101110f01060f0f090c050a050a020f0a030e0f03010509030313141b010f 72
    0x72041911869402009800040709069503140c0c0080d000b40312808442200083d1941d4001c060b0801c0ea080185083c4103e0030701c51301410b0301e01c2d02c9171024441c04000c820408039480c0c2c902660302c5030041070740102e000716400c001034000b007c03c0d40000d01820f00340f542c00107135070002605480e2140341c40401ca40d81c444285440381d0701c9018600004001960401040007003a4034400c8060112019011080c5c5140d5907980700300407a4450fa04c50702d1204800f28015840300b002d80700d1990b00000c0c1c48030034051a51503940e41c443c0380f11411003850500c80605140003c0781c804102c4080708851940080214549600c1e07082c0c001c500b5881086030142c82c0810214840180d40208013000945403503640c103100c81c142d4140c6840c1c01a03060b030001c6215081822204080410402541c1030203900d81d00c144414444c18001c0b2211620201c2e4001d80c148014440300010000c101c80c1e20500c06c040044100341d2510309401c8449040c01150190b01c90415510fa0703c5203284d9000f560401b0036242e02180e100702020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 569264604 1250 569263354 569263361
    0x10b03091009080f0742020702010e01080703060f0f0302030601060c03051602131b09050a0e0118060b0d020a02010f0e1b01050c010c0c1b150e060d061d0109 69
    0xc00c83d0209100f44454103840d071029041492003003044603981d010b45000c61403800c24100c9402441c0c0c0983d6a80d070304071015181c0000c1200c4c2c0d80b14056180894035000070b0f0294146600300c0d4100300300703640046c1d4158072a5002501611012804e004403560324541511400d44500099210b8003480000003603a500800502c00c0866040d2207150400b600302c5006e01901d0441e0800baa000f0700c24050500101541d4460b00664070300b42103203401002c1c42107000520f03101841d0015802070b40d10132400c1c400320042d1010709045540301003010110b040f0708541c40b005000e0725880340305151000314002c0c0031b1300382a4000e098012901e034001c200c0408035030b5991050700d0701650855019040502e0400a43e200c6001d08400c0da90306040881c904505c0c100c2442c2103900d0001c0141c0000e0005000d2800c1040c20b94590354001419004014024103015803100d1340d14081d501c003018000c0d242290b98468880c0c2060302d10102c4081c1d800c001469491142c02c44060000325a8013005040c400041000170f440d21 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 569265854 1250 569264604 569264621
    0x6060102012a0207030204050901050412020d200309120604060b0f0a0303110f030412050c0d030e120a02041e15080601050d0302070905041a07110307030c060f05010b030910 76
    0x482c0d040c190608800c81c42e9030000e09500c40b03011070107940408005a00c40e0b0081d98001c150010002410b40303007900f000200005652205421034110700c90710000141c0c4a801c1045071450840c016a5051510f0000d625510926007204e80004540742c0b010140900840c000d4420342c0210424080d5200f10010000356020380411a0340c003660444050010900c10400300c19017102c510215407441042c0303042c40385140c04c150f001c20106042c0306205070422000780502003030010282c50001c00707203c07a69000f4040d11a1048540d018400b1442550201c10f010000311000030b801800400c80090080c1c0104405c1031886a842842070803c602414003480c01c2d1001c00c1152080b502070310041c0d00b40700800c9080392104900b03404510807180d0210301c941c00751058900503486164120201c0c5250444040d0080c0000c011409004e042d00c42000c2a243c044210f03009903900d4509582c0c003d01c28500b0300010010b03002406d646518201c00403a4030410340d401507008103000002c60b007408494440200c00d61f40500c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 569267104 1250 569265854 569265881
    0x207060e060712051c0606020705010201020c060430020d091508070311071e0b090303070e060d1d060912210411031027030e012109140606010201 64
    0x1c100c8900403c10b55000600038005030b14016142907070301c0c9551040c24907100c0342442e099503038000402002d5010440a80203000c00c0c0025030424800500440e00d500f0000e001402108a800c0d0f410603200b542c03607150010385220b42c4810100c81d04150b0095444890b6646000401c2d816800420341790407104400d214480301e641c4021080e03076022000c40181014070b00c2c881c41d80c0c40a01940000801d841510b0950801c984031103614004a801e00f02600040a4205c0400340c000b0018000743c154040100a034220007928420380e980d81d059448001084040c02d20509001d0001c202040c0800c04a4028090407084040305d01001c02d9a0403811a032240c00c941c5507100c0310000300d000c80d000301000314a9101e809400d5003510b84500d24040307070034004002c00c0c00030f41c9940c030188442111380385400c04a104d01100c98110764000d059030702420180381300e0110341c10f00c0300511000c6040121184601d0b111105014184104c1d001031510380c00c0c402806404007201d010b1400010031035481440b40d0318000c4d03000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 569268354 1250 569267104 569267107
    0x11030a0b010f0b0c0a11010306090c170c09150306180406050402120f0304181808040f1a030c1803070b0703091508060d050109061409010c0306080c1327030207060e06 73
    0x5e80da21040f500240018141c103144e00c407000000d0703000d118458240000041d4032031092900700100c0c102403c50009210360603184041c00840a40c0c1c4900c00c230440c6480700040d0350ba5a0b92501000602c24a00b4117400075008517018040208010458000c82d0040d842510304000c2c240034980308a46409281900303058990041c40100b09400d00e001c8030b01070a00201c0030004000786810303188000c1b400340400665030408005005c000c0301842038030380001001542d0008901c0c2504040d0401c041c80003402ca81210b810105844a0b84080d0f0b01e0001d44913403004003100d9459a0301c800018054114100690100e000302c0760000307219125400700c3c400000555110349150b5103800c204004103001c15000d481d2590780c2e41c00500007071442c0c41075200490843c403000300a4034040380000c5c25149200420381c1050f05141c41003102c98030005140364a20011500d00700c14040d4815070b10000c010303004440314841c030f51401c18000c9070303014034a80c80440e00035401c0c2c50071103480c1c1d40c041e10145030144940d07410460 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 569269604 1250 569268354 569268373
    0x1c14060c0a030c18060e0310020a023304030801080c010806090117030d020406030b040c020d0e01050d0e01110306030d0903050d120219090e060a0b0d02030411030a0b010f0b0c 77
    0x800d0f4004a090802818501031888814149805419085d08040042116450003e5142ca400c100c0c4041001090109500d00621034071700940b5010140403440301041030f00001903050043c1070740301c2c1101d40319031b0102d0040d2409041c0240310040a215580540c0a101242c0f4015481808000d21400010f08445101d0f4a44400c01941001c6c03040c416074103002c1400322a0700c841403400204020f10541d5000b04020f00403000704012180100801401c0d9070004180941f02500408000d0080100f420026110040d01c441203001e008071036091700c9154030b8100d2030088818100013442c0a14820f80440c1d0503c6034a00d800d584134619070001410650100c424801e01c544034042d14000f0220002c805410140c5d486486e101c4003c5032040c503070109000c80340c02c0c80500440301c50554401c40442d0701340e42ca14a407200c3c8019a22a00081c41d003940c0e0000001001d00000040780e40d82010b02408841510030b460901481070799003801647e80404c0680300000f4104c4050040c0c0b0f281d000d05c48003500c0b0264 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 569270854 1250 569269604 569269607
    0xb160212010b091513090b150f04090602041a04050102060c030403030902120d0305151c06061a0c0705030c0616031701080f0601050603100b0a05091c14060c0a 70
    0x40d040c01809159290900442d158445030300040c000d140b0682520480300b85241000a0144c0881e12591021303e44034485000c9050440003d821030802c20505120881c0c150201c2c10000400d00392a0b0000c0c185100002000059401002200e40f9800c000340042100001e02080744100c0c411103005074172540115485101640045801030312070300300010350b034100c1e0303002c15035031301ca030760700800498110710091014160113014240e4400c4080d007030b82403640c4d07090001801c10012140300320710204600318201c003004021350282c0007601d003860103100b80100042100700b065100b801070750024040c016000a540c2030000f406900c0c00c00c000d0102e800c00400c001d84c407013045011750060b030030006043e410300d90031840c003a201d0340645508005002c200c0c1030700e404d9034900034040e40210700490007001001810a49040600203450f800340810fa0381325141481120729000d200c1405500c851024001e450303200c002660b1a40d060b100c1e90032489070401032000f880d21a182140c1d542107448040160203c0ca9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 569272104 1250 569270854 569270869
    0x9110d150305070e07110703080405090a05010e010b07170d09120c050a150b0406030302010516020a12050a1101020408100b041a1210050411190f0902130b13030c0b1602 74
    0x2c0e507140015000a6218206d0318050003540240c440c005e001405000e1070420700011548041100320038011549400104025007070140b01e1405c18000120320314040000d0034080c46070b42420301e10600e031500c00402c0340000400001904480c0703d5940e0889015090080c552400a0f50f0032102925500b036440c0c86a200788a1414409500c450b40d40040c5112951503101da400a180203074000510341c9040b41e01e890031391842c00901c0c0c0075036010003000360001d440e01645c070708600340e107150054640c52035040070b8030400c02c0f940c00c2d00302950010a010800100015052000504510007800007482d0082400101c82000403903000301007a03001c0c02c0229050486081c01a51001800c6405d000300740006841102c5065a0803102108002d14020484c5001c001030100c4801c0054200e64440c6400351044008540d031040b00503440c3c0104252a400c003840c80100b0051800040141c1c1d030711845408107003080103501048980302e24440c3c4c0480c2c850611025904c0c0c07190829200000c012041e02002280c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 569273354 1250 569272104 569272111
    0x31506010c06090b04030c03080606070b01140301020c1b0a09140a0b0f190e1b07030e0a240207080c0a0905060301091a3c06010909110d150305070e 65
    0x15603e4605580000ba060030a8500c2280030f541c546052040e06c0c80e00411031400942050f20405003400003101244000310740d0b9045500c14107099118a2401c2d0100c3c1c06030049440194007030085c800c0100d140c0c0e03040e49440c000403000302d80845d82e064541c0b6510303007140d40c1001e50344200e8030302c032000644125880c0d20030080c04100400202c040300d1507500044000d400d109500d20541903600701001842c0454150076081554108440d42c3d00e4994010201f0300d01440001800304031f4841c0f15a0020340701c10781a04054802500003c10300d2134294982841c07030181c070610400612400fa000a01c1c44070114590a02070030003001c448189103442a50006072002401d040d80c955600d00f03080300002c030354280240c100107114201403d81d142c5408540e5040d8039810209a1501c0310503d0075410798121290074014400001d65094551203010040b250f0104a806c41c80707480d840c0c40c40b40002055803001030942d840c081034007404020342c240e81c040c03480c944a01c4000c2090780305403001e0040340f89010341d007580f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 569274604 1250 569273354 569273363
    0x1106011521050112110303092407051203040b060406050a060f050904020a200607200c09040b011412030301031e05030a050d0b0402070203070e0c1323031506010c 71
    0x140115805045001c0301c0c02a072010f84054505074164080000d291035420f490107046001d1030804680e400811199003038002c6102030a040414003849c07480000301030394001600803007141c04076030351041d401d48294400d6a059444031007840005150740f0305409940d041c0c80000c0c000e2220340d80f51110641d107003415241e151090107024440c0940301d840c0c5101405243da0756917105019035032030402c101c00a030200c0f0407880030740d00b001d01048000c03504940000c280b0100013890f900d13136180508640341403040c0509060360240e60780f0203010501091403181c0341a03d041e040403035400550942003020003560340a4561064100303000420201e90704d8100b40c00d900c1960102008007000740c0e580c603030440d404000342e40041980030403e080c52118510580c4450481a07034210719014054000903a12220786c85440c40502d91040081c0c102115441600c0c42e270092030b4883c000d0036445540c00001c0710181d0f03c40700405112141c00c80082c1c50300140d0030740c01d18147c00715910941c94142c011038400484800035078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 569275854 1250 569274604 569274647
    0x109150903140127120f0f2015060405070f0c0206090d0b0406021c090812041b0902071205131205070e09150a021c0b04090209130311060115 62
    0x22144c0c0c9003260a1009080240c06810074007040e03103483c54401c255901ca44080000001035124019002028068241e03614209000c40c02996098120700c1c41906404001074040c03100c2084805110301800c5000710001c960030310095640c42c604a5a8a00c401e441d500007514808840d405030501000400c0c04003009809060600400d80780d070141071a09580c00c4600c6503001400c60a00144040c1000c90300c0141107090040941c10b40b07c1310107a0051210304494188004080340412011112121580000c400700b58105907076268140002d42042c1c0c41034038030160f000529811948554201d41075041b401d80d06018044c20300c0540e031448a40c40d58101c0315441840030108091400c03048041c401c40c0500c004003a440c48164200c44131450240484c040c1a0061141d05c2049030070304070041e800c07084080c0c002814690720001034058034680d6030103500800502c0031321014072000524400e03004e00988070220040b1501e50013598984092003103205240c0000d04040401d841112140c060142840144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 569277104 1250 569275854 569275871
    0x5030402061303080304140d09090c03140711120f070b1801110702010e01020a05100e0a0204060f051903050607030207151a030717060a020f040801020408070501091509031401 77
    0x803040b0080e08103860445000c4100300402684044212a0802c40c1d0060292103014400207001440c083c00b44a51094940800310f10301ca102e03500811303000384000150400c6044c1264003501009030f4212448182c082c0710100a10703038a8a0007150003280a8802991400030562500c041c0201c0c040d206807a4409107440c11120310341c0901466280484062030790356680024400540000e4611101c903041d900804e50b00008980041400a44020850f00c042407003000c0400c194100b608070b0340000e50040c9016030204100119a1401059a2040d10102019107201c0405804c0644502c40101203038410000038821901c642c02501d019480754007828140c8216942c10019100a24040500701c07106a096000f1450304004000007441c0d070040501c4006860344c602d5448070402400d07c0c4004d0340000310b90f015511900100c40081660100840d01c41d80c540040a8580c00d03540b080e0750024003101c0021402c24900c1208000b0100c558a9120b030442c03a40d0381311301d0700d074103d02042c0b03804e5541d50303454 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 569278354 1250 569277104 569277127
    0x9270e0a050307150b03010b0d14160e01030302060f010312030f0f020d0506010f0302120f070e211006081f021c05061309030f0c020409060f0203070e031603030503040206 75
    0x7928107103100c0d04e0040c4455403483c00300c00c1100c0304014003500c66030509004031a2510741044042e0b40a400074281540c01c2d00b00e44080c1d1500c0344071042c50b080101c0203440007a440003c6030005059070300c640c0c01e464a41e140c020a40d004400e0038040600090500e807804115076009a008d8003070410520404100c10701600d8141049811449580700711607294000c0082940c3d106451a84980761401c0842c00c0c441000045148910010107811015414030041400300340119070f29403107400d0013800d03000028040589804104900f40c2000d8040c8500440d110040c5001d0080340c1c2035510f15001010b00c0c1c4036940c0300c50108817104c85908401c503403c002944141081410303202c941d01301d450b808112802c08105021000454544c11480d2515040d018000254406540041100b4600c1c260091070001d00008004000642008007458070f003100c4802041c150390042c0d0712940350ad4480d01ea0103030b400c100303140d1100340e80c01ca03103c800d80b0408002e20000340513101441d0040d002402c500d041c0f2076101c50 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 569279604 1250 569278354 569278357
    0xc1d0423040c1208040b1c05150901082a04060e1306060b07030816031508010b19031106030712050f0f100b041a0909070c140102070b180f010908040609270e0a0503 72
    0x600002c0720b20b0300c2001c882d00740ac107032081d00c0c014070b5004001c0441f407a40c150b40f000c620040320307003002c00c0c601102401002607855030404c1e4007401c011485682c1600303000e2001c1d4061105210111400c606012002903e9028030050790a42034050320f42c0d41056890312060015803035003c80709002d15903103211100c0340082d8617100f03c1c080c118001c000a40701e0b582e00e080080400c21081c040400c0000c2007014000154011140b10500c1c40588960351030b600d03081010703101c42655403070804a292030182004000382a541360203001d808600d56556807078690b02c01700ca0540c82c00e4061001c040c40100010003c0305036144a80d0007140300c2c0f0402c0c500b821252400903101440a80fa00c0c00026207110141c0c05110900130541ca6800c281700085180002a45c0d902110034401171030300c6e00507960020113603d03980c02404070040001104001700300701c40c11440d00c5d1000c1e410500546002030500b00000c00e061400141d00801c18110280d40030703184140d143c800c009456140c6000c070070f40c050121140c002800400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 569280854 1250 569279604 569279611
    0x91e011b030504080106051e060a090902030c0702010806030604110918030f0a08330109031505070305060303040305071406130605070302010f0c1d0423040c1208040b1c05 75
    0x103440b2541c1c0c624245500b401e50b0800d4204c284100f000c0c0c01d5002ca0030041c1540d048150809546042c1c40380714440b400d6940700010791201044d28000001c00110300055030090070805c1c400d032100314039a00d85a0a00d6600e4902300c900515007095007111017164603000141a52000e01c100148450041165506085800c1300b2000740c81140d0102d031b8050f60503007062250364003094440001001c00c0c900903440042000402084940541e1b031060b001c0d45920038504100556000548504080070113024680100401c0f100403000130f1801d0086441440d020080724112908000206249420300400140c000d5104c42070355400002009480c0d8009040c82c000c4000b08000e03201c0b1915005581406400d43e00c0b6048454041c5182c000c103801460380000b1004401c103040c10801d007a006885c40400c0082c1840c5840240c442505c1d990380d0707001c0c0c01c3c50007128801c9201d007001066596403004c0d40310f084200720200400300300c0244024040404400c002e01071400320788094038408801600c09104580054 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 569282104 1250 569280854 569280857
    0x1005041103010806010614030708060109051203090f090c0702150910021606021c0806030109060f0f1d0a021203040f1203021615030b1203030f0417091e011b03 70
    0x1100412400c90213000f03440c010051030a10f000c44640c110080e41c0e01c1e200c01011ba0040c40001030202e08145d01c40c41d84000030b00006024480b005640d103c0c601d07501d410070180c29110b0308100d1801205400c16040590141102103850b0b801c00d0825400c0100700c01c2102d6400010400611000c0084d5441020750702c0c0b14106500a0000840c1d0041000b00340c0405803c03400030741d030041d00407554149160b81c529500e11503c1c540651541c0305c44000902414000902600300d9040c0401c00c101500160b20200c41100311000400160351100002c3e4110012100345c646c4903003140c042c1c0703009400d00c6103c85a981080710f056034030713180e280c0c50000105012500203080202041c0200c0307007019010007508400c5c40000c0840c040651400141d00f065860903079982041644036011304515403141c2809507860070900d01a20b4480c0323003411072200b1044048400391140c2041c000400c044c0d050003400c990000101814040418204503101c40b001e6114402503410050076078501281c2003000081000303558440d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 569283354 1250 569282104 569282107
    0x44010b13020705070b0f040e18060a0510050102070b0703050304020d0b09010207021005090d03200708030c011506050a0c020f090a0f0c0e06041e172503150510050411 73
    0x290030110b02d0135a09401808598404025901c420400107050343d04803a41708204102039074a02c540c0040a018500140b495031140c10107020002c400c40e007006205034051001424060b60700c2004995850b800d01c104829000200303c19404070748110001e581c00350002c0c200c404141400d80d1030341c00d510b80072550048540d50102e110403c600d0040604090001146406401c0c5040b0314002a21000b9002004061049401001445032200c041019041c0c0c0c2030402d9404099941d05401e8030b0340d008480010555181140b48a10300141303000c0c020a96880b940c4040c200410881d0503191400500d2090341d00c66150403582e04c071076850b583d0451044c0b2240101043c1d008100d1460403d643d04500702c5028040c101d400f85a085d221b580548041b0358039408142c19040c2045813030700310b0110701c4e00085441520075000111144001400e4041c0303290030071482c40182c461801d032010342012030100a1445500360f4110713160b550903401c0780d5005038021100e056990b5840000900b110440542c4e404035140 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 569284604 1250 569283354 569283367
    0x50907081f0506180a0b0f03100501081c0f0804050712082817151c150204050108151207060e04061d040816050a0303020444010b1302 59
    0x54002d5035007104003641c42111414049800e1841e40000174030f20200340d5520320801e8410f03502c6002e0201c5c19080034050340c1d684400b00843c034001c3c00c801d0040c001e443c8100e091022000f000241d528104ca11141d80d50480b07154441d0781111051000380c01a20184a201c1d804140003e00e212040c03416845122100d60301c1903000c0010034910500ca040c0c3c000303007001c90240312010750400660440000365a541d10803580d601410304521400c8400040d8110f084003144201041034032039959005805010304000b03141c158446881684214081c170750018403140d002c151041c20000d404081d00384000d02d0004d01c100c106580d0b600d04841c41e07001c5c2000604c0c10034126041c0c00d040c480c2001a00000c040e103200c100141101e0800071001070310082c50310300c00040c4526100c1c01d10f50003031200741e1712000b41d0b5551002d07030400801039081401282481c0412a026480c4290015100c030031001c0e082140380c650f400c1c815241403180781c052403d000103540303460b200c1c001a41e45075448041c00651620041c1c42e40d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 569285854 1250 569284604 569284663
    0x7050708042303070b03010620030309070819050c271005010f020a05032514030a1706010c02040e0c03010e0d030b0a0e040605040309030b04140c06120a05090708 71
    0xb08860180c034000d4118000901c0400008012a41952401d05001000031421488111091034141c0683e5240c00301009100b4000e402141c0401280c003a4401c444400054100c3c817483d101584200411681c003c04681216050062110703a522140d801d8082c14000a400c41c114056012a0110341c42022604180403941e0054607043c24107486200604142c0c900c1e59842d5640d01c106041c0003a003141005138406601d5101c407086504070340c000c0049551002602c50b01d5501c1d04402c1d00f420109505200000b541c00c1d41000d014031640059451500d0201d007502440014025100c201c1c0203401010b6603c0c4864609021302110428110018180044905002811545410407203849088075107820080d03080a94480740c1c102e0f401c41c01c001020744032447c00f07130384441da01e40c0003d28040000c400c200c14851b10550040307030103100a0544146810742c4042001c6072240700081003c5911500226010742041d610141c1c1c00112002101c680325190400103240130407400e0200e01d134640740d40b140d00511 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 569287104 1250 569285854 569285909
    0x110c0f2b022d04020705010b0604060201020901091d060111070f1e060305010803071502070b01090f050f07050a181d07030c031a0d020109090501140405010e0705070b0705070804 78
    0xd411840408411042c40314525050341c001c011201c2c0b10f10f80214207802442030070345c00486240300081010b42d84a0780c070b1001038040d4120590b95408656040c000180840c6800980c00307203031078004070458140e52540010b440381d41800c6c02107076541c40b46040c0400c0e02041e0350941c01c0906035140200034207052500d00c24a11076066041002014181801000b0000c000811f0321090340e8040d8090080017009944d14009010700300015004503134980001403820301d0f540c80107c2400d1605410710087d43d4003115403054502c2600c00a001801c200212817034907120b140304144a507460300102071040c0c0d80d201c0c4080d6823011a0343c1c912369400c02c0002c0c04500c94161203003007010325160409000001d1039100a482d40c0c031050f07000c9030155905d41d03496411a8400d1026030054076552800b00110b5844022088000b01c150b07842900a628000002c500c0c4511002072a10808040d0b9030305103808420380d0b03200000c0344090501000e000b400e214120000314030038060005441594141c6c0980083c0701c1e078a0044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 569288354 1250 569287104 569287129
    0x120414040b0904080703180609090b10020d05071401110c070801050613020a0512090c1c0c03081606050f220f03030e0307020d1a0601110c0f2b02 64
    0x114640025485075032504144554050b0b04504035607103600d01810142d07040500303c103050050804a20000c584280c0080202c01544c0e16a02e003003206410341000c0c803106030303110001640564001d042c1490020300c2040288000d0b4450000300451803000414a401e46131203410fa40d00d200030110359401141d508115800007000048002d101c5800c040010034070446051051041c500d40001340c609041c0d000301c003100e949140041803034542d13103040040709880d1000c0388a050701c20704440100500c420f04a400201c420740c2c11112113240b403440c5545034440d42e441a00b01d5101029015080008610284229031148007100c1d148515864400d84060300d80b0303400341c400c131301c900940d00c1110042502030904091250b41400c2c00280c034062080450b18500640c0f80007580251503421045c00c01c02158036011800508a41c4000e16880d82001503560384407520309101140d12150a0034100e190103440c1d00405000640306441c0070822082d94141d2324103900003001811311003e09a002c50074018142000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 569289604 1250 569288354 569288359
    0x30f06030f170f09061303120e3a030216031a01050a0303020a0b15120115050901120f173c090108041509030807110a0b060402130305120414 62
    0xd4110780d8083c2030b40074090498000d000d031a010885a000200c551002c601441d0000440c5101c0c000750800103058250300300c00e140c0100d0352180b035911024910b15201149141c40c2042802c00800c0c21800783c003c510034502a0308500c03840c4070b142d40060141c5041070165000e83c8500348150140c1c1142c0050140680c4024001d00704104c080004c241c0c040362132040c50f580f11101c980b440e00c1c0c80c8019802e800f140300c10791742c0c0130103004800400c01105500400440010740d00c0b00100c9580c030000c01400420034851386c0c0042d0380c0c10310103600203641c10042d90f0250b44540407844922948401c4100c00342c01c10340c80d91505030720907580300e02001a41030300008108038032103c00303501e02c00e040f1030b05843d409903240701418850040041420003031842c150a0801044580c10030411649060050000b4000c0c1c0e208408a2210607201000103c08545171040c2da800162248980d101c560074000254424110b00c180f02000da040440040d03414130007a407a140740b109030700b910381d0305040d620507600c00780c000c81c0c51 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 569290854 1250 569289604 569289607
    0xd0c020601061e08060405280e0609010e19061b050702011209021318120201360b06010201020d0f020d0f050114101205010305070e090f0c060a030f06030f17 69
    0xf500564050401c1c0d502c18000d440116050b04c6010030308102e0070510030180102d12440d03241c10558820b5912440341c11a140341240d1407a101c40703200c2c5003240c6100350320440c075810041110000403034008109810394030505c000200d1005a8100c1a440405000316000040e0002002c00c103561340505071a060a2a0031000c000c6c400295001465a09410043d01c09590b260303421143c418107012900f41940703801900e1110301c07403038031080240280740e05c0c42d0920140c2e83d020800f809004150110141000146c15514810394543d220480a0500100300360f04664080013844c480003403034021417101c4103031001c0146c0c031803414402000503901c0e165806c410442c0740000410604a01c8114042c1c291002d5424150000c00840c04032148024480f2060010341044000810414000b40c2c4400300d0b01c02c440c16100380d40360b21420030341303070404103c160115070700c181040f018038507006000785104000b034180000e548600405443c144c1d110359200780c0784483d60708084400d1004010161407028004c00419 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 569292104 1250 569290854 569290907
    0x15040f06050a1514011106010906090e150403030b12030705060403020f0c0609060d1514010f0c020d031805030106030b10141e04090f0803040302120a1407080d0c02060106 75
    0x180c00741c01036129813250256100701401036a4091200300019407500402e8581c6036850748849005070950388103000c20300b45030000d10001104042a003810341c104000e03c0210503100c44d18100d003d0190070344400d50014440d8003c9509000800091072540d1140014100a2800d404d01a00f00301d5031143d000d580c1d8000100e403810700c0c0e484208039140d40501302c403515103031410504590700900d00341840b880400080c050100341c07100c0305070300e44c98000740036621b41c9809424101c085070701e8050040000c1d0454207044002000034040d01d003900d03034a046600c00b100c0082e46d8400007420f4545075881640e00031002c03410700c0710890f04910b03080043c0006114001c0c68100700b402040c01c0d85200b001c08600d512041030031250030b54a03504000485034010301804585800c90608448603841038030204c015204d01400510f40c1c600c41c03001ea88400185448896890011088800040c0d1102c80100d840d5881045240b07a445003174454040f2002565005010660500302c0240101c495861409500310003802030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 569293354 1250 569292104 569292131
    0x3050a06050609090907050909030c070b04030b010302091504020f0403060b030606100f09150e01120b061b010e0102041e0b25020105090a150311030603190515040f06050a 75
    0x40356080441911030901a90b68400d529007010850b4007c258050100b409102c4141d00000c06060078401d100c054501c036640d40c1c0d038011014070541c88010450000e20700100094a4100f1074a54088140800b00c8041c600e4480094101d9018030804589400302103401c6c002c0c0103181c494020f00290503001000700b8100100083c0d204582d202105082200000301c0c0402c091103845d00c1c3c402001c900f418104400c2c0c1c005400b820441494011a0028040c810002a41200790241c0d0f03e003120007074002c0340740c03503401011204c190b951180c01c8032003503484d0b00c820910340d50700748014002819041032440003040008220260444680d2250010540034000040d103c0d00d8006000c56500303e00340c01c200500301c02e10050781c59000b81131841c0d501c440305210016485000d21140480480903980410065072040845540e40c001a00c003e0f4150703000b01d00e0005c034422000c0940c0c00c507500030700454110381d0743c1380106070401d00112400c80c3d1100900705500100000e40c01410380000d00303c0d0040c418280386500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 569294604 1250 569293354 569293357
    0x6041112242b020111030a0f0e0418061815050108060702030c060609040c0314070501110a03020a0813180606020c0109060f080a06151d0405010b042c070f03050a060506 74
    0x900b084502c108503489811a07015a440e503841c0200301040e40e44408070900e001c1d21110400b01c0d080d010800d01400c416080c5031074821030341007200c000210712031400310f034466400400c070101c0500c0c20050310125040210751000c030a02e070030030344c0701d0000b2540c2d604140e0882d00305003010b001081558818440c05c8001c03a0701041040c0c0c8080280c90403411507907242807581c1603640c00e5001500100b5104445194120080b860a0039140d080c0c03290103003800003250240e03885501c188090300680001183d10001030402d80180b540d10740c40d40c80f07442d0803900c0f540b459512125034001902c005503035584c2002919014881103403501001d0078030800c03140c90a84003038013903002842c10500300b11240740003910b940c40950140000d8642081d040c2195002d4000242c43c0160442103200105061052000701c0c2c50140030b070f030303060f5104201201e040924249040031031404c11002d011030440740d0170015100d102280d0000d48140303155074600405481d00030f8068100d4a0290206800031b00340101803240e919801d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 569295854 1250 569294604 569294659
    0x70501060b121303090b0f03090f120a03020d060b040602030a090e0c030c03133302070c050d03022404031803020a120203100c021c080702060604111224 67
    0xd00d5100c803901c0c10310f005c41758100290024500c5a80c08114007200600c400f01851161038540108d8252040281c0e845035211100e0800d4148030f0070400028281c2c034440e4004d010480400100418115100d03403210000b90002d8000200690010481e0100e480c2c2c01059038008020701020324056041001207000d0034800140034050020300000801d01040500b68042100f603008a0741c1e00309204040c4000b0302580c11034984590f206101c00340905032880c1c030300c210b540244d4040d0256041c40d02e46401c6c00741e1050819810323820340c0074070783c10f82013060700450b0045954aa401900071a6141034034018010003c1002d2a41d040f090114090005842e5803041c1000c1d1201808911f800c2400da200081c0350a03003107d60301c0401ea04142a003001260009200701500740208002c682240c21200101e8070120225540340040e407180b004104141400c0c0c0c0045a0b4030f061032941d07403600c8220124208840800d541b0038180c00c00540510a440010b1222801207500c111505107204056080c2030342c043c40b014 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 569297104 1250 569295854 569295871
    0x80705190804030305160c0305100c030b0306043302030a29060313060216030f02031809070302210115030b0d1104060812070c06090e160504050a0902070501060b12 72
    0x30310784070f03040c1b1494901d01c0480e800b40385041155200c0c54100d442d00303803201d03080035100c0c05c14000010700c5019000301c0100700f40140003095140c2d074030344882680d0480111801803c00c1110f008003907088511140d482d0944d400000541e807401c240101e20700725450000d03680e0790803251110701c1301a10302044240706158811038504d80c80b40c9400c0e124540c3c021110200414151002031070030303000102c1502403103140d8000e440d2000d4141da286010380e01d0b0712804446c3d044408100b010a18140b4041c0d500d1600001d41d8034005091040004800840c00c0c0c030b102521804820360300c010460401d050300300354a8082d440c50300380245524a4049140992811401007400020f501d11000d203071150303404180109103400441d400c400b1003404402e0a07601049058a02c2c540031413000c221503014859440c2214020141c0e00104e9403018080c51241c50890800001c002042000055543e5040c00c0701010b0110302c8801a42c542541c41d14a00312460390340000440c1c00207010007000d440344a030700d413988010300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 569298354 1250 569297104 569297107
    0x160f14030f1905090315090c06071113050103210302091804020a081c210c0f1b030504050603061f02300a1b0609060e060604090203120a02010603020607080705190804030305 76
    0x1030f8010541044080b0223841e0300808045449410f1140b00e070007800080d41306543c0e10001e4140b03400e55400f034480901014100c012400f00824103452140d04010060051b40350041c10285404001020841902412010843c070380b0103100c254a410304036000146071280c0141003682400c0e40c900c801c042c0300a00c203414030081ea00d40b0140c0030008401c2c1c24105000300c00402503213400f0318018010200c0440729070001144000340110380c0408408813074106d0b070942c44460800340b0b010100721160740001c08803608000c1c2e04860a1441001201820485a076034014040c49403d1701c14040810742201c2a452000c400440e828031440c4800040700c0101d1a203250881c201504410000400d0441c00703801490145003461020501079181e01425400ca64002911155180c0c80104070640b55a0760b0701946c50703000000340c4c4100d56200750041c94422400e000100701a81d5070b40028505401c40170040e00e40240020f481e01c10044103001c0b903c4001202415103090715850b85079540b041c00b66000041c00d0000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 569299604 1250 569298354 569298361
    0x4060923150409080403060204081c02030a08041e020d060509010c03060515070206071515090c090b13050315041e151e09060b0406050105160f14030f1905090315 71
    0x2c40e017250040c3d90070800641d5901d031b84030845030f40c4120b6810f400f19482c2c056442030703250901c04000c80b0459922a522100c05492310385901036000490005040000846410007005072201c3c02c0c0704080e2401100d0020b0246000e00b00c080c01d403001c1e182c038035007003514118003071226035159a8040c489040190000340c07503c1e82403010072000d10848001130007a42901000505400070f6030030010f611441c010060782003e036280404015580e40640d1072012417581039040c815046a0406000121204003030752b02c246564101180c20580c0340b5a00001c0010004204001c0c8441ca480445141d255070030850300910950b01e80c01141040c002c1071043ca9a00c81409607029040c03600a812290720607003003001010307041c0c070b03002009110810495015034180500014258020020f8a02d81e075458060800c0c08040781d80c030400b100e8211b40d42102e40007000603219070116020405840c007901c0d0f480c0f02640d6980c10340e1440c0c1c1184500c0824204008040040c1181d40e1004200c80440d180714224031549501c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 569300854 1250 569299604 569299613
    0x1703030a0207020315090f0c06070b0609100f03080d1808160f1709010207090c091406040e190b04020a050d0518030a0207030b0a020c03070f03030b04060923150409 72
    0x481c0201402d070f0401d1780018800c0c26140030807000c4c40c85180e0011200d41c0324044081c80000e0150303c0000e80020405c40000e20a400c1c1174000d940c0c03260542c80e418441c0707a168840e03601d001400d5081518410030208440b590700b04548074030341c1c03d162607540d01d20801601c1c1e5100d543d907101c1d030120b1541040700c0d0b03c008000c0041c01d91746100740c2c80d4098a490400e00b100300c0402c1980c0c0000071101e0040c4508070000036003c04600ca40c1400100325a10544024103007804d4200140500c2241030301318004000c0011030751070701361449005150b103000003030411030041c07290070980f01d050650b2031180b44100452010103800000b120035000858001241a039500c49050102c44401c40440003030b07000001703403a03280c0c3d44d02041d040142e901c05d09011016032901107020040380912807803210103600c00c1000402050003e07003100d0140c0d02c00e14012900707204010200e416141943d0140e1709082d2945081018882c40010b0f6010100350058011840d2500c0c580021055156000e49030003560703108074000610 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 569302104 1250 569300854 569300863
    0x10c03030b0a09020307180501020d0c08071202030403140105070914130f0506040c0903150525020c040b0418140a3005120a050604090f05161703030a02070203 70
    0x24000100550150303651012114040e5000301c421b10f002404600144104405840110090f00c0c1d041c0e006107030024003800246c4500e481702200391100381c811300c400300000d43c600003d04503190f0282c1c040c6444500d10702d429204116074003200c0440d41d05040030440b405a00c98034080c21210304a05051900406c075010442503003420584883d6036003803408030600b44031142c204030b0144406031410401c0140c40c0b082140d0104041c04010144540d4158041c002c2c41c0c10340050340c01502446045c485503103100007021140006c2c520308005600f0041e100f0207145001e00c112003030050156030610003204884001850a1140b12004103104180301d1030b100744a00c108800c2c100c0715405466400000704036600c10340c441490480550103050490342180402c3d12070400d649032095150f0000c2216100c2e00e8852015240040101d074100c1d560703000e05008144210a0420004e028802500304d0000b49202480401d409400c102d40354000620072042140000044aa1207180c01c07a0060303c480c52b610000f81003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 569303354 1250 569302104 569302121
    0x3080f04031106040506070e0607020a0510030b09070c260a141c0504050606041107032604031808062202030a0b0906010e130309051009081c11030c0c010c0303 70
    0x1440fa65040000304040068524000d21440d02c54103c1e8007403100070800c0b0703485000c00080d04403d007413004002c0d905080c14010810349013401c01141c01b100304404100400382c101e07160030000c0d810030b41c0901801260202004650450600300bd056115081542901d2140400003001c01c0b00c4221201c4580311070105440c4400c003007242d8505030900c650000c1c8050601a80c0030b41d2280121004110646400d00c1580035103408504e1407401d0148a44041e54100c1811039114101000031001040f00881030360303524420f5100703071a040c0d00c1e41c1d0000e8081d46100080c3c0c0090310310303500080c14800c0030324024080c1203144040202100386180740c1d20111b0305080c101140244148011814044651404100181611001c0190342c1490b40c4207040003130032004403000540411030006060109041c10b001c0000001b4050410b21b241c5aa40c51405150051440d03018000700b031541c40c50a152503001b0a0307001c207400d8110055081041c5480242d071912664070744c1d40d0506c400c40608104040c0640c100c4110b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 569304604 1250 569303354 569303387
    0x1a09040209180f0723010903081602030304030b09060709060801090903090f090b12010b01080408090f0d030e03120f030c2209150b03040506010513021b070303170403080f0403 77
    0x10300f654800c8143d035071010140140c0d2112a1052054031441100d100e141045190582d40c0b840414615208c0c10340607808071420b0400c0d540f03c1c070803840c01768504200a000075485540759a8680c6001e00b030b5030741003000251251b0f080254000c801c12201d540b242c0c440d0706403000c8c8180003031882158682a03906018a40c48146030700c0d026000050441003550061a240005a485201401584c41c00d6800c0740c4d1400101c0d80070038400d10100c4c0c00701e4901d401509034004040d28080e000084000024200805101308500140e842e2007a20018103007400501003140307101d00c0443c207180881c0c01400342d41c00f000b080b1034218403010503040002003d4040b01e188540090303031000070584d2a980e00030003030301d17600c10705101c619582e0100250744240c0400b200e1241e5017190240c041d9034240420480407107505142c54103c1c54080c00a40082070350307203038030030340d0005924010135146180d0b02e0054501900c2002e03121000002c4410040883d802c42d0500380e10601044501ca0b05907110301d0141da50441c07800e106007 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 569305854 1250 569304604 569304613
    0x60f3510030209010e07021e0a03140c060a0e010b010f0c06180c120b0c040b0d0506060d0609050a0605090c0403060c1b0803180d09142803061a0904020918 68
    0x90071709080c8017500d01aa08a41c01d80f101d94007030880403030000c0350321016010554420f031512400701e442601c811a0a50000111925159181ea401480d18a0a480b6000907a070340e10808080d82c0005d108034005c0f400c080c20b0614420303203038090240901444030310244c80c003901c0305440d80051798034080291842d130b0302040861319113448120440c1201c1240c070080780c280c10180041150001100142da044510804049280180b20503d04010f48006000550044028030036861402594018000a82554500091145050400941903c84907444280102c03024420701c400200e00f501203605880d0050400f2405840619085852948040d42c148050824a00c910104600000110300032045440800c000074107200c1c03019107071000340c502c03036021506d81e010410a06030b500c0c802050f003800060419071014000d1041c0300103048000140034840101020602c10010a032280fa864000040b89100701b07594410081044404041c101911601907400050701c0d55030704007038199202c8031910684 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 569307104 1250 569305854 569305859
    0x1002180d050d020d0305040803070518040e0c1f05031f05100c05060f0702030301091109031506100305041e0618051b090c0a0c02010c050304060f351003020901 70
    0xc50715110b400039404014090501642e0002e4800e0003140e0240c0c2e040454146591103d00301542e003903000c48202081d80c5280e000e6006690b4461043e244070380300d0500940120307081001007154201486c03d59100080c14880c07070b42c0d038090b444420b50b07034000c48c0034035682500d010031561400c0c4080207038461540201d0010081600580c01100c884100340709004480058407200c51000c421348080ba403400050780180010007814203150000c4100c40302d10204503140141440209003092900005c104244800c1d2051010701c2c101550000184d15052400300013500f015610b40401240c45e44540d0341c102a00c0a9540c1071210700c0d40810140403444101c40e005482c0e52501a440d400ca113003407000c07095010220306080d401c102241c1480b0380c244907015898111012001e4a00002040c0144d040ac40c01030718150004108000501c01307052941c96074000c0ea54851801480700c07002140d40c5e03d1401e00c4c0c81648441060341c03186280101c51401c1c58944659401705c03030310275003249540061b5001480e039000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 569308354 1250 569307104 569307113
    0x110a0306150f0b07110918150f0f010b0f090112090606300f031b08040905010b1602012102040303030b0405090d020a0b06010302070b090f1c021002180d 67
    0x4008651000c00b00501040da07410070b4071443e026400c4003620f40702c0120310105980c581009680e81c860501d0740030341408510240308924005a4a0421120f0744801d4240520428204071710f40c3d01c104020461540d40d0305001c1010098055050044060307100854080030750b80c0158217202c01c0c804c0b82d100811400c1d44d04d0500e40050441072003800e0040080a0380c40d884900300c01105514200200801030030742c0b40e40d0b07540b0003190f02c07007400680c2001840d81181000030004201ca01c121801800600d40761410002c4400450701d040c0c1c40a5002c51003001b802c6410541c02d004a5011602400c04a44040d4604810380e0001989002041d52a1000034048101030b0982d00000b20a50140c3e820003141e03a4101c03510350348000355401c90015a224041c0340e00040d200c50b80940d4041410325015003080d000b035464405820041c0c1d4244e180c0c1d0401d040c41c6001110800198603100401400b812418454000280d00c0d40740f0120b4080c4801d0700064500c00c0c240650032401607640001e0581c0321049042e042 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 569309604 1250 569308354 569308391
    0x70b092e020f0a030f0b010f140c15040c090b010504050a0306020c070f0f0602123f04061a041109131803021f050c0a0c1b0b030105190e04110a0306 65
    0x2411213050716115855a0303e508c40c2020342d10008050702e0340008100000c0b041012a0800b1b0015141441602004c141c010b41d800d0415019520505410500a0403e4151020381e403050800604004082c0808c201c1695079090210440307420584c0143e5600b011800503051201c150481c2001d40220712001038401b0406074514101c1c0c080b0342c2075540c030fa022b40362012031921030484800e644c24805d115505040011080d8030041e2403545054400142e0030141500c6070f19003c030b5043da012565994680c418010000a062481100720303800c1149030104240300d403507406000e81085c052a8103003514242c40c40d03a0340c011089510f942161880d84c0c0c281c1d01d002903031071a01c8aa6015030019084032702e08031418034011180600071035545a41001800713030b821108031118410988460007005010071580102c1c903507003406894044125a9258102014440c40050703a05227544070301d00300324013080b40203140c00446402983c80380d9103040849a44001401c0304c1040d0b000074094502e040441c0b032050300d2160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 569310854 1250 569309604 569309621
    0xc12090602150105151c15030605070f0c060509030c01050103050c0f01110304062f06070305060303070b040b0c0c0f0109021e030d12180305070b092e020f0a03 70
    0xa084840d8408010750ba45210002071003110b8008210303c0b1441c51440c0800f01522000a4001101003142c010380e203c1402c2d070342803000d60807800b81c2c00c1c5400c2c400d2218900985900c9441810b0019240c85040e200400110096401030000c59944020031400d28090044640082d40e4100912980d40c5a08000ba01c845c0442d403054861040412038503595405200c0945001d106ca074050f41c140307898030000307441c1c1006100b8900d520049541c2e0031802900c0d8a00980420b049010083c20325140c0344d007014080320005020759110394014040040055000103071213078443c0c0d1191180c0c0c402d40303a0507505a0b840c000d15004400d1401130040c041820b020542c00800c0e41c50003150100700440c540100c09100b188030101c140c2c0c050300048600d1700900e0041c0b948000c1d58034000c4c00043c4180454454058800002100f00d00094000504900780a40c40c5509a0040c000401410f032582102c090b0340d0401c004000310380c180c2d0348800c0e039030b031002e00c60303a03041c5c40130b40f001040080d540324800e0500400802400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 569312104 1250 569310854 569310857
    0x151509092a030f0601050603010605250803090c04110406110111040303021c0315140111010e0102070620030402011803170307020d2316060f0203060a060305060105030c0a0c120906 79
    0x90f0070121850340e00090150407140050314207880c690a19030b0466655000044003421111440c2080c0e07140d0080c004806d008a008280346a100e06010314650f04125030101041e20480c03c108001c3c8825821030101c40c200c9155003050003401d507089002d240540020b0307400599032540400d001003819004600200c0018281310204050182c3c0341041d41200d00081a6202942440f08240b0a4030100700000d07200d000141090390064084107074090075500c0c2d605818103240d40103d068010040680501102c0444801c441c042603075205040c00c91078000204080e04001400b459180f010314244054806503422022700c01c500c000c07026011040707520a03120003006100c1d45010b0706803c2c0c4a00d8000c82506401800c1d1900b0006c0740492007140d030055601404040456802000040c0c100c0c40384134000e40c0500f00c05610391800701c0400120a00c0e0b40c3c8424141401c240410000342c1c0c0c4501201d5010602c1c42e2082e40703404e04801c040701c148003180c80081c902c0d00420181e0f0a8680c10240041c102c680a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 569313354 1250 569312104 569312113
    0x60303020d0201151a09030609100608280f050703030807141303080d0f050f060a0b0309070909173709050d051c030e151509092a03 58
    0x2007080f4200c420703003440e214124204070310521002d0204550140260b031030540550030141517400181c20075500b9601521140e100c61805000407220703015030350092240402400708006c0c2e40a04444410000c0c5180b901c501d0001c255100300064807841080f1943c00c0b2048421058507840e024020402c00d0b50703c80c5c04622504801e04904448074201c0c0c8040c142e40c40280c211602d540d8541345c00790089408110032944803481e2007004e4605108480c80341c503090f02103600700d0624606100e1002ca01d0f400c441030203c4100100f01001d42d000480e1700c22550b540380005901038040c00e00082e8071201d000b1580001800003000580020606d501000002d14040c070289201a0000d480f206800c107602034001103248040100000c2c40c04020000c0d4850045c3d00760380000e46c400c0e08400d9948220343c0041c3c0400e0391041040c001400030820001e40310309071003103581d203410513000070408646510049481140c2450001d1020501402070f22003000741d0700e1451030b42c2a1108102031244041c44d00850082c800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 569314604 1250 569313354 569313373
    0xe01020606040504110f060c0a06050103020a0902040812071a070503060a0803160303020c031b030a0809011e0b03010b06030a090b0f040b2703030a0203090f2d0106031506030302 78
    0x42c03034410316000304d03441041c4000440c0383d5000d10248121056400d03600170300920903441250f01c10300c50002664414100010700e58190300c108030600d152074000c00381c924410b102c240445040021548000010b40d82403c1d11307107083d4640b0205509208003a0325601d02910207000380b03a030708600036501031602200c0e01581c01e5120541c1a90f02e000b400c11a041048818001501003406540181507070004202501d19002698001040d20f608140d480c0322039070f00015590401681c010412034000c1c030700100030710286086c55130100d441280c071941400101d68072070300840c1c940d4003507210442c00c0c80701400642c1c580c6800180303200184100710003a13411f40c41c1040068054060750030801c0c03143d64880020340403a00d8041ea1445144800200c211030a2182441082d01c99420400386100707510901000d41da0f03203850203249003452000300341c02c40b10b5805400c4021100c980441840c200030034040c0c405180000364030805016000c90760000d00907030f070054080c02203210303250072070801c2d41e010b41c017280c11400 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 569315854 1250 569314604 569314609
    0x2b05030403030333060e01051210061403060f010806061209060106031508061512070305030a110f0c060310050a0b07060606090303080a050c0f0c16140915030703120e01020606 77
    0x55000704c0c64419030403007000b0b00c00c240c041c1c01d02c9205090107140c06828100841841c0c0c08039201510720280a0507440410440c2036403040750310300c2e108602d45240b815801c00001058a4440c030040d41810702c030107080050004e071101c4069400c1d095141d2500c2807142000c0780c1440c3c40d04000c0c003440c40042e04040b0614800c0d0011202c0000710346c50503004007076503035880701d50710000001300c00f43c0317903021085070aa0b00ca210802c120f0a009540150044e41d9668032401e00a028010488100b1803c0c0d0002d13159108d02c4807002c14501c10f02d15041d40c1e10b9583e6514050800300b68980e41d04540c0d0322050740c2c1c0b4080340e0400c514000c0d00c0840e1180a0410040b602c038903007a030f1a0320aa2100600080c13a10000402e862000d801986c0c008a0302c10300181040b5440c0c02034101a000f0035941d0340e9981c810b48020411403440c601080003040111038102d00f00060401081c1825001410008000035031003101040392000c1001d5401903800c04801211031600d00002411101d01d403581900620454020400a1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 569317104 1250 569315854 569315921
    0xf070605040b072111070c0618170a0b07020106120506090114090307030302071b060804050601091a0915060a0f4a300c2b050304030303 60
    0x54100c1c9034200e5104034132650040280003060100348840d01e013881140002084040d0045c0a85056100e0094180c110304040c039820185030310444e01389095124089685001013105010b5036000501c03043e0b03580c0d8004050b4003404035507004141405c2c81440e11424018042040c2b806410120000d00c50003100325106c4500160550f180c00d0349800800c000740010f0301950040201d14864071402000c43c070004078509070708405502a8022820f000c00b04010070806104080c00340185400c10424041c3c11088035500420030b0701564020807620300400d922101c0c407103030325030b06290042040d91340b8404140024509041b64000402003900314000c107100c15000b02d5501c0c85011460708900e80ca144000311076401c04540d082c81c10b5080c04003404a031103515000c1d011040d002842070031908060000c01c594600b6100048807141e550450011108256200071140c000c1003449100c05030400d1750f40380c81c160200e0f0101380092052000280000c105501508007407a00c1100e210b0f54800303a08a000112001d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 569318354 1250 569317104 569317127
    0x9010e010c120e21070e0a060f09050702010b0409110f130509030c0d0e0310020a0315061e0305150904020324061c030906051804020c1b0604140d080f070605040b07 72
    0x4941141d5014400d104d0b602c0543e1fa8011011000403407226034034291111008130f1600441000c030b8880b4100710380d8607024010300400c0c40041e41d08000009840c3c87d103d509860705901d4601c034444040500c669a41c564a0b8070040003c260030800c1076007410090117a0342c0d405114101e103e40948031000204900580e903408400b81c01401030408640003c0c2980000e501013034842c010b056486141c3c09404d002c100d4080e01401e0780351244108840003050071180b503201070080b0b00401d0b0400c020007050703002c0c25001729011403081c1d60016060b201c80c40000d062107082040c07000c40000809200304003040c1c2c074114030301507802511051039480105e590380d41035102010010300422102e01c0104181da01c101e0043c401080804040360306001084001010317a07224007246003a03a44038120a08241100c55404120440101d0b11240340c145000400401c00d14903445461080300100d000c8001e0003046002c0340c0c0032a00d45941181c0e6296070f0300d480d50040c2020784056a140c100040000c034028003c01c0200360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 569319604 1250 569318354 569318419
    0xe040605090610030209101e03020103240b0a05160f110409030206181606050714160b1303080d0509060615121306020a1101050705070809010e010c120e 67
    0x480c3c0d04540030b00c030786100051b01c0020582c03002800001c202480110307441c902d500c4001d030380011500d14000103081d92100c0110343d0658000c91030800c0d400d0000c00b8480c0864000d94102600c990980b00241d484e8040c1c4900c5494281580a0140810442001040010b8401c040c1800851841014081114098a00100564020b1020544407008411010b0070360781020304a5021013032112a0048004650f8003a10100c0d1020075844100130086c0306c4c1c5190184e07613000404c181c890074114105d28001ca03124013045c0c030000281c9a1524010038801801854100c1c004558440350410b02400900086408455500421000c5400d40c60520100b40640411200240c18081d061600c507210200240454046100c1390015100040395400681030b4030b4825190048507400708000c43c2d0944100410480030803004100c03005c000b444010a84003100d9080c44c018160030100030041e518520034080140c020180c1c42090880b603648440356181042081c3c4a40e081460000c0001c0143d00c90b44c240d189 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 569320854 1250 569319604 569319631
    0x204060c02041a130903170c030c0703020102042c0901060612020a0323060306070804030f0f0309020a0e0105030d110307030c021c050d140304032015010e0406050906 73
    0x1015150581042078010445500d08a01c801042c001462162691012131190340d1113600c041d040c0760b0041c52101c064000c512866a02c0e1411058400140c80b00030090903100102103620401e00d407003581981c000d000c440c00600303095202d002c3c94110b0360b1700c2e50a1108c90748070745200040c004981802407008950964642c0580d2180c5042150301a400c100500010190388a028456a80700c203501c0c0a00d04c54107030001c0200c2d0030800181802c048004245406004000c41403000280d80403007144038400d005d160844683c1600d41c0c00714087d084a0300c010394441c0300d50070082603050408403103d0403038004400b11011501c0d1060299007208551810060b42d400a100070300c040703400b49506494130352001f454039605105886040403c810304550950f19039106460742c40d001c6e0342041c940c001c01800c40102c43d00b54030b029540206840061b503510310020209085030559648104200030400c4c0c52504080600c0da102c0301082c12402e01121300756489030418001c41c3c2810408245a4003d91003641180c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 569322104 1250 569320854 569320877
    0x12020901170601090b030c0310050f071b030e0f09090f06010602010c0c0f03090b0c06040c0b191110060e150609091f05090c0d050709080d141209060702010609020406 73
    0x118000c10702c912031103800d801403000741f101c1e81c3e03010710900d040d8080f020b100003502e0401c160450410900100610203029030034460225662440c84221981daa1628160354103205500228910520002181c0d2b0410300c0359060020406000c21365900781d0480030b08480c80c0b6031381e03804201d09840e04c0301c1c11200410365001c8041d011990b0b05449400f218004d05040c0b54580d0b0315414408581d00c0803940c08100d80110341403104014082c09050001e0140b40314050810fa100b0510840e507504019040d401d00180807440640040203005103200481203c8041002d540d441c41d00c49403440f422281804c070901221803205280c940501500c1c44681c0140000c429551800126061551700d590351160000090100080c280d5500c040c0520500c480a007054403504108100d100341c0b80c02034038031000c0c0300610805003d07001c0300051550610100f860181410401402d0070f40f0705204030710481c09041022800c1040c0307a040041c04030300614840e40204105c0b9510711040040340100d00131640003c5400c0c119 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 569323354 1250 569322104 569322119
    0x1c2301050a0605073206090a0804140a031707111c03050a020a020a0306090201021915020d1d010b0a09060e06010e06160303060f0e0c07020603130c12020901170601 72
    0x2e404568400c42200194500005d841941c0703844460280c02040c2c440548941c1180e0240001d90b080101080103003008141381d43d03011100d0003180115200d00d4005030f1102c1d03055480c0068a0700840d007125a11140e2054903403008000d602007842554062498092900b0a007048112022a01540c5c0170801c0050074541d0111600d034860a04c2508612403506070300b0142c0d4408a44070000c42c41201d000515000501c0060309080000d0443c0c401041e0329036501d0b000c60079180c000d0080d1502480c0040e0b844021114010081c00407a041b003440000c3c07100c184000010542c0a4429440101c400c41400ad40d41c0944200340d483c2d500070070741e2040f40c3c2c07800f04e140c1d94021074140c1354400e001080c40b403d10a01c0c480d2a96020070550050300080e0b00c80e402002600150f140f40070240c649202d010407140f80c02c1e54107a400380b0880400a000310300000000e280c60481040140b201341c0d010742070f8041305980b10321071414219048026071050042c000002080d0203050322210302c4e8145c00d000342c016607190214 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 569324604 1250 569323354 569323357
    0x1120f03021c020d030b120c0f0a0b0d0501080f190b040c05090a0f0e0c06040b0a052109100209030c0d02010302040b040e16030b0d171c2301050a0605 66
    0x8080301903204240c02c0002c058982c0d44007080a090680c000e141000070542c00505541486a0103801003240b046030442034000803070b4118800e402070310440400c011003404291042c0b100d40c032000041c040880c04851480d440e0b04a141203a034094100e9075030441e800301031500d030403034100d40c406050881c0b42c880b400101c1c81450f80f50b0040c02001c0c1180590758900204001c04021240c4001d02907031030640c40c070005014441c02034041162401402e0100b00324000c52030501c40c42c012078150301d4011809541c240c0c071510807541220a600010029013110003400c0c07141500664030300315140201e07400049072100d00d10a032440064020002c0001e18a01c4080c05052507404100768101074003004041400d1001d00d00400060510b04020f41041c078180c403440600c030071141c0100c0c04060400c0724100d07140d03485501c480880c0d500028885e01503d2030007a0502c42d882003c0008403182c0708000c02034003001d0317160b02c480000155105200740a007420420545054000d02840d07a11a281c42c00500c0303494071500 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 569325854 1250 569324604 569324633
    0x70c11060403080307050702100516171e0c01050f0408070b1e070c140a21050409140114090115050d1d0304080709060602030d0f180b100e0112 63
    0xd000524003602da03201d0801d01d0f4801c64220700412000120740c2c04504000c0900070100c451031400a00b80440c0c203d210785a003074000000f8209000c191407c007031000c05d940840700c1484103080c841e604a245031090a507190003500400090754a04000504000443d8150034840c41d4030280c414500701082d91556955440600404402885410000039280c04040614059665501c42c1621a5100e03c2c0502551030447d40c4120a0382290b00755200084101c800f1640d2a025048000a003001c0c24004480c0c5004030350180c0000350070115800c4216003069040c80c1655160180016090011402e1261885080c4140078940c000390100d0030b4420710860103031914003048400852400c4840540c006c241e40782451140c020742000a0400c04040100603000042c40491010b02c0440d00e050006910303401006808444680c4822700080010b16543c009a0b0000a04803205103141d07190500313588000013180d82031284200c211000c10700303000d02034515040310304441c07900c00002c1c41c0395541ca000c01c0520 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 569327104 1250 569325854 569325859
    0x10f031409010e0c190e041502130e090a03091e0305010e03040501180e010303200d08011511030904020c07180509240703200c0708060609070c11 64
    0x451048980a04249800e030240c004040082400c000702a452420502d070410403512842c081c0d070740c41020b4080d082c0d10008403081c00c0f0707180003582e07505c0c01e2400c1c40d450500c6541075001d1001070b544050b0400d0685402c04d4542d001480c1c0c000799500380050b50342d80420100070707021a1183d00c04005000224910300520a84e200c14041c200b9541e030ba07020f081d01c50034507820f202600003080c04d00155038071007224484424040c0d400d40f855403810040c032060310410701014040244282040242e0151a0000a0383c01506021684052218070004188840c07e00032003100c20720740210942802d2040307810150240b20000513610302a8440c040000139417052008051601464100050301100b0170590a2101601540820039280110889040c00e80740c546081036540c010001a82c0d900300b0000031a441240c60030b000900c0c2e5100f850140351400c02c00d801060b841d40c005000c0d07054100c08140381080b10190801c4480e1034a8200c200071144c1802c5070480001502040442c0c0450820901d070415004003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 569328354 1250 569327104 569327111
    0x1e090102041a03060906010c0c15020138031609150302040c050d06050402190513051207081c081b0c07170d020d0509060904110412052a010f03 63
    0x80b60400c40d449402030051070301e01c06003c000c1007030605018407615845a42440c3c0340d018146a607554260340c441c0d070300030510041400400d042c0b00354000d41c8a0700031610080e1040380088001c01110701d080c50b020042c07600d80c1000382030855403410300242e0944981400d9081c0c92030141081240801400e009441c841c84107902d09000015807500d208960300c3e1510b40d582c1c070340d40390390b8886a14195001036010358002d074410084500c0511806001150824151030b002e41d40b607100200c400422021504465442030f01c0080803800d405000801e0300031035220b0010790346880807c07800007500c0c001c0e20100201040700c41c80042c8040b009000024415000c000900d410078a6203070f240d5185c4101504010380080022818044042080011b001400b0341813005084500560074010454000d03100082d0044001040e410410340da940c101c1d480c0080c10061140c0c031a0703982c0e1211051608408030546e594001c000c2c20b003500d24284000340030080880002280320350324040044070340c2a02495400109580c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 569329604 1250 569328354 569328359
    0x220b0315150d080a11160609030b06010e04050a20090d080310080f06011d240d02090a0516090b1903060b191d090a020a0c12020303040c0501081e09010204 68
    0x103c2001e003061032a01d6a88451401c80c0d070710a1031801a820800160303140d00414204015a84010050103a9a11003002c04803034071400010380d0201350800e0742ea644617003014200b20049003994049240040b58001c0d0590005459001820034414100b009400080f15012140840c070680c0055070003130303507007200e4890310b036035880e9424200a6140d00c0c0e41d160740c00240c010440a8044510050002c85500080c005824400b400d00d000c181800718810200600050703007144ca80c0d61040784030b8029000b1302541c40328a44810041c000740b508961000c0300c0305c460310740241241c2c4aa480c42c0140c4403210a6a0300c1c140c0c0c1000d00c4500450105209d0040503103d04011071030360056030280040c018184480c031040605100c0203400700c00d60b0003071044c0c5128100200643d0341d03541400d281d00300300003c00040e510a43d4a9040b1402c581034800038006051802c94482142d43c000b008501c564040c007005041191a8001155400000e0340d409500d92401c1e25181d155850700741c4101d4000302040001440c003070b0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 569330854 1250 569329604 569329613
    0xb030601140406030b0a090507050d0b06040b31080601140303070c08060420240f07030c0501180b040201110a0203101e050402180c09220b0315150d 65
    0x42c000d800070f40021740c488048201d5418201140c1c1c1c084c1064030010320891402c4040100540124100001351548400c00d02c4196142c00d070481d0068a14020040d50b21520901d00b04d403200b00f0800c40c01ca425001801201e40314126001c000265681c11026160f280d01e090280c064650151119035450700040048900261030701e108030b4000c06405019004600d070504000340e90204510012810403043c0300c101e9402d0b9035030098211030800d14072000e5051481415105024042c80f040c19011300e8000a040c000c2c5500101040d002d1403003a0000c0c001300c20700001c003484035140148020f0032101e0410100300158040c10252045025800c00c41c0c08444903070700064601003000e44107514a569941c8506400803400700003504480301c4401c140098105940800c40348a11f0a01d401c0e004d010f21404500c40e1280c4c802103c6906000414400002072406101481c503203032100305d5441c00745411807120780360501048000b01185078a070640541c2e41c54030039100e01c04890142850340240500721880005 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 569332104 1250 569330854 569330857
    0x20c091009150302010e0d03081b040e0109021e0f0a03020d150e09010e0a05070302090712090c060305010608190506010c05010f090b06151c1b080403020c06070b010b03060114 77
    0x107030480b11642c4410340c41d500000d005407140c04215402856841142000300f60003035402a0480072036000b5615a001090060707010340103940106420030080000000e00025580140c00701c0c80300d03501080b405141029200c00d86200702c1c0707030410225a06010074480d00c0d002e540544101d0141240200340340c5006034503900b0b2240b5542003803c501443c0d42c28040d042034248140040c0c0c1e90000007c28102030340e0740f81c650b03aa60032440024400c0360704200041310b95104c1c5070030400040e0b042e6000d11803d8010306e07040c902d00040307020304000281ba060001403520700c500e403824001d02c41900c1a5259610262414018040080c030843c107008803640c158000620920a00300f44e849030603070000f1842d00c60700d41044248000780c4513601c541420900c84070001641400c894410000c0151203d42040000050003d4040d040180030424040203202c080d90f501f08140038032841c400d6080d00d19007540c940401c0200c0c0103145015207044015801441a001d02600a41c0c01460505048192000c010081d1516 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 569333354 1250 569332104 569332121
    0x1d0c0f070302061801061419030b040b0f160503070c050331051f03020c120d0e010609050702030427061215140610120f020a1d01020c091009 62
    0x164412010007881c030882a940004444d41c0000900a8525045a1410704109442d15920650b040b94000a0a95040c41c03803030300465000d0482070701c61800f810700600d001c100329480d24080140c10300054001c45600b1410701000c141d501d64900796140c4043c03c80f40c8200303100007201c1922042100700c070510844d80b20300b00d0382c42c0d6200040c42400028040c001c407a1505903c814040d40120b4000d11000ca03240044a400440500e00180c9400700c50201c40c0c50005081e5044494020001d0445855501900301c01d00300c5122100074010b643d03544007034004540b0100c8d440030040c1c005002c1800b05414582041d01da04007502c803000c840d03240403074182c0c04a6440b41e100310501c8800102032000c0107817203400c295040203244d5080100314020704109010490003400e45124000202664140701e02070b842261644640800c1005103940d0300440d000294040708864001c100302c01d58011080c000030bc0c0d10341c03100f0410390203800c01054000c140411010040c1c00d4002c2000350610100f0403210344c2c42400d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 569334604 1250 569333354 569333357
    0x17090d0f05070f05030d0f140606030117010b090c0d05060102070b19090b0309030705070e04170c031207050a02010b3a080f0703080604020c060c090f04180b101d0c0f0703 75
    0x10318400440e8541f04944100b22400c0030880044c007004071036038400707055a0440d654000c14500101ea03400c00b041c01441890303183e952101e01e400c1409850080e80000c1d158a2600010400c02c030b4031000016a5680d030944541c80354110100039104070b0995090100b00854035908000202648590601560750811550206241d001048045c1441000c00c2828020090a00011114102a2140c52003298012000c3c800d0210004500d1030b0389008100700d444105041800142d05d08003035038020465400300580d0300040d800e1a20b05011454100c00445104078502402500c242d001c100342035108204003c800800100082240d01287c1d40c0401040341d0743c180542c0c1e961702e9000e880c0103080c41e0303806000980118414442018012400036490390483c014807000e503201d01042000aa00c800515250381d0484d0405101000c401000c4000312407291280440000d16035500500341004042803245c0d05178441641000b148400811071f120b03800c03030b20884240340b901101050703006807035100150860 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 569335854 1250 569334604 569334611
    0x4050607090b52020306010902090f09070c0507030f0b100302130e10060b040806060105191409121c0201060f0501030b1f17090d0f05070f05030d 64
    0x30420364040c907640d0140104840701420060348040301c80302543e480c00040088450440040d000798882c96112100340c400f9244119030f100c05041111201103000d501320700038480c0500200e4885807074026102c1928020b400300d44100d800404200b40ca1070301912040038040340030f950303001140c000d01c14071010714015043c000038561203140c41c02e50004001c0503038004003028142840142e55003c01d410140d00c0110010075040781d041034450600c1140c2c00300c040340070703d8020009844a48803003c2c00480c0c0000341500c03250b0350368034010b564a100f525480c43c2281241a150703184a0f0181d4044c0c0490f191201000341001a00400f007080107101500f10081c96202d15103140c0311000c03048814804120503c003c0c00218502811603100e009103025060500d17442c3c0c0d80c0304442c0c0d1501d2100c01106881c0b045030400d00c2c181c08030003070203480d03500d000c1d2544d200d22800000d0700d1706030000300d0482d40c9040369210707841d001d00054120303503035041030b10112050f41d81a08001d02103481040070345003080cd51400003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 569337104 1250 569335854 569335861
    0x8030702040b060705061e0f010b0a05130510180b0405220905030f071b061d0411040303080f010e040b0402060a05160b10120c0509100806010909140c03060a0b18040506 74
    0x1010547c40249514143e20082c8010300880c1d5110003501e0001c00182407860710703011500d80e403521b0240302c3c1e00210f400c80d0030407002c01c2401c6d0348406e00501c90112440382448844d11440d0520f410710440c00b41c00d4101a40c2400404c00505503480500040c0030f928000404d02466a651402c55004401d8540502004140b000078441800c0407856480101c0c0340798454945003450291002291030013004900d030540e000c001440e26650801da5440d1720a03481d01c2d44d241d4a0b854003030030000f410380d0803c049130446400855880100c00c4040e016030303080081704449a540b0b5080201c0b41c0c0c0550310782c03400c02034103001c00550780010306040b40e040b82c401da07800c41ca03030320b0003400028000b1107a6209600c1c010302d20a0110100368810802c0050315404c0d03c2091141d6a9601c3c2007100300c000394032038030f428401c2000005801c801a0700c11007240744510004001c0c80c2406860959a4282d00411035058104e800031a11114484c1d10004070010007414a94112028440c0722002001c22a42a14248c00241c1003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 569338354 1250 569337104 569337151
    0xe210c0c1c1b03120302120c0d060e010e0a0c05210403052505281106040f0e0108060105062503121802090609102d080f0d020708030702040b06070506 66
    0x4c81c82181a86411410f09060000300420400c01811004e4406400238100315036500d190401340140c03011100c001a40d5171346580181c1c401a08075402da803028070f8203c2217981075204500311030450f40b032306010702505000441102040344014104a0030700c9010090328507503561801c8101c001a2085048411602050a0841c00c00d0301d2040f4006c49800e14003145d4031615504403085580c582c005152141c107440a10115402e4416504919140d0403000800030305a0119924681030312442e0060b54111390381e5030280b024074007031300d00743d1406c1c0d998070303514000c0407003042541652642c0240340000d004d41a289900d0101c543c84842071500714000d954000550070480703c0380303401c004162003100551070044070201c1880035902805030020400d00090081200ca40c0d554265814220003802086650b44003069446480800042050082000c002d1502d400451210221070700d2001542c0713000c0040e4200402404510f21641d4400018040080415401c002261045084020800010110084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 569339604 1250 569338354 569338373
    0x3120b042c06060a0311040e030705030706110a1e0909061203030b061809040510050f1f140607050a050609030406080c04030f02120f010e210c0c1c1b03 67
    0x918002660101c0d080c8403003a12407000703000403070fa007010700c2032084d0f1801d03400074002d803080748e605003d944004681d00f001c0c0302021008000b100e10a0704100f104081211007000c03079001d84102c82e004a09281d41c191408920760f00d0700f5580c240c4a24005004a40b1084032100b01e13056174000074400c14011001c501019014407506081c91021a40b85090500c800040c00c40b00392039100e01c9014035515404541086420000200f46026900d0240024901401c0740a40d0300004c030340b01030080c0c14801001c3c400d541009078441c152510352160303203413510781d01c0e06001559001180031101c51141c1c500300750201d102070007600d02441602020350750300e40c50040700620341d81000d000e50350802c008102c2000015018910484e00f00e906a44c04806640040c2c800b500300b06004004060380c2d400e00c42d114003103c08c00301d07403000c481070b560241191807490300c40d2800860140041c0c3c1c45160b03000703141464141c68008088465a203150348800824102ca036034258880c0004000301c007003440d80302010700c01c203d201c40 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 569340854 1250 569339604 569339681
    0x20d0f0312140c04151b0803160f08040201111905060a060f06050d0f02040306090320010e0604020f15041701111207030e030d020c0c21070303120b04 66
    0xc400d0b0070781c03c04020701c440a224500c2141090707400510310320380c183d02130700d03000c0f07403050300904202d1600c010780c14603045940c01121800c40d10603003280a0750b20b4600a40c05c0303000d207800c01c3d40e07421400ea643d94015038200f0203203940060701e0702c100c507504a40201c80413100c000c901d1095014001d9030514030f00140c165071a54004902070700400801f8441c25070f02c40c1c20755654861f000c00110b6086584d08000000784100d8001402071828100c0c0308087c0340c2c1100020210b981c2c501da0000042c400388984508840c10040140d030160480d601290140c43c154070040070b598001000000b140310502481121640242e005110241251711210181a401c0c46070701d403426011441a0b00d40001900d000400d503c0080810060640e100c2d003103032601c4e100300240c41c0780c020320803011903031a2141103d042d0703940034000d001445145042c0c000080c210060f150750440c04040c0009002140c256a81500c901141c4a203030408070b59111682c5000340d407180508000c80d210340c40d040100b120020415000d011010 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 569342104 1250 569340854 569340881
    0x30c250501050304081804060513020703080106031e02031f0312082406070f120e090a0603080403150e071401021b090601050f0c0304260d0f0507020d0f0312 69
    0x40c004c0002284d07a0034101c4481e420395400b45444030303a60500160081c02540c0185801000c0c040642d4110511a030003483c2c140d009407175400c044d81c1e89100880a4405908014026070039102c182d0052003401c2d006190014049009462240407080010000104640c42694081c140c0c8552220a40c0c0211146805c01c04803100c6100309400210360980d464208100d003400303a00c0014a045c01e000c2400400c41c01c4550160b0b41d01d040260108009000c41c1130208650300c12a500703408241700e200e20b4404d02c41269401403400d401e1620355140c105d850345c840c00015180c140c440b0354400c0051400d00080c4098030400d03254501120300c51000929240b10101c4003004c4107940c07110301a040d904c03507074284d038001000d10701035550f0024240b80c03025a001d4000b030062036210100300401c80a0390000e1300140061000c7c8144a0302c41d0f0290010f61b203000c800810b4020034040c10044000310b00c00c070010502c1c0750020b80310190a044c01d6403180303140c5490803170903400241040c82e140b400d0302d41ca000d03007885041131 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 569343354 1250 569342104 569342107
    0x120606060f0305070507200a03050102250b16050c0604060f1b1e1215050312041406031005090901091b05030c240d06291605030c25050105 61
    0x21084c082c0c51032003640c40280001910f0b41641e005410003282c2c141c06c003100070740b48109131503503454001e010707400a81c0000000ca000403031182040c0358151b1000401c58111480304c0258032000c1c0c02c0d02c9048040708001c410440e040101c0003000d4000c0101600561007050000b50414426040034122090110340e07552125a1502c121841e951001004041007030310120048030310362a56050b82c0002041c1d040404035410700541b441002c02006005003164415000d56a03013a02c0d40b9410f200d58840e60185000f140806082c100300c0d41402d0000c0c55002044182c01d00145440380001054104100c1d00c10b8040c0c0c0d1030ba07402000f08041020225441840018480c141c541407200003901d840030201194043c843c80c1900c402505007064010303480700e4080c040c0e640e07500b1407840c401e806032105000e5840800100120000e200c14841841c0104040c41440c00381001c000c18100d49010089000c11380301d0f0f01c400e00001e1a080c4003400b500429140099003099500c13038060740114200c071381354862414040d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 569344604 1250 569343354 569343361
    0xc0506010e010e0a0b04150807080607020d170403090518070e0303030714070206090a0b031b12040809030703080301060513080a0f0227010308070b150604120309120606060f0305 78
    0x840c0f168154105902c150003013104058503010074000c00191020301d43e041c2d80c4900004070280f0108502c03003903480d400c064030340c281da800c0420707655011a803604000050417000c0340d4000e0091031708250381191082c0340140c25541c1d6500000c1e151100c51145007131900441013802441c0c3c3d008842c10312035801c298003850451800020140144d0802045216120400200c4a007190354000489802c48402050b000d612a211050709003c0d4008550801428919403840315407050030390709403a9040700c20064003181d03541c0d43d900c01c001078000071034103034044c400c503580480010521000355010341039560300d0540701e03440400341c40b42001403544501c0d042d030003107001c0002040402e80b4880c101034069070801c0340702d030313152803105d075000c0c0902660111202c41300300100030041c0e10001851400d0040a142c1e401c0c0c0c0303c0a035810400305d2400603403544644204800c20803021504480f0b80c481e4001d050043c0b004e990ac0d0804811500303140012100540d4038a418809517401041500301700791285020420b03440c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 569345854 1250 569344604 569344619
    0xc02030606040b040f02070606030b220212011409010e12031605030c0c19060507031a12010f0203010306020a08130c03061d0102070c06030c020d0207141507030c0506010e01 76
    0x80c0c0600041d000c1d81e11609500340e6511950803c0301391204086045540300c0d007a05001d00141707182d0200f141c0d5841e1050119040e070103440c13005100d002d01c1c1d005510f91040c0540c01c00401c92610301b001c81c415502c0d43c824105070a010340000b4455510340c800410844c583c0d60a05061008044050120600900074000e031a000150f06522450300e074109266640c4071808a55404d0150f14072100d140d21800c1820071103800317019117180d2828803614042c00a61582c7e2019401d039800c84110b0380c004904609100d82a1074806000f80002001e100005070509480021009981c000d0300142c0f11a90000b0310310050030b07402080254802c0f07800d1200c50703010029958110305480c0a20018050586412116080c00300b90480c180c00d8080d0741d002103640b0100c601c1d0000400166100b480701086c130380040500380038000300e00c0743d801c068a0380c040d09034141440c410302d801c0c006c08400d541d00417205036451688201d6450040202a00a8542c2c0842c1e00d00c074070302146081d0050300f00341c080340d11b41c2c0300400661 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 569347104 1250 569345854 569345863
    0xf01060323030f030402010201021912060e040803070c0615030b041703060109030602070215072a0605091e2e02120708070302150a02090a140319051203160206070c0203 74
    0x354007480b141513483d112800100d019015482c0380450004508190010240d005000786501e98090340050110f65600d00c100c00d40c0c03040845003c0d180c28410000501e080d8400c00c2c0b602c0700940728510024036154100c0c10349000c1c00640d002190508041010301c07080c40200b8080b180d0315800307824070b146140750050008050581920009040c0d5401041400c1156950209003110701c2401d0b0401d621041103041c410400d04441d000440303c003c0b6040e109440e00301d2200d011041d1481034986526082400040c03154841030071002d0304a280300301000c002c2d41e956100014080c10140c40100820036050701b841680c0c000050b0303000c0f05541c0903414031280032138141c05031070140b42c104003400d8032071003542000e80c144070440d081070520310130304070801c46000b51a5000d0301a02005984a90304076445600d03c40b41030b240640540d6065121400e400d4450260055030a0401d200d001911030a1822892400d642c1d0020343d6030744215844411001c44044d4104138a1742c0c0a0198581540040000e40120703848 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 569348354 1250 569347104 569347117
    0x1b2703051207032106061d0a05060c03090d0602070210030603030c030c15050c0d0b15030604020c0304180506090601170a0b012609151504020307110f0106032303 71
    0x441d0210314002418018059900401c0b40f00e10f90306a01d504d003080d184004c20070350081e0004516402d44102e04079028600700c0721010005021030b18500c1c05c20341084519005103024002c1d6200803c00004a07481c0c040e00c03000a6485010090b03120b04107441008681c589101000f01003502d0250b042001c240e00c8403144400503010b0901e001d1404040c10000e10b4030300c0100d8401c4103641004188080c15400304010305414010000401c440310a000c20000c40c410140700300d506070b16050000c55283e1500350300808594100c0021030745041e070340f80c0d00d01c0b2015102888000c03840d5990810440300d0304007003c08682c885801d00e498030303d0064040e10500d0110001d0283c5c2019550b9044400c03841c0d02070552180d21407007aa03200704440700d6001091060f4002180c54840f01d0144c12a010b41c2c0450b0300300c8040c080c035a020300303044042c0c84c0c0c01d043c00002d4000618a808101d500f035180080582c2c2407101041008208001007602c6045050480c46442e03412400c0381c1e6a008840c11920309207010098405 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 569349604 1250 569348354 569348383
    0x5280804060e042d0509030c1f02120a0501091d03070b06010e060f04170304060f0c030203160b07020106050f101d061903050105010504030215030a1b270305 69
    0x54110b80901040050440e00000480910380c0a0020803680c400c124007070004219660511540e030701c02c10096182c0c05100701400c82540f0100203150891212a00c103098440204030042c200846000d032102655020f41d850451159034030b00500107a0381c68000d1740700d4090141032458081001345c101903524852802e01404030384900d00803072410383c860000054211401005c07942c440b641d184040426521a00c07441d200d003c4544080394400302c02000740c4044424580754030103409601403080c6e65201e21500100d0441c0020450003650920446020148902940b000f42d40c03883d00c4032001c0d08540154014a209150f50300075001c1300d80c1c0d03070480c440c04600c80c0c8c80d014081000c00004182410b00e180340450f4410750114a0329a0004a01c0c0741c030140062a907410300045c0d036210300545042c4250300000e5004070300c50b88525003600b100002141c12030540840002c2540c3c4440191300400360001e54030f800200a514180c5202420403207103003443d402c08032100d00b082d03d9540c40a540d807041160b10b10 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 569350854 1250 569349604 569349617
    0xc0e010b0306010c14030a210b01361401020f0a0209060f040b041b140403320703032102030108060a0504050a080301150906030c23070804030528080406 67
    0x4200400440c9940ca070145e108200e030b4403002d6008014007841c0760740d00740541c8885034090396009680d081c0103107106450180c4912030000c824880c2030950803045400180c050400c817005402c41801d510000300141f44a01c1e40702080b0f0ba101c00028105100d2049066980c0e20074a255009650303515600f5400c0f01c000c8135590001c2c040c0e480410003801c1c40305c2840743d0280c90520501d040341e04a465003103c000ba260340b0b2003c2250306e10324914490080740005002d030070640021412a81c145040c8001141903000c0035480c0ae1440501140f83c200e01c0d810440c000795520406841440c9041050800c00e42000300c20f60640d03060821080d41c0e40c5008010707800749a140c00c0400c041c0b00c0f040c802031003066040412140c3d01d40c0c5402c100c401c004000c948c40000104103000003d03c292180c40303444801c203610b40c1c0305d1400b550700300d483d000c2c00c0e02c5d1600540ba650008108000000d01408000c1000b54800e5014103951501504080c0c11110703d110342c038005000c81b02e00c210004190f2421281514094205130 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 569352104 1250 569350854 569350877
    0x1107050609030709020f090405010605070f030e0d0209070c0b090316021005090d1b06050c0a020103090c090c020129091b040905010e060f0402130b1b06130c0e010b030601 75
    0x64500f103007a0f44480c28030b920000e684520307241250005d10703c45d82c1c107680034030560b40d07501c000301e40034403d00d40c1c040e003041c0003000c80d44002803145410b199409002001c0496030442d940005009000a40e030307400c00306841c0c1c0580d208204100c0e80c4154014042c3d0055424803003514a1000c281184107802441210310790189400180110b0076903503103001c040c1402103180c0d290700c2c0c860740c010034081094554240d5410000382441c0300744104c804100380c010180c426501c00e540150080c1c21682c004a0f1500c000307410100c0c3c01c49080c03180c4614143c0603070001c0f501012414a084500602010031602140c41080c1010a40c03101c102c0b0641003c0c142c02445001c0400703840c2e054860107590081c864050408000141a120003240e41d8020300e001c4039140052404001080100e110b0240004003450140000708500440c00e400b82c4551000e6800102c0a0244040d07600d00301103003199560003030341004032508107100e00071403507030301900342c0f1030b06240154180b0950380414000108440e041100701c51300c2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 569353354 1250 569352104 569352109
    0x2070b0904021b0f0a03030f0605011b140f01090b06090403170a0902060d06141f0c02030a080a18090e06150301090b09070501031113030f14120d0c1107050609 70
    0xc185120204109840546000243e035607103909000c5c0303059000a0a001c9050702209842c803030141203860503119407419104803001d912101600c00e006031001c5804c1d40040c04841c000380300711000c43d0941400003400c00101d103010420a00c01406560003206148100300009400c100300090b52139910314480303150341e0f6001c081c8024105060000b500100c0208201201c0c0c81c0304d400a105039845040720b1450000c0c0c1506024402068444607003881c038124003920f01c00c9000302e61608405002405481d0140003a4070760009582c00302400c0400911004801c2c070b40a600d1034919005030280d400c00b0300c900001040030545d5090b01074002440c4524149080d0300c81d1390300750710920140d607200d8002c40d00b51500d03024558a6480510986000c242002102d4001a5040088906401c03060a903c000282980ca40021010091004851000c81d0607142048540200501c0c240303d001000c1c61035031000e801e03612005036803100c0343d20014001c000ea4041007000000c290041518415508940c031303012071800 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 569354604 1250 569353354 569353387
    0xd09080607081f0306061d1306050a021314041d030a082d0604050705280c0203062503180b282304051222060206040507050102070b090402 61
    0x2941d400703030f1078020703000020400c00b90440f1003118030322804480c1c80e00c4801c2c482c040000d8100e801c0140c1e120004820000140c483d4403050b000703101818014184511040c06800b0401c0c581c10440140f0f0410800f03803028986801178080ba903050f601e69a058005600b403084da07a0145402d1072003407025480c0015401030f001221240048450550815103c0300300c81e0b05588518151221070160382084c002901d0140150704503003803045140c100f05543c071403070400d0164240c0e0000303500d001c005843d41180003580c0c0400240780282d04140f0001f5196103500241300b0f00c604c00c108020245810400301c002484c0e013030940d08135810b81180c2c0410b91961003400354134207030b0301c0f001c01c8a0041c2e801c0102c024500c50594000b0161001c03012604024031680700d80303204002012a0020025408182000d40000703000019200790040340425000f204040b00541c40343e200103801c400d0042c0c0c8040100414000104030600c0181020300207050214188001d0344260302c14000b2140c0540c0e000500103102009021 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 569355854 1250 569354604 569354641
    0x60203130e040f0f060209090c09061b19051605011d010309031403010621020f041a0d060b03061c05060a0903020a0f080a020f0102030c09221a030d0908060708 70
    0x5000100d03071155140c0b40d40250030000c41c00740519080000202c03543c5d27081d0115818103200402e4142043e81c46844880243c42d100d00014a40c06032402880516410143c02e10102e80b01d080a041d01c0546801141c1d80440a03610413030402ca80340343c00c1460031019200c0202c4101d0300f031030082440c000c07a0405072041e00f80b0624030342007035a00000001d4003503070210301c00c00c02542403a0010a4041007045403020b9000e03210381000c0015041204000c090708201282611080c00c1802a00301000000c8600444469a0029460050000400c5501d2410079440224004105040c91004449845103544d03a80020074003441c1c160348007020018036008010103100c0e558000424440300d440d034030b400700280d005040b84101500c49d00030502410a418020f0760f00c6207440c849503034101072405082000d0400128040c0d40d600d4010098226540d40c51f008413401c100d04038030702582c005481414180303040a40c8025400700143e450381030080041c04100d203900301c005e45ca4505000d40381d02e08940401035400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 569357104 1250 569355854 569355863
    0x7080406030e15091c0815040b03101b030606030c0801091a041e14090607230307020a03020c0303040305030304080c01020910020f010c03060e0a091713050307060203130e040f 77
    0x34070800a100d41300096103e21103030034460789461100400c000352024101500c042a2031144209580443c0c1069480314680d210b00400b16071600311300007400000c031f400c1c6c061001070140035040d4100b10981c150081c2c8004049518080080081c0e5590040c0b21290600174003440b161107144105940e00c7c40c0c4000350200f00d008008020005030945204054038600007002405410310048000f281461265540710b602d601001e0092a40c6a030310440b101c900c2c2c080844a1350b4024000005000d401c0c1001e50300c95003544e002070400804908019161100d5412600c0c480e41c0b040005000041010007901e8100341d00c407003200e413105069207000e40603014000704a50043c1300c40c1c1811810f40e81c0000d2200201480e10000c005a43e01c15000b01c00743c584c02e00030009812001c40109555a106a00090305c050140050300000032100019074402e81c880540c84002c201d03000b00910281ca014172422005007454002107141000311121803201c0ca50b00d10503041411141c0c8000703020720208000d5401080d500 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 569358354 1250 569357104 569357143
    0xb01141c0f0606021c0e03150a090b01080a03080f090c040203091c020615040501031a09010f110904150602191a0103141506061c061806060f030207080406030e 70
    0x44020017952121611603c480311039982c0d0b040d1003000e02600f12407188400207405001d114940e04140780305100060b101142e043e40d070b0341e5131901042400141d2806421510050407a010039410300400045000d0000c800041300c2d94180030800500140f41d20085200380c60158490343c4002c40d86003440c4004545440c6902d2040e81302801e13580c0454034500c81c0c2c0c01028801c3d0b140103c074043c08100c1d2400d000c0144985801304070040c4000c0b00780001d641c4003100b40c0011901c1100803130540f042c0c030110900c002005602050280ba60319040c0210b850300c11202ea680c81099243c000002d66030b04d003521070704814080d460000d10a0052000a483c5000c94600c2000410350352444c00d400110a240303804009405480049050704503070424460087d54002c064509080c1e400c140f05007d000c07401c5400d1031140d40c600000850740b850401225603c0381ca2180018040d1810501611068002c2d044400f0036104210082c0000c0301001551b064444034600011169200f4205618110603100b41e11031440740c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 569359604 1250 569358354 569358359
    0x90c010504091508030a0807080a020f0d020702061303030509130902031207230606010e01020d020c1c0f050604030305160807030207080c030d0b01091a03010e09070302130c030b01141c0f06 83
    0x8001c0f0140e030040c00a0f40d1042c00e550b40791844ad008030701425012800c08641000300501010940e0081c03e6440d000600007450440701112118001c011640b00720040307840851030304c4403403904484290400904071024450314206a0020791212400d45030048c0312040130030581c05111051a00c03000182c0580700103da61000030300d25685d5040c0880d480350001d01c40e104815525440499008002b0045400400081041804101003810101e01d104070909414a081001c2101c0015800c207041c0240064402400e00c1d040c001e0036200d0003062103000b0680003110241d003650000916a0000343c07440c0050305d405582c9003102c047c1c8508901c032680c9100100d010b440c0d80100380d00080100209072030341c0c001030380d50303080200c4410741c800d0b070b981070b506c809000411030018085160355003c003060042d01c0240352030740c2c00900030103001e10b0700c0c4c140a0395641d00c601c4001c5d01807045141d00d01090030070502180e01d0a40022262003400903000600450a44240a110310f0307401609544807080b205104c2c0740d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 569360854 1250 569359604 569359607
    0x9120105060310060b0306130b0402160614010513090f1709010809010501050109140d02040227030c130c2a050c0621100902070f0506090c010504091508030a 69
    0x4426601c03507202c0d0180700b00086080103244100c4049500703003400c507400c680e244420042501c07d2904a85c80407919121561010350b221b20082c41d091411004014111409040210850300c0d0005c8a00f44c01c0c3c0d503100140700c0ca90310f0fa81034551000f5900c0780800d086040380b5100c7d407000280c24000305039001803004540300311220409005035400a984802095031500d00c41c0e401d85800303200d51400704040b02c00c20701c0f4807800d43c2010600c9400140c10314828045a40c041400c90388848089400400d11000c01041411424030351400044218020240258104005480c0c20350720055010040c1da100300c1c1c0003c190003007883d9140c08890024031208507000075508030141006030011110380c0a071440c108204c0c82d11500f0f1f134911005000d4610120304800c103003c80178190252500b42d076021050340000b00001140000c02c41603101e5a45607290405a140c40c51400501400800f01600711001070700c05a4ac1c050199007c40b0140d1030003003110a51003102c6030f4400d07010340000240e40000500464243e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 569362104 1250 569360854 569360861
    0x308031317180109030b0105131e0605120a080906160605090303061011120310170a0c12150203060a09021207020f061b0d0e010f05070306050f0307030f08091201 71
    0x114400101d40c9040844000111402c885500000f0300201b044001480b50381808030400a0640d50381e240044c1c4107079540b1904041070514a010300400c1c0c0c803000c0c24401030070b000a010802c88580e000500100341d407641c6000c084d010758128140034240108018205149603800701c0c030000c1d000381301040701e810300c021910b803a903001315803041c0158030500444c1e0708079100d10804081e00c12020003520708a120415107039282c0c2d00150144e23140000c40c090125000c0e100c1e802c04564141102d00901ea8065289050f084c2804e0561004480300c45810880001c11034401c41107043da070341448016960342e0317500005003c3d481039070004149a4400704103000c2d4000e14035140f5000b02519000c0301c50403428920a1503030341d8022181030f880002142c1c1c114100c9100c44014000d84100700728081484202e00c0f01c9030b800c65140c250326105658880041c44034607501845084040c2c40300340c800550301454a00825034802941c800184908507451201050210640585d560709070000c10114038415030f181141d000c0c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 569363354 1250 569362104 569362117
    0x180906021908150a03080a02070f081c030b010203030601030c26090c0603060120071203020d140a0c150f0e030c07050628270f05040c0503010308031317 67
    0xb280d142030101d4940b0250942c0c11400320b100904038100c050450395500c0007904414084401c3d0701c100303140400c0700f440800600c4081d0071064000c1081c40f038004041e00781d6158810414050501c1c04100350b07540d90307020003141e51000c03084c00c002c0b40e00703100c00390100e03840004c0e921010f03100120324080910078104040d00c10b0003400c03045d0403550044480810090588400e403a114086203050900d102b04da10b140340003549028800060300e0350181c1c0c41c100d0b10202550380714100d0041e041640c5034401c864110300320f00c144002e0400454280780003500090542814079002030009c525038003541c00d0f89407880e00300c02a0045000c00500c03543c02045103296aa4014185150b41401121000706090a094040e43d65541c1c02c05503515442c44980c008404440c3c0b02d086507c20480301c441011f2a2150103001904084140b44c0e071800810320748020f445241c3e04070380205124034246220084015404400d40b81900d4020100642d2a01e4100c0016040c400030703c0c0041ca030410350900f1141c0161840c003d00170 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 569364604 1250 569363354 569363357
    0x7080d0f0915020718020c010507050c1e061326042421142401020601050915060c0106080115052e03020f03040b01060e03161809060219 60
    0x100c81d41c07111074901e02812494054401a800540200981d01021805c00c0c0d078050408001880e0082002400d42034840480c0c5900200300c00044044080404110b11144030141d10307803400861031000c0ca810744680000e0002c40445040324124800c0c003000300d40d6403400c9005186040d0318105803c440c0e00741d9030481d1244500c010507400300450590040c00d01e000e01c040d859514012052411b40d03042c1c480341d090703404000c10903a9845214070991180000d050182c0b845104c07144178521203e00554009152400071070454202c0e0004002d00c0c0c68903080c650b04100300051000d082d841810104109024030700d19000650708101c40090f8440d03065210141090105003204d40032038640003405400a1000c0a5a2324907603a030340c1c072203a0b600d03002d4403070a12138400746000361600325402d000010130b800c15103003500c1503004c0324010484140c010031549070380c0f40154090424a20891480c09502c011480340c1c09003158190300c0004680e03210b41c8850f282a82c000000c54a078490b440001000c440341445460 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 569365854 1250 569364604 569364617
    0x40201181e032d06021309090c0e0a02040803090d0f0807060603110a0b180105130311030d0305090d18030b07050315060f040302010c0c03020904082101150e010207080d0f 75
    0x4072039540c0044003440300e02c00e038054200f440155a5540e8000d500c0000084109214030720045007a0341580510390a02e8000c0141c00290f07803c24034911052640074100d4108188104020480c61030080700380e0b549118119080818900c89040c200c80500c100000103003807a0002175280104001d40d44000152406980d0491206031000c003400011505401100c0e401803051051054a6442147c403039000e94042c54541c0c1485810590034070048265001110940c40055080040d4142000904003000b5507140c00d01c01070034071501968075015007214800400001030035070380400c020202c81d1401190f203d41b05900914000500401c107070001e071254a01112103101540d41d0f46403550030789034180503482030149001c0c515401541c1141c2c1c5114200ca02114071200040581e0b5070682040c440c500404074680e80755401c0080e410b142400c0c100c2506050120310040c01180c1c02240c4120440629003840805400c01d0310041c0e250800c69032040c0c101d48566003a4800050f40031000113202c445544890 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 569367104 1250 569365854 569365883
    0x2d09050f0a060f060e0f0910050702010b010809030405060403120c120f0f0c08030c1b010906060816030503070b0a0209031c0e01050c300403050d08130209040201181e03 74
    0x3d95011784610b140a0241d10003066610280d10182508454a20221032100c0001c1f0741800907250210b4404026035550021002d440d60031400540c0d21590740005107140074101000034441d40181d001c003034480c41030b000700401c0303143c0903075031001c041c68200508010300110214003c096404030350b46100069100074401404c1d03400f40c810388a81d25800000241503070380b41d2144c01505d8015401e11900340d83c45000b00d11103c80280304074034044e402400040340a500382107200346065040003501c0a032580c2603d0410110f5404000e407410b03039605c84e000200780d40b55010003a01034010340c40707072650502440070384036650440b00c809508032710319544031440811005001511540607513011480c02c0e401c880c000b45403039516481f680d43d004100b9465000095010685058941c00507001201c00381d1009060340c410b9900020100d5029070355030b001100c007800540c0401c041640c050402410320080b03585280c000782080a59001600142440c0c42c00d42c0c25040e4250508a8140b0094422071080d9420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 569368354 1250 569367104 569367131
    0x60406210f02060d2d1a1002070512030310050303040303090b0d24080706050c060f0403020a0b1603060f080d0309081b100f020705061504110c0607030f2d09050f0a06 73
    0x920b038820120203a984906d49901d4184440451000101e6046028186000c03505543d1252200e0049030383c0e0000b036482c1c0c51310380740c41d264200c07468100500c1b96009100820000e680003080009695094044c0707900c07026903030b002c580901010b1000e14019800c8211014001d030019901004507904c920484860035950202500d80f0301c14a1a48605074000400007242404200c18030380e0030500c603204a03040c5140e56102e055a001c0103440014000112410980d140303a80b6026507005490340f510582d901d686880400c1c3d988031303449040c0e80c09142e15600da401c2801903003403e41e50002c0ca4091b22008604440f00c0340e6850f0b4034400f91101f9564988031403030841090510030740b05030f05ea1043c001c03c05c4d5282d00111030b4444c0c0c0e01c030408a078066214200c030010594100c0190509016034001001c650420050140070745d003840d215420114505125400c0c00e910b0850030070b40000301c07400388104e0b140c048049100a4148180007074120b00c070740c001c442060708000a6406640b40907031320802500005501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 569369604 1250 569368354 569368361
    0x8070501110301031203060b1611121e073203100608070911030402061b0111040e090d02120d1e09050a0309090b0907050306012303060406210f02060d2d 67
    0x509501205461513542c0003e600c02c0c0c25400484030081c00bc01101400043c91890160358a544800d0301899482c52628030100700801409044042a80c6550580165505aa01d4a5454260301e81071000d4640c128030b84061207000c118100c1d0031414421700f601c7e0700741d007a910810b034841c400d251460840a80516240714050b07074002d5600600310fa00d8000580c00f80109080010300d02c82e42035581d101586200d440c01ca00401c001c049544040c11545011340301d0b1828643c10307000740f03000d5400110031b2440b0382d11100c017242d8400c42903000000715402803240980e010b040c0c1780300b1001014a460004421b002e800070b80e04064500c03e554907a90300752524051419941025805900300000c00042500c8900074405140d002c038041c1340180403484c25120b500610940d400c00326500e0403000080c01140c0c141801080c000d00102080700758007400a4102480c4440c5015015018400035515001155903c100315007649060120900000030901001609010151044541c0c40d1401c610039040d13004500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 569370854 1250 569369604 569369617
    0x20d0302070c050405061305090601170a0b06210109080405040e03040e130201110a030c03030b04090302071511060f01080706030605030318150f07060e0604020d08070501110301031203060b 83
    0x99031421220318203c140300142c41c015100990001d40c00c0c00c0c100b10300c8640d00c50b05100350841402403466500d0f1451030114610341c8203210034550000580c84010542c1c22100a4001e50141c5c0c81401e54203a25159080c001031100f00300ca002e5003001908000e000e07151010704180c4104890401c4120303e09816244c0d244034610072000060240c01c001030340c0c2400040060103050041c1004600c03088001d0b0201c0c1002881c81044000c03032002c14039941819414443d0b107500d42c0f02603c0401054400341c4003c3d603222020b00c5400c02590a83c1c01e42e40c8250701c00d0152800c0d10740c5a1003203e50078201840c0f00c1d004c1e45070034012189248202000003492500c640035200450300003030040c51034110300c1c2281060880540304074503040326485040780c0403c1d588000802190351400c000d6a2203003010b181142c00d59105000181c00f540c410b00c18031000d80c1e0784031944280c0344c7d030000c0c8281d44c170f880d6890464054039150003402044080440000140010500d6409130400c03d5a010802d4503102c004c0c0c04001d02a01c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 569372104 1250 569370854 569370863
    0x1103060f070c0305090d022e08091221070f080a060608010506090a0b03103816020405070804030f0807080a020d0b0306042f151b1507020d030207 64
    0xd0b58038003c0303401000141600320b40900300c2c281e0140070341c011900310380f58511518880146003540000d54402d0b0702250074160103510b00078079181441e80015550b400c944540601202c40060b007540b40380340c42c10090203400c4102e040100c403454000c8010380a184161410000f11b000080000e1148c6003520840b400d90b1104d80b1648410390034401406400e40004007680d4225084c150302280c5000c01c00095803107021444421240c2c03905280328418480925400720303418010b0b81d10000420b8202401102e0404201c06906446890505407a00c0500324480042e40161030542401451544032801c02c0c4a14020b4032401c012031682d1030102d4407008120cc0010004080304041000301030907400501100c030001002043c03115001e80080d0500a058801b242e124001c43d0b480f024001c000316555160420040c400f0011440d541b021840300c0b03604c0820006840c0700000c80344070412003481980541e0f810710048030715400709650b04a10003003090310b09002620030310407542d242502c2402210075140d4807 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 569373354 1250 569372104 569372117
    0x9010906030b030a1a010519030b0f0c04090204030308041a310b010b03010302040c1b03122304060605040608120307050f03040807030f030c08040f06181103060f07 72
    0xc1650440051003070000c003c1d85400341c1e0607810080f4241d03124021054007415114445545043c003040102c514854550054026085041010035003032100158020407c64480c1d4450ba00c24641e01c0d880c0c030a680211000340d01c0441c010040c161f000502d00c0c4200d01c54061844043d00760341c84041700700c40c115031243d0341c92610105115104000d03442200360300024010b9048040c0b45a40d03448020030240c0082d898801d001c0010030940ca0140030f055400700c40f6050084000000e100c9000c0d65610b4241d0180038840a004140201d030076550140489103504444500d000e160014204003041e82581c0540d601424200007054600e450303c0b41c102100e0f0110000c02d04042c0b421240d00d2903410052180c014400c0500c00801550451001107100e00e2140344481e540344800e10b1b02070044c049400107001058905016070915542080307200f134019400c2040c403414a215403620001815004c1c103180e241e003084070005410006c07905100c4c191a00218103603191b0b559585548580c0450480c0c440000451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 569374604 1250 569373354 569373359
    0x10e06031902030f0106080a1104020c030a030504170f03060415050a06030e0c03060103030918110403060b12190506060306060f011206031205030f0a151403030d051e0705090109 78
    0x1e01d11103519030300e03202600380c80c1c25107141400341c0d00312801948240616040100340400f040780c049031b54074104e00110340443c24103920380155581da01031078200c03006065071540428140302c25481003244400c0e030100d550b40d50302e0714994030903000e40081c4c480c64019424108410000c1400440607801e8410207803c004000d484c11004601802c0c0198101c24039005440718031006450134031110b0301035406526680f00c40c0e031a000b6040301c01c0e00d5031300040400e41c0c030342003000b8a120081c50448040b2904040042280b080a03800500d100c000c2c0308003260903216907000c0410a03d103a00307001c0002c9000300141d0701c0c2030303a50b001450f8451004440407503203d052000074600a60103104003400b41910744000040c043e45a6840d13481090360404080041a00481003210781000d03550540d038480358000d01840f8044031205000303100b9a60b070003440703950750483c4200c004071740342002522060581d90806100500f400121894145d02016002480d80d038401c00082c5400e016804aa0758030b40c040c0d41d80c00c0043e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 569375854 1250 569374604 569374633
    0x6060d0503030a0b12030c070e161b0302100614120c0a0e04140703080d1d0606040c030e0604210c240209030a14010510060c0b0604061205030a08010e0603 68
    0x2130000941e0300c1201c1e0034450809250410142082105030350040001e47e04000b1084102c400040001507841c08400059092540c0400c8910708401ca510030b100c1401020314042c1d0510710100c03032404030f243c6050800940c120070080052043d11059640a802021480c242c03902c1c0c04240c07140d1500600c640004002000250052580c06800790300c81c0e008200c44a040e540c1800714640c01524100700206e120300c082e511510901c0542d220314510084100c9804251540315100141542d100315550341c035050001c1d0080e004031807424a131070299042c52502e440c054800100080460306c48110168519030182c0c000d10300102c42c0c0d904002c000c000749240d005400310000c01410501031103602840743e05031584040080e0b240151185070f0f9900030f428440101400c480300140010300c0f0112512041240a4120710400c280c981c000c00084000d64580300410007400441d0700c03524440c00440c5640061050204c013a010201d0140d48210150342d80d114140d504032001d4521070340c103410402c1c80d010140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 569377104 1250 569375854 569375861
    0x3f0903021f060b0301030506040b16080601080702190b0a140601120b010e060a05070b0a0c0f05090a0f0605030f0a0507090905060310020f0d110703020703170d0204150206060d0503030a 81
    0x850064001160881c0c0310007190f0100d402c2a40100e80303580c003801c00d000801c12400d81d400d600c111071221030040810385800060400b100600070905021581003c240ea00c0d20074400707441011141e1140717a40358402d070b2401449107201191034a8110b460304901d81c12541007200202d0003030342c0580d104005500d50645072001000910b0081d418002107906c4510580c0766070300a80011120783d12031580303451850034608040d94009081c5400f903450100b0409070150071100b1464079800b036203012a110400c10340420495009900039016a4070341040025071594003034000d41c0725044220039400c0545503a54034200350b840681e42400400c02440d030602c050009a88415881a8010300300d4002c904250740620407a800440710240040d0000365061007040c0c0c60150600600040076001d1a05034285c400a4a50800d404020b00c00000400781c501d14a112000381c1d502c11914000456446540300361144a03404045843c0c005409100c001405910b41f0304c4004400741d070401e001e1455655a0702000009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 569378354 1250 569377104 569377153
    0x11010b0306281103041401050705030c2b0e1504020a05090a0f0c0e010e0a0e0a02091f0c12020f0d0806031f060302041d0d0503073f090302 61
    0x10140c0a03032995010010303002e00070030410056603c9a581c141030418480380040c1e03030306c40d4940341c1c14001030013101b40d4000e04507a40004a420b005480b81c030710a02c1f10726030640540c00d0800082c103074004c103c18440c440d03102138103513a9040212103038280c4510881c00b071948111400780d800403054008001c42c0c10040c010660001035010005282040345500000b01c0c2c075000c0c5084001420440021a1540c2000c00b450300002e084541e129002d20301064090000b50041c0b81500e615004a00962251940c03c1521200c41c4941024140440c05a6000f06095102003007650019140180343c203520b800441c09008503103e4001070030241c540b07010166604a0007031b00507a018850840b050034a1700405000d500841c64019000c611300b4914010841a1040c1140d521042e50614807d003000c5c040c001003544154406081554480d030300c2c10826a404440000d240c5484003410b801d00b0740c00d1880800207010b0580241001200ca0040c54840380ac03aa04014002c015070701480303000388404141e00c0000e44 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 569379604 1250 569378354 569378401
    0xc01032f090a12030f09170307061d120309010c0305010e063015090304080d110a0c080c01121107021c05070b040f08280c150c0311010b0306 62
    0x31025690079807803070b0400250b83d044d0700007a14010301001c0c8580c011903001c01018419556403024206500745522803082d090020503440d9180e20034003039440500c90303c500d040e051070107031244000703141e0658060f640220307a800c129500e400c6028150901078481d49059801d107684000140c1d8907541480541025100c10308440d01007004503030540da41d9200310b007000c40001d002034496000902415451824060b100d01101d0f041072006004000b400100d0066925480c540381d1850540120780d241412440071000e005980c5080021800700000500c1d100b0958081e6140c1ca028038403001400d0840e10a04510000c10702d0401034400036180441603040d120140d10008802c030400d5980b40307441d02a035603201c0358010780d02180c00c2040d0035401d071502009103071302c10250200070040d01c0501c0f201c80c194203140420f503852400c00b5091000564480001d00f80040c4420050942d001d000342c20380805040c12400500e030006035001d1003906004038448440041c00410003500e0307002c040780c196080d0550815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 569380854 1250 569379604 569379619
    0x1060306050115031b0512181207020f010f0909020912011803080c0a08010e070c150f0f020415030c02150a0c0e0607150b061b0c01032f09 61
    0x1012400901c5414000d0151441852408018074806426521900c06500700200d1002d9000489900001103403c0c80c00c0c4904034442ca591142140301c410f6658000b03040551162021142000b440b61008217655402290b40765070100008004452010482c16680e00080787c43d0010807009071160042c00c43d170071000701100420021000c0413402c42d10181c8038881c0c20308c0c9520040e014142c1001c40142c1042103498200c1c0340010f0008090213900061003241c00000f20840050501481602c0003040158001300101a142d007120a02000d40300004440b00014507051100d240c0c3c810034421141216020510342c600440c072100190f0051000391101001d6000700d101038102d000c0c02107440d52003120340702400030744081d6640e0014514010301c1c000c1401850704001c1310300894010344140b81e554550020105403ca40309010031400d0050702c00c62151101c1e40f401c0741c02c09000200f4138940d50301c000c1e83c0401800c0b48840c07004100010501220305407030403860001d1219000c090082c07425030809002c02c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 569382104 1250 569380854 569380859
    0x62405012307080409060506040b0901120e0613060507020c0d021002070302120102040303091220060409020c060136020a0e060d140708010614090307080723010206041208090106 78
    0x440c90340e4007a002c01c4445900c001814400310207940310340406071006882182c141400c04c42c0d600e0f103c2c4140c8540c18140100b0422141c410030350358020002c0356500074207660550a12a01076400c0b82c0d844a0308480403820b0100055170180b0004013082500ac00403d11001d424070b42d002d0102a01c0710b600d4110841c01010320200150321242c04029140000c0000141d60b6491810010594032141d00030629061f00002c01c140480c00301c41d800c038000c1448030a00f0800c0186480018400e02c220b500106000d80040750b0001744142c0480e4541c100d55044100d20901d440c00010003406500701c0c4d14031074020050002c0300b04a2003081e40985020700140c14203864060301040014116009464031a140584517807000d09100d55980b60070b60040b00030f040c8101c05504052010b0b200300c1c05000e000d82040c1e008203514440c2c0e40d0030083e41c00108180d01c00d84c0e00d03050303c030500f01c0d860121442402500c420a41a0000329500c00a101c1d44a00c0c0c110b848500503004816040702e90743c1d40680082d22643d01c800c0003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 569383354 1250 569382104 569382167
    0xc061a06041217040f031118090708070f03020901061803050a06020702040c030902090a0f09080301090615091505070f05011a0a0504020304320f030706240501 70
    0x40c03010b0b02420a4112011407103180c00b94060004100700c1032900c00a100c10072002a001c4013910581350b10400e006400b40c01e030000700d54552070440700041c0407881c01050007051040070a142041c0c81c01081502d40e10f0b40c87ea0301803850585c491000a401081d00001008094400c1040181c00c014200c048401d55a0740e4483c1858007a403100c00782c5485500180003804c40c50a4490020108000e05083c0070100050700020f03103801b4001c01c081c412075280c424082412140c0e0740443c1394a039004400e213490396115800e2000500301c81c081c40d6401441c18214079000c40c0100c8142c0700700d03040d0070200c01c181c0c400b5080480c2c8540210700212100315456003003a0004400780103a40100c1d40d00407004007100003160822030349141c550301450082e44100103010108440fa04070084008210809904601c03019082c44ca0080e880641c40b89640110745280d0f41c010302c040003c0c00c105000d220144062600304800001004003400100d0128280701c2c020845075000e2004035070080041807a40d200c04a28264 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 569384604 1250 569383354 569383357
    0x70e1203070b10050f0a030312090b0408090405090f19030e0409120806010c0b0604050c0c0d052106100f200102090315040302030d38010e030d0c061a06 67
    0x60484242c01040c0c200190310721140881801400115004600c0300d00079000b10f08903c05074003018080002d24800b0552207503442e003040400320b60120094045250a04140c4010382100701d4140c411824200440d036200c0d0001a00301b1050b00c020054000b00400c0c101010215000e064100d00f48040c0301040b40441c0c3d80d521400c0055406a0001c0203030030154200109805e00040400e418000d4154601c03002c01c80310112658004c0781510001042e03150900c4416143c01001d1070b2025600c42c50241004960740203016000b40e103071020102c51600b25a034000e6160340011a800d0390440c00c1441c0030860039104000085e50718090341031100c40c10703646c0c140b00e100c001c40070200a20561340018148485080800c4511207182743c030f0079010b03018103040c0d80c000c0d142c0c07040c02600f1160503182e12580c280d030b21004503135511300d0220a255a0814070302040e41d000c105954012240801c40c4052421041e04000c2007410000c5015034400d01e103400302d5554176004000784500c0e00210700031240c0c00c20050300c8190 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 569385854 1250 569384604 569384617
    0x903120f0c09050a0623090a0f08060f0f0408030415020c1e0703030527090a0501031a070503071412040803041202031303060c02010f09030e10090b03070e1203 70
    0x900114039040701040c081c0a140c107a034451809a60300803410004d5a80c0b11446018101c001d02c218455618030804809403401143e02c502c1e4000d410b0040003694006102c028012604d614050f14416070301c06204d00d00170b400c2100d4094456407a800010000388400c4011a40244640354100804012051003801c07038000c8029640c8640c071048140400044016040c000081082d000b8013855046a40040090080c0c000e40416203924907000c80140084c446c14048000014003862441e21301940300c02e01070582032206441045201e65940c00c10800052842e12540054039510b01e191269a011550460f899010030340e40c070002d1260300002c0d45a0034070580514080c4000640342d0070300e41415052000070548200a65008001a0900403181045401203030b400c20340004800e00302d04000d9003d0039100c8400541c02c1d01d012030080c20550000c41041d03040c08166032110a00030680d609407a001003901400ea46c0c04014000220b02c5446054010140900508161040511030b5070b55891070b044003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 569387104 1250 569385854 569385881
    0x350a14030405030f031c05040507030f11010801050d1703060a35060103050703031407081303110a050604030f0f02060403050102091903110108070e0307081e010b090a090312 76
    0x1c0d0401052804000450103c80010b001d146450550700a00302d044071410b4165600c0c54680c4005000e204051240780001d6400c400046025991480c101e031500300704151007800321f101c81e40045540d003026a03c1e40d0500d60700010a0605020781c0340c41c82080d0b00300404050b40320003010380205050f803060314100100760030000440c42200004031081c0c881d0915040300415a4400801000420000640e41040329010b0404070740c02941c22050f440c8611800078007411031030700001d10f00080791a05980c0002c8030300902010518810010411205190f981719280e0311143c00d0200b0300c040380890000d810510b00ca42e1300e100c140300c4650f0104820790071690056445035400308485505051200c1d00076809444a0342d009a0315065030780300e010000510384035074108219540000e0496008001e208000d540040444160079a81c00760341d640c4440c0c042070012401041240f01d00c0ca1b010501a160301c4050003030000c442035a880b00c2e01c03001007a81c0003040d02044241130100a6044444c4509180d00c0420f = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 569388354 1250 569387104 569387107
    0x1801020408010e160515030a18080406080610050a0e04020306060702150703080a020406090306091a09030c070e2716030803040506091216141203040507350a1403 71
    0x780d8001c1070070031005910050140c0405503c0d50106e031040400c40b50311808202002030104a0702154404502041c2c074001c00b41c2c84000780201d1516000704159204031022100c08001859030310301101c080c007803800d400b4042a00740c80c42e10010320b003a8002d198000c0000e0201030910f8943e400080d01304103003107016200000006420300078580d2100d00305a2105042500f0740c98907142c0b140040c400c9101e0f210182000740d40b01c6880c2c04000c0103068551a0002819007170116003001d4410b0b94407588544802c00e070034441c9040014021807001c0e0300b184580e0890700180700607510900c00800c404041000e94103135004010041a034085c11040e040d001d51300800e1010b4580c5018541549800c501901b00011640118000c1c032001100200b140d5204480800102c100205443d1240107041d000d005465240107808078900085844400345100d43d019004996896a43ea0300c2642101c0d0130702e41400c9000400001074150050001d0704040901c81c070400c0b140082c01715243c0132411407000b00f038400d440e0030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 569389604 1250 569388354 569388373
    0xe0a03022a060a0f020f1b09060d14030d0c02010e150c0c031204140105060919060504020301030501090b0106080c030112170d060614180f030f0d020c0102150f1801020408010e 77
    0xa0400c5201c520850006c002c0944d038048101d480c0303504a110540512541e00103000400d1520307070340f040f040780c103034003811201000c100d20742104e44940086810380390071850302e407840801c144140140c0079070a080320041c0c01c00140c20300580d98101d000401030400d0402c10407400540c040304000030105011146418002c03030815141600481c2d1075600500c6e4541e05100c24004184d5800c900e203078100e01400c40541d02540300040c0280900583e80c85564400d10100000040c420b0641060030703007520a030101e4107140c0e00c1e0760003660650070680d10803078001420700060064648081800a00c03d01422982c5400e5141410034600c9a11019054002c1074442c4420818103803c144c400903400321010724a804c020700c400360500c14101251100d4071031f030100c4481c088283c80c01e1100764a914103020a840091005030b0029683d00354403a00c0302e005101e000800518621070042c3c45000c1c1c55044c0010f09140c8406140300300700c3c140d400b0200e0340c65600b0400000d02e160240300e8030300c20b0038810001e004040c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 569390854 1250 569389604 569389607
    0x90d031107080f071208030601030902010e131416121503020904051011040b3c04031505010e0a050717101802040803300f01090e0a03022a060a0f 64
    0x40e2a40041e40540003980585e00045c14941a20b50012080c039001814801c5400109c5440710001c4c1c1c0329800c800221800a4000c500790003000e144248940302910b90f0721007584034811468100e40740f0000500d500c2c0e4002078010607810541800c072460300074548240c2c03240c002443e80b00003594100c0d11503115090014500443e030043c0241d809441d500c00303050a2030b100184000d8803070307100031201f000100c4d000b02c03090803000c1c0443c924040b41000040c140d0040b45402c03070f019502074042559043d065400c1443e400c41c050080c14103a03210040c0340c2001da10780221000141401030001390920000d9060807031110030344101144220352041003d030020f40b91000c04074150b1151a281c413015801044144010100001105c1e0442220300c0444c200842d45082c0d0405170022508002014010344c043c4030310014207290130740c161020400100078811400c4000c95071505504001409a04404c5180c5103007001c4904010000300004900c3c070b03250002d5000660664400c000d16404940040d103450000b5 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 569392104 1250 569390854 569390863
    0x210091a03180a020a1e03150903090b09060d05061f0201050601030b2b0503040b03040609020109080303040f08090126070201060b0406080411040f021308120f090d031107080f 77
    0x203101c1d0a02420890034107401140f00401e10740120520106c2403a114143c589007000c42000440d0403039403426002042c400c48074090400060280c0c00074504180c041096500d5200302c4a142c9030003801689407610200c1c152001d444024070495004228801c2400f074215501015040480158000929454020005022200b01c0380c21103000311820085103000301114840018080303480c2e401c0c00151056868058503502c01c54104004003c804800e010401801d034001d000c8c100d201b600c40b01080c603110005250789000c21200a4014144d034075044010030120320041c20443c0c01071600c110f9181c001c8802d00e0710241c24182004203298000701300201e8550a02c1450302900c080000302c0d15041c43c1030380c01826008003030809424000701150801040c2d072194440c1900340c000200035511903401c09120903d40040d8450a02c0c2d0b405841503464100d0203807022502c3d040360403420581007101010a026030314080020440512000e4817540782d01d820108149002000424020403081401c10074107400c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 569393354 1250 569392104 569392141
    0xe0c040e07050303040b0d2703020d08060310090212030f0301170c090f130b0c0d06080706120f0b15030412050f0306100c0602130f1509030210091a03 66
    0x80381c1004209021039034022003203404a51203500000e0325441c1024000c1c00600103058024400c0c2503864010018651002e506021280682c00755040d04001800070b840442c0f00f1601c4544c1034200704001d14402805500c40031180340050081350b50680b2500c0e846145500c5201d2800102e6070100c010460fa5000f04903d5006c100103201804c4404141d40200b0014800075101d000c802000340000780540c00b20b043e4021809821928207602400c1000072211075501840304040c0c014282403001c40c0544000400c178007142e003140d4071021b951a41c0c0032800014610390900e00c0c20320340c03941e070808166928a206030051154503031200342c4e2030070315183c03452041041c1940403043c8030050207080f803032840300026668486010344600718210711042003119030070b1511b40700401113480400c10030441c4035030040310415140c4d0b001d010b01d41652183c100350070340207014000c03800203090002c0900c0113091807a1030302d4411009080c4908881d840380c030707440403143c44540c200449803004010040314180b410309040c41d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 569394604 1250 569393354 569393381
    0x20071403070b040501201603060c030b0a0806240306010f05180621030910020601080d1e030b0105040b0f1213020904120c0b13021908060708060103020903010e0c04 72
    0x24003482d14002900d106841003118062034880841c1180e601b84c248580c250107040320b034581181a4591610000400c0d00010500009141c0070310058103080c030700003840c01d482c188402080d46a4858440c4807240d00e0b007008490000c55564140c04841c0c03402c03c102c901800450f1103d0340d0305824081400900e900b07100c01c0c81c550020220038000da60f01c484000420301d41282c0440740748010b034181180e00d507204d024061a0000c691608080c44140d0106101d4141c5d02c0c03da09582280407402c03022610401c0e401081220402e28036054003100e8000d80c80031840da00306040450500399503841403259600031000000d14030800003482d224014840c0c403425804030380a03d80d10303184082600800e0700c00f40020001070040c031a032040e210364107003c0c0a48801065000c03001c0340c1c4c549062201600040c40c1841c2c12401010150041c00d42c0e480d8400c0c0103015150000c004180aa8610300c00702e45840004d0074540c1070660810413000750751401e000b40700080c4d0340e0500a0505648103000d000854800440260 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 569395854 1250 569394604 569394607
    0x506070203040b0421050a030305060406050a03050606060d14161211070f11060403051c020606090708060109180b03060604021c0213080a0b0a05090703020a0620071403070b 76
    0x1041031038480585003510705071a80c450a40000e81c0c0e10409040708020058210301c150301f040b40070035078580c120307500ca0241911305100d405d07518800d1100481e028000141a074000a00180580c184800134003400c0b501d81c10042040618074000001680040d20300da41c00d5552052402c443e140c020011400d540b007180c0041000400442d0b40805a01408000034840c0740074400d40818410740b80302c0744080610007440c20b80e032181d8920f13250340d03288211403a486492000031034141041d40081069403003400f002e40300d030007117a4030030301c04440481004140d43d060000105e4086030007145480032a00300c5035540c0d00041c1002090040501d06007004007020b10690040150009042104406000c0309007a201c2c0941c4900d400d046500f9400303401c3d040a230300d83c4510040803081c070411900460291407140030801c61601c03200310080d141c0301d4501000e90041203071002044118030807444444107501c1683d40f101d10b00b200001e01303820580250301260f0001101c1908111034031302401540b0042c8a040c0185 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 569397104 1250 569395854 569395859
    0x50d0c020a05010f0207050901060201140108030703080c0705151503010e1f020a030f0e0d09060c0c0608131b05030d030509100506150f040f09021204021903021804050607020304 78
    0x7481c9651500600341005605250020618000c00814000e408018440711301c0e5a124080280248040c03010042d082c0d41000c00040d01000c04000c84022980565800241c0d50b200130752105994000c10084405220300b00070306400c9440d2181f86400394082200032003e03294904109425281a421100c042e900202d0003040d501c2203c00c80407810310341021016890315000d4400790010704000301c40074040c40c148066034030701d030b000880e800d9034600b000d4407010080c9131600021249281080c2000f010302440710b0082c0800c900a095140e48005e103159400c80036580744eaa1044201d010f11240403401685c00018001450140b041d0244400186010002c0c0d01d49603411a90382c0004181d21824996905c0115125446d61080180001c100d404540d41d00e40305000c480119501610603a40408900300380822003505074002c9074070104401d2000425500c0b41e800300180080c3d140d21864211003445400030040c4c464007019003401d103141480b2010b914050405600b030001c01003041d021500100b009 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 569398354 1250 569397104 569397109
    0xc020f010f0827070801052208040506131215050a150e060f030d0203091306030803041b0504090b0402041104030b160302040b030a0902030c0907230702120a050d0c02 73
    0x5a8000581c84118800005140b40c5206164550b0003850013030141e90400301d020001500464000c860075000140c04840d1801c00c100f051001c000010400f80c8100030422a510b00341d806006803200c1101c909403040d0303640da00300d90815484003003258400035140c156402607145220745540504403031b00a2140012142d11210141c006000e5000030402400208203642c0320700721038038100c940203000c840501401c0b044c081d50302d400058902d071240c90300868810740e00e8a280601011280c0c0110054119105e582e0340c00b1807007008000e015112000c003400014070369107900400c50f0745070140f4200303805824139005000a54003000b0b6100f0b041380e0104010000929644556540800c0080e000d881800c1414000c4010740b00700c2d4481d0031580004020300a10145640c442c0808138400c40840b8803010070081409021a4120b031f070703800070894407030b0b02c1c030b8445206000e40320044000d42c44103403602d4040c1d0b00040c00c00005a070421141c0d80120780000c1002001c011800580540f41040e825501d000e500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 569399604 1250 569398354 569398367
    0x90806060109090f0e1e0c010f1715040f02120a090b010e04170310051f050d090c0f0603140a0228030b100509130509030706020f13060c020f010f 64
    0x41e2140c2d0640d904103801e6141881d620005405c0c07691401c1d900c805094110511081c507405240940b01c1c00750781d01a03901580503035291442101d10361166100e50f40403c0920505000041800103500041c0981300709654451040d076401c106040c0300141c842d09080c1c003007460a0b0300140940c0640349405042004280c58120040c11a00e58580f4800c80d41e443d46003038003038641c11104148076800040180040c83c60310b6071036141615410342c0c3e01901c8a0700707840c0e0031102c188118514004a402004030007001d8440e500050074042c0074400c05041d8075907032008c482050119501c038a000a54030714440c0301d0140204812030704401030240c01e5080c40003918030000400b420120b9007111140c0f1031301d41c400841c0a50803803202c0d0000100090384030404407401405a074442d01c2054410079441407031a001007076902c240e9001e00d0741000103604154a543d41e05000354027480c10b281c0488402c3c4158000034014107003c1002e03042070f07641c00a4a800e6031051010141050309030703a050002101645002540c03100303 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 569400854 1250 569399604 569399609
    0x60618030f081309020c03090f040b101b0218100b0705030405060306010306120f02010f0f0813020d17040f0501031a130b03011811010c0b04030807020c120d090806060109 75
    0xd4400e6500c45103244180350510b03c03a0b02c54030244e4000b1603030250400022000c0c02c1040020354160616020400c10401290304000c01158854042840c41502510580140d005064444450040c20034242c000889100120f04500e0350342606000f00002d41c1e5400124030000c25001c4a01c6041601ca81d0b1510b03128001e80c041e15000c0c4c0300110004400d03038460780080d0000e0141842c14602a00f0038100000000040c0100740c0c0030a0500610002140c8151504008a290799580348550f0b100d85551045a0f13034075081c242d80c00070b5682e01d00c501244000c0c400118807403640b50f0031a5610300d4003400c00d444011a134041814185040b40c0e00910b0a140c0180d0300406d40704882c5620000c8440c8128002040c014075155099071030520900c2c060b140d00e44002640a004102627507202d45400b0046901c0d818054000b442d0503941c0000c00c0007e8028901d00f034110303d040c0155400c05175107c004c20000348617440004000d50007014045034458000700b01c01d0152181a02619407032400d0000a0848c24651 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 569402104 1250 569400854 569400863
    0x33040c050c120d020f0d140606030907031527030e0a14060706110a05040f09020a0903020909030909040c030605090f0309120715080610021f0c0314040303060618030f 73
    0x80f038907820020743c0e04803030405040c05c03102c5840e50009501d00000780784441c12004802000d2000c15402d14200e01075070320910481c030040211901350340c0c40d0344640350341e4003900050359150040c1e101c0340e084070750000d80282510016881003202605000f4400f11000c0c0140e0701418040038288207040314041380c00030f940410b407901c80d070354803c0b4a4188000c0a0b1000380c05400480840d00600781517001340204101c1d035420b050b9010072a1100c0380340080740300c0c2105039004210855020001801d0510b904c0b54004621016641400300440104001550855080300e0900d0305c0708040c03080200900c0750030782000020005202005400c0000d5949109103e41c1234070440c0480c822030a008001c20994010b0161443c480c01c10383d10307845018045480c291509882042c01c040c800388414400682c8001008205145441c42c11668200d000240001c20001e400c054954030320b811215603090095024501c030703550000c2d409140407c001c5c1040088000514a801101420400f18048031210740754a03410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 569403354 1250 569402104 569402107
    0x201020a021012150f0b0405030303060d0305071a01150e090105190801110304060e1b04021b0303040f0506070306081e030c061312052133040c050c12 66
    0x401200f03484031070b140001e0004840c148001d180444000788829011901410484a0300c40d0b1500800d010034012405040d4041c0d000348001400c91402c4008242c00743d0090410700d1802d506c42d180d028003007182003880706c0360110140042002c42c080001c24454110742d464061100c01c540c80000f10403901c10703c00d062003401e50040007459910200410b4000780440002045802d046000000080d00304480c141c0e5860b2801c881c80b4140400490310841140340c0c80c64000350030682c1000c001c000d4120000c500301c8000b50f4034800400010400055004c3c0b4010031245032881e0903440d28038078010004140d1030130142404000c00c000301000a4001c0c8090301051555070b0410080719942c40c5010b010a201342d144152014048101c651981107484103008081040184041d44801c2d540c611610340c0c0d1400d00e58140c0704800ca00d40b0001d58080d0401060b10030204408081c000300f40156104180a4001110710141c4424a282c14443d12005c041b050900d541880c0e69202525212490080101d1003010f0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 569404604 1250 569403354 569403379
    0xd03290424030209010501031b050703090f030f2a050f04090c0609060305010902040e01150314070509040e071a0315151b1b0d03020102090a03050c090705070201020a02 74
    0x15940c0024090401402607002030586800031964940c1c007600c0168000d941510022079507520900915554820440e440d01004100e43e0040702c3c40d0344029000c0d020021483c03000b24446242c140554020b43c012071810412020368140714500709000c1c0328280070703e81c61858049003800e88107140811200103c5501d0048942040858040d094511008220342c003410804600c10350015210000d8a116980801c060b0380c940102c0070407407240e40a03040b59000e03a0f000421141c800030501c510110b8980c0740205000ca41120703900300060b02035aa5001180000c02c0140c001e08042c030901100030b008000520125182c404511040001408100121900000011801c040c4080c030380b2448034010b02459070000c0d00c19030351011504154042060500014180b590714080020100181c0e0401c2d410452214005001c103c0d401c1030221048055540030b21044895954669050f00194068030203492090b19007030402038500001040361080c00b0040c4000b00160343d00248400200398103448a07041d001 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 569405854 1250 569404604 569404609
    0x9060f0d06060b3c030a2901030b09040f0209090f0703035d180b0912030105040903200114100308032418010303020d0329 54
    0x1030030310182074503041160005a40a090000f82121100c500300800d440480a440c4850004d00c03c08100d07441c058003150491602d0f03010700842c0c02c40045200005c210704103d03180e888004800300c80c01c07a480c0d60213100407050750701401010745185080b40c4400b05850503984940c030511000320301901500e000800105041e600704a001d205101042c22074450950303a241c0202041215120303140360003d039000070f5034150808a035031424412007194500500d00d400c41c443c650308500704201021042024001d2400d980c0502c1401c50345250040181031000ea14104080601000703440e50390140d00100060006045034010b40f0b0560b0412074000c181c00159043c01c9480400b0446200f410005030070140a081c0c2c070541c000c2031141f02d002601070b8143c2d038801011181c10039521000c0c110050402c005451166205800304011002c8540340d070303040b80079a0215035811407010200000d0b100983c018828150100280e10442100d854244038200105843c403950394000b548e0368064500404201e4440d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 569407104 1250 569405854 569405869
    0x70303060b0408160b09220b04141b04050a060e040b15070b0c03090a0204050919080a020705040203010506070f0f0204050a02070b0105040b061e07020607030e1e09060f 74
    0x30080640794645079500c51030019118141c4030140743c0004104440020b4029140c0d0503901809401006050708460100a90861060800c51a00480e9403410245540c5d52207220f11001000032200039907181c40c0c500c00e07403c1541c45034004101e0741042071200300810740d20700c01c1090136a41a458841c0c492203c032030101d800fa216030f000c00d542c440c0c20325100f01d00c108a0800500b003100d0190300019000e4403102c0a83c84103200503110b00001d9040341c0031100140c00c05401968201582100b101c41910036400d001e031000c03a20f884116070074000010680c81c0a603041105102605084504614652402d800110386200711400186084114129441071011100c0c40029513900030307000780150710385a20014000c0d848004226008003161001040d241490320036692402e001401d000c2c603104503941d501c00d48174a403403811140081c0c10880b241c0180c0b242409810203d00c83d80b0b0722050350b807103801000718002c0120800140845901d24607001d69561304a0240c0110081d24280042c46082e8040f0b0600b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 569408354 1250 569407104 569407109
    0x18061302130501051c060921020c010f092114010b0310061d070e03061008010c030501030c090213170102030a050f060d2303040b0a020c010528030b040903030510060309031407030306 80
    0x91010350050340c071400c40e2208d08000103080a609682000034080015681200e4030450301d000102c07280014400c6206500f410503595002000444c0856116a66400040f084400b0740070540d440f010340044508080050400c00ca1038039006010a0382031050208003010845c4014110b100040d011522581c002c940108800780007400382e13201460b00307410500318605940300300c080e07661030207030750710b12240c0710780b10392410799610004440401e442c10841002039040701d941c1401c40e64070f0540c0001c04013500441c1032415055500050b840346488044101112001094981141054801c10020341c2c0d41e10301e04e180b4264131218000160701d01034004040900c1d40030b1150081e01c00040d010860076084405420480100e50031135102c1c0711600011100c900075081001e5603401c00600c100d98502540681140d64405841c0000d04c5440c2c8070b00080646074140001e8001c00d59641c1848400fa40040c0e00c0c0d0050920b03403c061103040d0702542c3c010601d01d01404003e1a40030086184010103100360442c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 569409604 1250 569408354 569408363
    0x1002161406090d020f06150102010605100909054507090501090e0a020102120918040f0b09030a17090703050102040b0a0e150d0518061302130501051c0609 68
    0x5400d003409400c41e94401c415150740c0518400c0400382c0f00c0080c070000708440300c19510409406203440381100d104510005107803650655480310400301707103501c03140212521101c403581c030109030600d000480c1049840203415101c400c400010042020802010684c0321040304000710003010944401c074041c200c1d2061250b61380d85c05030103000181c446980d00114140c03520208100082c41c80b0640c8907035503140040009015800040000d02c42030002d80c0540155103001e0320100f0a00c00e01d0326903040d0441c089400302c580d4500c0b0900c03101403003070801200b0b41c8403010780e0081d4586107454802921040c0b6282000c103c1500c41d00014044103410305c42c800c01541c2c080c0080d0b46441c0c59140c0000e05400c041d01900028460304510501d42c40d0198800540c01141c200c040d02c6d001202d820003000d88401050f8103961032510720350041070482080454410402042480c0041489104220b212400d4042c060340b03103410440180000d9440f080e442520b030460b100110740b000c005160400c050110300b0340c00b030b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 569410854 1250 569409604 569409623
    0x609040606080f0d030b0d121d10110d09060815040237090e0109110c070f0603060504051006081b07032006041101030203060411030a150e09100216 65
    0x1104040024582040e0704c6a8605204d161080c100307100000e040703182d000d814503500c0c4c0c0c3d000500ca402040c1803140e804481c104620b41d0b46203031010500b00142c4005900000b46108038041c4041800d00401800310f00c07034903200300654500200202809030160440c0c2d03100d068408403450720b95465040341c0d940c0c6000c0c3c1610950001c03100e42e0107a00d00b00358256a40819483c1200001c45201f41e0090b01601c04802075241c0c1070342840807020080039003000b0580340c0075081280e40481c000c10410500182540080804054244200141907501c2580410702890900080c4841160117407166802d036551845d001115130344215010a400c0e41103500000d030180c000400006041c1d0140c11980e041d023400300800652110703140b0040d66003c0894010f414402a008005003946c401d800658000320001c1000c61418594442407010b58000c2d1901c45c00e042c0e0b22a038a074a8100504c41850013000ea0600184451908054898035400200380e41000c8950004901340603502480201c0841a000034044 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 569412104 1250 569410854 569410873
    0xf0d050a140d0c031b0204181401060b0408030f0c0325021c02132d0608060a110f09010c0f050f15090703030e040e2e0204030b060904060608 62
    0x4500342880000022940c0c05121210341c903680c020312140c1903c50341980c42c80040d603c02c4030049203040d0700c0102241c1c4940c4480c0c0e449083c150b5881402c180c0e40c000c90a4040804101a04a0131240b240e0304c0790300e00e100c040c130003000383e000044141d0741c1194200352196600c40e008100c150a6104000070790715619481c1c07181c0ba110118a100900c2d42520039540c1c00208540c1810030702d009208244000d41c4400040224520030003d50000307450140022103c520f0503080116000f0280081e006c540b400b1a0788040030080c00d40d00f0030015070000d16400040250600d511540c2d410b900c0380d0010781781f4a200001c0c103030410383d10600743c1d00002e540041c0c0d01c000181e0103142c0035441d071403402c0401e13019211b04c1508240c4039140c0252507002d0702d1720b40300401a80380345580545c2d0f050034542200c1d502075928000c2c1e00d00d5400038080c603224003041903000c0d0240702e24182d00c48520140035801c50720040c410702c018000100b44048413a0090400c985e070781804e0f80e40d8039142d0003506190700f0012950082c802e04 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 569413354 1250 569412104 569412113
    0x115030c03050f0313030615170d021506090f2d0702010b0f060d0b0301110d1d030408060c0c0a050a05030307120203061302070804030501090302030702040507031a0f0d050a 76
    0x200001e580c801c005a400341c3d40c180844680d00c0c041e400e00e4005c0c012154900700002000c661203007502d5000e00c02401c201079640c82c030040c001a04491a5103282d00550541c4024039414411040b24150f642140d0300107003403920101e4800c2c400144540c50f200403450200c0c610071541d201d841034603200c1c10713030111515080d80a18549404180c440384055820301420341345c20316200b00010214500900b44505100c131111240f0040e088403000d0b250103550b504051012551400001e1003450041e40300810580c5050070703122401d44a42c03000072a190401d00c400d010190b00030458507001030544d1000f984580f40da40d1654100b41c001c2e8401080740c4603000b10601040f60201c00f40d8400d18a6485042d9000c1c000010300302130388800c88040703030300a40041841c0c50022640d800784c034071140502c002e83d0500f40c032640d9a908407550314500358050380c008940c0904502e058001c5a038032140c02d1a040c80140d90101c442c0a03a0300902c0181807003140c00010100040e210040080791840e0031100300c800700441400c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 569414604 1250 569413354 569413373
    0x4021207031a01050409023601080102180907020303011511030c071a0403031e1803080d051e060d0302120a1d0a03081c02120403021608062205011503 66
    0x40ca0b00800320000008140c641407103540306103a001f400408107006888100203c040040c0d81c0401d070006500c03803400e0340815004d40c0c54040d000000c0010703070ba640743d5014404021a0010014072680000701001645a404425641102c90b0440c00544403016a9010780d05000b010a80002070720001c501120b40b008002104400c4441060a050100600082586861280340005004901c0780c0101d0700c0d164142d01100d4a2407051860300075044510960003440031840c0f680700390b690810128005680190b98459a60400100f0328251081c4880f03440c0800180d0000304210320400e52101d0540c10300d40240070109200301503000842e0b485500520241100704c2404034505c0c45155480c2080e040c0c140400c1503801d480d0010503250414014601c8442d0141140c03440340241d5809000d03005040c258020601c2c001d0748290040d000d4194020b40b00107403c02030350301600c500d0340440c0c144884041d1a40c445540b82d001590002c17a2402d640c00c0250140c12030307210f080e0242d10480400003d00500c00c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 569415854 1250 569414604 569414633
    0x7020409150e12040608150a060809010f05040b07120b040609060612020708041e080102040308040302011205060a090c020c091807090c050a0e010e040c05030912031b030402120703 79
    0xe000c009034544948610742d1504404aa405001c4040100b480300385d0190b140b86e40d2002c81145644515244400860a4000e09a019030041071026081c803400640030300640c0c1d00656403036020025032a05071074207505480c001d03203400140018100d5041c050312486d00043c200341000782050000740e55407500e000c0203141e03900c15400043c1c2e40c1d440381a5820389500803581d980f904030101a050030704000c0700301e46480e00d01191840280c0300a0000a040c2030030300141006500030241ca0740c84d0303450350001410458020341c8001c2c07000c1c80d24040050969170f5801c00d4060301c0444000140f891004072007686407800410348203502c040441d04204c8101e002e01000d102e60034010064a042d0b903035660b5107009031500400400d001c2503040c840c401440d4450921000c001c2014036081c032584d9503907030110f400c8900a120100000704000b0402562017010485405034000f01890146903151040e603150080340442200958a80c00101043c25560780b04007410302c03081c100041ea41c409540f454084880c05004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 569417104 1250 569415854 569415893
    0x6030a0221010f2a11010e21160611130f08010b10090e132a06050901020c151908220b040b180a030905040f0c0c060506010507020409 59
    0x50303140c841d4a0407900444c9141110160880c0144100c0da00c4000c030110f02421031010003116400c0c1441c00c2009004031140201d040019042c56000060030602e10140c0c010800c1090b48100004815044c081c1c9031068104e4001000080d545900e150f00c070110700c101040d80295040c3e10b0404200e8541141388102111180030003084880c14803c207210119110300c14400100761018800c21404803c1b0440941c000c0000700101e000117440d40d00c030900202c1403040706159483c5c4107205840b0302140d04800e006880c850425a042c24500d2000030b50b40ca0b14200043e00070b821801d0300179000c006c4081554581c44440f100e01e132007000c005000030f000c0c6000300c4030302c0309035002624a51a052828140c03121402d81142000d8555074840c1c48100031074902801c5070740c0060101440400031501070041802041c82a40c55009141c608400c0106942101c070ba10b400c81e03450b0405200c000c0b9044001081c850303511080108413a620040141c0c1c842c0950301002e5001400d01c4808010002e0a004900d0042c800 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 569418354 1250 569417104 569417111
    0x80c04050423010e16110a02090a150503061513060b0301080607120b1003020a11010e0d08090d0507021504031a16030908090d0204060f0f030b220b06030a022101 71
    0x1c0d0014481c00c1c0c0070a07200c0d12115040a03c00c240202c1c030400d0304201c520803500c1211f500c244035501150150400700d8034030101c0780e0303207800300540c414040c44c0d4407000300000c5008000c0d50401a1101a2050348182038a10400c100c444540891b8100d030003a6000303021543c6116101c0d82d40c0c0b0039064903440104c07100c00008100e90301d24141d8a45500c1004186c1c00c0250042d00d442a10400139030080d44a0740c400c07000d0024100210344418070900a1400084148001c1d21048107100c0c405401c0350300107000005c4d543c000da5060250160300c030061354201c0760111010b01d606103440c5100c40d0310748a41e401c041c1c030464580d00e20107002050748a2413030040300280317408400c00640030012000c54041040050140c6801c110202591611076015005a0b00040001520a030342e4a5031805210301c55000e8a89103a0464040007400440b0220f0f640c803800c3c12681020b20341c1e140e84107480c581003540005125001501c0400c08030b841c01c2204000b00c5a028080030860030206290422502c240c8490300c582e0f608 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 569419604 1250 569418354 569418359
    0xa05010e010e2a130e010c1e17040f020d1205031602010207030207032607050c0a120c2c1e010626060411030a090c060504030302030703080c0405042301 67
    0x102c01a0368002c10601420003240600440108200b2404e40c903007603011280c90b00d900c644c0c1ca103070a2141c00c4202c2200d84031904151123a0600070340c0d168403400050284141207011003a054520740c03020b42d0250384015811440c00d81480010741c98140000b001d01007818484900c0451604100154090308840c0410601040510b4080f0300382d11803803200900603003290300c0c1000051803e03c11001d924500c40300300700012142c030014a983c0c4e04100d0341544c403907000450b0b41026051030954000540b6041115011780543ca4840c841e100c40c1a01c110601e50704da44a00c40348004a5a00c41042e100240b400e8003894180240c04041303032043c80007000e0718031a001c00005241070003070006a581100034925881710b1140e0342280540400c0091420790884e4883c0b22101445c02011700842c4545460710b00012000c2c2c5030304281e440c2c0ea149030844021301000304018004207800100760740c8181d074117152040340b950702d03030701d42e82c5c0c0340d014950049400505240e4000b01d001055039a1550825070604400c1e0240c0c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 569420854 1250 569419604 569419633
    0x50705061801030b0303040b0f1b151807170f060c040513090804030515011a091809010b06210a0506101d061204030e010c020915030a05010e010e 64
    0x7203000c001012555540004940950003900080342032100107050b40d0825030f0b00d0180300790950203140303403515100700043d03d0084003040f4004410300017180401461130380d0403500d452203050700241610000541010642d0405001042004e001d40540b000350103490380d004110a03501d48288a000c0309a0040d0700c0003c00301d48000d820f2b07504440d801408164030032102c90b02180241148081600e444004000210100344208103101e02e0011441c2180030540c50018100000c6100c255001c003c1c1c80d080043e107040359070b2443d03940c401c0b0815803452003007500c030225094014440e21805a40001011510b03160100c490300101e488900b40c40205800d554801e000d6001710f0700100ca4483c3d0017440e241c07141d0342051154008485074000748104811025040000502030303088111059108040007040008040e80890622203ca00c20308002d010450310341d0010340241b20041200301e030034030044c1e48151596030070048103a106401800070020f9500d02c0c407030f80d07010300700701c04165000e44a03054000d036046 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 569422104 1250 569420854 569420857
    0x1091404030f0f031b180e040b0105090a0b18160c020312030c221a0304111309080705030405030c0303030403120c0e03100c080c040302031906151205070506 69
    0x25075041e0303110b110b400c026990a0310603400003e00f0104055403854404500c80c280805c4c1c1c039074004580c450500324a004821118269030980094501d5415101407100041c9810061819503500f01e66416140c2c1e902624100100b20740c0303689aa12503201e99980510b2811200800d0085498282c090241104484e0a540c100080d100c003d4142e40b00341032190f0022214070145800924082007245400001b4032055016031041c18404080002100100b14614060aaa440e03966002100350b0a5107460313141c004000e02400c02041c003c0c050466200d00b50460b82e0300c04141b25500092143e12600c42e0b0821a03a00c0d0030501403140a80310342918802945000800d0340d100e240d00d0b5070b92081000507201814081d040c04040c090910248200d415100d42e424040c024403100400c40000f004900c114008081c070300e014001c0200d40a041000f4070150b100404e400c41012400481c0f1030340140d0500e0a2002042862101941081b000002042d00030000791a01c40300c5000d8401c680c5625183c10411405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 569423354 1250 569422104 569422111
    0x80a0201020723030d020f01200702040c090f09060302030c01170a0c0c0f060e10050c0f030408070209040b090f010216030e2e0206090a0c06140712030203010914 71
    0x35a014071820020101202c039100f060003400c52640c3c0c4401200c0c804603203414000084c8001603041403a8400000b202440b5069010886200c1005c019400210707984140c810440041e010701d4a40303401e00c50441c00b03612550014643ca204081525a941c8080c2005003040d0108a102c0d024a1b1408851984181101345060712402c81c180303c0c948405a40400400a841114090100c07070701280d0f002c10140c1c4040007155008039400314500100c0d44c07040c1d041440c030218244810303203440e00f448401582e060940e6102150207956075901d8985040c54005402100c000962000070f0340100070800c10700504442c0650070000403103402684000d0507a083c0d010320b442c5012011401c03400382000c01c0c03041080000746070001e061003c0002080000d001c01c1400800185950240c2450400910b0380c1001f030581e01c8007040010b010100180c0d076640340c00344124800d01c81003014440c40d200240f04050304440d1216440406036040144038100030f0088c3d002407003122013942c60020312004030b0007070b01c54882c80b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 569424460 1106 569423354 569423357
    0xb09070f0810060504050d0c12030905010f0509060306040207060b0d0606050a08030405030a06110408070e0a062c09190605062e0e011b0606060801080a0201 69
    0x10020103821618070b0081076104100350340e8040c0c01d440c00d41d18226003421140e45070382040c0c400000b4a800c6242c1813200b000d100e108040d08800312508465003a03c0e14441e5100c3d0241c103031788074081d00101c0d0341c1006042001072640d2400d0ba000b0301803240704900004064942c00085810003001204c12500380d681c950080c481860042040c0d40109142d8000313619040c180401b20751180c204800c01011152200104c1880d10840c005803005040403400702c85d0543e07902e01440b0302801050b503801a8440c9040e04c08541c2107101000c18003040649020038507078030b1000c600212100c20007049c2c00d469000e46110701d00388080011000500f81d00440c1e0110b02c509003002080801c105405003840e1100c130f05054500c942c41c443c9110040e1404504064906102250050790100c0c079180704544c1901e06661401d00f000320942c01007090710388039075a0044170780c0ca5002940c1d9031200c1250190 = true := by decide +kernel

theorem cover : BRFrame.Cov 569244604 569424460 := by
  have h0 := BRFrame.cov_init 569244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 569244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 569244604 ≤ n) (h2 : n < 569424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
