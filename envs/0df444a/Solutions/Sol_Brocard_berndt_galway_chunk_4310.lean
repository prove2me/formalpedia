-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4310
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:12:30.777808+00:00
-- url     : https://prove2.me/submissions/737ebb4f-50c1-48f3-b295-76fc9deb9f0e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 775000000 ≤ n < 775179856 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 775001250 1250 775000000 775000013
    0x1315020a1709100f02070b0306030109060908030f0a09331b0905101709010906020a0903060b120d0f0c0606060806090901020a020a0305070302010e1005090f06060d020402090a0e04 79
    0x1049201d1040512050765040c0c0761140b08690f00d0015070380c0003004080d0411f10b40c004250001010b494040d135139003842d080465114010302921a005e400c0e03980c0d40e07082c6500c0c60b001003000103040048050600c070001002602d50031840d05250a146034500744440c2000d11481d4003200d00c1c00c022851402c00440c08401c604c01c122031643c1500030340300d2030f405c0c0b990703003040c881d05417846005500404e100c2e10701d0001941091b0202e0b40d00c000032a0002562082070350b03400041781c02c55018030001844009082c02048841d116820041c0f4045130001c503003a00001c0555900c070041e00e000010820400c146503200c4d4080d03241608200c0d0301190a110003500c9600040005000b00c501601c9042d0220104400e90818400c8134821621607019144481d0103480640e06940401c0b0101e04543daa0200020f440d4414850f0441c040318130000800c0c9800d03d20002481c2c4400141b200b40240c22010910001da9100600c0e8417001e80d0646001d0b80310014100041c0420029500c1086183c0000080000f080b40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 775002500 1250 775001250 775001257
    0x10e010302070c080106080c030105060303032a0301030b0a180b010b0901211b080411150c0d0210111305091f03030302030f31050309120c0a0b1315020a17 68
    0x1f0b80008840005540d602010700340d64007610840d806800420200306240d0403e107030200218005000c444042481c822070700102e9200f64010b0b22011404428000c03031240b0303070190241c911840170030007214800c035884524040d4418452071803e08800200c140041c1d0045502c450201044402d02030360441b03010803200500000038090643c00818030580440030300424003180a06d400200c040c01041ca14403c1c890b02d070300d18000d08681e00cad0003030248132661081003059040c1807031654040c0c0b13104400d01466001ba41c441c15443d40d213155040c000044606603600700701046030003c6801d0901c54988865242448041540010039010420400b00515170160000d5000d09585060207409590704490b5401a00000005000e00502100308060780800141d0b4400707000e000304c0070f8900d0080104000f40074001240c1e42d0590940200d6076154040c58110070403002850802c0e035441ca042d48043d02e0341e0103c0c8981c002c8484464100441081d81442000300300c88040c0d001a002e0920b03000294034244c01d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 775003750 1250 775002500 775002509
    0x501020c060c120118090c080d171603091e050318040c0503040602092b021314010501122720030618010b10030203040b0702060103050309010e010302070c080106 71
    0x10070040440c450800e0300b01140c440c4180814107100c503900b00071406082c1c00b0103c0c954000303c2d8840341420045042007800303c1c01040036400908c0381c61007500c0080e00c0790f0714120032500880c00d0342e001c000007240c1d00c54440082c0003885c9000210302c034091600703403201c00b100c041081c000380803804480304101d00003000f0404185d0655001050a00140030041030350760036012980022010b0000ca00000c0e066005032081e0344008007061012600900058040149900c24204600b29400024198100350300402c0720030807107100c03d001111030707000000b18005040c0708003810410006000b00f92904598800d4150002e0f10721800740c00c9203441518030344840314550540d98003081601118000185030460044514090050012541e50300d0b800300170f0100e041c2c2036603469502c601005400c0d070340c0c1c00f080c0c80780c9603115100141c490800c0d0400c200110001040c080c10356000c0c40050022440000c03d64240c0c007000d180c41200f2418100048020380952070006000e1300d403000000c15014010340118042c0c8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 775005000 1250 775003750 775003753
    0x23151e2806090f08030a1e050903010908181804290112030e0f09040308090304080a0b1e01060c080d0e01020c150c090f090403090e0925030b07080613090501020c 71
    0x1070f6200c10103580c49115851b0081d000c2808009000a10711030300c1d16000440ca01400c08a0400f000a0007203402e440c40c4c1541115240000200780007142c005a07400c080000c01a5001e41400c83d0082031040e512138090320250040d200c0307c0d070340c181060880761a0300140c0045240b500107942e5818040e441c03909180012000700716086d030f00d00c02d00c3c00c040b00110a01080100340c4400741c0c4079605d007a107015401030320050640c00100400700308000100100f403225480f03002e01c005245040450041c003001200764182c40e030030b11030004103e0b0582c05440004640d0300907050070381c0c80000c200c049004218420310840f0950010440804d0b011010a0115114070303002c115128554a041d11012603128107248a64000c0c011100b02c01541041c40003607500c24480d08101c29119183c41e8903800382c0c20211202c2109501000440320400c1d548200d0080d01c14040f0302000034142141d6400321384401c02440d60b400c000b811b034000380031603807580302c0340c00c01201d48001001811824103082d0301035070202c00041c046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 775006250 1250 775005000 775005029
    0x30c0801050d12110106120c05040605090705040e0a180b04030f020c06040603020c070e0f0129090103020c0106180e120a090303050a020123151e280609 67
    0xc5042014200c0340300c2d940f29030201025401c100d01a0f40500401180a5584d07595030404540b802d01c42e40400c6040b4040c840c0d0805035807414003080161105508400d000340b10202c24046004d0300207098400307991074103200f0310b410707907640d4242c000034204d070854400e0940b000140141800003600380180514002d03a954010020042c0052760759000d613100554000c41300b0401040324501c80c1d8054001c208042c41900e07096a5188107075034040c40c09440038500f4150f40001008498920100301c104000d080c51f282201a182103003d094a02401e201603040c1500041c07001920310080d48440c7c0502000c484c0307170351420641c0b08144000c00348107902c01c0051081e101c11081c41c002000c00da031401855030b5150011142581c1d0b046491340c0055145d007083d592184801c0c200e102000c01045d0f00314400d45c184040e140361903070307130842c06422018000e030240b407031200b4144018003d2400070004e107200b51500b203040c0e100420120303a44100304002c01c080103211003001c611542d0201e01e810403074211440d503404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 775007500 1250 775006250 775006259
    0x1024171504060b1f1b2003010f0203010602010c1107050102060109020f07020d0809010e0409021309081207120c0c020d0b09190602120106050f04090b060702030d02101805100b031c030c0801 83
    0x38560314900140c80086540c004001318400031b074140c03103404809000425180780c101c0d89401641c2003038228101603516103080c20615540b0166074624507013081e000380912071034440080d4a90ba418080e501c849900082c603089030000403800c903051a0382c007502d62440703800307981004030300784c1c101c040164006013149400d122245042c0c0036404c810394000705202180801901c5180003044100b20440d5190024031581c2e8a021503a00c0c482d210300b8407034440032031610782c00e07a640d0104c43c040f1088605000d424002400941c03240e03046070564650014a103000c03503c1d15200e0300d03e012006003a448905046817020403c10085030043d20f00505040c0c210b079400c1e40c80b413100b681c0c1c601804044449200e001c0c4410820001c4942281d050103e014000030f1900d078294002c01d04000d881d4000e4405680a4a1012103680c0e0604c25035011036403560003004025000d95a0b941c0350304072a042240d40c9602c541d000381142e90300b84511206615681e040704d40328801c036200075026000711035103003002c103c50400004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 775008750 1250 775007500 775007537
    0x90f050409021c060e12130b0f0d110d06031a0603060105010206070e041d030a0905100e04050c12040c0e010e060901030b091024171504060b1f 63
    0x1c0e90040c0b410440e0200b21003902d035142d00384202650240d40312140c1c3c880c180d2040c803c801050141d070342115980c44140300c3d0010f00c0302c031541c095002100c0411034440030a041e403080e030304071005001d000309102002112000090089c03903203000b15903141140010030425a09110b040c14400100321104580d82d060801d500d4401c01d20406025030003080004038180e100f03401c001c01144000740000303202000c40404400034041000000c8040c1d00001d11035020641052042000b03240840b44443c020785508001005040c001004501850f12400440c10340054541680d01a5102c0441e5181902d403904082080a8062150041c2a0012400459011044180c151284601415000d4181d1075a941c41303031114002000e145c2140184c1c400070030402124007480c0316816800402e07030101d040b02038104684540703a0380640c0700d6881041507006c0901d40800d40481201c01040b1202c41a41c950500300b002d801054a6151b0203c001c0f400c80c90308049030340012503c0b1450341c1d9030f0548040d1070f100b0803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 775010000 1250 775008750 775008761
    0x60f0503250902070303050702100603150e0f01020d410402270108010605011b0803091011070606060309050a0204020309190f03020f031309020307110a03090f0504 72
    0x1103030160031800c4016041d10342648a04112801c1540103000503503a425124202e801c2440102c000a07115001e100896504001c001081030500608100591841e601c400c040740008440084503034450103103ca0303140302406440310029000009550b03c0c50244842002801803c1101c0388650b060f03040c00c60100021502c58043c07145110504100c0c220520107140e0024008104980c8894426a02c64544103520240d840ea1612401d50300d005c0c2d410000d4060030758105820080c100401c03400c200d0f06d6804204070600c5070136003240a00d0381d01d44556900c5030410118800b15000141000c24409034051410010305030540542020000c158960300c0c200c0c00c0c0c5042307030000380c125401038003158058034240e030085801c0100c00080303840084a103481000702ca034100038107031103c0c5071500814080c150103000001007244500040c5240c61070b5008400816041c80c0283c04001d64007200040c03050b8065200c03518040700d25004c071007001480d8540201145d0003070203180c5941031904000100d606250045 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 775011250 1250 775010000 775010009
    0x80303040c150f0c08190306090e01090b150409080301060815010318021e0a03050102030103150e0d08070203040b040b0a0905220207020d060509061f0e01150210050106030e01060f 79
    0x208041e62101c01c108807811028501d0075a00701504001011b00d203588000100441b290645020030094508610301084a100c801c821605904103888030380000c42e641c54490744030200702c40c07c410703a02030078000c00c00510110034002d000000020020403070036080303e1414862429001c400c1e00c6c1b081e19400440c00d5030000f005c0a81a6542c0385207540042c030300360884601c3c0d031258445c0201192420400101800181c0d4001e0311181d500000510510620021040d40541d42031400c2c481140c42600090303031078070501c0040c1c08201d444e40118a0030f40c424001c88004000d84d810460320703240ca54604039060380c0100d0010000c05c0b5821030010385c60030030100c086c0c07800300c540343d030f01141070b110544502c0a0f5000c0304003203034080b6180b0043c82c000f407110300c01c00d801901c008000f4404c0c0e140c15110541e4452100701c8800c50149203400030800290400181d81c1518183c1c2c8034140441d00102c0280d20700001904054800340c113010022a5143d03055124032444441ca1000b4403a49a43e1a030301c3d69090814001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 775012500 1250 775011250 775011257
    0x51b01140906060307032f030709020a02010e15040210020c0303120612063102030106080601081203010e010527010905100501050c1b0102070f0803030f060f0919090c080303040c15 79
    0x2400501031000790390321100a241c003407010510303022490000313040c40740c0d032b4000c41c407500d03400320350000d1040d030912502c0c09480d603e5009084000240c80100e84030800144020300c80c54800405203852482400742020703a8130003400312621246034580303c03001f180707003201c016000e00107808440d8070400f00007407040d00811410315401d1a00c0707080e00003804a801004c03040c046082c002c240050040e1002d00c101001403c1d4040501120350501c0d82a609109510300601c28011080c001030084a03005010541141d10803150303d0301120a0400720a001201c403e524032105079448000282d6030720300d40000d486801180c0d0060415511000150340fa070103010400b507090360100c0403900042846e5004500e008005004480d40c041da2813600340c51080e0b060f041400281c00101c14405401e420545494112000301d07a65904010310201280b460800203140710503000b074100a01004031081e0303001a030055002410080c1c090b48030440c3c140e0301d0b4003c1c2c800319440403248000040400e048000321007104020b69 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 775013750 1250 775012500 775012523
    0xf0f13090f021507150c1404170f030712180e090105060123030f090703050f01020a0e04020c06130c0f06090e06040207030c0807080f0a1e020c030a03051b0114090606030703 76
    0x40900003013078001c42000602c48100c2e1542d10000c42000540020116607030116540ca505270501410072141c0703900c2070381540c01404034100154001d04101c061001e10b01e04000b600340c0440c0703402208041a40500000b48400c41400725503041904107030f1040100b070700c0b0648840714800080d0311407a442820500208024000b0503829191840c2140d080520f0504881c002a140d0b16823604291075a141c0c000d5a030350004441030f4180d006801403040c45000c480c11401d003100400c14039142c0c90000c1101c02c1a800c6082c0c05c0c070800542400705005402c4818560144075110b44010301020068004c07072207100788480014200d890140202c40e940e6030b245c5d54440107001559990780154000410403103441b081807143d0070702d84c8030800c00b411042c0c400e80e45400c801889154883c58070041e5410780380454009105189543e140020f0b034a400917414a40140e03288007014441107244040c80d40e4a5082d42020360720f042d4240c020210380d00418091080c0d54054403458101640c4882a00c0003c0041c0c0000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 775015000 1250 775013750 775013783
    0x1050109030b0a0209090712050c09060307181802090310020c0304061b02060d051e07080c0a03020909040b040c090e060610020c090925050f0f13090f021507 69
    0x78031050740142e0545005030419011320006840c0680441f046000034038640c090084481c0c0307a0060a401149080303d4910785503034400403031401e10004090006104050502004041003280c1c80002041d001a104c400c2c042922003a0000c4d60098204500c07034402d64a410141d2040c0b442140ea00081c2000213514161405406440400140300e420780782c0c6440c0c00e29403000d03849407402000304081c000c5001400f4a0400500c0d840e4420425a06900c009201d04119203140c01000564020910000003915071114040441c080e20400820039001141e10060104200340e00c50040d00840c070070380700c1004c07440e1641550300458400d2400d0501541c0481c000c030b00241040c1c484e04204420910581c0c010503c1c2c000070802602c401c2d61050001c0c1d011031402003c0c0c10200d002528802c2005004c901c0e0145400c0001c1c42d62040695241d2155100502040d5640d035074483c1c0100e5099002c20502046c0c03104d0901c1300000f0ba50b008160300032030301b01440c1d1040e8001d11085a18035a40000c02d00d8012025 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 775016250 1250 775015000 775015013
    0x20c033310060c1b08030307030e06040f020f120a08030a24060503181f0c02070305120306060c10020d0c0f050a0e040b1c12090501020a14120c1605090105010903 71
    0x661200b99000ba002182d6481104d0514a0303802c05010841d0045680c0e00380140002c0c00c641014030901e95039001402480002036003860340340880c80d0101e84610036150094000340c26207182c00d40981326886090b44140801110304003031446002d00800c100714900c0b40f51110001c66120342c0d41c0107110180d031201800700600550107035405c0070b030003411300766800030210310145807000c110044884600c40512004162400e80074980c011071461004d000e4161031961450741d10305c140c000c804103070940400090419200e110940380300d2015501240c80c01c152480c0d01e04001d51007564480380160411440050751400390140c07042c0502240e441d217141004039042203400401c2d0580542e07210b515440340074000d503a08480f0b84041e003119240e105000105182441c1000d040c80860010301600041c1000340da0380108101100343d400c42322050070410b804040c5801c0c06182c0c40003004a8501156550400c2c2000030000d1303810000314860403401d620740c0c0c00c000302813001344100c0e030010300a1001400060134 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 775017500 1250 775016250 775016267
    0x1c0308130c03150b0f030d030218190e0109060b25081801120b0d0b090c04060b0a20100b010c0f03260f0a0903020c03331006 55
    0x19464011190220a40d4454440c02081d42c020303140841144400c0300074004a2203120903045080342c019201c0300c51507012a0b11000c1641d00d18050541c042101d001c10001d401800303c07a81c4005003080800410080f6242090241d4000d01a0f499200342c0089a04030480c468a13055450f4680d84608004038044981c20740020003218105070240c00400400003540d100103481000040858601101c0c0c4030f00005010b0610f03511592403240c28001c00d48000d845481c0320392840d46d0803200806550365031030f190034900f26005c0e803140e82240c600600015490515030217001d080301c1079a10500c1c803500c0202440c0007050750909540700c64100c8111080b520009a000c5400171106040c01d80e4180f80d261100c90100d20f8424059004c20f0403a0b1100c00c0c4008030302c04000c000c0700090b545810078100a0b034041200c3c07100501ca901041d44e90307184d1509150007002259880e910040403124481e06515855900c40b116040100b4040810a00d08103041d002c501c1c058071501da0035140454003407800c5400c5a8244 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 775018750 1250 775017500 775017511
    0x309090402040c0c0f0c1401091a03060a1d192313140309040e06010602030a0c210c0516030203120a110a0606031203020909160210090318051c0308 65
    0x80010000c3c00011078200c005d8124500611403005010701d4580004804801080342c54104150a001400001030408014030080e825074a40c50b242d544180128402e8802e80c0c10516440018444880c24004210f02c41c82c0f24900319403642c040342d0f100c2c211510582d461041c8980c2c940424684040079408845100d40d072042018141d50007204a03131310361103d1030000c08a001c50a07040010700305e20324142400b40700444c21100d0018509980340c044025103038001c1560004c100610340c6046c4041c0a80c4850900700300c0e0030403841d10441105d5070380c080e128804042003202c1500800200e000d4503414035260351304803034019015151030360710481c0c0030105500c0120749206011041402802c04802000940c00b02485003800040e083d00b1410a501d80140c04402c0c982018010082024551101c4200d1600592454000d072040c64000381c00340d043c84210301c48150190b00d8003940c031082c10343c00300e4514042e5a880c2c91078240141c441090044034241d9411804110303500780a4000028806d112407544403 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 775020000 1250 775018750 775018757
    0x12a0314041d0108240403020709021801090b2b020c0a0503030403020601210602070c0b0f071407031a150a0303120b0415050d0f0c08010c110309090402040c 69
    0x400c00140c0404903504a50842c4940503000e0003201c400c014071a0a02c0d014008460052500c0c561003070310031080302042568011408007220201c0c080500800003040500910841552542c21415050305011a25100c45000402103140001d55055000480d5005441c460004205034086403142203640416000326952075030810000442a4062004100da64894800b0f90740d64141800c2c0207143c20410f800c6080d44094142c3c1001180c04041c00d41000c0075070210002da1140310a007401e60300f0007003583c041041000c000070300b146182803200003172850f1442080c0515125001004890340d54465000c024030903442280380440d0440001c00c10390384400d18040107401134160001080c50141b041e48100c01051400c0c40524109417036004002006805031410006401c40386040404110340c2d1113054054851115020b040c000d02c0922503104540080c1300041e0140d03211500c3e03000b00000e902000c00141090b139040c540c2c02e004000c66101a2000302000d500340c03102d0f0204401000c10341c80031401e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 775021250 1250 775020000 775020017
    0x30115020115050f1e120706080a020a0c03080604021b030d2414130f020a080f040c0e0a0b0303031509011e150e030f0c1906090333060302030c012a03 66
    0x5c680c1d441040955181e00a0040d050a03440d00e00c2c0a850445c002c1c2c501b20b0000d0040c017050840030381c40024900c40e2901031900c21010340750a0301080c000d11403564450a08a0051060b07881c1c114004010088000036000420000c13100010310000e801034002c0e00802161018400c000440340d038800726000d0100146048606020280c40400711145010840d604039008105038540c43e4008112650005504510040d42e180c0340d40c8200e00c662840c000e9040782d9045c0c038041000c41b0100e074040c0603429030140071203a6074240b020901e15080700b0000c02038407032034080002040c0802c00c40e0340c0301c40158003c0038100d5098140040903540c0014028500104112800d26200a80d400c000e00c0e24800e03a45405070100f401070000f84916034603401412264a00304c0c075020803441b41e111012004690f0000045107130400c05401400100300d011211001041e14140b13880036505c095408a01168800c50031108c10b512154019202007a144d4101a9061a1184480d041000d10302407480d0380ea11a2501909 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 775022500 1250 775021250 775021309
    0xd0e070e0910060f0305060403080703020d150f0f060516080d0207080702030d030b130213171c08010501090303050a020a06060801020705010501050607111504050402030115020115050f 81
    0xc8069044544410640c010415100c10038414843c54014080084521603400c1c05d5849403966100060030060412a0301c50000c0c5e042e6201c6e034140d540c851580407041c8400c60000b01506030051036401070a15103e244440041e2048002d5001800c1b035a480d01caa5080052501d00c07180c041c1c0701a9030a40764890200030801c4500c0807031004143d124401c0d03240c240c958000d401410b03c0c00322148030300e00604d441d0807102021a03807041290b07601045511400740c2d5502d07800d46040d800c110207901040c05800c1c01c0c0d1000f6400c10303000c1007a4001d043c4115402c1c42d604035400781261035440c05e106044c0440c2401d082070001c42e02c120010000720443d40116010810780d90345d03000845010380c0c030102c69a540422050100032080c01000e0040408940c214101070103500c03038010600c06144000e1040d02d0302c1402c0c890450189054038002c01005000b1503d0790394950300c844486c40d0012103e00154030302002d10381c0540c1a21010400e50740041c0400780d0104010003800540340d4054a40ca503104201d000749403 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 775023750 1250 775022500 775022519
    0x4020a03021c050f150726240102010e0c0f0a051e2d042d061a130509060d061503020a050603070c12020a170a030627111603030509060c07080d0e07 65
    0x7405400707500e26923956040e4a1003c68441441000840d0442e41482c40070703196150001259900c101c000c44440310101141070001d072241e4400d030b0140f81c002ca4a440d1696031031060100c50742d030741c0c64152155440900c003042250a1540c1c10b418207107a12611426100f00d9080c19070003c3c0c0c0040c5040580c009400480401c50100794003a4107503196103855810500200b14000c250160178541d0b04041d60401c195111414001d00041c040c2502030300309100014510fa4a00d41d0905071150001400c20020031090030f64202d001e1180001d9000300c05409002500341171030b800300e80c810805c5030382c6d07035820144a985e20940551060a400114130524804102040382c02c0c042da1510071011444541d01c0309035001c05011746002c1c0d44030b81c08940401401d660100120380701c03192400546180000d0000920aa04129000d100106035102070009080b00c101a0075502613070080c00c0000458003941e403101ea80c00028800c01030000d0402c0402c2c02085001d0540740c001845584503481a100f80720703106c09500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 775025000 1250 775023750 775023827
    0x91203050d140403020d0f050306151303030e19061205040c05060d02040f09090206070303020c0a0b19050c03060a09091412040609090902150304020a03021c050f1507 73
    0x50072080c0000780f208141e010007103000d15120604080c40c8400b10764002500c80e01000b0285401343c40401d10840300c500c0c0f40340c101d4120096144a40040b19241e060040114040540d841d0003074440e554107401020358101c0e001d04454559880403011003131095514040e000243c0104c1d0001d10b11040440c00e035032400701820502203080344c01600d9510b0715110f22050b02003a88000c4d46607103015000070158a403481280e00c1e55402d801c000d03941d2285401494a400c1462602a12500540061040f41d4914840103284810280801d1006454503090300145101c00e54031b0980c01024840d04004038403454201091860065480074840c411444100b400d0000080c45020420700005041c002c0035040354480c0068001c011003084110b80d82d83c0405c55402016010360120000030001030115540c10001c03001841e4050300a41501c081c0079400c885540c1c9140003180c0b0390103110f44500c00207000103030758150111810625a2a03407a681ca068030060381503040103003b600b28441c288503a400c0c12694 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 775026250 1250 775025000 775025021
    0x813180b0405130507060c0c0b030109022205211e0105040201110c1806060c0706080a061a1608070b070f0909051005091305122206091203050d 63
    0x10403103241080401c011110001c00300c118107441246060040340e40003a5640a484c8181800c000d1140d96003082c800c8080e1560002442c15000400407a102600340c0107400190030380e82c19410000800e44038510cc5440c54021243c12800d08080d001281003002c481200040f03041d004d55060351a54404285410400910400b42d42e454506110442d6070060807a09121400300151803400b035810001400c0d0369034600c0c00070300c01c0d02c1c040c013064080e95504110303950342d81e8020449500031783d9040003a0448004403000030310540742240020307455040c2d180380e6000b040541040352801d010885030080810070100c054a2201c2d09001500010304440c0e0014001d940b1500c1c2e0400010803050700402854a980216820314145801d0200501c405260300c4181c0381c003120003030311540c0c903201a060700d070100b448040c09621484001c40300288681c0000c2c44ea024014902040010801c404104258010b100700c400050b9032690810617040c1c4de01012107003505c41e241031441c0c040c200040c00b0a40e0381c003465 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 775027500 1250 775026250 775026299
    0x501091e18020a1d060114032a0a020106032a03020402070602041802091003021c0b063903070b071b020d06051e0114091008010c080a0b0a120813 64
    0x6010540794404d21340542c03000091031b0210f21404522142e01150001500b0508001d69001c44070032806082c40080140c241c0311401941c0f21480508000d02074072503481306130340580c0d2080418180b243c4000301e000c1804142e48504004618540c00c2c040258000e5200f507680c16424000480d060102140c030440006e421038015071a1a400c41c00c1000035000114440181441040020b8028803241a04500c40b045640001032100c036180100c0d01c50310442c502250303e0a241c1d050700a042000c0c1c08103014030b0104a8045548130100c1801c184d9034400c090026001d48405400590341521482e103010107407200c41801030005003240c1c04940c0d20030700c1c4002112900d881d0b00800c8549c84062003402615400c0f4629108076514011060310500c408010040c0a601c4c0100010f40400280c0b00000c001c01c84800200040c1d2004080284003500a5544c811054180414604985440c0090300207032a1816100524030502c1e9441c20305075440310100a03030200844030000707281041c4c1406201080075545 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 775028750 1250 775027500 775027529
    0xf1215050d060f0c1d01080f1303090b2a030306241e0d050604090209070c081b150108011109010c0614010e1b040b0d0e03071b05040501091e18020a 65
    0x40c1d0105c400c00300f08059040058800c2000f43c2c2c00d082000454024421000c150b16110150400b1182c2110340d80040c5001e400000d112188201c0000203500140c58440c05103a20581c0d011303410351640300640343c0562002404015146003c0ca041e24a00c445984d50405032070308154100034241100c524980c10307000300340411248000302d81d50040c0e44d40510102c80c200520303030150380000d4803c00d0152080d003c00201c180400c0c1040a5036084840c98407468949202d82c0e5407440009540320b1420900140052030306000041c58041400750a07204080c1d0501c241c2040700d143c004440942c84003c0941340c09481e098076844401c0121400790280040318031115261034841581c181107211a610714180000c200010494910002c0640344990052000400d80418001d4640d1542c0078560005d092880344103002c038240101031818400304c42d0180ca05200382ea030384070080c2d001ca0303075111107d285003110401201500e1a00c2e44c40381813000e2400b0850200d8480030307004115290740c0c0f50001072408a148 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 775030000 1250 775028750 775028777
    0x1142b06051b16140321011403030310061d04050403120b010f1e05040305030a0819050105010e0108090708010c020307022b06020304060207120f1215050d060f0c 71
    0x6007420503a10005011500e402000d56050f4074022800601410084050300c1e028296441482200c800d40401c09050b8501088603c810500c040c0a11072010a4460183c0040c9581400b20589100d05031118944842070711b08142518011030b0485000031f9880d0f40c4190714000e070389a12916008900980c1c9801105100101c104d04845907400c80c10b040c440c2c230644860600d03074404034130204192250003640380f002144000703584034003454000400501002c42d8021455511503640c0b445840c1c881c02d000000000d01d140d940413034800780507560014401841c94030183d4004c03824180c12000303000441d0b82c196030342d0310f610342190100c000c0c140c0140c01c0000d4113003d516021665240304c2c14030300e03000401091450180c0400811a0000500341a0040b00081c00d000c80ca9050310001900154845400300503c28010412054803001c0d101003031105905403600710f1a40b00350300d102c1e00e608060344061410f20302040020360341c0c18021a600b9888071046014039449010b0420740211648818180c231a81 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 775031250 1250 775030000 775030021
    0x2805060c03060303041404060801020a020f010501061715010e0a0f06140a0e0d050a020303070605041a0402030d0309050f0d0c030f020d080703110706060621020301142b0605 76
    0xa003180e804200140140712141d078001c0b0440e0102c961400004d4000c10220002c00d010300a607600100c40b03544085007075400e46801080800044101d10000c003c1e07aa254001a22180c0400d844007441280580c00a414042420b000c040308180505000c0900240c0200003141d8018035000860445c074107000402000d82c0004c00c0480c000e00e0841c00d542005e6180d680103010b1048514440d101c4c1031030040a00a0003400d04c200c401c1d541e0003a040d03c5d507a8940d030030004060041560200e660040000e4890b0115180c11440d41c0074960080c0581079192102404602900c420102514a8022000d100354800303420001081c0100041c1c40b0b06200703281038113015108003812000881917410030b6010035203103130748542800d610400c0b504002030100c1d15600480b04500a0a100400f524604400421501d400c200040d800032100381050510800e082030807001d0b80000e00c01d0041615030f0f04c1510409180914030700801c0e8031414002a04828442c08941c2c1c010511041510b102e90b0704c10074068425113 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 775032500 1250 775031250 775031263
    0x204060207080c0d1e05010207050607110102090a1404060b120105040c05070b072613050d021f02070f050a0f02091006050d11090312120106020c01080114032805 71
    0x2d40a0010880d00c2008070350a13080c4158014403801030098842c011010080648000342d8005000f1920343c80c0915025903680c20a030750400c040f841a80109113481414000c42c1c9814501511901c2164644089038811241003400035502603210b10b004a483c5081a01078105101c02ea01c001d43d15500d46020302080b1003200d100102007040420814000c0ba4001c14113030340000c12031a04400c40c3c500b056140c3d40174603c541a00d210301c00c2100a008030f0402d80c0e401034800c40d0003003040c0c1d440c0e120401c00590740c59184800750340141c800004604480e01c440d50160005078060312983e09191256500e41d402c051040408441e84004128154198104004159030002c0c0b800d0402102509004001d032941c014036524050203521908070341000450b040a41e40000750240458451b1624040e4500c00703600400000d201e5034a91000003c0c5841c03000541010507401a180c0001a0b405c20383c01644030010020655058403030020341070a05220b03030000250390500c1e40044400c420b26454064181034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 775033750 1250 775032500 775032509
    0xf04021f200a0b0c1213020f040c020d0e030609150408070f0507090f0c0e060313061a01081b0306061e18030c030708060a330f0f0609050103050a02120a0204060207 72
    0x80040c09440c5d00c8820400c00e0341e4220381084c54039031140e41a440060512220034070b242d40c0007401c0c0b50891662503000202d985009036561521025017000405250b641d00b000c0307172802c6c50f690140401c0c40c00d5201100c10f56800a009601d0107207400003c3d00c600c04842c154990854250b0710800e810400c001143c451020350000030b040034030012a540a0040249500d502c00341d00c90500000401c078540745455145405c50b500000501010314102c2c0d50b0a00300119000450204104800043c1440c3e0b504480c000000504684a411030312400c0c1401007035001849251850926000c040f00174030104000b520b4240c041800e0007840c401a1000c3c581417060505005002e0345c4a20300612021a005c00c41d1503000c010003400280002810454445a0314402c200f0254a00001d0341c00c054200302c44840c02c1a43c9508851a40c0184e54002490310411144948000100000e90500096200350400350300400c0558025081490640300c880d610b030410785201ca01158001020080f20346c0600100d4000e0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 775035000 1250 775033750 775033771
    0x70803011d160807140d0c0203190903020a0e040314040f0314011509021806120f071103070308040809101d0109061718060403170f04021f200a0b 64
    0x2801090000f5111440c064400e60034000071002c4c140304654044240c0d074180509440500c08041c41c96000ba481c0e5020240103d0101e56070407440389074501400c4440100da074068018080c00d840c0c04014800030b40301800460811010182403001034200c000a4000b405000030840e41480c5145011000000c9031007118081e40d04100981080c40f0022007244200e680f8000c0260303540c0c051140340c03e82d44e0140c41000e540440045201c0c0300030b50b000003000d4411100040c1400080d02c86180940d010740d0401075040042e4010806000001e1156000369006407061035080e00708011000002c050801034400ca10001d500180c88188090031041e0060000c94213013000084542000303c0245507115411912000504140203d101b03449149903843d1411710f04402d40742d00d402d0602d0002e01950040900200060381d081c08120401c004280031070040d039000700b9065603100c80f400941102a1f100106034240010352601c40802032401c07403507102400c202006450715084604e0003d000300d1000c2e01c2540765 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 775036250 1250 775035000 775035031
    0x8070f0303050d090203010b0607080d050f0907061206240206010e01181505030114090c0103060605030f090703050708210301030221120d021209010509061b070803011d 74
    0x119410104032121071030340032008213007000c281c008203014102d0f0580003600420000b50074820f006017203001c0c2c1640c251904090290303445001d20b441000200307640860b610740140104001290003445440360408d960000490101d81d5031041c141c0b1015402003240b420710421213000c0c0000d0781848098094840001490400d5040c00d42c0c583c01c0c00d0800f001000b100d941c4401409058464140303040051000034024440b07050400405500c4031401d6a25a52500c9020300e0a80151702900520040c0e0340d603907a903181103640d05901d103400303050058044030450040c0e5a020012400c20300401c2c0c060310200005184103211440d100229403410000606600400d00c01803005a275485008042082d15001c3c0d0f500881414a5550074800038503035401604000146410b0016116000303000c9402a0304141c0885545480c40c2600743d50342152001d0064100600050b1420030104405280d141000728481c10b04106581750011030b4802e07045803940c8200c200c5c0250b031135242403071425448036010030003164 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 775037500 1250 775036250 775036253
    0x40e01150915050f0d050106030e0f0606010518130c030b0a050a0807060305040519050a120509010c06020f04050d05030909010611150c0c19200306130203030f03090708070f03 77
    0x300b1201c0450700c604100001034000702c811a45070503182031208170007003001196500c441c0074000b0304a440c2c0323003002801032805202c40f0050101d00729110b084180c581e20710b007842581d034200c021040384d003091750300c0544a40060081c0d50b942c881c200c03900043d52400154249410100109544c42e617001e02e200b030100110034030001d200410304004584c5542000300b1161945e250003414900009071408105452140074020b000340042c40c5410240a10070221044020f0142214980b203078842e40c1d03020400e41d030481c000042d02c55000f071055041d1845030a0034146c0300c0000554646081009540d04e80c00030604080d50b141c0880058010b15840c18aa844070019244803522440e1322061104011800000912003088940480349011400000c0d40c0d61080c82c0c243d0510184610242521106425010802d0b907003030584240c92000c40c001e000740419507501000071102d40120508076010b0105120921007400f001c00514000d6034154080e020207405d2801092030440c40390311034086079991483c00c10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 775038750 1250 775037500 775037519
    0x50907051201021c0c030b0306090601030314040e071202221d04240902130207060b030303270a0b1e0f041208090f2413080a080714040e011509 63
    0x1038641419007404240100c5c410b205500a05040c0700d016098040c8604202d40e217000401d225050360702c6515119204948440c114400740514044d4050300070700c4102140c4502c0c0144040402c3c00640f140151030807800827041040e80c0c1030300d5001c1030401d02d00b031824800d416a20304000324041c5900e400001d9460540c03510001c0c40c5c454000110f0501408100b0300702080550807241c00c0c40d40242003021a02501d00242c070081d44800003c0e034000d0f2400c04040d200d40781c040201c90003805e111400d44c02460300425840d441c0500c000740c4002610491307804400080002c919284114135224a40c044a00c40d05102e001b0000010003c1034071050110400002490440b8450840c41480c40e282c020755803401c03c5070789404450041d2543c00e01c141c41d0082da41540c81480c480b4400b07004003190000b030700d441280c00c0708480340a070700420002c010300202c459948145210b5030b0058062903c2003044801c1151002c06502903044810102d0341640144880080c4c4402d044524209251500c3e0070f03494180d114 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 775040000 1250 775038750 775038787
    0x9080c01050a1d0a030f02030616080a0c030204091a01080703060605031501020f1c0e06070b040b1009060305060402010e06030610050d27021804050607140d05090705120102 76
    0xf40011030307901c0030909403801850a0101e60242201c158182c82c0d040401404075400c00c2244288120800156840300345a41ca81c41000305490b91045c036240c012001e009000c010120301d0030540c1c20310000504030f210703004a9071140d0000b81ca02c911001d00d84001041401d000b0114401c1c142008020000f1940c800c00301ca5003c3c414619030310b00a107001c070040f4101a010320b0b0031a070503c11449858030352641e0000301d0700c1040300c5440d290910410102404540d01500c1000380c02d0401c40700c00a0040784112002ca03500604203103040d802c15451303481082c22641c49400540340d13039000c40204011940c00032411019100115841411843c0910000f825a11103d500f9000c106010428926481c403941118020300100c80450100e00080d0000c802e000400503801d81c031403240035410220340c0d8075110305c00b4080ea400501400856441d454203584600c00000001d0b44608200944180e8801c00d1248501411114001e4203600c1c2c03a0008020f040c440c9a42040038a0344104a84010b0380d1000411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 775041250 1250 775040000 775040017
    0x230307020402090103060b0a1206140913140d020303010f12020d1b05120606040c1e030b010512010605030a050601090f031e0c031a1324060b180109080c0105 69
    0x543d4560f18000102e01411031640f088888810100318890400d410003001a2041e0b06440100716050b40c0c1c1131002c1c81c911682030115004142078000c00c95460304450b85500c0e40b4080c01e000602603440301403180c58808a804030390010303040800188410140c10410000424842500c1c0c4107880490300015844852444001c0008021a0b13942040320303801d00105000744001005c03401d2034100200e142d9118a41100c11602ca14a05030b00d4190302406502900035070314016005440040302030100b60018100c1a5256040c40414030510384400e010882d814040c0031035a40e0a0340302e04220513100306581001c0d00c0c490500c007248405200c450740c41c07549003080700e4120f0b2164010181805d03519540e146e80c41005481c003140c003440441804221b000c01d903152180a00c2c00603140c1d82d00707140106107040d100401400720000c0c040300c201b000200d0300c0e810000e51002d200018003a5440140700760503408405024018100e00c207200b0700039a001104800144a810058010034015200080c66031107000c0c131 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 775042500 1250 775041250 775041259
    0x201110a03020c070503011e060e07202107031b050d1803060903030501180b030c011d09010f330309050a0803010315050c0a0c0b06010309050a080723030702 69
    0x15000003c2d41c00701300120003410017800030414101190900c2000780704616102c2282428840002540c4141410300c1e84500584e69851840c40640c00c0c07640c00901400d10a1481032141e12089000c0e0f404c1180c2001800307c0c0c00300076a5840803185005800b600d040c1310050f0031000c100312000c000c11408180c05514082d1850804120b02440d400d1420242c095000900aa0b1800318203104060301503019030f0690700d0140301040d104030a0b209030710903102c9405069030142c014050b580015405a65854601d0303c010100c00071054031003001c81d9021000364006a007601c07802404202600d108108048074180c0c26054080b8410b00068030120181e03200a41d40404d5687c0003800c007031100c107002d030111013580014480d0b56540d690420403801c039410300c10380b820640b0341008215600d20640440301c10a9641d21541c0c24007a9545600715120307030081059050603240c0441400143c018040c41d01c0140c4601d00383ca803521020f00b05113600c0551140e076420003104940703080c40c88100c000147c03501d43d0350444 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 775043750 1250 775042500 775042507
    0x120606020a0f11030f030c070620100207080720040b0d0b04021c0c030c230108130c0b27060403051903120606031d010c050a1b0804081c0201110a0302 66
    0x140424502464121880c2c1180401f04816040140c0401d02c201118403d540e508202030314004010315088040d142c208043c0e220b0325418a448000741c026018060044180b10304001540d11030005440c400c031015031145010410f401e5103482c00d84203500500d10242c07203c040b160300b20b80c2d070300d03c070040098400303842607441e01401080303141c0800342482499400f0742c100b69080e5491502d48a4210305025400c0000c142d01d4100b03601c00700780d08000315840700503512081240c48194034850304003c0504182d0b5030640c01d0340045a2201c00d000100b00c807039181c50348141c0c9400301d10130b0b04014000400c4003a128038410002003010603000200e5820a50f01460b481554003103504d4140c0e40030041000398103405080220003e04140c1550014600c000c1e024142c0c114110428030103800c0341ca807070880c1c03001300f801400321049452040c01a40540c071415442d5001a550315151a29540c200c1c2e4010145030307100a4105c25241c0614540700000c0075240002d01030350304504019107045c00707218569020183d012 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 775045000 1250 775043750 775043783
    0x705040e0603120a0503010e0c03061e0406150504230d1e02090a090201080a0507090b0a02030f0706051009061410120c0503010503010c08060307061419120606020a0f 73
    0x10303c0360f100300706641d00c1c0c0c00d1383c2c80c0c5040d400a040c9400034843c8040086440c80080d41381d8a40700116072081c5030041c44c1c042c07000c00d05201400000442a140c030340195940380041944081e03c00060002c1200d5211035485900c0c1101014814040d290303066a8903004140211168641c6012403240641c044d10700e0100a01c0350b840c03040c011501b51000396000082c0010300c01c04049507402100c1d568002c3e80c41d040d507a03503450a110b0a4840039207144e80061881c400800401c40c0390300c040c00000040788103880c6020303881071480803290012882501e400350f446041c010000580307106880200030041080c0304e00ea00d41004020310691400255010f6001d07941070841562140841104403154450f0400c02c9021702e400040c2650801d02035240250b10f442c015202060003140e10f5485510000c0007000040d0510341b0440354403900c01d50040d10f080b802e200a17800f100000d0791815143ca41540c54218002400c480541a141c0c5c6e42e12807011741d04030241c5030011030080c5003102e40d0a504540d40d00c20b0746015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 775046250 1250 775045000 775045003
    0x8101a04090312020715051617060a03060906020421120f0c0203030d0903032318030f0a11010b061918051309052407030c140a020a0302060f0705040e0603 68
    0x64038a00d0000c14400503608007000900e504051002a0b806c8040010b90381c0d446102c55003918818400003c0354525034503201c4440101c94060b070020010b00300500042d81c0f030783c5200030f1b25850355045440c1e54000c102406684003404c007006003011031008103010592180c0303032400e1004a00040c88100110000e640803064021a41d0301c0d076259028003120b41e18919131404a0050000b00803ca00203402c02001a0032164031148040c0958012687c038031030341d00e0380380c041c245180403401c0f444020300041c400407500142c0540545440481a10303003071080c00c00101841c0c2140c020f060044c5c071540c0140a485000e5041b03180380c0054078050708003400c2c0c50b0314050000000c0e0784d950b485107500c41603100c99080a0340490b080300348118407900c08c443c50500041d407203044100c01c080d0011814011000003c014601c02e40008280b46001d003042c1a0328a00e0355080c0e46580e02a0352560003607409207410000b01681001a540c0c021144686040c80e41043d00000f0710511542c0f2800501c40068008102c1d01d650 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 775047500 1250 775046250 775046267
    0x804090b19061e0905060a030b040e010c081005010c1203050414011a09100311010f0e04050c04051017011e0e010e06100507020d02040903200708101a040903 69
    0x15003100d03403507580ea640c100202520315840741c1050b1070300c1c240d03d048609401104854140d034001007500f410415240c0e022401020b24a01c041e034407a0725900c040b101c0c00000e03c40c0b01c0801002e9611b80d4070b9881d010740c20032a1424550300a074100040c9005d0200480c00c020110107444a441c035010070161102d051120f07200d10342c222805400d502c2c0807401f000b181142d101c00c1c80d11a41c25208078000da580d400b104004d0200601c40600f40300c0d010310780808550305c07e2051840d07000580c20001c00d882c86210200e401c452049522100c68580098207000c3c0d803500c1101e203101d6a83d94508a10303443d10b03281d41542c0178481841142c50503d0900d10300a5607413005000c0c0b4020300700c00e180c1c04c0c04542e503541030510a41d00907140507004001c138602c09030f400d41c890004c803000750350080c0016401c44550341c01c0c00024800e03844150300700113080d500d01000580d846001d4080310240345c001c02d0024103050304182441818002680030328030345021a812034441012403081000c080305e0000b22028241420303600c010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 775048750 1250 775047500 775047529
    0x4030b0711151f0e1501020a0f02040513120302040501030b0405070f0e0a0e090706030e19080f0c061302040e010b0a09020a2a121b11060c012906070804090b 69
    0x3030400211388060980010391041e886920240c1014402d18016601c0782d02d52280500006140140d0b82c0150070903801040d00034041c0040500300d00e805480d00e0071400044441400020340010702007206613454040d48214601c00c031010001420f0030100034001c1c1c040f49000f1b1040c8154070401010f2a950200c0c980d004010070300c980c0c081d91800304001e030b456500900601010a182016085125000144400ca04642c031100089001103e4a5a08076600f00f02080f1080000400542603c49818002540030b9503094031654081d51051041000381d07603900700003600c568901a040180c03a0707900300b1030701700f15400c1000c01a070f03c001c040300403102002020a40134000b00a031102d60303134001d4080bd04030324841c06190741c4c003544180d40741b00700e940c100848900d200c114420040103001c5403d900b403080c100718005241510300070a0810250948401e20030103c580030000c0300c03c0740d1019040d00800607407001140c00380e141005664031030056000e0341c0608003200d640c40140c6032503a21004078950254 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 775050000 1250 775048750 775048801
    0x30f0601031d01150b0a02030a080c040b1804140c0706050c160f03080108070608010504150905130c08070e07120e06040b16180b07031205040804030b071115 69
    0x100c00c2c20100c0740a45412526050403031403580f000100350b04050b0075542c1d8030380968051481e0580f01241161104009000409440c030208000200c60b402040145040803203d41c050241541c0d0400b007204566580a4070300b010404078003041001880082200e00255212030002882e446010480b035442c061000c0c2681112140f841070002e00c141c40800003040c512aa0341e8a510faa29401c6503602e5150604c1441d0101d0000c00043c407161800c0c0c0c1181320074080c0b1045d41c0800c10307038030344841c0142d030300030390f00b8141c00340711610f000e000d10180030304140140410320000c0a5882c9809990700c00c00f18001c00700020000b040860b0b0003102c2141d005404450280c000300d40c1281001c3c01c040e0502c0034180d40c4a07041f40d01c80300882c603a0b940100b80c81860304411088500044d49009a14003040e8000c030700440800c003052007080d529a0345c5126560040b40181e02940d01d4a082d0310388400c09880203898035051200c0800711503100c080009415540c400300c21100e04ea0350301c524080000d08801c0c0c1d0b1520000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 775051250 1250 775050000 775050041
    0x106090207050613020d08030c19030219020f0c0103180f030e01120b091603020903100e071e1e0b030a0b0103150506270a030501020904060e0c030f060103 68
    0x11190090702049018000f6102140c0754071aa4411100e0000c00080d0444403140d80e0341c003c142660060340c0c0c05105e10001c6440d06400803201e000c5050080b944501007540802c001400030003071250f001e0301c80854002000537003188007055a0300c19600d061641007613119642c069480f406244c2090302180e100c40303d5000f9000b6454050140b40040300a140000d101803607003c240d01c020701800700c8604002d01040065116683c0c00341703901c41c605143c9030525800f00403214642c1c404100440200c3c12581c40040d4114040740454102401d40e40030140314034054400d0010070780404080811605403a840060005041100208100b22580130a62901000c400c00000e0301c06a04007003c046402d0340c0030016010020840c1c0b03070101440c01000c0e003000092000100001b41c2c1074480711942c814403110b098000c00400020901c014640003154565004240302c600340c2050f008131006800e28611007403031031030408013004a50000500d1a0341e40c047e403402294491b4020341c00450462284080041c1d1f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 775052500 1250 775051250 775051259
    0xa020304080f0d20191124040c170601140a0f06080604050601050a0c02010503040204060b0c0a0b090a17070201031119020c0f060301060f020304080a031d04060b041a0403050106 78
    0x20025000c0c1c007200c13a04804e91542d500300400b0100e403103030840ba5a4080556102e00d100700d03031013058030103407030311900c40d07901000b030780042507580303c0034480d030314450000300d46002d103440c02240404d0381c808900304002c0282503081c03078030102d182815141c00c0d10b0506141c001d400d00082142403207030f01910244074001000f01d43d00754000c5107940320300e00c2a107041c0901c0e120940115414071400903582c0c0000d4201181e00010340c0b085004540150004001159064481062007200d0744512115013403139100a0340307503003040220150264080408405801c0000e0b86803600300c00701c19100e04000300d4140c00a07400c01168000c0e80062482490012070545940c1000040b6102c411890f4102000d4031814a404c80e80c4c1c5802164500c801d1406000b960030341e464040140d40d070b039008450100550206003c0400c0d10101080030740d24450003981c41c4020644000c1415950a008058590195003071243c1404015484422101102c081000348241d05000c0b80010382c99000300d42006002c0d500340840080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 775053750 1250 775052500 775052527
    0xb0c011a0a0e100e0a0e0f2a040b0604060c03021b09060405071e0f1416060e0a05010905030a08011d0720030c06010e10080601050d0303020903160e0601170a020304080f 74
    0x4c40d00082c074011658184000a0600d0340c412224000000b080c142040c014494811a1954889840003800122b0a2611100011074982060b0001d200084001e815a41416230400c803201c041d22080c0d0a20b011080170102040b00210001c0540e40036507104c20100d40704030b120b440701003d1071142200e01e082c80c081519006090224481140001682d464168482501c41c8400c441d000001c440c001540c0c881c7c00d5544601500344040d214a95000300c00c901c0700411828013503031041502c031380055503841d0f01303024001e8045041a0080800c0c1882201e29002038000c019449070800081c0c204903a110801c1500300d800003001080c4200c1500001c1070f803000c454000202c0301d05807005a80c200c200d65617022000c08104110b441400420742c0020010002ca090100c01c005101c1d0007460054906022007020031700d07100d07140102550b11518444108044d01c80180c0b0746401860900c0e16040380c040066684410850207010512450360000128040010b00700848a4283c2d0440c6c1d002e4a6006400744031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 775055000 1250 775053750 775053761
    0x513020319050610210f0b0c0d0f05060d0308150a03080d05060105072a030803180c0907021e10060305060f101d060a050405010b0c011a0a0e100e0a 65
    0x110b07480d2040401040140c800c15503c01e0035140218040d040021002000f981c000404031415100070300b400c8502c502044007003034501e1141d0410301c00156101d940980103811640e1a1994114083c589803e10070f4960300d0340c0a56501300e415242c020025203070103908030f400313820355941c1703551021042c0000410803050201a295000e0b0103502003066546000042d9810703c103500b0001c10750700004540c00c5203145481c1c4040303529101c0c5c2035030380301141d200d6690584580c800d40f402d0400440d481d91510401c0000c0140d00545a401c0e51350103114103105101070340c7c44002290602446030414005140110200610f007681206000180101e079604e040440c0c03508400d85d425010702c00c0341c20001e4581c0510000840440d600e8000a11001d60303107a1843c0c0252a0140c401c0d030703010704010800182603503180520b038040e2941b04100d5569a45400160342100d110781c0d1114803000c00500c5250a554a20104130704840341800e0f074020544d25441c80341558201e0f030700008036402d844001d04c03c604400b030380300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 775056250 1250 775055000 775055003
    0x3150e070918260f07080405060d09020301240b0901050708070f021503090a081818060a050a2402031c140601050310090c02030d020c0105061903080d0513020319 71
    0x80d000f600030403804600c140180c20a21004000c020024101144081001032410320702500b481400c0136101d06c0024865804074440007641c585481204081d8682803040082d66601e4401000c003806040150b500000850b1045d600020700100b14910541d000f0012114801e51006056654000c5841e1400060a031402c080c0d0160341a214581c0d0402d0f05403044a000d05064070080c03500c4802a0707940c040319441140000080c9101c00e0040159440390040c0030b0005640f03c0095002d442d0081c144444520b265018034441c50715240d080240c7c01c0340c151900d2591780b520400158440c01c884042e403441c41600c0c8001c41d140d920120144070100d0369404041e00c4c42900c0d88007030341519280c00440b158081940c6450322203a1310300041200c6141c1c0d6102d000041c00500550b414980c5813004030003203821098250450765142c00404c4501e01d41102c0005408070100b4282006504640791001d0601502d1000d00926035100702048040240126a002541e40203003110480b0f281e4200014a4004c0d8440 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 775057500 1250 775056250 775056263
    0xc020d0c090c090b0304080a1707020105190c140711130204180b06031f12030801050f060a1b0c0909050d0314060330031008070f03150e070918 63
    0x20000e4030342e00c541260f6046a20b0f0440e06811511076440d10350b00c070f9110390310003000d0142403910241c10700404000c0c98466a1541c00000302840d04400f03142c0411118400d0111091034468a4a54030313811841e02d4100c12190816192510250301d41400010200009150f000303108014202e50000180c0080c015a45046100d05a40d051600c4101c01d40d066100c4c10780d0b1080301880042d43e004010004200e44102c089460100c150380c41000c401c408070b841c181500040c50340001400b05092441c42c00d100c400091b00c145180c5640c0c0c4500400032608408a1003000c01d601920900f1322007a1400b130b07400b43c5030500c020445c8402d1480d0241d55039026420300300c0801d003081a8140a4030344210210300c10f82c0b000e4040d00704903012040700f680305018041a43d20240d0704100e5105120a100301440c0b20b0001000c40200882c200300e02c40b1b240561540c07140704000c000007030510015080a13042d071900340c60602c000c80d84200440c001c50502e02c0381d4000e00e40c0c01d403070918428491010080c440203840d010700b1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 775058750 1250 775057500 775057511
    0x10e0f1023130311070b16030221090108060d0b040308090718020304050c0d05100207150e0c1c0309140d151d0a0503040e0915011202040c08060306060609010c020d0c09 74
    0x80855031200283c1c8100142030078107100887c2841c0d1144200602d05100e07206542010b04203003180c2006001c490701c240300440000c18402510b581000b003d542042d4200e030003002e4a143e981d01c003890203d00910050800c07141001003242d1060030059140a8041102042001c0c0240081d40d80290002c80b000c2c5d40f18414500c116907103060000c03071001000e800c030000e00035040c5540d2004002c2d5100c05800c8500401c2c1c01c0564401d80f290340309040009c020000a80001e1081d6000c00540c0c3e08110321024101804c0d01161001030b80084400040f130b011000200f444030300c01400200c040e444081c01030003c6075a00007004005025a0184619940251078010410890440c5503603c80c01110b00401d264420082400915007850125500860202c2200e0070f0b0b03d080300f4840c0d104042a40441594101082e8200442c03619000d00c0b01d00d4900b92500c21005d14140740001d58500015098501502c00000c0012450744140045051f440c1c002d040e044080c4818a0301608489251080c81042e52808 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 775060000 1250 775058750 775058777
    0x3080105060a1e170a0e07270b0a0503100b1905090c0d0204081516030507080601080c0d02181003020702010507080904200903010e0f10231303 63
    0x207019541c9035103466550519034038001904807100c882414504060210300180d800325081a08030b07007031040b1818030010480c0c07010031030780754036003002508039100e06c1c98180e01000d02806035911403e0501c04184010414807000804180c1200310303604501d0f05801440000201a4020380045074055000d860f40d2400c24034040003000801c10744c2c0642c95002402c50f0116041483d070602401d410503503000014500750b65050342528010b0415080412801214100035000380b550740c8400700007416040c140401c0c50200300c002c11645004001c541030007140804680030703001c540180d50217202c2040c0c08541d10070b1285003a04480c0b2070210000d1113009860100c00f0030764880c1c000c0c1d5034015130603128a41030511a40d02c40280d5000006165001580e403542824070040c2c07003076001684460388800c10356440c2c2081c20306003550303045504410036038400b211070030807040b0018001d00c06001188000a149101502100b81c0d0402ca41f07503075451411000c248040401045140c1480c94401c1d11088502482c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 775061250 1250 775060000 775060009
    0x21c0905030307030825020d08010e040c051212160c0506041406030a020d0204141c03080718050d11030607030c0503070e0d0b0c0301050a05030c030c0d21080403080105 74
    0x16000d29070301a0010301c00000024051310310a900003080c42071022024450004440070860084040b4006a06c100c40c10202c803900950118090100080b07000d03090b14254603000c1c09a5568420180520207180d00d043d8040310034041c0001c0200ba00d01829a20032803804424185481400141d82c10041d0490002c2c3d6450000700300d404841c1910258002d025000007000002d810042c40d9242c0103408104030b0701c41d09481c0c40148040d100b04001d0440b000d00d0141400710070100032040301c1ca90f480b1a070710b03080825044640154400c5045c6000783c07064048005100e9014803d41c08076030440c8003c4400c0c0c0c10080e690040c0482e4440c16002ca9055585010007101032720104900300c0e02003481003010805c5140300701c00310700d0070340d0001c0d00c10b11040045543d034007005035048804110014020005001501e000c0e031400e00284003c900a082c411000c00c00241c9601d4030b0b0713156a1080c1407915816040003000220a9404a07038404100c060b441020009011228210740c100d0000300188008505441e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 775062500 1250 775061250 775061267
    0x9021e070b0117030f030708010f2c1003060f0b0306060315040813031b031e030504050906150304060525050d0e12300c070b040602070b0403021c 64
    0x10081074000340e59290007250101c1031942c3c3d009501c280001c000000d000040c040045025840300d6076580281d43c5080ca800403c02009d41151070b8071040340c0e400a01107040303407040700b0110031031800381c186546541c000d001c00342c9400d0b0b0000b002c40d800c181840805041540c4085c80481055081e95540c0d6a110205031b1100030403c43c8030301c0500c09901042c0400c03c03c00203000c02d03031499072030319208036183d8444a08030040402c00300d00381c180e0f00e8001d1080080001d25400c0c2c00c4005041e1340820040e42c0e070007400e0ba0040e800361038082c2d4408000a1740c0c0d952038080b490b5500400200403a542c0c10a0f040050162400721340402e400c07020f11a50400134903130b41d1000c0e51001ea81da5a05418903014080140251045121107100c0340304455000d0140071b017460083c580d89802d0701410302200c1d140080b031001c800c0040700d400c000c503c0700b20400c81c507005030104440d1143d43c8418a02c4107a96907207007040081c0a100f00140c000300549003044209600080c0b10800e07003c408001c0303a090500c00b00229070120 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 775063750 1250 775062500 775062503
    0x910050918030904050112030f0f050a08042d110307031203050601020c03010c200607021e07150c140c060a0c060b0303070c170102160f1b09021e07 65
    0x85030000680c0e100007180c900002084040280da140038405800601522407e0b0403440c21183c00c41120000c00d078004401e03c15803201d83c18002d01c8110f07124000b922070302030080030b4414085440006010088001c3c0b1400040c9500307107112410400c2004104a1a012154201c480c1703517106900040d240381c001100c000f226803194600312820326120040340078181c0070f4446410740c401c0c141c8900d91940d0a0088121407207a607074030700320040c1c0c00601a102c008075001c1f092540d40c0142c000c0c0706003294003080e41c50a0841c1c4038074100c036444084504e2843c10805500110f0000c0c003003a0b83c0e1440541c82801d0000c1d05004249203031000350401d454035100e0782c1c0c05400300c0d4040010840e041c1d42ca4007403030081940c10300a05002842040c0140032a05661040c00101c0e41c0da01c04040a01409030341c02017070ba8140722281d008505010a2107110580e00040000191141c0490be21620401c01000d064401c094440c21400d005a039480036064045d41010000c40b6003040e0b6100d50a03e5104903905949805 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 775065000 1250 775063750 775063759
    0x810060302031c180305420603030c0106090b1201050906190612080706150b121012030e0307120b16030b03060907050406051203030a0507050d0e0309091005 69
    0x42c1e201c8aa000b84690403079801505100d0580014101d880c0701d0400c2d03400860060000e00460f515026881114111f07001030002c40d200204400351004611444a600c10b80b180b07500c1c9406a00c900c0300181c40c42c0688102000150708106001c600c3c018240c0000c00c0411058601e07408210010a202d426070704204c40402031541700300b000482d051020000c2d03030b8488005030f2000404075140d055851001400600c140c03416032000446804016451140600b52a01480d0600c8018100b251695452103066869400403460070b010408802044445800030005005032440070412413030041e024010012085209001380a00003034078400a0400c04400c41e4010301c880819920101c1100380000c0c92400304c1c04240c4d03541480c2065072801c11095018140c2c80e0020092030b4030302020801501c0d050340210380920303440c1c60030101400000040d00e0b041901c144000c291980c58801c1200e181c00b07548000700285007091200080e078900800200190705082c1d6040d10103603240c0d140130045c40c40510030076802 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 775066250 1250 775065000 775065013
    0x90312031503070609141509060406020a0c0b0301080d050c010b04051306111305041104050d200409030e0d110901170c06070201020d0c0512032401020c0a05040b240301081006030203 80
    0x241d2404180d1f0540c9244061425820f200b01140880c40342d402c544c0083e40980d2010180b0ba0500c102c880703281c0001d1841800080c695818600310035190b80d10880d041052003800305001000345802c4d0040005880003900c100308615001d403194494a24050080d104a450035001054448083d821a000581c1c840f91a141c50741c64103080c4002007810084080c028002484045416918100800c039094043c1880f64900c18503a4400000700001d000c07d94030582c07420049000198000ca80010805012111305810310128200003a000203580c06242d4081c1141002240f150072018005a51040150403145421441010f100040c481d9482c0039002d0782c40010781e444440d10440d5002d2040f072013101581c01d03150300303601c404c1c1143d041034503003000403803000001c24503000900c144089411b40134402800c0903000000070400c90840d84c05058000c0d40c48004822080d101c0c00000602d980880d81c85024481218884038010341082c010804207010304105070030040c400f80145001d4030f400034083d140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 775067500 1250 775066250 775066289
    0x6030f1b01020f01050112171312050102120906150301090b062e050a030c030b09061e13021810020304260f0a05061305060408090312031503070609 65
    0x4a4900c04820704501ca880400c2041d4182030149900801a2460924244000b03190a0701060055200c44282d082c040c0005106825002c5d50b07107003100c42864180000300c2603030424902a01c9881030107600300c40c441d01849641c0d540051014810b40e1560184400219804d00309401c2c1e54030007074094001407035000842c44614015412101c8045180104071081d0b411004401003801c1080400010444c0400c03140c45094060107460304003019481c04012122400380007440711400a030440e4015804c0640c1108000722510500e0742044000309280011034004140402940c0b01e02a8501c0454800226108a041c8910a20300e40b180980107907041a00381b04160030381ca12a034100e440d045a5100405480e44000c3c008085101905030107000c1d01c0d5000c0c2412441d02e0005881003107030408810300100405c5000c102d82c0c0d00241e200d00da0702c0d502d0a044000a1a01140140c0c04071801400000d01034020030012040007103020030790031344820300d94888040c0c0c0d85000500c9048000d00c040c111140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 775068750 1250 775067500 775067533
    0x20f0909071803031107060305010e13050c0d06050901060e1608040203070b0408010c140a0e120c2206060c020604030b0402191503061e0e220809010806030f 69
    0x40e8000c00034503200007160480c4441103941100c6503c15008103642c80b1032070810180038003050b0042d1010782070910465141408941c000c04000302018600145d4440340000c1240a0007065240c2c0070040050403a0240d80c00d00000914054406503c150300e0300400040e441182d1002c64411007034080350500d860008030782650000030003441268540583e00c0c0c0850340149080240c00900400400028000090307500508441441890088482e205100c0440d90310fa110340d00c0c02c0c94940c10f070f801c500c60442101e600342c90000c4070b04400f81d02c0076481601c2264044040580d000712444000d090203600d548a40650350344541c040b0283d00884e0400007031012401610640d6003051001c1c02980144216101c0000c14448513002482c1c4680fa0304064542c4a525000d00406805184407844502d03100c0601700045003650302c1251242c0302c2490000d0082c0c0004004160056120000c0c4a0000b40c03c0c6000c10b4142c0c4090000d60204500c8008201caa041c0041c9001e0300c1c010501c000e00003646006540c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 775070000 1250 775068750 775068769
    0x9030503040b0a02070507060509090702120a030213050a120b0f040f0809010e1207060207050a051305060d0804060305070f110a030503180a14150405030d0f0609020307020a0b0901020f09 82
    0x443c0d10b4082100d00300042e01044004001c010079610703030751a0f100c13000801150000140c0480d0455000040040640319203004445c10301c4a142001a55006c91000044c02e00b0401c0d0301481e0300c041c4040000441d0b5403c2504d101da55807042c0811b030f12070358032020149a07502c400e0b500680031707105915041c2c00050700b0340001e01d00c0040505152001400d80740c0080c7e4510800d001a42071500102d4040040b5501006031501038503048400c04c40c21810b01c00404c03c07012600000300780c0c2030703100e0b03000c9007058a480001181060f00400209d50300d9444020250140c6816078100f000644003016001d030940c8a0301c1c8102100c08880040c11001d1003d807000c0f142c036080a0010644a00c0408050b180800104105000349100e407685d0064440c0461501d030510070703040022064064550308010001d80048216124007101007400a2503c803a890824010000b542011403518400001e12444079000140b0358a61441044980800da41b03111849082c1c3c0a20403041000c400c051044045c94a04070101 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 775071250 1250 775070000 775070011
    0x130b04090f0b103c0305030328020702090c0904060f0906030c090203131106130f1a090105160c2c060a0510080a020c0105011701050a181203090803190b030109030503040b 75
    0x204d00510313440391162403d646c02030390101d4042203140c21403503940e0615254a41e04200440046003031103159004911800780c014900c0908100c002204003050740c880e40100013800900b240b6034410b54650701440001c00030347c00706490081150a000401d00070074000c50744141141075122036000c525030b485d4103207100c0c3c0d1202c9590081c802c3c400b4403140c59907040b1500003800c40d6045043c5091404000303104100d10100d028201131401c01c00302060740d1b007040440b903282c22a107510603284810f9040a45a940e01c1e50444002d08280a419a102d68050124030084018034440800c10303441da40100700ba00c100503c00c594025149842e4006410b0044640a9110258600151500c0301d804052800c50b0000d070841580300401104501c1e010200340f041561101e10302d1002c00107205c81b070b101c0305d007034078020440206400c01d100400411503100750003210f0764943c45950039440c3d041c10008100700892a9010303440032480c1000c50941850705000b00d120303954042e200c2c00d15544454860089440d0020030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 775072500 1250 775071250 775071359
    0x11803030f0f05130c0816150504090c090816030506070f0509030102040303030e0613050601050405180709050612030712081b2205030a02130b04090f0b10 68
    0xb00c9180c282c0706010f0309110340308080f00d07001c00c0f404c91324240d440300881d60000f861503031010f1880140400700c06110307800c3e034150850092440d4900e1104540c64820b54014680b4981031180000c8190b801812900a6a0ba0b950a403028091a6003002010204500c00900340fa07221502013000a40180b009035000e034814a0013034034085564000c6408d90b0300c07982c0220002a0758041c08130030700405024582d00f142d6000208501702e034003a10340303995610041c0116445241e856011038070031030104040800f2148107102303540175250b8444020004047c112000d03806202660303220780d1601404402c56004560002a0004400010380102c544000091107070b81d40c0354051880c051200280c2d005000245000003a0b030307c4608511003104585402903114034040d9000c1401d980041e52650703121402ca104e00c5a0000e1030a08110004000e05641c0310301400e0640000f00a00520000d0300c5424841c0040c2c547c207a09040d5148540d541c2d999160f031319514007010070301d103544002001d0503451110700340303005 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 775073750 1250 775072500 775072511
    0xf080f0a0b09011401180c05031005011202160b010611030c030412030512010311040b1c020906041107050705041104230604150503040c171b060408010c050a0809011803030f 76
    0x861507107801307003a00403e4560807490091006408540902d1840181c03e00e803107411804c0030194182980050300a4505000d1680c040e13803c20f840c40c0e4140c540b44204400180c180c0b00c90f6043c6255010800c0c040c0800052020001c010321000000440b0220480100154a0305141100c0310307201a0b220b001c2102003113000c009050080c1c2c50a10a81d02860240035810869129841001300b12606c000009000340c00030609040b29007034542d650782015030141c404a025a0300e200024006003058240305450080200d055010302c0000100d00f4280c0d5410b440401c03221810010203203840c000e034070440c103100c0e06c44960000c01d110819a080704880003d070a80d803d068994a544004004410a40000803408801c00c010300003810401d400070520a0501c507602600030b4081074a921600c441c41c3d072140315200c94440c1984564013110014000d4000810001700c0c0300000505682c040c1803180006010400421249038041c41850025a040d003110041c600481e90f090307018040300c6d400b840c0c15a5440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 775075000 1250 775073750 775073771
    0x14011413030f051e2e11160b06120c061e0d0522051e0a0804080a0b0109110711011e0e030d030e0601050d14070303090f080f0a0b0901 59
    0x10107540015600c02d0020700002c80808220134460b00c1c42c5244190940e02442070001104210348094442d1940124072072209800b005451000e0490007110300d4861200103260452181c005c0c10043c0020721943c0002415250344003084140c03d041c400711203c0780c2014243c1c1ca01c3d40750a200800c9446055560312680041c1d0625010340741e00025003070700600d0b840e58204072000403d03119441c02640c6080740d00c9007400036900c4407542e4840c8014417401d000c40350710000011042c108807150308aa4060440ea40d1281c603486115250f4114400855101801d1030000c00d024007540140180b0303d141d00a61418003019454006810b01504a1981448450301c1441095030000310320807000ca004d074030b800d24140500400e141c6486c00c200c240b0300426144c82c3c82025841707404180f03035044500c216a50703135043e0118140302c1c3c03011010441100c0c080c420380c42c00004041d007000007034040302c4045001d0104195200c5155469204401402009400403039040000440703a500150b0802c1c0c0400001403840c0c2c00 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 775076250 1250 775075000 775075013
    0x306050109090b06100207140609040f06050f060c0c0f0103180b06010807020705010c0b04020a080613060f090510051510080f1608070507030e06180a1401141303 71
    0xe0304001e412540300c0c06054140704084030342c11380001c0107403650b40080f000424000c0d100c00180c0075542e10010480c5441c20b496642d04291400d0140041c0200009035179a00d001d8020079042c843c0324027410030344581c004245086000e49018404100241c00001c5161040150b0203000c3d0344490b0506035a984e01c0c41002190480c0c10384103511a000c00d04c500e041150000d0900d60004100c0021075000100034041640c0c041c20b03108d14241d200026410030344484c80003a4584400d50403100d102c0c42000308003e040d07403484242c0d400b01c0b4080c0360100415204c1e01595804e59414900c060103913480000c144004411315406968400720101c1501b140622032000111040b4090b81c02d000003c4002040c040941107143c509600188045103122004400300005003440c00000c00c060203101000c503003502418061500450091802031102e55503210070f00008040f4115501d500b4050504100c2c045079040b0301102603040b40ca07050315402901004c44007482c59580c456000581e0300b1a5141c00000002d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 775077500 1250 775076250 775076261
    0x2030d0c03020a020c15040303030b03010b03031201030311030f040501110708190b0105040203070905062d22050a05060702040b04110318061608181006150201061d060a0306 76
    0x20681c0c1c0580d5883d5000b038020310b448145582c0350305c19a0804500400342c9049000c039011640c2c541408580d03a07000300e001074014031240f0441ea42602000425803036454190020f00c0c10703a4460f8460b00d4060000d0070b80581c5c1d90069008840d00440100400d200c0c560203000d08008440040080b24181900e038070201d810104180c02021958030340e0441401007069107036540340503000c151421820f514081c1d6005008003060712520303000da14002080c1c40c0e0203c684015000c1c588012070200b466034445103030741035142c1c00b0078043d00750700f4122000c96100d0002c00014000700e400080922030301c0307400d05081103419400694100d074420703650310075840284c40c0d5020b0380078914107d801c200e48a01d000c00c1c200703468540180103010b10f41c2001d01048104001100d44001450701c6107092589561340380040401101c82c03074840e5a8501c20310081c521011030540156007603070f0841004108004441ea4181d00380c8082d07025503c0d24a0348401c5000d0f2154085015682c02900140350400c42c41e52a22201c2c203d54 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 775078750 1250 775077500 775077521
    0x905010b01031109030304030f03140a080a0b0910050909070f0e0a061203081f120b1609060c120201060b040b1201050d020d060e0f0d091e05060301090c02030d 70
    0x9468021503103440d0303010710490002e54000c101c000c2c40c00441000081d00c910950200411410420143c582414400c082c1d009800f1812070740e80380d41c6e85500c2006001080221520000309003801c1c403003100707828501c5d12035000c0c00d03003110700c510400d040c14108542a4402054000c85101d2554000b800559501d40d4074020019040d0303907206410004034032010b4039401d0700649040c00c80b10000c403000a51044603607502c0500501d541aa503100f065034400d821040f5400010000c0072402100c050141d0442c03514013541150100200709403440d0000d440000461141c200402c400780301120110340c940400000c0c02005100001e090303902ca800c075001982082d00300026200c00800d2005107400d43c0740300a8054601159101e011074034560000f440381d4601c078801401c40c0e071144500c200c0c0d00b0080101c05d2156a540e820340d24005442c2d10028907e03011485600c048080030043c203840c000b8200085010354030b0140080e4a1340c1e0030f143c0864050450506403004510042080010241c01d41c864401440b = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 775080000 1250 775078750 775078753
    0xf180616111008040812100905090c130e12090d0b010b07050d02011b20190b15010e0904050a0f030503010311010905010e0f03191103060108060f1302130905 69
    0x4880300c070500000401001a100900c9400350610020502078026110108030741c00e0b83c0d2000d644c41c442d854000c03280551090720040d09060610003004400f003200d104400041c0c2e407001120809018a10036694003460142164100041d1a445145100000c3c2200c0b040500040880c4055541d44662503a09078003880f00b000c40403c11100708007041c000385034140100d20080c4146d29000b0284480040680390b450144007400c032000d150300d80d545040d40410f02201d000c0d1a0307001600101c0d803c0d815070f00803044814100200018000e070f01c119503e2102207206075035640c09005500281b11041c0005441030b120b6102e0454403400284c08100bd0414951295958075100d524514002c45040c00350302e082818070070aa0750612103640d00640440250008640c9811046030f0500403a052245002801043c40034607098070f024031000c9120f9541c008019800c81e4100e0303913240b00d50342d1900c0b01030307c54035a000585030200b03e0009008002c100842e0000344440c904c0101c3d160043d00b221603070107003110340c0d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 775081250 1250 775080000 775080023
    0x50f0c0a1703160c020d061d010c050f041703070c03050a020f09090a081c020708040e01060c030e040c1b200f0d08030916080303090705060f180616 65
    0x1003180d000c101009140d80410003504604054400400e280c4403200c4890420072200b41050075950b8401b0b0181c10f0a412250800218601500f821280c80e2890303501c0c4055821311a013612140d1065048590280c1200701c01420715040100b0345908108500519802d8402800304d4804283c840158400852040000740481c3d00c043c4103000448150013142c0e480ba00c0514200400b0500108030101d607070340d125442d1544c40e500c02d896003161407901c2d11307000c26440c8045881c0003009002030040094aa90310a460b4060b070fa2003e040364080c507203030001070001c1c070800c2d11910076090036085560805500d003440c000b50349030b150b0080d881e0014480181e441041003101d03900c1481e828007007050b036030344107554219a0424013400720b60b9600400a00602003440080002c041e5101801300c1070b00130580d0079810a4143d0b55580c019502d400a41c3e00c12414012820002164a800c2e8100d5420203c0210400e0030020115400c012885d44d600340d694000000308440c41c00d83c4103600c2400c0703e65101d40e44002c036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 775082500 1250 775081250 775081253
    0x40207140f16170a02010f2c130506130c030b040507180801020a0212030901060f0e0f010e010302010c060519050112030809030c190c1d150f0a060f050f0c0a 69
    0x20200d041d444010040c25180c4441c5890700041395022080340c080c03d110b84c81d4040d5072030449040391200f400b40a200c02403a02e0110f4107001140c4148072101c11075031040e000648020440844d54103651b510f611461219034100482d01540107035094070b441d41000960b07412498045800c3e26801c40d680d0000940d481d81c400c13109807000e5131407005014542d00841c1000c220201c06076132400c0b0842c5150710068040006500d8070025004030f0098861080d038151050f60b5a8003400b400c402c2510803105640302314002041044030260020b04036a0140e64501d440c4186488a034018400501482401202141188100003813801601e00910b841d6003c190302e034117142001000c3c1d400140940c0165041000301705d40301031000640e01075100071000c1c200c07807007081440d1a2150ad1116480140301c2c0003840035000d140c0803460300e0380b48502d241011b00c00650444800308180c400d40d03600d4695001d06004418001d80d80708840c14055404e090030283d14040013418a0481ca80040d9a0102a0740c8101039460 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 775083750 1250 775082500 775082533
    0x140910140f310b04210212011e1a0d1509050c040c0507081e040e070201060f050303091011011811010207050d0803151c06090b24040207140f 62
    0x1a941090194035020320708007a62240a44182c0c8200d024500445c41050031070310140b00034000c8154000c003010114400c405601d40a00024a145044422354011035582540640030b05108000d0740c101c1c034105140c214003003025124401c00300380c0d10014110f4603072209203002d2081c5c4100b540648024541286910100710903980c8035880601003020511501340094a000c0c00d0700c10860300c4140f540207030150610b6515050055a00c1040c00700503840038080e074180c0642c02401a150190303440783c0391580f140e05241c0d0b40d04c1aa10010b400401800f55950003520540c0718140b1000c07103000111300380e118051100ca0a0641d92000d9600106a0301284019038040003040300800c0309846002d40d20200340c54100d2075000c014090000303154040c00b20481541d07800359940c0c5040d100f082c0785100e05140d080c21030040410035011609201c01c0001704100716140d810501c8032260441116100e0004a001e01001e5004401c0444050014842c4808070410070301010345859036410080c03030899650602032 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 775085000 1250 775083750 775083817
    0x130503010509061b0f0d0c1b0b040c050d02030c0f01200708010510080703030e0402040f0e0a0b01180303030b2e09090207031d15041203140910140f 65
    0x11144c1e40403c0102022030004098510075070007090300142403440c210040e13075441010040542089002e050205c10044000c000074062030283d80380c2c940180d220401e000b861020301002944c554007458501c9071900e005d4550024040043c034210829840502d56540c003100740380700b21070f21504104c81c18805c0f44000d1191641c080002c441d400040f40c9804081901ca0602d404082c0c10024030506004464a654040300c2c0140700c2019480002c0d5558038404120b0002544e0008029003010010111984039041d4a500384500702aa000403078610750b010b82c02840c1c05103079283c0001450290301e148840d07041000302e1241081006480b4126508802030050710a030b0404080c162050281d40c0101e035000304031303141180a030529030b44207d9040c0000703640c400014141c0b1908590008010612000c0e04140340b000a00c20345441520341d0b440e4890703034818010019402d03001072504642a941601c1510106d00e5441207000b501e00e0000c6284032000a540681d9a410301688456000341e8405200e2181 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 775086250 1250 775085000 775085041
    0x1060e07050c3708090d030906081b040510031b0503101703120c09040c020c1e1302030c070804030b07080f04110105030c1b01050106031d0304090213050301050906 72
    0x3505084004140000041c0710783e20356121040750a601d650013001880b40c11101101c0b00180003803007601083c5002405000240240c6000a102c880401c5d00c0c4003140b00000c1e04030841418050606051105000c00f070307014407500308101602d0711996000207002c02128584805ca035502d0950b24078100b604001140f00c00c1c0d009981043d0345203400e076060308000c4242d80b20104099100f1105490305da0f8000d6441c0507001407194098030700b82c00c100b1016000154061403140507100c0000344100000c4603226044004800c0c0c0d0001148242044000000c0d0b0085a001c8031038280c0c40e081c1a1652108106904503401c112a440c000106100741c440d008a52103900410440010340705151994030440e40c881f4500246040c04030200120385810803100230b444231844c480100e00c2035002403004580c0604001e11404010038070b401c41e1002448951105250b00880c50802549080d1400c0c040710025405040303525001111440045426a0280107484c002c0c2020302c010215400c02c0c510001d0710009240c00c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 775087500 1250 775086250 775086283
    0xc05040c0906020606011b0b070305040c0506090d1707140705090c0708071103100e010204180b1804060f0c080406050705040f0e0a0603170a1803020d02040e01060e07050c 75
    0x810410303107500241309a807148003803a290010000b62000240d0b1003a070000014807601c100001c1002d8140e241d404107110358080c4001c002425655401c0c050b59201e94440150030200d690300220104d43d609035003218150301c00d00c40c5880e00800340c4035980390f24a136240200c030a0700540802c1242e440d04250b066004442c2d01220740c03030b0540c00e07514a0b0803882a944010300040e03003000004101d54083c00007145917054640c051101d244a000c241d8000e502c14020021003201c802e034811203007442846800324880003d8803003140c446007034828a2000c0c42c002d00840d61107842d50040009009107003d41c00180f40300b9195842d003801c0515181c0f0585900411a80030000240020030175000c82d00d60400495002105500c02c44d112003000c0c1c805029190009400c4002d0306040d16401a00100100020402562408225054000c1c02460600e10b031101940c0141344e4144100585041c0c0c0c8400c6d400d01d079600001400550720104032108150407501140405d50204524140041c240407481c50f01660f0724 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 775088750 1250 775087500 775087517
    0x803040f0b090a12020112020a02010e0111191b020414010509130206030a0b030a1407050108010b0f0a050a031b020705121501030803040212011b03110a020a1704090501030c05040c 79
    0x2030100703c04107150320649040c03030141d00c101001d59016580c02c101042c20050155511101540040c0c041d045090a17042c0c01e42c40c0034512a01f2031040d00035034120801042c481d41e164000003078201d4420400044043d222280031049400607607452054000d40012000e03c640c0941c540800c00c44400001070103041c19418021803000140c2d60402200d5115043c03101c00698508084007292805013948401400703001542d00400d49100000364640403518240d0f03030312205030b0301d0b01c072910518003031b80714000d002c02c4090040c1704080b03004038060a04c403c550301c1c00190071021f0f03030002c03002082e54180c2e40c80540c001d18000c0c041c60501c0701840104180c41d0f0000c05200054682d60480d2410500c80a0800d00340800070134110754807078802c443d43c010108000d0140e880038452450000301c03481d0345030010034541a0500c80880c06c1d0030995100303100701d801501c44c00c0215212040c1d51511103245525105003000007082e0906148102c901860082074075440e1a4102424002102c0400d401e20060040d82d0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 775090000 1250 775088750 775088767
    0xb0a020a2d0e1e010f02010603080d141308040501032d0c0816080f060103090c03211d151e0d0b0f0604061b060207030210060e070c02040e1002040803040f0b 69
    0x1003c02241c0e81801e10f8810085003e2407001c90040c07501d07410051a90070002032042c038945103900101c00d140507040c000e1400e529111901d50349001e08140061100307000b800208119130181d8000c0308840c1c100340100400190341c3c807035101d04240c13005051901684d1080c101065951000340150b001402c04940b10720666042c501a02c00e401c02880c01400d11405e1001684a92083d04a00c0b0b841d80d00148144d12192245001d0036644501c52041c0100380302d804c0c034000090b219808142000500c188114001c84d1103005014031840944514980c1c400b04100e03281d984012174040240700c0300030004a903119410005c040081d40d403064500c070f20456007034003444402c0d52842c048904660090030000811031001120200101d040c40c400f800c0c240c0f0100d82c0e0014507801080c1c0c00440b00f9684001c0140710f45852a820011405440c40030004600c68481c90040c01c09a100e0a228000201200c0051100241110982e0b00c82d41000b11281c001040070005000d4001010000d040c00c00c440f01d003414500c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 775091250 1250 775090000 775090039
    0x3030e070b0f030c130305030712210b03010902060d06080c03150117100603060203071e0801090e1507050406021e030304030e04020d11040816030b0a020a2d0e 70
    0x800c090000140b10000109560030088403c907034982e100c0180034100c0e15501e04009841c0d4202c21001d031540c05410b40726200307a0784140d499070464130505805040300c1060341c40800040000100f001d81641d0307195158000342e134840700a40340300c480c40c07200865058141b603501410100540345160180d8042d091244d144050030038202d05450380015101e1510ba1001c000900c0c0c11440c01c007201c1c1c41803034208080140245074006510070412a00e0703120145148035855041480c901e00c1160006212400501c40c0d0405600140040310814080703c1030301e02a001444480c03003094a00c5130215000080c100400d94042c010780c2070342c9004000c2c42c0d501d4903022000070346a110050000301001050710b2103101564459040d00e412615982c1c04001f44140c40c1c1c181042503111780100c1c180ca200b03082003105035011207941c00c4142da42c003000500c1103172162503109029410900060003070217440038907815403544008010304521003906030b03603810b1000000040c0040941075541c900658104000a041a06 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 775092500 1250 775091250 775091257
    0xb03090f0c0d060b0112050a0c080108211318020414060301060206011e0b030708070e19050402031512030d051005010203160302010617070503010c0c0b130c0e04060903030e070b 78
    0x100b21102256640138100102c0d011904c040d000d414403440d0409004601c0c0c035a60004c00045810740710610180d032182002c60760781d0041940b145c8085e0115410348040107400001e00034813400c0700009a00780380c1780c2140d461610705543c1841c1980d54045403c020303c21560504214001c1306075081890b5506001c0006d481c2c4805000f00f80107480440700010035840c111005200401c010146d681e01c9040042e80244180801d4846400040c0c2107010703d01e4900d08040d1080c07071140b10104841d22180f904091001a4200400c8040b00c1d152140da0f0071b07410b0702c81410b0001030120060141d9030340e10203580e80008852014200e001c3c000082c800a02c0141d0300041283c0010411595089210903540b504038050b26098010080040e0500c0c401d20000b10009a50029204c040b0000d11480d507940a080394680460034024050120010100b05284a42004484031a005042c5064503e484803031101100500340c44c22036100e5a02c0e80758505141e818410a43c903440da84015000480c50051800708070f01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 775093750 1250 775092500 775092503
    0x50a05060f03190203090c0f030d05040e04050c03250b04120201032a0e12010b0a4a28180b04031e02070609090504030302070c0b03090f0c0d 62
    0x40c00201007128007a143c41d404002c10f402000c1955645410380030b0b641c45640c801c981c0c9004090400814800740380c081021002c0880540d991400d0a207032403680002c1d048050010b403050300440354660070740d0701c05003d080c030002c0d88c2002c66001d030440208508201041941b00c40480c00e003c4c0814881c807590b0a81c01d0380c0107502441d01094001c24650800440d002603072241202c00358031103c001d2000d801003111200031004841100d0689905200c2c0d500340c400e001001c0e540280d15030810b01400619141071117500390928984040a9210300b482a5601c90308448e000e010001d80000f00c80c20140400e201e6800074403641d18403050400a07425010008110620080c0d540e1107490b0001e1070100e2120303004102c2d400c01241340040c149400c0180c840400003000c0c148a40108a900503003d00000d1800c0880f02c4540d170b42c0561301e141000c010020030001e002142050303000c0024001055514140300090810100d203241c3c2e0f8180128403c0c640004c0c50140b500542080e040130000d075032680d11380032106 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 775095000 1250 775093750 775093777
    0x8100e060c0a020606040902130603120e0102031821070905040c08031602120a02031509010e0a081e0d020a020708060a090b040b250903021005070b042411030a0501050a0506 76
    0x7c292034400100d6280c2405840500e040c0b810308004144091103c07464082c80302ca0b141c4440750a8094012600d0788244403c0c08142c8001c60700700c1a46040c4000d5281003a40031155070700d822015100c2079814503c2a0b880b0a07080c540310300c103000511482004079402001c0c0817009518285401c01c00b0040c2304451100070b48900c91204219140035000c3c011820741a034001d040d1030070007030b080c00101608241580c05441c15841c22943d2819001c000412158442c0c2181e405800c0000010901c00100c40c0707805c200440134401d10540e120844e4500160a640c0c00310b4000d0404641042075462500c038001700742c651124105030400e004600f41c490141d41094001280e144aa41c5030014000340301c2a080107003d030307a00b80307103805841c16910030190415030740300303ca202e01142418541110940600c143c05401140d0301ca0100380044c02c2c0e84400841d54401c00c0851489021202000c000c03504040b22039018003000104000e1200b0386407052a004d40822149100003908084c0414940d00441e400259007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 775096250 1250 775095000 775095011
    0x80a0e03040801020a0c06051503031b01060f03080a3009170a21060b09040c0903080d0e07080a1a04030306050915010806220c0908100e060c0a02060604 67
    0x1642050040300c0207000d1801c000c2d035541d0340080005101030241c0400743c40841c80c02d004031b5429503c100307a13400e200e18024000c508240c1030f004442d2800c1c00b8451842038540d40c440e000508001c00e044518000c5000380c42c416203c046814000c0c14104040381d8040e0384803105d00c2201d60900c00c00c6032816400d211000c002640142d14a420300c3c802c08071280c0303c000e5150100d500b000041e8000801154161200180d1030800b022a02c40e10503a00d441c040d40a4200f002e00c4002054101a0b004d2a1045a24a0038442c11956921400000d51000c43d000c140d0548811184000e41c00c10801c0341c00920380600240f0210500e42c88013114950700405000390741c1212030100307041c50f1181c1c000001a01c8000c00166060030400a07900d4802c4c0904d05440c041040480020018900300e902008200300300006000e0404403010030b40c0c01480000c1c103090510441d5130f40481e0140f030800038038100b040700a900040031880c10b03000620701314008017548990a03081101140c0980c0c0810318541010056034003250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 775097500 1250 775096250 775096271
    0xe0a0b07020301090c092004030b07031e0e03090a06080108122b06030b0604051003060b03010207170405030105011712030709030f03021b06130e04080903030406031a0a06080a 77
    0x142040d20301c0a030455103500300c0414100680d034048004c05141d03080c009850041c0171f1020200e4052444060264500c01d000524158000c0d040384810900301c5451400554000b0364807402c54a41c0c1403203071110303480882c0074003540c10200d00c041d000d426a4100b1060b250b24181c1d01c00e5880d007110103000200000886c15450309000c43c00b20b402c401c0e00b0090307000c50b404413100c80140105442d100a0322403140b0480821200d0802c3d01c41d03030f0f0103680441c803e00000c0d804c0d07403030748800f40c28600043c5805660800600010810006000c0c3c4040c5035264150b41c2c1c0da00d842c0806003943c0040c0c1250400729100304418866070000610210404003190403d912903450b0352042e2013018159001510455103001c1010415901040e00490f44a00000480c1a10392400c2031007054050300390030601c014030b0684288108480000341c0c650061241520a2401c83c005000c6811500142e00c510040b070f81307503140099500d861821388030001a054034944501c603d4814028030910018099290450f5180c04910 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 775098750 1250 775097500 775097503
    0x6050d1d0706200a061d060103050a0b0a0c02210405030a03210516030c18062f0c12010f1103070201050a0c0e0111070503032d0705070302060315030d1e0e0a0b070203 73
    0x5100511210544080350b9403401c0c0951520003840c400c80b1200601800503181d290f0dd0311400300d80d010180d0003402c500b1400c40021010900040340070400c041c0c18400004c2681d020002c03007542612135680d0301d41b004190b14003140c00d034114420403140c0a04240400010035840741d83d0080440712458040798141800c14203503000002c07045c040c41900740c2d000c00802e6280c1c0046040d26240a0300c0d1007041c88812865000c0c01c3c01088848590250300070992446035881d207074006c0b00005036910000981d5071201440c11085600c452800003c4405c04420031000e147c080c81813540c41000b43c3e90034440c021560304000d01c25160742030b038107041c441002d41c0314412080c10481400a4200501229a26000e00700c109c0b6140c01d1003440034446041d940f480e000740050050640e880c0c4d07540100148100790561b400c02c034058200a010300c14030078030301020101e15903040060300b469034500d440740c01030b000d1103c600f4100349204014600600840f203500100644410140d90100e542d14480c144e02c0e620303d480001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 775100000 1250 775098750 775098791
    0x313050f032a03010204030308041103010509032a071e080109261b0c0415080304141f08100506070f03111005180f1606050d1d0706200a06 61
    0x40f9010740c4017107004004c2607006a4507034061b9004882900b1060608410903098941c201c2d40c1401c01d8005000008030490440c900d815800f0001480d64020140440a140341880c0d07a40500c05003803208444004501d80600b100c00a0704580000340460001920303141440d8424a20410f208111220b50881041c260000d0b40c0580303a0403004460401c50002c0e0141e6100e112140b01d5100721300c0d1044444400c1032101c03860b030845140c2c20256043c0381c9009041c010100c2124403454120036003858118103148000922407041c0c1d01d80c0c440107200d06100d2616100c43c1195000140924810060000403400e80024007074581e61603e41800c200b0500c0320000d062802d024203a000150074030041c030a1030081f4582840e082e0300a101150f140c0c2128048860350381e40145040e010080041ca0240a0703030344154000d0840110a04000c00c40040301005607040f0500007004090303e0308a660180409540304c442c44690311555440c1c8040511001c003400d4031605c503410300402c01540e402c09170704010081c4c3c280 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 775101250 1250 775100000 775100083
    0x203030919031b0b0105130606021e21030106020105061c0b06010203040f030c08060a1116020a0302100206100605092d09040309170604030807050c0a060e0313050f03 73
    0x1009020305181c03805881d44280a4241f240075501c100e030590065502c269002c60790700350300610f0f41c1c1c011a201080c2c0f58550038440401e40c0140c4401c0c80d400a50302540c650b00c0e004803441281e89614240000b8211100600413501c5405032141d20815121180c1400d03100a400c4843c080d041e80340d03180180d10758403d0740d202024004001100000344490200640112400f02041d90010f64950b2440300c12100d0042003001e08400030b100d40b06035802a0056885107a201600480d0701a0700c070b800098600ea031280034240140d01882c00c00a03900c00880c420340042034107040550410034007900062800003840000744151000c1d10010000c20605840c0320700610014200d01a40d00b01810000c0c0402c40b02d006028842030404401d14180400285042c8155019070f80d8400580314130303d04803085d0344034462113405c911401030310401280d4144a030000589400005591342d01c3c81d0584101d840500c1c1c2d02180c8124020455505240c80101ea05448811042d01d00384221210740383c4140d481c001c4000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 775102500 1250 775101250 775101287
    0x20a061d100f030501051507080a09050315220302100f020403020a060906090b07110d021f030b030c03071401140c01020403050601090e0303100501080a060909120906020303091903 79
    0x140000c081c2c01800c020200e22495030188442e07070326a01805880e04640c1070404d001c00c410004c2c900811500d50140000304070600d030007030b04c9a03a00e41c00a46003080841008081c108013106001502c00120703050040f000b440070035448950b505d40c40194455280d00700c001d19241c0c5070100d43c3c19000844e41203a01955004000180042d1181e100800c2a0701600031800400c4030b0b0800440c01050644c141e8040d503602580f07040344400d041c014006001120b01c82242c0180201d0146007000e040005400c2010241d903400141011611041614100c81c03c84402e0213908028801e01504201c3c01d0b0340c1d05070386000e00b0030a0380d4080002c41c61003c1d1184018002c803951010078044100127020400710b0407594440d03000c0c4162890703641070548901c802d40d0701400b5101c94880030042c40d402203d065900801020000500c1a50f450070103050740da5020089500000c84a000307000950021442406018180300542c15450160b40803561100352040b0403850000c440e0752a000c151041c0780c0e070100c20340180e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 775103750 1250 775102500 775102519
    0x2151905070c03171518040b010f0810090807081903060b0c0309150c0d051207090b0d091b0b0403120e030703150207140f0709230408091c031704020a061d 68
    0x60b42d50b0404c42d42640c04813423881d03144000240b07005040450b001034070107002c0030f0000b01c0345060314080102441101100e8100c001d0000101044800001d030403031032650203030401e1140c80340f640201240c14a0300a14034101081c0805a164040003058a20451040d6001c1003c0c0c0d03581004020b15004090813141d15100c0c0108014856a006c000352404c9044190201026110340c80240d440c0c032043e00a0500c0b04000340004258075840d034121002c441c0c040c08503034040001301b1451071041202500040b41e08000050100100640c030540600300d480107141000d4260a944002170301c03402c1520014090407406150304002d84d2035581103410890380500d80300090000074104945a0084004101850203107010000310002540200c2d441600180340040d18104102112141d505000d80282d507511400d0002c0141a2180c01d0702c80b408100100c4450241c0f2075600d001030055800580b0500d98256100621005807140001002651420b0602e100700101c0164030701c07903108480b1075480d072012440 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 775105000 1250 775103750 775103779
    0x30c0906130306092105040b0d1503060e1506040e0c060c010f14091905060a020c150a0605090a1413080c070e24030a1202151905070c031715 62
    0x2040c6140c1c03080c07410301700100030041c4e403001603c42c0e008511880810384020482d1a5003070059034400076405500e80e144118680c0c50391980d004840d07a400e0310441c1c40c1e000300c40a00700c402d00300840c15845002214144201106107011580b00c0c1c512440380341c0140d4000c6500402c060080d00540d1110079030f4030082140d000c00274500941008283c1c0e10030b185028a0041d0740520030004001521541c100005041546802130900003d42c040005260540201d03810007003030700c40c030203080e0303002e108181008600e9a04003420410b003420302400c10710741d0a00d413040401e03002403801c5d200d82d880b000d11f070360010301c1010f903051001007880f4500081c94580070703408002c142c103507104604070300540c5140b10380c030219183c0096101c1d03035140e00ca04141e451f510040074040090094480c02c03a40070804e20507100c01030032080701c0510105042d02e481a6040301c810340c41e85109a14491039502c60b01c90700e40807034039646d5928060020b4a0941d0001c1a402c117510005001c3c1c09800c080c3d0301c00007800b400600321681d01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 775106250 1250 775105000 775105013
    0xc0224040306050a05241804050c040e03280c02030f0106080c0303130314010207150b03010f060b0702010809010e100e01051003020306190b04020a050a0e0402030c090613030609 78
    0x540401c0300e46500d018042620400a8415a07100309016107001083c071000c42c0001d03140200c140b030043e40c044040c0301c400300b00700014a03000303024511271001020302560220400c8140e8a03900d4121110341c1c424880078052000310455644d0081c207001518510b000c904a045400e1040a50080c3d003501c40e000703403140c88142c15070180e4100c510703210590728000c600c041096147c1c400c500400d0711450200d5070600104038540740f0320309e20014071000180b400403165583c04105120322200071405654001703210742c0d804c0038000c0100c4420000010450103050010310404d6006074080a8100b010b81e0307000540b040c01c00d500c046142c8094004640010002d00c0d901c0000e400a00c013400815400c2c500480e440b1000706000e030007502c0d40100030700129a1491104400304c4507040d2501b24140d1120041a0350361a14030007030000b002956140c42d030301d014040b00500003890f41c0660600981c4100100040114510255590424121120780d0f850303200d005841c20000c12900082e203010b01c3c0c120702c00c0070084c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 775107500 1250 775106250 775106257
    0x50d081309061a030a0b0a0303080f0106050307141b0708010213050a060806060f160f0219080318030f061e0115020307030c0320010f0b040e0a02010c0224 68
    0x20400c0514a015168040041036480714030402d0644408000040c0090100d1000345074010000f444c0000c5a80590000074100003950b8003e07004a40100207000c010040a00302c580980081d0502500c2c40c2009032000340310108021080035402000b082c0d0130b250b9810005001c81c0f50205a04542842707071100c14182c005d6000300d0b00c07456000714209000401c2d08050706074000f15952034680c03010315a80c010a2243c4d07079000e4901d0840c10301c0104120030712440a02030303000115000d00802c950580c414414007154041c2d516501090b5802e10004004440d40002101c062104000f0003090080500002c2490200e905080c24854040c0c101001552504507003032400002070024584070343d90380d07a40c00e131912080240c1d01500580080061700c0120f0b028804641c8030910920309011829504058600403600c80c141c010116511041e000b03600c04064000c1044072042254104118402032040580e1a00c0c000d1000f4180902000c0490a40d903c401c0405880c00c0102c602010780103000364180580d51 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 775108750 1250 775107500 775107517
    0xe01120902060d11040503070f0308040b0a0c32030316051b1b01020d08070804081c050f040204050a0b061e130b09100c0206070b040c0816030c0b031308090a050d08 72
    0x1041e08000031b271004113281e0b103c1c212500b0141c0c19103400c0c20b00f94240d0066005000010a101c0c51180060004000c101c103003001706908840c1c00002d010201151081c2c26140e80d214281e644140103203e080f01060111040c0724245003081c99480292120101700c06420102c0740c00d0b00d004d0f10708084602980b640d071407045003400b41d080c0d50103000f00040c2602c6128040d601000068000c034000750024225800510340a4080400c2c601001030421055082d01e0b42281c0f034190425942e411311003141402d004541d000000e200052001403500030216013103001e26580c00e0400000c0101019024222008464480e130701c82c0c0300004e50b10f031204505100c643c48210035a008800540300040e22a103d901c003a44826802410360b460a022500c07501160174024100307866580800c0740c00a54040100440c1207000d4000500041c41c0b451410116a0400703a0b40c003002d00e01ca800c00410a14081c0c0e15008070400758050285a221081c2c1d03000b06040190b9900101c1e0803000040503030040c42090310140c001c01d03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 775110000 1250 775108750 775108753
    0x130212090f06090d0e1302032409061012091e030f02010c08011e05060301061d150a0f0e060406121a010f030c12090605040b01060e01120902060d11040503 68
    0x400d1500c0200740e4032807040f80c400c1c280da0041510011030b184500114441c031880200084060078030022000d040764000d8070340100c5c0741080c5101d8511100390540c01d004c1604111000c03000c0c1c1c82c0410105d03c880c2440d03203801d405c100e0100c0e40f4840c000841d80c00108855005000c440815210b000e46820250310b11506038007140c2d0752000d030005c1c0b07803050040d914203683c0c5070b0795107c441c0d19000f007130030030071090480216000d81e22041c0400c9503106c000140d40241500e03654144410710880c4001404413082d91528026641081110040c21800080740d601071020700d0304900150341100c045840005080c20b16a11540002e00050842d45c4105074111150200c0c40c02c11000d5509403078141503680181d0f101d03002c19036444070030303400300d0280d0b015032030855641c10101c00c2e0700b94022030001241c00f180c80450302155504284018040c100d1780705805052203080290080302c0c0c03080046c280e0511065007042e403c0c3c030341100204540300d90342511043c460305001070005030050800308680c0e401501802d8000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 775111250 1250 775110000 775110013
    0x415030501020306181003170c0f03090a060c050a020d0f0b090c1002160e071704050703060e061909030e09040308010303020f0309240c15040b07090b090d0213021209 73
    0xc5411038114061500100421501031942d48c40003215004171041d800c179003900303001880c2c0c040d2040c406a800014018051540c50121000300300e0b070301000303410980402811844101c00160000341003160160100e408015000191901400c0c0303c1180c0c3e802844a041070060100c41080000d01c1110044115240c2503852800e00d800c0741d0b0303550400c50904800a2a030300400c02921900200c9802c40e0b02440c0039a41c01c0e0481c45411844a000c1e08c2c100e485501c407100c07c0052008522450055450305400790034282402010b400c04201d0a4440048107a6545480010503000e2000003001c01c0c4064800c84051820742009000d0f484240700607005030044800d48480b61401100320342003040010400041c43c800c00820380811040c0192089280c0f80400a54607010802c10280500181040d150f030100d01e842e01d00180801c40142c40401400307520b050030320030707a910502520741000d810744240004070003030700000b01841306a81102820610001c0d4601481e111108001e100e41c0185080341c50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 775112500 1250 775111250 775111279
    0x607030f080c0307020c0108072c09010b090d060b01120c0806040f06060c060b03070e16020d02031305090402130e071a13211b050f0a0614090415030501020306 70
    0xb014441202e004005030421445a4140d45c096203030643c20a446203403c160204c0380211080781039003140c48c1d941c00004480c800c0f80e65850115007460150111258580c00c085400740802c142d8101500c2c014140d680350154a8200d0344914080d1451810420f020300c000d640c039880103802c0c90811340b1114000c506005150003e01218003d040c00c81c0c0305a0b4456403c220141c07150802000b00c007021079818015a4000181c02000040e10760040d464040b4400300041e41c031002a00c0c100307400e1001d1066410501482d4001a510041001240c0086e5883e5403142d40f14400504809040303142454503900d42100300c0f4441d48009178032420346110340c07803842806503180110002c4d4003803054072202018510005025486020510f005070540ac1c03003c00c600c0e040c0c3d41c0c5d00d00c0e105d0010381d12034001c01030300d51204004034035100740d080f21000c00980e02c40c90341500f41f04c0020096064008100c509400000d13400d4113071b07242c42d4000c003000340042c003e000360302e038691505c2400b070361058036420312070010483c3c07507070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 775113750 1250 775112500 775112521
    0x111203010e16030519110c10051f0302030715120e010606180b030a09050a0501050a0209100509010804060c0e0d06050f0708100302210d11070b210a0b0607030f08 71
    0x303000d0380110008003154865590610080c0c44041b480440c030800510000d15410010482c0a0880101c0140403809140044000321a10300000b2042002000e1140800168801082d120155048250b4407446c5404c002c01c10f4903040303010380451800d9440c048500d03058076010f43c850340c20307602e86540e00c030350009001030f500610084c4c50184000000c2c042011a5412040d507121070305042c41001524820f01e01070326032508440003110070021450b00051925100d01d401c83c16090074070004d06106052008802c0001c242c030740003c00040c00c40d599007800300070f69030213000700020380c15000b03241407001d0015184c034401500f01524112444184400854145405140c1d0140b00d8100c03283c2454942c2d10710b408010002c00017640c0c03e0090645d010554401c0340041c070000303010405907150f010740b0501ca000764900d0142c1e00d038410421000d003409811101c0401c41964068040c0000100c840c0707468240b90b00300100605200b10360f02850000c1d480c400c041e0000100b14140c4004d80f21a0340c0c41d540c296104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 775115000 1250 775113750 775113761
    0xa0308041b0503121605030301030c0801050105060f0a0c0201110304062c010f0813020d11030705010206090c0405180d08011502070501081911030c071509030e01111203010e1603 78
    0x754590824944d07a014550688054101d0b41898540350100f140e1039200d26065a1082c0c009445540c17004030140082c102c00d0264500410094403500e29261400e4407049950080e104400300300b081c8140381000303580c0b190210100b40040761050300d947c6e07a600c5402908042c0c640011901585481150199004449160220820068489034646100301200b154820801440000c00e0402c50105c40e01603101d1030000702200f445001040c040d00369160800d03281407916440300e81154415020031002c40408518071400000640c0d012649803a0303c0a206030744a00c50807881d00e50300c00c1c03484880030360707a00000701812115001040a6100308445040761038200ca401080c0c081003070700c8082080080104400b1003003880d501000115a0180c5601c03611a9100340c071000d00709a40071501c201402040444205203601d0602d0804c0007074080c1c0c0d00545900c45000d0303168140401c40b500b03d440c00b10b050040200080c0e01c2040039030740e980c442c1004100342c0390540304101000300b2224141804c3e030003445030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 775116250 1250 775115000 775115009
    0x9050a050102030a3006050301180312090201050c0a060207021c0b0408030601110709020a0f05040806130813260a0b180304091b110d0e061b0a0308041b 67
    0xf0b585800d545400c26a46020590703040c1e480d2000240201c00306408080342254000002e01d4041034851800e0b08040c2034803940c030070412120100c43d240c100000e40242041607076070f0f419880803030202207034001038401d40900d601d0b400e058002d4034110400c000c0d0580c01002424400c45c0c0c2108034441da49141d40301c0301204140145000d4680c0080703408100300c40301441d80300d04140360412000a15070681410240d0aa000c03a001540229180000541050714103134882203624100d81803901c2c00c0320265a0b550094030050603020300c0d6402c0414044100c046585031042c11003001c0031259580c1000ca1f00c24010100907441c40c5880510b2000501301082254501d5001070f090041601c5181c004e03003610140c2540581c0d203100030800041c00345024010780c1205034030900740340d00c40c07003070b2070300280410740340c282c41115a03040700703080204841e0003241c5a00d0189003522413a40303402d080da031055035000d80c0d801a54854400d00c0300500805d684030750118451403240d00483c00103001c4c100500780c03500da00e004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 775117500 1250 775116250 775116253
    0x3705010f090c0f0503040b13080c1b01050c070b0d111314061206041e09060203060f04140a0f0207080c0a060e0d17040203071e080d05070209010e0406090c06050a09050a050102 77
    0x486c0c08035028140481d00071000c4018404011440d50b070340151540030300001b003c1034010034641c004003031040824024100c000e007850b619081800a8564680b00e05018500d45842c0200d441e4100244591200c62182e00e00c51501c0d50301c00099030001e0034039506104901d502c00214440c90141d0a001e020303101907142595440c4e00b00d848000402020782048180d250643c0d11144c500d0031460040d0144e030f000300b4001c3c0b00041c1d981c1018018405804003504241d4062800d10310f090403503403403062403140c3c8245088000200d01002a030721001a104903440900041404101c0c000c44170808280b4200e014400c15081009020740d80000b602e9025021851012804410138203200005c94804030340d10500c0101568040c0e074881c40114112031045036080e040c03170303200f900600000008000801e101101d5062480c02c2151310303400604031502c140190444440140d0100f81002400e070000542c890b845410340c120941c8819006240d80c01c501416400030b140f01c18002418280b050b003a40a44806a0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 775118750 1250 775117500 775117507
    0xf0403021210050a0902180c0f0c0307021003020d05150f0402090d06050a142a091f03050a1d0c09060604120506010911033705010f090c0f05 62
    0x8003003215410032100c0300c1c101c0d4080c481920480711450700c502d610074002140001341060300c50040c003d10b100540c0e8068541e00e00c11081c45a143e240c1c01c20b82d114116003504003565030025480b814210f0050b900c009400050031451100540d4068010b03200000c500032003001503070b644107075403e8640351020050303800c0100124504558180340d00100382c815000307810750b02c1c400403940d00c400450b00100d42402c403440e80c90700000c42c0080b07041843d607000110004118944d030004e00340703040f240c8460264510091000151a141030301c507281031010072030705080c1903503882c00c1e091000b402805080b2401130010b494468070885a01c9611041d01d040302c03280000b001960294004d1144101c2c009c0c2c901c560280e0305000004d50712100780320016031544a038003e400254588a5042c003621000380f802410a5024000c0008940c2c068858401c440034042148200c441504150240c1100d0700703400402041c1080008078810182036090000c0701c414460800c030b4039400245c21102149090f8100c00056401c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 775120000 1250 775118750 775118753
    0x302010f02010b06040308030103060e1f150b03070306090501080d0c020904031b05010e0c1f0804061e02070215160b0c040504090f11030d020a060e010204170a0b0901020f0403 77
    0xc0082212256040c00002485120395002403000e80013544200ea071200c00000510812900e4014070000c0c000700001040f003002d241110220010524088080455031070800310755800c00c01e0b610400030b0140b19001641e0741458840200030304030340d0080e480001e04103400059041c000041071031040d820f0343e0b0303901c1c0824035507803c000b5154405002a4100200c561500c04566002d10401e0503003841803000044803d1500c00d401e0924282154907449490501c40c03600504040d121755040d0300b68a4038007840e140d600c80c0752660007400da6541c92000000017034101c2052581720f60080c103040d8022200303424240401c1003900101d100703c245040f030a035601010030700004c0d00703890b030550011500600c0310300b01034407900810b049480f0480c0c1901d01c401c41c40d1024050002c649070f00d0400700c5054016110360500d904020b50f44a40540006100543d03a00f02940e05400070b505860207802e48030303001a001400034504954a001400090341c0400e002d001082e5104014422240c50010300c58156080c103145 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 775121250 1250 775120000 775120007
    0xb06090604061b0206130810020301120206070302011d0c090c030403090b0a03060902030c0301060809060f0610020304050d0308070f0e030d030c03152c0c22030c06090e060904020a030201 82
    0xf5440c00c0d80030718107a03208240042c2c2d02c81003c3e03c8904004a200603204e0300e001030542c64401e004242c0240c140c4100700500010300b044065054454042c0c0d0250368510440c50b0490060203c0740700030200e05100700d01c00c0f05040012450074a07900d0122042800340c2c032544000e0226120075140100803803120300081040740b80540107841009010b050001c0e48a559109201c2640d20071100a404401c00100611010383c00c00707440c1c0d4002c0711341c0e00201070600d0550b50805010b0800b43c941071151000240b982041e40c07082040318054103014100c5400901c5a20b8081c140711026503c5a02199425030310102d2284203981030140d90701c0090003891541c1c00f1280a50040290600b000101603d590031262040e541d030103110002c0c010035020100c0c5490a00105409007500301141000032014018004541c50017410340710f00d111a49030150303504c2c0034011280d8000109a200904000604000042e0b4982041b0102c04031350752084282196601d480c1003005090017203400940c040705410703050015510 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 775122500 1250 775121250 775121267
    0xf080618090307080304030206061216050f0a09060e04050c0306160806210a150612020f220b09100323070f091a03120f0a05070b07120b0609060406 65
    0x1c1c50020b9914107005a1242c07855a48112026001360380000140145030524507213a4000095200160503008030700c03d10103102c034020b4407800384a40080182e00b0404c2e950380240100070700001500f04407059035607503040c4140c4000c44060f00c0c507000706141c0000c0c9090110312180301d100c804500000c01c4038007c009a511030b001411325a04601059681055288513100c407031100107a51008201d040700300e2400e14180d52210614083e0f4600308030381044580890340002c40c816504440d884a0360541c0400700e06e00c4c85142000c00c90710f41091046049400d0142d01c031502d40b19090311560802d80c0d402c001a40301050303510004000c007000d0300c03040d0b50b4034103e0050030000c88030038415105079682e50304101107010540d410112005582c0c0640b034541d01804031041c03c69403802e41c058404d41885103030f00007280c042d0a2221601000c001902c0a0540c81101242e27003036a4042e03103050242c2040c52005020010410142e00f8007440c14529410520300a410741300d417210300801c1b00d03143c0741c1001400c5900c0e20 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 775123750 1250 775122500 775122511
    0x2901080c0a0f0309080307030504350d0b0405010b0a0806040911121c11011a0a170a0c0b0c0606041103060d0f0c0303030e06010b030106020a1403070b10060f080618 72
    0x640d1900041c0005460703170000c50003980565404140d41c01c0600f881303800c0d11a000e00c0e98091440050715410310000100d0046001e0300c0c41c2e1000342c0c4540203001c1c0107000d4410cc03240701d43d201e80360a0001c514454104023a280204150303640310340540c0c41006001c21100e545502906400300030b450a4518070b0841c80c040070304042002174440d10750325003d410006158140b5242c0c042030240c00760065000c0248103c62042c041081c040080700000408a01d025003a40941981840c20510000c7c5e80b96007044010384c000d620290074552f03166264903207800b0350081160b84a84e0300543c00401c1c46440d013405043c00c415401542c007480c5450320000c210040d1580a07003215001488804000450110000040154025180814012141000e090411405030081940c000c0c040c0018004150f002803c5d1905560010448040c120000001e52450007803d04c0104540b6101c002c00c8100728070f6201c660100c40a2340c130780f8480c3e27021008007039800c59400c036110345c1c010403007800305545104d291807040c0d00321 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 775125000 1250 775123750 775123757
    0x10e070b090d0605151503010f0510050f040b07110103020903122a010f0605030a030206010510110102130e131e0309031a100e01080a060c050d2901080c0a0f 69
    0x5404940e41c590582d40c0465542854170141500c85140d0308022a07040c0124042c450620b14640c14000d582c21400c9280c06503c2c01090324540d0018660300850490b05d810900070a0103031207540d01c5403030907190f500c00041240c003240541e100c101c541d4001c1c002c2e100e10322030003070180242410b0740d50407802640211a40040180181c1c40080310002c50b807001500001d0510004034181210f505618150341843d40014029401404400b0100760302091290540d0f00c2103894103d0640d07010800c59072007036458030b01c828951000412441c42d420b040d0103002100d003008503038045070b034416040c2e4070711195840740646220914051000e03201c22108111a0881c441e06121300000c7e12600c800640c0c050031a90000389401440500695210300c440c1c46005268043c05044d5540c1840c0c00c01b03841e00100000100074a071221454000240242c00760382c0400603d403404c1040300301030080e0010004a20f140350346244120b1000c02d003254032810b003461181050a05091906015071030413154185549421801c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 775126250 1250 775125000 775125019
    0x801080d0305090c1c020f1804030518150702100906050901050f0c030a0c0c0e06010f05181c1a0103050d0c051519050708090d0c0f0501020c0618010e070b09 69
    0x1550750131700345d105414160040e060704c0d980342d2060062901c42600c400d4030403461868400c02410242d024107070b000c1da141c275040d0b44078800d000ad41d0f120011b2810385a54014080c2408100741d462034005469a036000311031003101c6080001d401d032004c800c036000c0d9000048082000e442c403540550010514181c440c0d88a5140402c106281411074105c450300000141c2845400024003c0340e12959020703003800d245800c100d090810011f4800c4ca010240d14042c42404120030030442d01c081c24101e88404054034480400c10f106424200ca0450003100722000e2107840c0d641c1015000001c0e07281d040e203a03c14000c2c100303615200800c2e1200307031070f001084034280b00b045a5002800c4006c9000741c040c0521024904900d851542654140c80000700810100803034a41000010540000c60301c0381607103981080c88801c0070504201841c10980040a0f00b03940c000103402240b00c1740000d0a0b440340948004142084151812103401d0b1410503040b07000381ea0050405100030305855000744071152006201501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 775127500 1250 775126250 775126273
    0x105070302100f0c020f010c020615040902030d0e01020d021f020c1c09030c050409021e0f030610080705010c0c03110f030d0e130204051c080c1b100801080d030509 72
    0x5441d81c00f40148503082e202e88402d02d1a079010004410782441d030b0720007440117002c00c61001307507207a20082990b01106540881c0c0c90150325260321500b18150081c007076442c4d28508a1010f000480c01601076401031103002c520743c2032a0310226081030003e1410010a140c130440a0858019400c01d8504551500170089000600c42403800f80c0b800300499515078203e46440c5003000705018200790702503030256040924403001030765000210301c0290b50ba02a00d08070980400080f82c110b1400040072500b40c0706100520000c600d801d21103030700302c031010070031603039600d45071030045030a1040c0c0f0700000c0c2000c0c1980003c1c400180c3c0812000c03400342020300909000001100040c0c904081002e144010640f401241443c80c18035807502c4000d00709100040d07107030130b18000108144a02481140510b10f1502c4030100402061004880c2039000e148110703001c100f0380e208900050100c10031454800c007005e9001000e203a006003881412504620050b00e0780816031a03080d0301405004010b88880d0182d40507810 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 775128750 1250 775127500 775127533
    0xa020906220e0708041203050c19030618050a0b0103140a0203090c100503150901120b04020609090c1804051303030903110d211803120216030f0225050105070302 71
    0xf4400c01507039407442014209030800d00103c15042600c8010903042c60200400c01d40c2c007600715403958030100d03a0803540300d0f011801100189140c1c1c01000210425405950308240640c0005003d120403200c00c1060071040c80042d030032203401c1d10544610b10b0b001800600c06140503409540c2c091107160913601129021000914810110350304000450740100034021610310725021640c030410240ca0800d22075045c1080302010800707040300107002d950590001000c40d11258243d0308002000792012025003400300c1d45101940040310344081c104010742c2070041074500341c052140111020702407000e410074036480403000342050320001d90a00c48200c5140d0a03040c0100900b0601c0d81007aa20f55805c902c8401a42010200720000b2511250516440214243c003554400f0741d01c1d0341c036003001120a503440326200c010b070192182d14100103d0403040c84041c0b541180710f415003a5490340c00d968484c0c4003842540e000d02c00340c20018612080610040c0f1955000d10000c1041038024011120b42061314105038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 775130000 1250 775128750 775128779
    0xe06060c0c0d0f1b030302030405300a02100903172104030807020d0c0b0a270326040b0a0218030609010b0f060c030906160213050601080a02090622 65
    0x1c5502c5400c054401041c480541109044c10380725901c0c10300128510303140203607240140d0160a1250914940509040000b007000c103d140184c1c46440d5441d1280591b11604c50444140c01da00030522124907071000c0740314020071405d480c0d100390501c2e4000e054040d840710b40e400604000383d00541c2410740003020b03d41c1400c61441103209560384002c52904080003801c0500c480100c0060003000f00071600010500e06007241d200c1005c800000d16111900c003440c281c0c210b48102c3c1881da80b030310403050051560024200f04285d185031802000340000d480703141981c81c030896015221080c020301154803103605030018860795a44110780c01342540782000107810700c10186e0b0640d402d80e54406005d100d9003007612200c0e030070300011100c0500701505c240c100ca4403807142c1e0038000c1c450803000900031180d0320180055a034007a006000ca02c0980007615000c030050500380c0300b0320b0200b1081c034000f500f449054001c681020901130103083c103008540340740fa1034403818148101d010181404021440308148101c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 775131250 1250 775130000 775130003
    0x603200316171512030f030402190f080a0c0f0b18040b190302040b03030903030417100603080a09090605061e1b07061d0a0b0d2d060f0e06060c0c0d 65
    0x440700308a100c142000002c0601244c040030340d42051083c00c40c410000415654000d4040d6902513040101b9a0f080304c2d2012641c02038240c42000305004110f112001481815203171080c40c84214240d120320065240008520421102c08410000e803018840107101c03500e411500038101245264040c5e001413980d50141028009035114000100107502e024001c2903c0c1c1d8900fa030145180050540c0441c0e1240710300e004105800085240302d54414004010810340055020810030025441e8641030110f64080d0941800141c5555400b050140d001e204a40844030001c00492508016002e46c0040300e0a5201d102c586840500c40000780505100a603a180d862100181208504101000e070000f9084080c195640b5140c982003d40c5440d0b20350000107848060344e105888018101c4450050106003c5900c5000b8214000c1d00e001c0151603c0c0310361a410f09481031003e2a20b461010382c00c44040d12031040a44160404200c903802c080005140b01d04e00e480076039200403514408100307080c050800 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 775132500 1250 775131250 775131271
    0x1020c0f010f0501030b06120f12071208060127080f0604020117041e1b15020c1509011413030f140303060307033504060320031617 58
    0x1140300000081c4030700c01015010300e50401140d4155100d0f50020300380100070342d01507102c01c810220304d44020005500086c001000312800308401c0019007601d80c002c8281241c0fa039144010044001d801140c2d05403084506a5a2005204400300b15810030104c01c80d4400158000c9480840d0f40d0f84180b0442000355000c00080400e810284001010b0000310740d55800600e44200601001807210101a81030341090130003002460305506007100005043e010500e1980300c14031380005c010640801031808844036400f900e00c090300030000d01140c14007203a140e024944003005560060f601a0600c4041400080e00e1a4203100c4400ca000101c4070480d0070659040b640828000100110b6500a150382281c4401840c1142080b80229a40700c0340780c000200f600303611a0001040918012070b002c03100b140b0356032141c00014161001c80050f0302500442c800a400d0039415483c0c541040405131220640320b143c945103544555506010b09001d4821508208210420181100c0501e01460080c540c480 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 775133750 1250 775132500 775132513
    0xc020609270103110a0b0a050f1c0605040507020d02031608040503060c12060d0302100504060f061217271f050c07060809030904050c04030804060c05010c0c020609190801020c 77
    0x140303200090604c4400611502c5440414052419413034250340c3c800c6440e05005449220b5412071142a0150322030044e40000701400d80c00412044e60880b2003161000e0320100010b840d1042d049860350031406001015078400c100901c10350013103940488066014039085810070b500c510000307041c10826030712005c99110225001d00403581c601000e5400c504101c0311510792160598000e5140d04110052a84a83d503e0f00000e09205d4507400500803095005400c0100716250a052011117203203160956009518200d101d5440342008212802101c0700000442078404800b00303035540c00c000b5070312513400c4440c05840480c00740b6151458401c0484a460f91038403801c080c0502c0d0300e84000340c0d0142c02000603076014842980004022194844001d84010500780d4403940400941d1095134001441008001000602e0a0f4070101c1d40c85000d11a40090200702158102202c8007014510040d5012404000d001241e140c20598426030120441b1036034005544d515481d42280c20030b5400c52880d0300002c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 775135000 1250 775133750 775133753
    0x403020f070302010801030b13060c05040906050a05030c1c0f03030c0e01030507081f03020a0617090c060901030c0e180109150803070201030b01090f09021207020d0c020609270103 79
    0x5011810440320404020856185140c00080036a1010310000e0100b400500200388071101c030300d42c1e032007185402100034000450703129001044e641c418402d90140c589803240220b114500f00d1013680480b04010024140f1010324030410004882d6000c46a0403940021140b0000803241094613200314001e032000201a1000b042c0903203e20003203400c0303504052400d01003084440d04944c4c4550000b030001900b404c9080c40b910329642c4900c0c00e8102a610896461000800d41d90021060f602c46010301d08281842c0c0b15120354a0780c820054031001d501c9030050084c031001e03502c2540018510302d0030785015659407100340040b85d40d07034261549420000c0718203070041c04200d070140210903004c080c5001c1d040000745040b1404d6101c0c0a0280c0080c10140c0b40c40c10840b05030701c503034128006494501c4491a0b40c03940c0d0700100f4007d40c000403002c00c00400c4000012141c1c1c1c004070303080d1020b0340c40b03840d544400280755003000080d80c4088295540700515146d518104e00b2148103250f8104010441200d995040d03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 775136250 1250 775135000 775135003
    0x20409140403080a11040306020304230f030306060a0e1806040b0316030b0a021c0506010912080306040e01020d2d060303120e010f0f090c090b0d0f02030a0203010c0503040302 77
    0x1110010492100020038440000e81c05260f096101183e2100054000c42c00a000a001d11a682c000741100d40044207010a020042480c8000b03195440c1e003030000c480201c00c90780d803a210300311800b6226810520010f0910b04001b8010446100145002c100320b100d4600010b01c0d0061031000c4450281010b02008110306242c81400680c0e0011001408000c00d19400a56a0f14183c00010038060050f404910f0203e020740503907582d08003150003020700300f03000c20030040180012aa018005a01e40c0b000090340251b6201c9610817582094559255944031010310028140504070743c0c441c0d41d801c010300345c0718200c58401c10800c40001e180c49203000201c60742400d41d000b484c0381c05d115050302c0c00000f00f000903005001c00e070651034040404240701c00004242c4d80105070b090426650b440c1000e02d285040103103648400f2050344140c0c00b201907991501c0480084501d40c0e41a9a0000310030f41503200030501c48441030384034078402803c80c0c9040e030956001c28203450300140990040354002c8180010141c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 775137500 1250 775136250 775136261
    0x6040303031a12190203121215060403030503060d030e060d1e05070203042705180616050901110712140f030903120a031b090f09060305070308030712050a020409 71
    0x45803e48002c400041c1c1550300c1d10b04103650500b01040c08aa21421500c00b417182c0c54101d0710b560941c84d1a00622850100307400c8003161016140b039410001c809851415800751030940e901030b900c8a013141c1c0c4500c1444066415500182c09100b04690f200b00259070306402480400a183c9021a04500390500c215080c8110b46080c00c7c581c2c1050100407001d0b50000594080301d101482c3c0c00c007031102c01090701e1340c19004103105440e43c40c20b1408002006008032085c0c5440c901c0344e000c40304555240b11089401040540c4101c001480401c0a0f220302c1d84518100001d81c41c03001d00b42c0e4055030390b50000920007404c00310b04403803070101001041c440150500c02c00d60098010005185031901e40300c0025229005806c01c50a12840171401e526858840d5025025035804a40d00001c4204e171200041c02d0070b00c0c64800c0c4076102198100114020300c00703004100459034400000c1074003a055540740d1903640c000a101c0d00400019401580704440070380103c901425051100503039407410800c512060f5032 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 775138750 1250 775137500 775137551
    0x10608011d120a030b01050c1501030b0a140714041d06010212030408040b0319051e1602100c02160611060a020708091302090414060a0e01030c0b03150604030303 71
    0x4111169480500c03000404950a6003218940000c00070030100069550b23014a8104144900c82d07990100d0388620344490340341c103a90107000d081180303507104044902900c17280d182400201c00b440010582c0c0e80d02683c026441e0f005071105481c1000c0d140d050420079459071207036007902c004462087c05500c1d41c0510121145441c4207140601d5450981c54180441c482c52050740d2100c0e4001000540303000f10421403444201d943c41e03082c892801c00030301944101c44070703220084441014502246c038109400050301040e640d0341c1c01500d95441104061002020300d10710403c10341c050561801030000c0341583c41e9000d0051307a15035a42d4a00b0000d0568545800241150a450f00c1000b44101241240003a124079000403101121910800f11040300640100403c0f260491704105100b030b0751500c5e0704101807107807209617220600a907503840103040c0041d0a01c80a4404031003d5028040042194000c540c8a4900c482e0042c484440c00d011600c191f00a40c41640044c1d5542c90440228104035540484403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 775140000 1250 775138750 775138753
    0x19030e0a150203030c34061103070f030902040b090108060a05010603021e1b01180506243a05010f05150607050703141f0216170705010608011d 63
    0x541d42044040d549200103000c090004038089801c1c202c64090140341c00100307064009030b200c01d000004854003070b42001c810455440707041081c11301c0c0381c014070001c1d00d00c03410750342d80c981d200281c0741541540204190340041c0c0e04203480710b41d501d01c1520740100180c02860800c00505a81c0383c151b101d0005c40780103801110826004000074885513614840d0034101e00704407141c40e5682c0231039440c011221320306071080010035400c2c0200306440303580c15410303910703207501407019650182d541d01c040d0920401603021007464a00c1c403401c1c000c500d040240c3c400b50742280c5d0014856141c001120038a403c4414207403102047c240c5c1c000c851040107800c0c0038500d80b80442c424140883c0c2411100c0344040e03071820304030701d001d2000425044c092060800411000f16002006074000e01001d048050700d41c00d0314241c445009070b9040044e40b001c070b0b50b4402c45000c0030343c26014003400c1445645001c00c03080e42c0a018208000705001c224042102032190900910540c80001000500a4070b0180310307200c6c154072100d05 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 775141250 1250 775140000 775140029
    0xe030d17221e1e12050a030e0f03040503070f1d06031f020a0306090c09031205040b0c0a05010b0603070504030b100306150e0907030c090b0a03080a0c03020115030f1419030e0a 77
    0x200c81001306400703031400d410080e40352204040e04400805180035034241d03510840c0714114882c04080024410b94906906454003d511100b25601c40301c0701d48900c025410802c01841d442050585120f070708180000c090310a201c040002003d81c4401c1ca82c40103000960000d4821078082d098031640700140125a410b11912507100c80281c000301480c8000f400c4a0b0618001c0b0f2495842081110044c20305000050b4948611440065170742c030b41103c04a94035841c204036258149000d2013607a10810480c1d0310306c0d14007800c503070710140c0d4207401810022004090f040e01000081d01801140f1785d64981141040065240a150042c5000050f142c00c0b03080c0c1290805001040c8500101001c0e90260070000c13501009040c04100e83c51a241d10280c9190700200b14454032a9100c05001380707250281d80240006030182050448912140c070000b02540e28a28010000038008030300d800c092002441524011414822041407445c1000300171000134032182c40a54091500e841c1d000c0182070715400d41d070320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 775142500 1250 775141250 775141253
    0xa0b0717040f0f030e0a140a08030c0615040204090f020309100e0d03150b0307020f0c0913020f010e040f020705010501140a0303080c0c030a0e030d17221e1e 69
    0x442e480304003000e4542a00d0b54120018503000700c9010a80ba03001a05400c00280e8603003240c51100b010600041c407401841c48001110b03240082614006024000680b0058a035155041c45120340a400346030069000e0000203202c402030b02c20504010702c49100581e60b407a21407402804c01c1300000030641040d1415101e540e849a0010300140824128240003e4255415025100ea6a0151b100c0241904004200509141e001c1100d0b030348482c442084a910103503070300812a007000f0440300c011800f4002d1140302e01600d0000d500c40022001030408001c00b03200e100210782a070f503080c60014002500003468400b001000d1090720b0040c1880c00c2c1200c0a00126800140c08141510010b030411002c6004142e50840b00707400c94140500540846e503903052050005003076042003e10541c800c4c002c118021041c0c5014240400034400c0e68005550965150a2005000c2040310b0348240c0c00c514200c0d070075000170210380c4080c078000c0c2450300e600d02151140c039080e01c60680040da954142c0004000303010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 775143750 1250 775142500 775142513
    0x501110d0504050f0a15180b090c03061b07030507080d060305010213090213093c0e032b09080c011b140301030803041113090201020d02031201090c0309050a0b071704 73
    0x1b0048621124040b40ca420300203080d00076480c45440240140c0d40520034480711100000300040d0860058040e20500c6d95121030404007090000e203003e0407088204030900009118400034100c051040e41980d0501d142040e000d0304481a5403c1110146c1d800505480c024003c901200c00034001d038001940307030800f80c004c920b45a100c2d0b0700c82c00301100c0d1101303084040c4100c01490070000300e80560001c60720641c02180c49250400303424001810074076003000d0555003d000b2003110042d9000d02c2100a00c2210f050075003403800043c1200d810010340e10007103400040c02e00d02c001d10503032100800120760004181030f2203441000d0440c00006005803500040e240c3c003044803e8a0440b9081b4064980365074a9060240c0c03190703810508580d00604901503600200030a500c4120824000c2c1c1c00c4482c0001d080307106a81d2445041013604001c1c207840010031114880c0c0d00001f41d82c07400c1d480c002c50349000ca980d80d14a4408062001c4031815003e104106080740d00004004040c4800d08840300b2605158032501c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 775145000 1250 775143750 775143773
    0xc0b061c0f26190c02030316060f020301050607030807111501030605012115090c0b13090b210307080403080a030f0908190915020106090b0402040e01050d0501110d0504050f0a 77
    0x11031014550300d83c0c200140d4016040000c1258001e400c0c0c1e6070759010000d03809102e20780550100c501c40d01e8a03075000c0c0b0f01c601a10aa078103840020b40000d20300b03d100c1c0c409a5100400034001001c100041c1c0049011b040c060211400300440004029829411403030400c05070788050b0484000c400d4001e030040b128641459445588941254070300c03d5100321500001f014008450011305043e14103403001900c1c400d2000100214500c1c80c3c0400c107042d0b01c89030810159101420780340e9001c1d4070f040c2040200d2406407400040481c0805c101c0345080f0703040c1c2e036101090b0403d0b8070540704c2c104085003040c4a2509130003011300302c030070b0500100404440d56603041d44d54000d03180c1a5056084402103c21200e020f907401d50080c241c00310700243c1381540304000034044d07c2640110705d0401e083c0b00100060b401d1a000351826501c4208040d001c581c00c0005000000d00c0d47c440a441c103640b9000140083c4040710014074a0314401c81000c91940380c02e051080c6400106855079072103078064070b6a18045510741c1d040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 775146250 1250 775145000 775145017
    0xc03010e0c1201200d140106053a050609010b04230d020a0906140d261b0706080906040c18060b041d0f070c0b061c0f26 53
    0x41d40440c1500c0c18140f801001004504040f10098440aa2410030110082c002c0904040b2050262a5480a40c514450001e1266501281044c040680c51158200a0705141c030500402d102403051441490102003846035600d1050503039a1041c0443c41c2001c0c2c0135503002d459502e003214501b5140c002a240d1505c03014140803020340c10100b10300c840750384001046003856002041c01000b01d486d010440020212031140c83e00540040c1580d6001d81042480080b1181c1c11001d1201c0418013200490315040c440f01c048031001d40c08101040441079484866100d0103042c03c0104411810309174013030000980903208a255600ca18100300000300100c90340c800b9281d032100b50308400303905042c42310007410180d00201910000881c0201d124000c2440e00b50703454a000300d42504a4640c12400003141e007040d0741d0200064000070138078011503010718a050b0892000f50040000ac00503100c8181b020390015401c850036010410042c0502000728544c200901412007022010a00d001c85103006200b42d410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 775147500 1250 775146250 775146259
    0x405040204061d0711070b0f0310030f0506100e191505040c1d04020a09030b060a0308030103032304050f0d050a050625140d1a03030a02010b01020c03010e0c 69
    0x581151a1508850010b00310003040700a140c8801c990500958000c0307503403400260104159a01c204d83c0040d00c441200d0300c8110a43ca40f81000381ca4840b2903000400983c4242d61444000000071100302c1800c503503500071130192000e03042c0441d090110040d19030121080b200f40c20103000241141ca05041d140718600400051181c40c02200030442c1d43c0d2503131010742d00c01e04d001003180503290000107242c0c194020141c900c2154401c0701c20007040b401409910300c000b40341d121013400028581c0c5441504008001c1644401c66943d030398140a542c000d0f0000c500058030a03078030030110042c603044c0d1600d41780741007441401c0030304010100703c4006040684a116441202e0320009001d801c1c400030350400d030043c041c0c41503844e01200c1d011410f0300703030800c11140508041c0841200c51041c00340c0030000f503481307000510f03050030060208007400c0c4400481191803816203240c12a694104002c0001060780e8001160314014000064100422040f6070381c040d90422840c1c011608000c282251148002c68 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 775148750 1250 775147500 775147511
    0x142505010f0801090504021206090a140609151003082809050f0d03142802031e0a05160605060f0904020913150911040e0f060703020f1213021009031104 67
    0x902c0f000046e08c0c4c4804500806042c0090100040340c0d04546501031b200700304c861010143e000303507104401c540b681026045000416013030a50802c0180e00140f0858074030400c103840c4d0700d401c2400d5102e10504440d2034100b040390504400a0507101c4180341e26420b261400915040200e10114180c00078a40b04188030000c4008050048140100104054202e50307110030b00d04401c01410701d850303110100c010000340304240b1001d1000084510036400301080ba16640e26a940b00d080c2900048444000d108052222007000b02d24890700d180964007540e804201400c00400f848191842c00d62054094005d48080001689407240c205400022130b02004619400d03a0405500c0300c0f400b4a10010709034140800c01040c4250514041348400c0201c4007000101c4981c4d5802da680c10111662910540220001601c0140a58003405110944d0040b142c90140d50580c411038a80d02102c0d00c0311001c041d04d6141042d03050016100d01084040d04201c21541d0450312124809450810701c0d0748241d8030358 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 775150000 1250 775148750 775148753
    0x816050909121c0e01050105010201060b0c0d1d0607030815030d0e0f0111190615060c110a09020408010f110306010801290d0c030b0103060f0b07142505010f0801090504 74
    0x800d424410f940c120004101560400d030410340605020302c40c050056080407000f188401440c01150030110108005024261303402c03001359498805001c260301e0514042d0328180c0c241e10b5490007880014426610502c241c03902107014401c5801c10051207009038003100c1407040e03c40e00304031000712a01d03003142c41410f0140250012600c0c10742e0a800d4031158010459280d4140f6804c224200c802441880c003408041080c02c1c04525440c4644110000036200c03181d4131001c00d000c9c2c84007011249000e00f030303a880c150706e60310b014003a603106901020f20b070780d902c400440001c1440e1086102850f14000102c0c80c42c140000000e10303081d018010f550105d00d40d5031300f090f04506181001102c1d0101450140d494007000402c020060020f01281000700303040c4a40781d0000c2d0702c030744a03107010f40e0821564412078a0170b01d4006009508403c04c05ca408404e0110140400413082200304a0500a9066840c81845081640980d000306501544c103100300d0142c1041d0494001106905498038048000340b15641e6 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 775151250 1250 775150000 775150027
    0x3210a0509190b0703020105060d0f020603060409120906020609030c25080a030c0209160f1b0b1003120f05030a2d020415020a0215090a0b04081605090912 68
    0x2c6441025003507000100e1001c10b00207407021a009070001c00450369400103208600c00042030080007003180c06035410040c5402070180d60442800740000851800c0d41e900c04800904101039200840c440010400c089503040140e1a03001c00403c0182d0309202000c0c07000c640c1c80f034540403141080003616883c0e0401c24000c0411500801d00d000455203614500d04006d40304007803850059000725140800105190200d0340600b0000c3c440742e80b01d0008544542c000c0760b180913070580c51110450f054180c100407035642441240526680801049180c0c42d49c500042300000e0340b003010051180040041c00695046000e996000d80c4c0c0980125004003e02aa614000c01c00c01e404070341e4405890318142c07500c800b603010300300b600c101d00040d0100e00749081c0300b80e81c2c4a221500c02036100300100740010181041d000a012800c1e405000400d061f40c403110400100c0d040b68202071480c2d40003240b025141c2c110b54000ba80101016901003015080a40302242c0b2603441804400b0002000074518441400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 775152500 1250 775151250 775151269
    0x30415050f07030302040906060e03120d02090d0c14010c0309030b2805071101090203100b031504060524090a09151a0306010803030f0a0902010201110c030903210a0509 74
    0x42407032030356555103250316002d8001d41080c0201e200440c94100b0205132030b406a85280d580c03010060042062605080f69005240d100c9400e0000864003030240b0f41071515031611720b040381846010b0408401d41000441d03841240d01d0308420741000741015902c004a41c002c10500140d0350420301c0c0d1005565091210a007810880401104005149405464040d0594031460007942d281d03440901d0104520300d824280c904204010f503040c4c01010481c20b01440940c09403e103004050241c445a440e040340645100c201101c0a540d07280d00d680030401101c080f113070021002020002c815511440e044085813880300004e000e5666180d68002540510031250509a0840c0491000f8040c4d01441b0a400c0910402845200e0181c4640d0001080a40c2c0100580c2d120720002c41d8800c1d0701e41c2d103820b2244c01820307032a41d05074155582c80e00040b1410121a0040036020f2011008607520a1900d0034107203048540154400080400c25a5078550135101c0b00711070304640d1610700144c5500002e00064507100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 775153750 1250 775152500 775152517
    0x180f03031b0804050618120d0f02030108061803040b03130c2715080a021009030b0a1e14061311210711100e0102120903040812070503041505 62
    0x10300c5400201c0106030311100640c0b1892240d0162007458586010249500c025a24184407030b0700104540480052018050010b4a5080c2008201d05034200000801ca9200fa0425840c43c3c01003000c12036000a04001381180e8003e0b14010340c9054945080300000c0e000203880b01640000000201c018042580162000303410100b0400c039045017901c40c0c4103440c258034403e0030302c600c7c202144000d40041070740008040342c400001030000600541d0820000c11a81154001884241c4502101161201000c10321900c48002c00151300c0c0640c40c5140005920484411811424500c1c6110048445030b20660044000d4900880d0107042c6040724010301203521032803600b40008203500151108410345018080d02c505e082400c41c0c0c50700d43c800c8420010300c0760f001000350301071992003442c107420341d00041000300383c0400107003040b50350040384000010076601c07030f03059500200342031000790700034845105240a10243c4900e451416a5400d850f40918441e84480c040a003543c04400360181040f600c004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 775155000 1250 775153750 775153781
    0x80313032001021902060906130c0e01061d03030304120e030109020603160e190312050f191b020d0204020d09080a08090106050901061709070902040303051c180f0303 73
    0x81d610a4402d000707411441c0e10000c01004460003007444e50020036180e01550030400601032554031401d0a003007a01d80343c0c604030ba4281c9034406c001420788134503000d5400b801840d5a0078441010000340d481c480e06890490074030030b41040040c000010b1400d1230580d104d0540d41400c00f8480c0700c5500180c01845519000b03500f100000081214580b207488641041c90f4103512031000d000d680700c080c4540c1400e010303d403180d25601d04009202140a03885504e51140407440c2803442c0c500c00100038196500f0641008043c001101080b99103280c1080c02807901c1c0e050070903400d42c04205c9400003a0141c1e0b400d880030f8000c1d42c1c0000c0401c0c40c54031a4000114041d040441281e4550b40001d0003012113904a440d00081e502e0184c001c5418030f44038000d24100c0d1400d40e41c001d00d0034034102d07801c00da100020b0034034840ca00c182100095075030a140081d00066009807126030f00e646400e007180c032441c0850100d01032007a01e80381400b0751041014000040154218a6001458240e4942030f00140b01c8440d116420 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 775156250 1250 775155000 775155047
    0x60102011e051803311505091302090a03110a05060703081b03061003020307031b0c0507090203090a030807030204091d480405040302010c02060c0708031303 69
    0x10403041d0b00994010010f00c2c4003003810703418a030b91580e240d000f0b404000000000d07001a5241e01c0789040c1069009880c0004203610443d41d03241c214049420501a2001180d40400c003141d8074500090700744029407544005502e0903160900044000c0001c3c00018841222041090040d0722134481c0c500107400041c24070f40d07494519003400741c880c1904803001000041400c5806c0c80810091041d40c1c0180c101801002c42c0360a0b140d8190041c1d0070040ca00000c0664178009406418848020114400120b8071a0403c0380c52600340142030640c50b070003884049004100b40728124100161481c3c2168061034105802d4071021001c8019220342d1f88802030300c5040148480300c60b0042980c030300004080030212250502c0350035101d00141e050030300300050440451140c4291005e41812104940901e02a40002d440b410b0000340840300151420740050f90b40d61111882c45030100005a04240d040840702c3c100308640e80c0d080f2047c03100416007012203080501501c1010701446520681110301d104028a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 775157500 1250 775156250 775156301
    0x2712050c160608190b060f09030c040f0c09050909060f0c040e010906050a06081b0d0b030f06060102060c0304080a030b04090f11100504050d140f1c02060c0c060f06010201 75
    0x4400140d45448072901882c0c1c013004c011680d8030505c2c004c680042c10f080d040c46c0e003c803420300075504010516601030080721001e546039030b10791044454070780d102d1400007415031b810300c030080c407018040e007040340501a20f0082c015a6680003540c0342c3c0c003c52840010750203940300142c208550050364080c0021030180741c00802d100790207411040a1b07607001c0d10355040d401d0361100708031030b001d4003a60800c0079041c007880414107075021007004080d00c00e410761380405d60740f07800b8010a103001140d410790a802c2d0402c1060004942e418000e0b1340d041080d003405d89003507041c1a142c00ba650310030140c4001c141a56260307010790035240c83d0030800802d81c2048200107440d006042c10b01d160500103903610b22030390400d2a1001414010b0058805840014201d2001e00c406680c0b000700300340400c08001000e02c41c0742a408428001000b02c883c00d110252000a0101074440020f85442c41c050029200005d041c094000300300e034002410342c3c0c04403641800701c003261109401030b801444001c0040b035040c000c9400800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 775158750 1250 775157500 775157507
    0x5092e08030a031b050702011413030303050a05010906150302030915071e0305010f0902160b0118050a0908120712050115020c0d320604062712050c1606 67
    0x203800351840d181800362459001c81d484c0090381e6018850301281d0244820b0003d94171500c1003541800841c642a0328284001d0003c0c0d915000b5139004030002900e07241000315008440c0141030050070820300a00a0780e0a00b11400d65440c280000d5500f0543e002c0001405c41e84c0402c500c18000031030101c911141d0600c40b20040120407920040c1400c4c064491884c0c218601c00c0c17007542d040311180003103c41d0150401c042c50b0080e500605119001c0d00c00e92044101042211003401c0c0205240e90442002503600d4800f50240c0300001c142178220b9282050301d6010a240404aa201c071001d40d44c050165a07600b0310a4980d403909040e80200186400300104a60382c810003030103c1510f4a03022a200e107041ca50810030485000000280000400555003943d01e4010900d4a50565403840704c071010515848110300d071580844007501c4150700ca0f06d07243d40181400800c950007032800342a40513040215140c1600c299100c046600c104100000c5203a055202404841e481111411990020075a1448001d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 775160000 1250 775158750 775158757
    0x11070b0412050c0a030c0501030e101104031502090a05040b0d12050a090f0b18030304080a0c060909091a1e13030806010f1e0504120605071805092e0803 67
    0x119854843c01012465a2074980002c00489a001c404414180d05040044003c0c1ca04c1510b0144c46103d80d0125181e5000c1c68043c0d8038003071490650342e5850710f245092404001da030507a40c0340764040c81004802026110341c02e00b4403d0710010365020440980c2c0c400804c0d00c201c410200a00102030400b0b90202c9942d004008000c84405a603400c6c1116481d800700c03421f0b038200741c440c5240d10101005441c08000c015010f4000b0540020140c9061a0f501d5a0040c02d2980600c0c7c200c40c04c0c003002006104143d00301c0301140240c00c00d16010880348180d80c3d9103070a80660300315950700304207844000410301c150110700c03049000540c0c420902d550801550013400d40b00c000d02c044010410310b40018406500c151181c56001181d60750314442c084042c8042c0c44580c40c198540f40400a08000c0032900314078075000c5401e042c0c850f290001d1140760001e0021710400c01c07182d160301c0138420f900341000306941c0c0400c06608014000c0e8020542d00d45050300040f0036040c1003484201841116000551042c0440034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 775161250 1250 775160000 775160003
    0x60f16060b01092105010605030607090f0f120b1023030c0d2117160906030c12181b080f07050d0803100b1303030908031911070b0412 59
    0x144103a07040c9100556100c50180141d80307604041d082003c443c40150038034491014004d80002545036126800300b4141041110041d0201d60b1640d410810300c01d442042900400050003d00703201030910088100010130390902508005c40030000c2040500941510320042004842c0084585152a449801d0b4244804064400d015071540100c29040100380118a254441500d0101c0741c0216442050380d0181c4480c00c0c01c20031011030a402101015100030300501c401d03014840d074001c00500080c500c4d440d64000f10308040c18502041c0650350841c44002e0110300328400411f42f411030f9081c2d5169100d40b168042c5c0f40d040a1802443d8007894400c2e07000a5a40801c19101842d43c040c00042e643c1c0350920910380c2040868092101041c1010701070741e00309049601c1c000c5081e42d143e039654195001448610840c20150008004040d0800c1140f4000c010070009107090a0355940c0291401100039a90320600200481c0e00d52180001d0141d4030240100c001d07801e44894a401c0000d0340050556030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 775162500 1250 775161250 775161263
    0x90e1504050a0b12160b0309010b0303030403030f05062409040902190305070614090f22051e0f0711031201030b040b0c0c0a0213020d0e2401060e0d02060f16 69
    0x205140c0135100800c1c00041034810440e44540e4a1800903045403e82c40144902c019540e55040e802d855503042c8000c6020354001e039400b084941c0c02000200c121070300500070921072421080c8884982805083c450444c42c0c1e0511601c1e104d11a100c007040240c520850020f600101001e00303120440c400041090030b5901a80458608648076401901c00c0505040030301c0380c405041c05000902e19100c00340411800000d4403440214114610007460500018226403c25441d0010003120698071000f04052072011410744072582400d07048a2034012020301142d007040520301d110f01e4018001c100301e0700c1c00240c0d40507000807981e6034182094804030913901110000302d800c010810341c04242c02601c001c0080b840c0640651641c590810400382c01402d003507001c854092000c00301ca241140309042003801c01c0c0c0050180d280d44c004802655080c0baa0808140b654084018405168802e241d00e4248101f1b460b000441140c60001a01d83d0140341c80341050381c04d0000e586840c1c10300194001810034400c44 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 775163750 1250 775162500 775162519
    0x102210a080609070e040b0f091306180c0e071b05010608060c040e060f040608121c050f0c03281d0f0d120e030a110c03070501090e1504050a0b 63
    0x80c100015040c0c152180c9001940003c064945807030550311481e0707031705001000c04225801c40b00124500e510708032070303c1c010a0020ac000c030007401400d0060081ca2510310141d050618003940da00b1610740c075980a840d01c002e4a61001400c0d25010321031040c040c0303100c00d0f1511140020f916020b40600130340d0103002ea83c1e01840b400704030000c80e0841500c05590b000040d05100f80d0700c450602003190400071240303a1080d1500e5002860410501c945c0340911068900c1d981e0705d03659034095120484503030341c0e05448a0710700710810603c0c1181107580342d0040020148140d4a80702c090049100542c0d8800901500b0826070322221480d2960b488600f120720740f0307440380180c5141c0240316500c2e0b0003240456180340c0c02c404000c21800d031080200c0e0150035800000000e500c0d08540c0748600d150000070900021600c0500320111405c3c0c108056002010214002e051503800c00c0002054001184500c410030355900c804a01e941d1403854100c0c0601601510070400e81c50070802404c041c0c614880460701528004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 775165000 1250 775163750 775163761
    0x50c0c031918060c120c12020304081203010308071e0b0f0105030607020604030e0d140d02010c120c1d04020c060705130b0c031911070e0a0501080109110f0102210a08 73
    0x2c1c201c101100c01940303951808112640340c1205905c12821504100203412198000007030500c4801d100f405202c1d0300031616982401c09181c40c009404107620808001400104009024881110650380d88074076440303a40c544003412071421101c50700d0000c00702038019040150034052004a54121503040b0110340b41c9444401040e44c948000340c4000e00083e03108810310700039003040000649603d10900301418138000c01c4103258108456140c80100607512105040046940710324032500f00350000c0010014005400800380201090305a2507814440ba081d0610752685d865041d1008180c800055980520f00000024400d41c840c80000a400340314a402207801141c00050300c07002c241c0a0001c40c90854403242e15201030040d1000303102004048080341986000134000c1d040181403090075544e060030700c0c80109090b500d058100d040d00c0d170700d403110140108070001c41d840500706043e1061185c0c0f9580000407030403c0d10004032007089444c0b410700c0d889454461001400980010f83da4140541c542 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 775166250 1250 775165000 775165037
    0x3030b010305100510021e0c010f0207120b22060603060e03070f0f0501022a010c05181e030106061707030606090303080c16081207140d050c0c0319 65
    0x584400c3c00010400c0c1080c01641000100d000040b07020b401100c050034030140e600a5021400c946001082e007000001c601d407940c000007070380c0c400f070002d001500400341400740510186003802c40103007180804802150502003a842403440d8440481d0303500c0d040b040742d0b00b0b0541c090151071000b00c80040ca42201072941c1540401610103070341c0e000132100c0d8241d2558441d03201940741c26409850b0b6541c20030a400015109414500c0909684018501c0f440740e6143c241e4219090040741609110b820040c0344914004115444000380c000c4508a21104120410b030114004141100303030950320f0414003180e9180c12032041022440d207144030030100c0ea0341050480a4031140e120b072300046420400309200184c001ca021950007002021014140081e0b003102c1500351070340c031800780c07540f000c002034298501892564040d400f998a003440005651480e8071920304d4480d842880c04410b6960b00421800c28810007220741d103d0744071040307075110594803036180300f030754040059040031544018100c0040c116 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 775167500 1250 775166250 775166261
    0x91407080c09300a0c0f0602070e0106030f060306050a090c0f050d030f0302070b100501110f030301060302070f080406170a0b09160c12020105010f06021f0c0207120f03030b0103 78
    0x10103401c1d04410f0354038000f040340780c09800e014445401850510b4045406081000300311090160100132220351825850466210140d0054411904860340c00d02010a813040c0e481d0450f21145000034040c0c40e0202c0e003400602e12071304018080c0c0d051a0a204803030040750041400355004249030700c0001e07515a48500d8071450740c802c00307812416060256010a00611030f101c64100c041c00c02528001940e034500a411004540e0152410b50710641486070b560301040500800703581c0801400300d101d0f0710542d01e603640014462007081503000110001048441c62040301c0081c4c2c080038498031251545000f50440c6007000282c400c8a144600150700c22245020781d46240742c016151101030b4942181903c245031a141c5104144140902550001404001c8904180041d5400040d641d410b042ea500c0f42c0d124581d109030b003154040301132186030f030101c0b04020450020100c0002a6a684880241d05000095004444400e00802d051050080092800d071583d40f2945c1c00b000b480071500700540c00c4a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 775168750 1250 775167500 775167517
    0x30915030915021c020c06070f02060907030803060112021c0b0604060c110d0f14060108070b040b03070908061503010b1c020f240d0e0303090d0513091407080c 70
    0x148a40381034201c0b00990750003080340b0310072540c41109580002c24048241d9005010f2240c00b039100c10100054590300002e0048541c0ca2480600034034103200448995076015408080d00e4000008003080b2f050780141005041c0c41da9100b41513490340e4000540211300301c0c1801e000a106030401503410600d182003012078064404580340c80c120081907440d03011403100d070311031025007108581300c4400210304180c203400c2d0f210f88508244946032031022110350a0071410b2340007401a03801050203004201c0002c0030f903401d90b180c60802903180d9036419000c6888000661200781540101d030300340507898001140c06404e04c0002d0300240b0076840e0230024010925014050b40502c1c41c80880c055005203000341704082c10100007001004103250780c0f1507185005c541100d801c0d42a1100240c00081d07441d5502445424001c00343c050750552504415254071540c44044c0741080200c00220032044181081502d0040c200e0550200115101c00c003c84800010684112001c5482900010a030460f07a401300c03043c48 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 775170000 1250 775168750 775168763
    0x9030903190c0503151f0306020f030a0b04020a021b03030d1e0c0509010e12010902032a03070303050f13032102150103050d05071e081902010c0801050904021305040309150309 77
    0x2039903402060300c43e02c2c121b15042d80084213900400408a051800540350394143c0c07a0a085d41d9040c02c284060803140b01c041c00038001c40c0180445c0c2e940c942c0208a0400d9220003584a00314180c0a20019095200d0f4410491305030b80307400109001c03a4006912141840c4043c841000044070901058401c0e0003001415400a801201140450704112a404001ca20010300203e483c05803903000038207143c0030303603150030220518081c81c0003045140641c0202415060700545091421510b0040a901c150403141400440020b203062081d401c480111009680014409034070b4880c10031013880076854015064010710450022112096840c2c94050480354044000c0140c203640380d409a07525086498160382c940e10801c401a802c080e4020040030f9188521145030b550500c10581c46000182c0000c03d0b0110380c9421f04130503003241c0001e905c0f810344204984200c0c066403148001020000740490061509092101344010180c105407100207a07a08000e04400004400300c0490407602c01440140a8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 775171250 1250 775170000 775170043
    0x609051e0622061a030d0306150813051203061206190e011410031a0709052b060b10020307260702060f0a0e040506060d0509030903190c0503 62
    0x144420004580103040c00c2d900d0b116848403684403201140c080740200d26a80e6582d641d144540d00e0140324800058050341410404503003001109442640d4090805c0103010170903002c11000489518245444c1e544042165081c00b01201290309580050b40c1d8140140c04c0c4a030542c1e01d001010500728400d4108405410109400c1c00c540c0d8041e00c003400d07030801c841d584ca5088906c06800030711080c0c4a101c80d078251a40d201d16600e400c500e032020892004031203100042c18446025889414402140c0088540c1050000d0040c20208004031061003001c0048070044104100022904548010303901100c0f18040154228000c0c1e8582c030030244d0040c0600100100c038190f01d2041140d000107030700640000c908003190740d800301d0125444106940703118140411140b20f00c65010b8a80489002c0c2920207100c00d0800c80082209401a40512400b60740c881c030009038404802c00076031f011400d0042c1220f950f00c22005000c501e580818a0644540b00250008925824000b03107600705403c564080054 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 775172500 1250 775171250 775171261
    0x1c020309011e1706041d1510120311030d0501030f020307090509250b0c06010807090b011e120218030601090c2c04140703051b090f0d0602070609051e06 67
    0x69641d0082c5229070059490008086d010344030282c81d844800104018083e03290003d8002403c840000c100d81000c0c94000400e00111a0b21250100c58552500300000c99081c01c1e1001400c500520a43d881100c0c9404000400c0c050f4141010201030300030f5064400040d1942e5544060321000c803800d402e40c1c2c0c415002380900780321a40441003041d2040c14129801c90300d540400c403482e0b00c101c001c1800307580420b005005543e42030001c2c600900004504020642145001030705d0041896030804640c0c51601d01c841c94280150440311415810080840d48c3e401c0315041c0e0742c1e0840c0e50500c210302a02c54240013065032038061103440d034260019102c1220000e014021140424070b0414410340700049403406606075143c2d80240d100700105000d1500051a02c0744000b812140010511000341062285454420720301c901210045501654800181c0d03a504004c51319100380120000c04007403000031400305010141c1d0010b40c806201d441900d45070800f48180b106090003101003000180c0107000480c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 775173750 1250 775172500 775172537
    0x3080d1d0706092d0806040210020c0d03030e1c030e010f0b4006090e03070c0b03060f190305070f30060906061404140109020c1c020309011e 62
    0x3516032544100301c07080e20903181c40c0c21340c00034000c0e8081c03c015402003080c481103146c080000c1c9036040c120300c01060007000410009060350030000c0050306060380d80e9602d10f5903090910080f08204824650705e1184800da0341c0080052070003011010482d4600704c084503040360640103da52540005141030084000c000e81807540d600e41162000c1c1c0000300d01c0440c24800e203450320519894540388800913989191031190360690380401c0506a65070070070040b82001406003031155080d40d042081c0baa0b200e07925180842c09081e000122a64402920600d0000359029802040d083d64419800e0780d02d455070b20801c50003110310a01030210071249260039440d05000c050760903001300c2c1c10000b000c24500c00c107444400840301c032401c083d45c5598a17980107000800003265482d14950f0141c404014240001307982881e5003038180a103002d41c0390000345900c11031208000720101410700ca01140e4a0540e0010065542e80c07040300b2560109040042e20440c0600c0a2100e0f10224810303125210594861a5100c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 775175000 1250 775173750 775173779
    0xc031515030e0a080405031204150c110a03290103030c03080603031b01020304021206060a1e0519061b0c030b04020d05030316020606030c0f100903080d1d070609 71
    0xc40c01c15039240010000c0030400c0040503141030140030030664070ba0401c000d040c1041c003620182480c2d4581003104000c1103e400c070600c9043c1015150258800e01e5910b04003040f4138008172410b03800b6a1401d404800c0c484010300942c0c40e91300c02c1c1c10204480710403425a40840d002488040c010802c40c0c101c07280400c0c0140d001e03640c13281d0300405480c03502c981020740300f8081c001b0061141c8940e501004001c11410b02e0030344144d510700303014003e0880340381081c00030700744000b18065481c841d545803240d03501803404282c9141c0076100c020300c6516240144565400020702c035110780c600085a42d0110301c05090110003108081d6040203003804e00a0841c0c0341d00310001005072003260495132209082c00490300c148050340c00f88010b11200b6032404485500289807901c0680b41c580300b600150b0700d0283c0c3d55a140c5114152a5003600c03090040109054295450801940041e01c3e80390001010300480500354081c10b4083c103900804028005c84130b009039a02c68544c0641e07004140b102e401440b5011848050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 775176250 1250 775175000 775175039
    0x806010c03020304080d030209030f210f070b181207020a06051b0a2009150420070c0e01060309030e1504080106030803060406080a03050901050304060e0a12030c0315 73
    0x102c84c6801e03910b202003450210124400740000384d01007004003040c0b03000d00210840212280040c0302480078610121181001c5e1036204c1c84084000410007880f0540300103860070560003002000305880e084030b404821038000602c20300140600300017032020b803450350151161150003500000070242814001da03015880303401e001404500d24800701000f640c0410035010810b2085110780d0f61100c41c1540b84d44c0645c22030b000b0a01c100c00c003400300068240801109042c0420448020030028240c074804110039406114034103184c0c0380041c2c2d007400d0110007000c140c104c403030f854164030080c1e9072200100e04541c0078510040c001072191800340c1c00c46c45c00304a034822541211076502e01d0640d03214081d5007150100da01c00c4956860100c1040281c0ca0f15105020040c50404003600c5401e01c0c694000f040c0d4401c08040c41d05010010010a00740301d100d40c40400307402003d0342210b0b4005001e044c000181000d501c08540000d041442c48102c0601ca4020400d0409025065040312030810102d5200c5840c003160 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 775177500 1250 775176250 775176253
    0x3090c01180b071406060402041a0706140115090614072a0f0810200d0b0603070806210a0803091c081b040605030406050a0603080a2109030806010c0302 67
    0xa0200e00b000000d001031519522548030320076140c091040701418101d005290381c1c800c03441408100f00c5420780c22031003103500090410041e0f48a1451422400810203290721803005500f02c000400c4294070301c554a81ca400150311502e4042d03a075410300701c1c0c05000304410180703140014003c1c071000800701c1140000400051409a40310440354043c4d607040075041e030060315a140072882c01c0041c070f0014040030329680c4802009025003403181038500300042c48000b40070050302000460016910641d070040c400c1420040c0907554078182aa070080201e030045c0c403603a20071250b01200c0800314040c00b200d41508107040020303220203100f030b0716004420b8200078000c12241c010200c0f1030600d040090140d81c0040015100c2c4402424030075881510b000482c00c0318003200781c1c00c000500080380c211065a500c1507011001054a5884404000180016510040030007c01017041c02115030003a242008420341081d00710892848018894191259058050041403c40300480d02a521409010354014007a00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 775178750 1250 775177500 775177547
    0x70b0402040f0f0903031103130b2e090b01170105010f0311070309080f0f10050403020a05060a0204090b03060609040201030207050312072114010626040c030b090303090c01 76
    0x91050314140c401c040f040603950701a5204241d014400c5041d01c550780c1002031304516000780048914076501d040a482e1100003400100b22103401101c0c001740e03100c1d0081c0c071200441d0300e00d44083c2d01801401900e001d9420115a041a5481070000749145c80c1081012540e991910005450120780e11103200c3c1095210000c3d12404000b0200a01c8024460b07030340e908a032441c00c900141080290741c0d900020342c10202ca02c841f00300001904044035243c500e00003456444a00c2c00360f2828140303980040c464024101000064902540a0400c0310314a040911130444520201034071088111803440c0d0000704907012030099442913020780038142c030071030450b440c4c50011131071911000d0086403014002000e00700b400201035180c00705a02c101508510901c61044d520040c011900350500508040008090f1030b90702100340c800442d40801c0102d101c0c0b840b241400e0070311030404840c600041d1381814503800030a0240300d000046078495090a4040d00301c15051070011105642c040e1401c4000c0d00162 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 775179856 1106 775178750 775178771
    0x8040306140f070315051002010b01030e03070f0605131403041e030b16090f0e010f17060114040912050904050f010522020f1b150705070b040204 64
    0x18280171401e14200300c06906080241d51210768000d250b6010032803d41d4065202c060024001c1e07070240400d0b140a54030950702d02c40c100d4010b10170307000500c4000105042d41d22007a00180d50550542c0390304400d441c1d040295203154001d2045800010341080462405100880b20109501303600c400c0c10306e9600d81e80c606e050002d01000c15490994402c1c40030601c1003001c20060f01c181916015403035110541c0351400c034402d0050b02040307400484e0108120801c20b01e0030381b12186c01c000500c15603007040703101e0400003041c06480703030820707228800c2d031000880000b2300340d9080300c1c250303110f40d2501c00c0c0b14200020740e00c000d050340c290300316120014172650b04c032088407103a000a080942c0854888401c3c2c0c2030004d01c210a5030300c2d59190041000c08140d8500242e4403003d00a001c22140203482802c4142918001540c066000c00c03030801c80c0f0000580d08241c02035216000130000030b00041c86 = true := by decide +kernel

theorem cover : BRFrame.Cov 775000000 775179856 := by
  have h0 := BRFrame.cov_init 775000000
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 775000000 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 775000000 ≤ n) (h2 : n < 775179856) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
