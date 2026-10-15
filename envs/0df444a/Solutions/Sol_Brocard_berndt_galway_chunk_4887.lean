-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4887
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:03:30.566983+00:00
-- url     : https://prove2.me/submissions/76236597-70cf-48b9-a10f-924683e794f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 878776978 ≤ n < 878956834 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 878778228 1250 878776978 878776981
    0xf06060506130f080d09030b0a0f060803340618290714030f0711010f0c080906010501020a020d29061009050603010b09030f122709011814 61
    0xc50b40e40011091003400039a070312042d40003d1003a0041a107414035a520b0320b0b01c00c40607145480d0312200b502c004284400080d1348440b1844c65040c80d10850740036200c4c04006580f41d0b05c464910029400341307687e0f03000750003007084203070540050030303072025600164007070700104903100d022490050701303121500010310024546c542402450000707411a043c080941880d216152241001915030103040c90201442120400014900300f00101c92103030881024900283c01c040421199803c60326500d100082c0151a82407800e80b450748000d200b0f070000d0400014000652421340013075035554443c20024000d501e42c0800c4402d0104521901d00c401c43c80441910114a010b0700c40c400c20300b000c0b05ca643c442c00d51844c00e208024441c8098805807003014144501e180d0030b200f4001c1c1789410030080d07560315100702c01c1403009600c014008403900b946285407040e11003039941e0140e2060341c041c1008c3e01d4030070114415460700b40d440c00e00d1181100c1400b2600704c1c0c0984c40b503180c8806801450035400784136801c0700 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 878779478 1250 878778228 878778247
    0x90905030306090106080103151815150506180d15051f0603050f0105011b020a08030d05010e1605030a060312020a03030c180302040f0603050d0504030203070e130f06060506 76
    0x401984180c804465050907a170b2070f02000e48490b0400c0c0000340901c441c5800c102005003c1e80d114103003003680c41c210801c100603c0c4e504c5042101040d2034094480362a403103420240b0f0000c4c8024805010211603190526101841950300480e00380c85403032040801000110034401440c040d0b1b840411400303420700440c82e100a004483e900802200045071034204000540c2c00e100f03118680c082e03400780590800b542d02e007500442c0c080c103145004004070a1462404401a40c1759010744004180a60240d40c131400141014000c54005030321000f80b80d540102042004003030301c200d040300300c41103042240d00e81c1c90300c2e2100c00090006d6000200b00c080c4511081010603000185c0b985050302c20b40e01401106008142150f084040410b02e80b2440c200540910051915402110045021120019007955662509890b021030034030342e900400c00020b0180b0035800d082c0280d2001c5d0100c010741c980c07107003803040d0a4075034a120f004014041e03580000b182001c0000c650007800050400a120075218004e0f030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 878780728 1250 878779478 878779483
    0x1012020d022817060f152b06060c210c1a19020c0c220203011715070c02041e050106050a112b14070c05011206030816020406090905 58
    0x15824402186403d10b1485142940e404100d00c1010080e248449103014401817026059442c100104c80300700921200034504018900e840c0e1103c02045624030340c0120241010031988a0f4000008001304004082c3c08200703a61802c820152025907910174000500e80d044030309080c00800140840121032640b40c005440302c2e4680e02680c0b103901e165050440030b4141c5400ca2046e6111026150031100506000346403803501800c2c0d4072201e00481c152007055040030070880e03000741c2108107004820024079000725000c02018445801610380b2a00500b0900c90141c8100e2540000074404c54031034104007070b94120240c001030780b100d41440900013075849400140058000740c00890001e00000e040c2c04030284001003900600c8a80001742801905409040c203000c4400802e034410b2002d182d250b840025640402804858000c4040d14406814400010031004d24004001c845600340a410b10201d2031080440300040940d10040d040d80d41c0a202080240040da8421280c0500d003101302814010301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 878781978 1250 878780728 878780797
    0xc0306080c01031b050c0c040e0601061704051b010507050105040c090b060301030c0b070201180b03100b191b0f06050a0b01050c1504170313050c1012020d02 69
    0x6002551200c1207404011412550000c0f2903041c14000382d54140ea0290080300100701a00540c0140c50458949030701040c25110310000000c941d90142004005c01ea904c100700000400c1c10300c14000080c00c05031102c030340d07074000d59008600d210881492203400782e02603011502c0c0e01c0d900030000d11961815040c42403c0700058400d030940507040070420069841c04001300c0e416a58811000751607079040c5600f48049400100c0101d05000c600350790b6880141c0742601c080001c102050134136079280303480201b582e4107103039544c0301c1010143d0034081d8030410582c81c1d0340e80c0701d0030420b0719003c40003000580200341c3c5030641c0c10f40170f004140c84620890034403100750041486254091818000500c0f801c004564601c900c0b608114103412412209071101070244d003180d04603000d0010000443e0300b03c03800c204107900c165103030b0945000a050520810005002401c1014012242c1c01804011241c000d80072101c2004540340c030503400584200390502035070503a50006640960980700c0ea4540075115416083c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 878783228 1250 878781978 878781989
    0x180109031e0c05062220040b060c0a0f020118091a0307080601030618080f090f0132120106051b0c152a01090c24050307030f0c0306 58
    0x280c0035044041c0c40c0c002c1c0d8410340b4465005000b0070455454202c0c000036050358900844039101503e00100106d41c01384414480316400000890b4801e400303c0421003161401c50a0700d008100600c10610b01070808030b1180032241e000303882c410342c000c42c81c401242d0165003c040c0310000c01401e600401c074000030380d0025468544903190700d007032004458201644c41e145031144040e2644a40d0040c40044c1c1d15410003c24404800742d5070f4030010055a9980d41500001d14441c0ca031080819100e02ca4504040d40d462801c100f07090942030261040146401d07808400c8000701c14484c602a18a8000d14030380885d1015044103a0f003183c156101c803401001c81d441071803102002d01d005080f6411010340425203040d06600288111030070701c0c40603c80b020716084040c8901a102d50748080c2c4c0c1407030450400389001100d083e000000c89464520700382c42400c0090700459800c90b600130760a6114034a900c0401d44a20b92400d08035140e03650090114007400c24020f030f0341c600c142800790008000c0c0c0c1580181c410340340f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 878784478 1250 878783228 878783267
    0x60f050a05060415050f040801092405040c0614090d0506090607030c05090f04020c010609020405040c14122703030a0f0917091c080901031b0509010818010903 70
    0x180d07128100400c50185000e014a85020b0200344048980203400074141d0003a07040006007040d03034036844d50b82181e070490815941101003d021070900d0f40c03803030a80070307014484e04020011810503444040e42016140681c00c00d026558038268103070003e00b001c2d994600401040e150042155180071034588100780c4890480e849040c0105090702e00030700444c4035950300d555820342820500c004000307419801e20b030041c0e04260300304220707007140c4028022100600840c103400b5035524581010b110896520910202c20800300346010300c072000c40031044070349901c41020030207441c0e180c003840c41d280c4101c0070790400152206460700c41040023010016600c90207032103204008102d40305101c10142c07032403294010002c40c07108019034010901c00002d0191b01c000505201c42100400e10825800075500740d060b54880004100d621032586d0600581504403000150b090390b240e007990010f0250700981482034144440000001c2e4540c29000b403030f88006803544024008041d040c20040c18603800340d03002114a6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 878785728 1250 878784478 878784499
    0xc070306050717060f06120a051b040605180316090b0a050f011b03032c0606061c0905011107030e01021e0703140733090f0303051606060f05 62
    0x5409100210001c0b0510300b080f820950321a000c0160040481441a074082d40c10320401e018040e5040b922403040002042c00540e500300114907110f1b0000344180e1708592034040100788200351b0700006a80040d21034200112011301454002400c111b0f0b0000403001d20504640b002a02103842c0c0c008410340e9209031040c950451319a014403440051024115000c40c10103454a007901c800d0030030200010303000c0c0c0b900040c041589281c03004076405080c0c0d000e012481c820004c1c2003c050510401c0c0c0c11000841e0100e1900c0712840c6070521850f480c14846c900c2659030b02e84242031001c2074001d00b040c0b042c5030f0095a51040b1502c0c01421b8019003140d0103006100b0081034030700d1040c540002c1000403074500001c096003807031a501d01201681d815140e08250144810021300319640c844540c07050301411b8210054990035009882d00a4045031341d660800407010b60810070b440b400d500c0d0000b0f40c1c3c0c042c98243d641c0d120a0303119144086030940008c10745403a0080009102070140c0390f480540c0d001300d812200c0e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 878786978 1250 878785728 878785741
    0x90907200106050604060c03030905070618090c0c120504270b0306010b180a03050303010603290f04050406020912010c02150c1b07080607020313080f0d03020a140c07030605 76
    0xb00e5800f03001c1d0340d4121200b000244002c1d4044c02480c6601d074824038003c41c40640075a1001d09011060303016001180c0401410000925038140040284c0780120f020041c4080c0e502005140516240300500b030a4685108021464441c10456024204c2440c0c1201c0001184400f01c1041070850020b500741031a00041042600c2d02244041c12112181a12402d1400c0c0ea110064030340e100380b0400703503c010740d040008006501800610700900280c1c5002803416107891a2800c041c180050124203c6041400088280d980003401000fa56041d980010300c6d6690b0300d00342000303225086100d540f1440c10322444810382c10540003140f03240351075403c1d02d42c0000001c42140c1102015120801b91010900c80510320800c102814080c180c5604102c400050b070b104030590a185081e1080d40040c1c200060b048a16003118541c900149000c0004000c4450410709031611a02521520410150001000b0a002d0300c49e9406140521255078020755498102a00e88c0d03541d4440c1c0701c1117404904100000e00d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 878788228 1250 878786978 878786981
    0x606090612020c07170c0a0314010605150406080a0608011d1b061603140c0109060b010c0201050a0f032909010b090603040b040f0c060e090c041404050402060909072001 74
    0x1110f00078000070a81c06080135803040c1503001e03544e1a00c183c1d202e0707910350700841d030f8982204100440c0100390000b005c0c1900d00d885070030b54416030002406852078450068040c0001030072038045500b140340034000340c0c6950003910042c0c00940d2104e000c541c208600030700d4040c075200c0d0b00b0300b8941000302110030132a4026081c0e4040b03100c042c482030707202006120219140c000010b417100c84521174039141c44c101981c1c0c8106241ca8012129480207603555450b10403c1001c2d038480c4403031035030090030003280d2911540c0c00242a40f02e520f04030800c00010344400c284050181c0c000a0600d10355655180340201450002007880f43c0c143e00c181e1251021a00000700f098150b0111a00c4580240c0068510340d1946c542038003540028004886440c04024074030045640c0804450241003150741c2c04100071100402c003c0c100c2c0c00541920603202c0100f00402098841c280280402d410545001c02c00760b55500020303180d4041c4001103900301c2e2090082064040e800604c80038910a6a55840c84c1d90305000152030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 878789478 1250 878788228 878788237
    0xf040905250602100207062301141e060706060503031b060606040305120f130e15010206091b01051b0c091e060f06161101020c06070c15050409060609061202 69
    0x760b00010b0640c024007000e6001080614010700c030208503180704001803140d1013921016072302c9440d071728001405804005190205501411100c40d02c0781c485a200d00d8160b1006410380610480c400582a41001390300e40040c00108402420b41c3d440e000340e01800b0051724501c403110b01e014068140021614545001690160b0781c00100070007030f1082c40c0700b020003558400800340100c1d100c14045900d05000c923a2500d40070f491141858440c0d418191604500113055441050664100320100600a003000491600051030081141c85240b165801645d881c401c41606500c40c1d900d842d04205401000507241d190300800752040d0945688896407a000000c0d0205070303005a0b41100042515464030001d07526035000018003507860032040074182f14008460301811654400065809a0709607010310118030b4605054958614007400c0c4d130f4030070400e0780c070318043c500c000352200e000c200c007640c41101501d02400c000d036020802282c58000140002146115002c00541c0c4419050030520840c000e58 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 878790728 1250 878789478 878789489
    0x6040503040312090f06051902030915031509152e0e0105160c030b10030b0429010806190603052a0402071a0a02070215090f04090525 59
    0x1035041ca425680e60030401110308982408011000e03102160707058403109014010400d586a1594803500c0440d84102c060000d584030056400c1400000030503100c80030003441681181490a569a0b43d000507c0980c000b11403c06820400b0403042060b8499507002c0000c40400455520178040c03000c1c6045400aa040500040c110901040c0c0c505118001d042d0210030070320504009051244c9e5101441c0c0089882c14256506420711800700180a0110325182e00030714001820b84074035055032a030074201c0b034002d000144034481040030300c041c00310100f000034a58030816800d0380441d69904c0d04541e8484041c1c441e04a803810603c0c100504641d24803030001103c1c2d1090103021824803620600c0c2c0f1012084c88980c200d5568101c01044030b58852008010503031040f00c060407101000311b00c2d540025401055640400d10402c0000090f03581c614a03c88607180c94580140c4da4160107011542c5110300c001c100c0e821609210882c0d04000000c65040800030400c0da000140304282c000561800510b84500c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 878791978 1250 878790728 878790733
    0x6030f01180f0c1203030f0f20030c040308040e011406070b0a05060d0b091f14040807031101020406050903190c0b130e0117100c1706120708031b060405 67
    0x100800507005101c2610440d020f008a0150543d8598156811050b130b02c00c2240003940d06c0070b0244d40328049120f1043d00d144a81410030040d501044004500c152050800c40002400310006403c1d207421800c6401459002d0a05500c46503110748140d406030b801c0c0a03000b400c030419405824582007050580d648550050600801d035101c43d074444000f000050102500140950740c0e280c041100d2100050082d00e41000410310030780a51041e10310207940c1480b5845c051b04000d80c80980700504284941c01907003080341c40e5990341451900399441d0010084038a901c2d40007040001d20340760040701900a00c1c80540c140c8405118082160f03203210380450004140380c81620092010506440c007500440c070701000e1149000d82c5902d41d104540b00b09911240103c296002c80c80c01c2c005041c81039109030001160103004140d15840c02425200101e40d00c40c56542a600005000d40d840c4030b0020f0701410124283c030b0445440306030085e02e81e400306a12a000d40c03204507000c42070103030020380c03140300b02d03081704c003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 878793228 1250 878791978 878792021
    0xa141204020603130f05160515040608070903050d0c0303050c07021503190f05070e0d031704060f050a0f05100f0b0711120c01030f0c12092906030f01 66
    0x208040c980020b411380d2000075650405800255141054950090088000f003600321000c505089101e4841d404c0b00740141901c88003400c40b0340c11001520165040b03820443e550741d840840172641003580b944082c11900c2401c50700080c00d49c100c40380250150180c0e13024000360342c4541c040d91061042070700082d00a240140f25401c20105903000d190083c0003030760004848800150340c0f2056408580c000003501e40d5580501200a80018134604540b20650317519540c42d10030b842c050100712108403800c8038440104005801c05c98190302441c200425070700c1c101705070b0412514030700c0100088130303540200a00e0400410f0340c03103001000c80d03401c4440c00c1c000300f003c440c06c014540109800125044826840c218808482c40d03a41c0400803c5d0400c582c80105130340140e10700010142e54902c80e9110142c0d140c821001105584124600f1b0207104e107800218029580b0700c3c1903c5401e40c0316190903c060f05010307240006000c85a08503016801c00c0301190500f0420010380c03400c85651b036000c08004060b104 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 878794478 1250 878793228 878793233
    0x60602330402190b030a0b0d0b040b0c040306020406030b0f060c0c1c02100819200c0a0b15011e05030402011407020402040b0c010c0801050a050409050309150a141204 73
    0x400c465440740c80944184482c1000b403c04901001c4a90003545400700003204101107a1402d1180e1a1020411030b440c00c03003a80c442d281e035845403002074030181c03040c0c40301b07400140120610012070340150350140c021540e039960340c03d0050044c071414005030320404040d01c80038018900078080c1c6144030203440243c000d150b2107400304412140c02c9012815041404140c1002590740c0700310070341d52450b140e1110182d0f1700d0700400100381c141d0010401908145407850a1180300300d8003011210208001040c16030b0b81e5440c44480785010a00712000742034400c0c01040080c150003070403a844650b2401e80742c5000d282c1c0303c04614000800342d440c000e00000c505000190156114561908100300c0d03440c0c50b9883c092030f81c0c01045c00d070b910075000001080390005c1d18001ca60400d00c00c200c40088203242652140d41840002a003204980c40794920541e01e0700c0c540b8042c000248200d43c3d102000415030103140c0b8030310494424540103080000013003541d620302c07c50301c0444402101d0001560540f60039090b40c555 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 878795728 1250 878794478 878794573
    0xf14030730051903180b040203070b040b0a0f020a0209090123011505030606071401020702091f0e0901020d060f03120207060f030f0e0102070318050f090f091f060602 73
    0x8403d4000c0540303c520402d0303a11420044100041c0c0038083c992600d191600507d894002c0c2d03644120031000040204203c00040d40041d9281c10001e4503104041c442c28130401ca2070070b5803404c0060f5010802c0e0003403002441055101c205c400c5149004240e803801000340702100c000c42481049118090000400340c5035101d14011640607100510382401d181d00798541c1000504003400301e240030f84d80000d19406510704440041d90140c075038500024254004040141d11116078414540c0c0d821240001c0340d4455000e4050304c3c4013102000341005000e40d52101c00941428a220948102d4450508191580c2c40414080141d4600d83c864509102e86500103c0051a4510112419551760148514071060a0005002141c042d548905c1283c1031090003240c0c03423580d0303400184110304070401a00c0d0358071400d07009584503072404407140315a0351b400c08030f6003040008040710b940d41c00d0031201c0280240d013907800b010a580180d8203c6072421183d03074401a1100752041140c80b00500c0e00021910030400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 878796978 1250 878795728 878795767
    0x19030605010507020f0d1712010801110c1c03020f0a030b090f01230d0803070305041205131403070509130c0e0709120501110d0209120a030c0f1403073005 68
    0x38100201d03420903034814690148c02510300190104c03003210040200c12824000d0282c00303405492880d15000c0c10085242c1d882e0712055041d641c07030000c00e03041c0803100d010785d0550f80415040e0890a65072445540020002d01c1175040d003d100300a8840410401201c100300c0c1411382d01242140521945d0080c50301000d40c1c070408105920550420080d00003074220310155016031013907100480c4c18240ba2500049110f4403110000401105015048501d0b007044100c60403144112048d000c5072845101184c03d00003035030001e40d00800002c0503c400c000040203a0308499000343c2d4891030494071250110034456050b100000007c80d2810107020880ca020785110304140b0400001480c0d04541c0e1844a44d90000031015a046a0204003092681021864107074917981450281010300340e01d0b60080c000e59010b540c040e010040324100c0307404100e00a010040c20001a004132500d441c10340c030304045844045032544c1200b150a000d0700401103c3e50031400d1580c1c480380c1758142480c5002d8148821820b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 878798228 1250 878796978 878796983
    0x2e0b15030903070c0e09060f07021b03010e0d0c02210a021c0b0405070501030c1716110601030b04060605030307110105130b030c0a030608160302010c020a03060219030605010507020f0d 81
    0x410014000042c45044c005401004005a8040c0a15040c12028100f480091000d6201c0349030800f01b1000300d60118200c8094141390b1041d1070307800150f50219004054102101c0180c0c81240c400c0f4002c160856119103626108484d10101403007010f100c00505441407030418041d0b4801d0b000700c40145003044c908040180b205a10042c00c000c10749505c1604102910240e609802a407802c0c049540d15004810303064810741001d04981d10100c07510214807a0082817811070001040300d505e80e4030322507400201c843c485403040343d48550b1607003000d4064a0007a01d04403405482c1031400101c07801c01200707035002140c2090b00c01c00c004290f940151102e9210401492148a82250200f001c2c0e0071312014500070610400d169482c0c2e409010702804950103a0000c0070140c0c04191400e466074400c0700381500340c0b6420b20300300340807080b03510108000800640008002030b00100c0c03e400c0400025101c11002d49941c0e5042c00603941c1c80005541500c14080044e40210f001c041d424030a042c51280d1450380ea2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 878799478 1250 878798228 878798233
    0x712060b0a0b1201180e060a1410140904210f0f03060303080402012a03020a061503080a030e0319030b0901090b01050409111e0a0f1403040b09010603052e0b150309 72
    0x3d003031b4100c2170810b0005c0310304c10410307617840300d003881d14132541c61000e603002a5030b064004980c0d0a280c01220b640c09082c1c2e91600c81c44020300007401300100c907502002c40361740c100c0702c17108100882c600c0a4040e030020422100000d0b03078030315050307404d0340300380100b0044a405031203100b1180c40c0c980044542a6150030108500d0800b028140d0040b00c500852100301406540a4806041c95250110a079400500410040410f43c0000e01c04282c6e40c42c01c0314620140c3d0304000a41080720b80100341107010740550b03030030190b51741c0c0500c1e5003031a0540c2000791414412107440c03807180c4e00c4500351421200000152070000700c01340000c1c440071703501e1350100000d410505d2100d81001c0003222001c1060806035003900501c0c07070214030401100c3d0481880001d1400c18246003540c0103444207000500d000052026002e4400400800c421310029400500510b400c001540e080c100480258522441d0a20003100c024180341c10354103e400d0288203042c003402c0010010340c00d00d036548c1146082034001418014290 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 878800728 1250 878799478 878799491
    0xb10171b0f040603320604030807120615090503010e12031b0c0601270501053d0815030105060607030305060a0f0e0711010216140712060b0a0b120118 66
    0x800054651401c181c4034403000c01002001d9113402c1718410184105412607004100b4080040d822403c44d0342e100c8582c0c81e010092148812082003c0d000f60792000d90750703800a01e4415442544040d884003a5a400d50003445010b800701c1c04103a407144e145992041412007840070607c41c0740c0006140401400c58040641442d07807100c00c0c00c0c100f0200703074800340c40e41c6d140f00c19504c60000400b2242101006150041256601d890041101040301199200d521130110512031114250b00070424041c00542040024250012402030b00c00041910076074105600300c0c04503002403405000f900c0c4142c10140400d42807001566041e400b808020f0050755001e010583c001c43c09800c1020200001e20020406000c075080c115070107006005180c0700b08900d03034010000944160074402c00d401d03807164420703100b000c03211410307002d81e0600c0361175040320118000050340d000c1801010381002e608048129801c200c025502c1400308941c0c828041001d0f000c1c500e10004002142000e80c5a90102c2603080b00032990 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 878801978 1250 878800728 878800733
    0x903070806010b0301031110090308030c04090c08070219030203190e06030c070c05090f28090b0114090108060a0c0e060f1201140f06030406090b10171b0f040603 71
    0x10141e090b0070140702014040010401d000c640003458150365004d0b01c810802c04d00d0103034028216025400b010303203420000030109554981c2c0703408440090200c1c4108121211800c80010448030080c1e0345400144643d00d08804041415516410106d9040d001585404403710084911030403c0b03402c9814000400580031003a15514010741c800e2000c0340321165034420302d2402c1040407240d604260b0181e45100204a14008002051904545a5030011001390b41071a07000f811301051a1084020504120600007040360044100f81600e4a10105542c000c2d440420b2000da00b4091060f201c1907440103000c1014440958080242a852850f2106484003c0408200d1070ba11000351032401e21400a00e00751020b00540c80076000d4684040c03c04d80025084001550b9a020052090f07c01c490000c041003c100190f4060016a0b0344082580702c0c61a000049825400c0300e48500043c60441104079000d021002c50045052221209080e1180e003960301803042c0760214070780b0f55030401e0744c13917902002 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 878803228 1250 878801978 878801983
    0x60904090b010305150f040f21120501050301180b13050706080f10151b0c080a0203060a0b03100b060d0501090203010f12020f270a090b1e060609030708 67
    0x2080c030700031008019203501d1403910b00e00d031205144803846105901760900800c1110007400c1504a500300714000b032400001d00700000c05821218000d00102d010b403c2030f1480981001010000d0039803240c0820640c0c0c1da0b0350034542a1a40328501c0a1181041c15002001a0707000c00c1054101c50002030300c1026016603501d130b40c682500c0d034100b500030891910402801081c0301c0d03110703944240c0310891009080e20f0b1021540d00080b0184491040c00602d504440c040200340803013215240e00406121107039952041e007543c856010343c030241c0c040d00410000401e000c84e0341c061241d2038400034006083c41962480490010f0404907e843d0340114204282d044581c5a0700485000e401c09807001a03883d4500030185002c00360940c0104205030710200d0503400342c3c2d41d1215000340303030b0000d45a07041d904030581c401c480010b119500b60a20391111300284003001c41c4c0c6500000e0320501c00c0101c8199600c402c074007801740ca003200381c40d0080b03006448001800b0341000c00c064040d4403400f508032140b140d00d41141c0e90 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 878804478 1250 878803228 878803241
    0x905030a0b22060212060d02010c080a05093610090c03140405062406030f33030d050f030a0e0c0604090b3102090310090602030f01090209011706060904 67
    0x110540c2e0003040180c80c081e0900403464001b8412500c03031880c2001039002a0000c050a03101403c0e030140403424810b01030084088442d90300c0e0003046991440b0a019942091012040c0381d20410502d00078280c501d1500010001e028000c0040325581c00303458100c102c2c003e01000d61701a420952151000060100b480516074040c900c5103010f84240c1ca000e03000254a5954901419504040e00d0500d00d010b486041c00c480d00315019a0210030541e0720a040e0506968400d5440e800641168294800156600b004080c0d40e0f401201520500030b80e401c000c88650140b141c0c902e107894020030100303101c010b081c0d000005403614081601c0301e4680c0000054004d40107940306034007043c2c40d80d4204205192044000c0b45110703884640d100c90380c4805900c0b40c001110800c445040582c000b902900075a0100300b0441c00d29413548040c025015a46080006500182e40c0d4220f400031a00c00411a03006900a64200c1c020680d03c4400854030840c3c031542c56100135090316000304027080b20f000700d61101d00070103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 878805728 1250 878804478 878804483
    0x40e0a05060f03120901080406090b0108060f0c0a0e0f150d020a02010e0118021210110a0e010309150b0d050303040807170901090b07051e0610060905030a0b22 70
    0x52038076240061049107408800907610940104d0740000301d206035242a2001c08400780703413030015981c0f18138154000300041140500300700310020002a84550015040380b191410381c00002040e02c4d48119919640254140c02c8046042c072245500307541044203440549201c000d00e400da410790610420034980e070005240c540015000500064040c0d02402101a51464038000f00140856000000f04600341c000000388102c09180c211400f02e071080019184c0e58070100f40401200a542c08901902d510486214001c1400c5030108001d030340c040e1003418913450b08090f08040b40c1d00710307009050007000d4600950354800c500c00d003808046842040510700c9113106842d0513540d80080d0404004c42e00d4030800c22444210100907020250f60311421840c221010516115159070440c40c0c024240f0000c020041c1c1c44130040d0a0900600b030300016400c1c0100c0c0810040039249072107070307812a080700f128000c150f01580141103150014001503246a8450306841104550b45c500c2446800d100c40d004505 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 878806978 1250 878805728 878805731
    0x20f010c0f260a06050102070608060d06050601020f060907051c0308010312180306090b06150a08040201050904020a1d0114030609060303090d120e120d0e040204090e0a15020406091406040e0a 84
    0x82c171940d60104840009080b090901380d1075454000006034034801044c0c00108000d0f2641e010543d0f6034000c01c02e02480c000389a0070744016213001c4200903a907034214031406110703900d94651030350085000312401e5001d6800d50395220b00c5a095845006924904045032000c01105c0b0f8042d0050324040316807000130758810600442c0340c10160800518065025040601c5651080400383d001c0c202c40c1d045907101c025500381030400b0390f56800140d45500512813181c0d00140009400000b25600c410085c401c110540840c0905040700c000450790090542c0d42d2404001e010008101207180c40910aa4865001000c8a01e4055a8004101c0e44040d0706400c64a0200c80000c0307600703460304121142c5180340207650385130603c8402a81d103591040030703e145c1c10038002e00b03a040d06582c3d1075980444010700954142809511040d0103003550f1110590815144e004d603580760511059518001c0b64200e44203039556000301400c21038090020420341c2002c4c0d07070081c0200320000304041445035061240d043c0000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 878808228 1250 878806978 878806991
    0x50a080609010e0f1e01060e0a0c08071110090807050d110601140a030f0c230102011a2815030f0b0102060106080c0c16080c01020f010c0f260a 63
    0x525425a03400c000c910605800540711300600e0480021a001c540c04241340f0700c0140200c54070503d004004070f4100201d1104450304100034003965030866008000665a025101c3d962034004171655400ca5140c80741e180c01003d00107542013555013081a07801d0150215510300001340ea6510b09c0c045c650030300c840208000040305000107106000b800e00400420644008800982c0000b546860781030000404151201c169001400550144507000d00200c00aa81044008010505030300c0103040041d401582844440e0704410300c90414084d004001134210f007041aa065940440c902c06d108041f040e000c050040000c0c1e401c04070700d40098446132910006180e041610400090314555040a030655000c800100110707075000c070070f1583c00700d034801005407228120401c65080c204034a00a41581908420100310504082505603480400f40c0823515a80b0034461040d01740c03102c100ca0080400c254291180c0c000b1700502109017040000c001100e03c1488100400726004403d45242080c80c0e41c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 878809478 1250 878808228 878808241
    0x206040b030916120b0103030807050d0921180e060102120a091a030f0a0b01050f03010e060420120711150907080309030a0f0c08030d090c05040b1018050a0806 70
    0x3c200010306a040c0c1822034880340764035421801d801c180710090410500c6400150024032850646003101507c60302407046021a007000d1185001c4c550005800c80c500c458808800360044421640580c000401c030380710b041c5006038060740044001d280905500a0001144820000c04000c0c1225001c0d604c43d6520303d828090114042c3c483c0100701e440828040051180d00b9441d00ca44951050281d040841c03088072100049410340613000020060090120020908100945103640305560a031402c21400166012a140004020004100b442c100700721a240e100c01d0b643d11268003008a040c100030019414244a1624034080d031074040100c25242403100d075240c107224070402001004011818040e01000103a150802c401000340240ca403100b4000c1044244c40189004048200035a6114440c061002014014503407040342d041c2c09036800854185020305c50260034090280c80903030300f210429000d41d0a191030810890b4000c070b03070050020f61590b40d400c01030f015105a101400d05410540e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 878810728 1250 878809478 878809513
    0x31101260f0a0506061b03040803040e0603010507020102040f1206060b0c0609011b1d15040b04180207030507080304150c020a110301050c0a14040905040c170c0112090206040b0309 79
    0x6040300c100c0074140f10600c95907503215030582e103440343c42c01c0703060915040c0801300754690703c61540800001d00000c2170019900012807506882940150001d0109039a004001c07400c0740701d140240c02d18162009000c1c041c19203843c5c1040261840303100d0001c3c3d440d895010600041d0030201c001712050348020100000c0380f10078051881d40b201070101d03204062a181c0000341c0040340000021244001c01010300310a6950801c0f4041d0401c0c000490554507600c446241d441c5030b00c240a00340100c40d83e1000080d22101c14801c45011a82540e2910f0926220303549a120340d910241c03003070b540c02550205890139100d00b0f2044030402c80c001e4005000d40103a525107115903841c500540c1c1d20a900d01800c00200f50040c2084843c035400929048000365140201740c4018041d5030031102c003252901c000c001c200304d503004441c002d541d0801849035180004203142c030345d1004481e02e21800602c921036a98000072f025000000d08610003018a8109511032102e000990002c0322030300d03201e034040d009403100200007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 878811978 1250 878810728 878810731
    0x603030e1504050607080d090f0218041203020307020f070810060524070f0b07050a03051f1e121110080103051207170a090801051f031101260f 63
    0x41c0e8a40041e024912401c0d4070794029486540d000c1d26001a6100c100a2518120741c0194100d42d006c208500302820040310000d10510b04a02900c15042c5018040c100c40741321a124544c40001c00c64880f216000860180d04090110010341c46003a4500800440c00e01c6101e0141803100000e104d0481c030782410509031030b220784c051b034010f50849170121245c4030401c101c2e0036001143c540d00e036a02d807031614010f0410064200c000d170403160301c4c81c10f2202d840d0b40000281180705903070350244015100c82c00ea1100c21602c08040e00d504144051041040c141a41c0a0317400503840e040c0700301911961a2203071988101c04002c01c481c07900c1004124041440c001400044107003040c40c0c200800c0d0b0440d036910b6658240d402403d4440c200120381c0400b0000c84101c814400904603601a032603120584020b4540001400b4105055080a0020300ca240d110120118641002a6180c1160b844c50702c442e07071110000074402d41004000b910945203a006440811002c610000d1003041c5807030030403034000f8031160 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 878813228 1250 878811978 878812007
    0x160e130507180609050616021c05010510080c0f03160806040c09090503030a02070804030611030a0615120207050c041122030f11010e0907020307051605090c0a030f020d060303 77
    0x103281803e021a075404404141a20410b40e01d6039a2481e4200c8000319200f010740e030080d40a11b000d4100c1510041c0090781958281c0b2aa00a1050b40c555080d07080e0b02040c207000c2d6055940c04076a5440e020300c1d11b40c00321a01c294000d01074a140071075060300300340d0355805900b10b45e00650260b0144020000792050310001040d020a0400050f0402c1da581c507140e12015100200450300482d2110a20180c20111070086911100401051801d485a070905400c201c40050031145002c40008149640f011110000642c40e62001d034009034030000d6500a4201b580c003a111445814144500d5403124482c44840b01d1200702002d032510040500159145000942c001040340e0910b0200001540c40d210480c00320b900225166068000000480e0614014400707294003104841c203000000d1740101c020103a0034040c500b92034000c5225020103045484500c91503030000c591200049890000501a120000081c50045a440085810724060382c000c142502400d580e280820401c01da080707141c21340000c0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 878814478 1250 878813228 878813267
    0x302090c040e1902210103031d1011010609150816140f0303130603050a0605030604120509121507270501050309010b1507060b0102060906160e130507 66
    0x103081082d090b03910503001d4481c861000c455190112a0055501540c00c0390380c030384481d04400c0e0302580443c4012102032200f94081a8688440c55411006040085074610007511803000701d2540c0d10304440c0c0c9201e500a10900395603807100480d60450900802d800804011000400f06051201d45400d2044a5a50a00c11400540200440100c913140c00006690444410f454102c00c1c00c04207040d84940c910144040020b081c5c0440c80c1c0750180d00842c02030b00489001c0048071744407400e05955036010780300074101c0c418480b050800648141d0081c04045030203004849040c1c01c151a040c82c0c17854070010010888d481c0f40401038459400030380003c1c54508102c00000d10094515606440081802082d040043c0000042e285840c2500591014040940003c4000c108001681c00c0c40c1c000d01400c41c1c0701ea04055044016601c0010340c1070150403800e0103031002da101c0228064840510540c48800d200500c014649265a410200666030381a042e001c81c09144c00ca0000303000c00d0144040301c0040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 878815728 1250 878814478 878814487
    0x606030d050309060c090d3216090f1401060509010e01080c07031d030f010212100f090f09290919030e04020706090804030c0504060b09130b190302090c 67
    0x2c05000410b13581040116852640d41c1e0070039000705041c0c00003000064041881c0401142e460704900044002104841041504c8081002140d6444640440310b080458145007018404042294040d8003d008048400507040c50200340c00c0825210991162020030f4000c2907800b081e581294041c41c01d0407007441c10b5070030391038100360384401c0303025112000d4104100908519110f80317254242940c180d10040c00c036410680500c0d00e15000c2c1d4482500c031020001004045004090401100d00540d41c4106a0b100d4042c1444820720041207030a845031030080e111310134480415601da0070500e81c4144a030002803150110141e0300d4a20002500040883e0b00c009890106c0104c5481115030003649480d04c0c116020308400000d01901514101400c2140380401e1801004480c030000e2003101d00c1031280c401d00b917a4810030402103c650384111486d11200300078411321441e01d5600c000c0900710000b0001056440100860084c181c5148002034005154100b4000c0d03207441c0540ba0f902188810010b80703070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 878816978 1250 878815728 878815741
    0xa17071104060e0412111b03100e030702120a06090303050f0610120c03151d011509031218030503090a140a03170c0615041b020d120b09090606030d0503 67
    0x318001e1010301010940d045d85050b40d441900c03078160b0080003004030780040d2035030454030b48905290f559142c03203441540131210700160140140141c5240c0c10b0007660034131003250284044c601800801c5e07182400b900c201da0000440502c10102c02d6802564005110324040c0d05005000c180500460f10811703034a245101c42c40c2d40600b1032103a00301c031488081003c00502209601400101800ca84c0b402002c1202081d13814010b500010342c01d681924052190340c1e030304e8038210440c03845101440003a034480020300c04620300c1c86805000d00424603110003500c100307501071002254550001c59179600300080c02002407900d0540140681403400005090540c08000105004081e100040507039140415030300d5405000400d81d0310320300088060707850504e00190b0400c0520000030402c0d20685c41e15481c100b4030920030103403404501480c0c00405141204d21820b540100700083e00707413030751030304e6525a8006481d10150035024826140091000f03041000400d8181080404808100003040c001c1004 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 878818228 1250 878816978 878816999
    0x9090b09090d030e01021201090c030522080f09060a12050c090609092d01090c260a020c0d030218060c0703060b04091e1704180e0a1707110406 63
    0x44034000f070a001511001c030581841c064003d203008001891a0325000003504186900098014945079508014554400c00e254540c2c1002e6104d05000c0038920710f19800103104038005056464006500500304612500010178942c0700c000c0c6000002e84041d0401034910180c0221500900e000e5280740c20400038101140c80d50107070b070b00c00e9440f540001c0085400800454040440d1401c8480d106525503064203902c411020300303219031010703a4640341c0c86110301480b424208010454a9042c461241c6414501c11440381b4042d01c0d408003580e081040c03140544e01080460444100c0e81c4000d07840c1c0409a0840312002040c1d00d440c0d0103a00c040110450246001c6a00000c0e41c6e400080024821208404500100f00c10310006048019060360020104c0072450000b2200d81b1819120b0442d20114500c10000d00882c8107d41095080d520b084c1a001860703008031421000c90803c035a000c062a03290904178500c42c0c640004d0402000032050700b8007110240070f456080c4107903001d0129900e020070400 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 878819478 1250 878818228 878818243
    0xa03051c030606211b081803030103150209040e06101802040501090515070b01030812091219050f030a0b1f080a0c110d030c0e040513020d2109090b0909 67
    0x40c013100032295032a41d5000703203602c1903000556091032401c14501c0b4050142840c10183c1d2a8841400394898011300c072140042241d040e0380d4441c082008800c00c207c4c045019422480006500c203444004105100c581000003900c28002d802e15203507102e1800c101e80d0001c504058405540c0f0b40104801d02260340c1180c0315404903070007594016100480d8206600b018011404000c2604100c00c000000380075020340a403410004551030741e41d80741c83d01042141e550b0b02410492a8507001408202c00980d9000c09589050342d150410300d1510009000c546620780c4116003804100c0c5d41c404540301c1e5414007244074880002046416440b10000240c00b810490008029582c6552110b170314409040c07107030030700c0b15000d01e140c001c03504101503182002e00138016460303901c0c001445039050300003d0724160050704d010707405120049003900150317000d2003400489904140d5165500c83c0031060110000c011000103044140e4403040014104044001910100250f4500c19000e503c1071103504400451000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 878820728 1250 878819478 878819507
    0x101416082d0426010609060509060303031005040b0109050411031803032e05041805011503020607061d0d02060603100905060a05040201030b030307082203030903170403020a03051c030606 82
    0x90401e404420040c079080c40020f0290707480380d4248200002d00ca86507802a40c1541e408489180381a652001070607500e01040365000d140c030071202000c0005051507072185909400600d44422540e8130307080070a040d50b516400c3c2c0c82c44004000104401603488241410f00300d071331034002d1451401c01030307000ea81c0c0b4044880342c9402005a048807444410b40110000c00419004c2d20600c560800c0c040d44c82c3c606296800152a55424882c01c41150070001c445e240549500030000f074200741c115119080282002400c8004428152400031108141040004001d0b600b0703500a00340c81c9440418142011603094581146e44d0824603031000003040030800c6a44880d14940000d030701c1c2c1d03172800100c1c0581790b10070640b60940400607410302403180e124014998110303200e403ca03204000c040c2d0b0b1388034090214130022b800180c0c6402c09000007120400c9418400c1001244182000d0700e940015a0f060010303442280c4940c000c0d9401091000c004031448103035045400c080014a290100181c01c0240c0400391 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 878821978 1250 878820728 878820749
    0x2030c1c0e120f0105010b13031709210c01020309010c0b06150c0724022a030303010b07050d030b0109060e03010e30030402101416082d04 61
    0x20040140c4910166044910014a0210b0810284600584580201d68800c80329424000081194040708044516440c042e0348040c81c010725545070464160120702e4002c480407400c100c04041641c0e0343c0041c1d49003080e05000742410740c1d403024803a4507003c00c007040d40d41550000e00c40d0524a0303811060f1300da07607a41c00030074003a01c0e640e46200248503181501c8030201c05400202d03407069207080014032034007914211040095500742d1000505440c401240207800180e11030005004103545c03020043c03038104110715058402ca50558002030071a0803d82000c3d2401101040310024030004024808404803203042c01c0103020803040000305400e2a40c0a00d0080c440a000400d0468400b54813044014940e1303416680802101c440401c2c14081d0b8400c40c102c0345616482c105a07954110301145d0144d0303030092020b0515041d005096515481c541c00d10304644400748500c544c140014000302c140e0074440c1e50029170300c0c02e00e021141c0074002034610581c441c881071208a51501c0342c00c81241c051b02d403c00d64 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 878823228 1250 878821978 878822023
    0x160603050114150c0616020f06040c03330b0901050402030f0406050c0c010207052b090e07112508070503031602030115080c01032003281d0d02030c 65
    0x200700d015109900c074006042c0b1412003005846d2414107102d609000869099940122030030b00b801d0341e296010b5401500010180d0000c00015891114140719000701030341c80758456502d40010075103d10304200490001c0c0d04c80c80c1030324036464080280782c090002182d0840c21418008031215070144003c0c4004c0150780d03590046400b0090940603984403400d41d000966483e090341c83c0c0140c0f0b900c0308580d5824442200840c202c4888030480d03140c0d83c0c040a80d0f48000745645044105041d424001d08002d050205059070311441c500b0a1101000950b000d04c0c0d102c00710b401880e981c640109041e0710410f001c2e00112000c0c080e40d9800b0084410241ca510081c03021201c1c9400020300502c050042c2c00880508418005200344010900c1e0600d00c0098a041114104401c3c507103004074600c0d0740161a03c0030410000d03042d800552800c4100214803144080d90075511900141203920781912071644403a2141c110f02c10032010001510811070510146003040d0108026982c5d5072000b496402c010800ea50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 878824478 1250 878823228 878823259
    0x17060907121109041d12070201080411060f07050f0c061905090a050405010609150c0f1b03200a08010b0607020112200705100903141b0a05160603050114 67
    0x20039240c0181d0010b004011070b039170301100030040c4040e420b00c0080600580d20511401d04000c0d003078030b100580607150f0904550302c640c0d03402c04070b80c0740c2002c0a078441030611801d0004044040645035041c4114002e042d0210808445841e01c46041c2545100303e0040140e100e03d1100031107a0b2013006000e0600d03640742c400e25400941000307001d800c035507001482c0000020320aa0721650400c1200c1001e0500740300106240403c4501c0700413040068000350308201a07200040d15030001e503401816080c201c16074151030343d90300700b40740400801c6401503000401d00c68820303290002c40d032401000820020446110440d001c80e50324010030001030f05104000440c039200100c186c110401c5801c0c0300c040c0c03c50814055041c514141c010032002c5e6050300c0b8061094240c5003042c4102d0b8800d1781c150700e074401c0b5031406041000e0294800e80801005c240150603050803000308220100340c4500c0340026001d500c000c150701c0320341801c1940c0108105070608004000020404c0340700b000101096034145120400319 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 878825728 1250 878824478 878824511
    0x90b09091b040608010c031b17060907030207050d09141e0d050a08030702031b031612020a02030a0b0a050f070806040b0103060b16020f040902130e0106080304061706090712 76
    0x990020313445500344036800c01440e80c164490300b01c52600704e1060100c5a5070843c00c540c480d00c0389680a031402015000308005d4078203032035955440440340c9000341c60b154555880f1030801421021010101f43c0e8560103209442d0600400d00c20b50006540c03455800e030300d90400b0444003440c1d0071020301a140082c10101401000c0c0022051184c021101d60750301c0c10729400081d40d1f50700004202c4007402c6030a403d064042c5010044840c044502400183e031402c047e1103204c00074000f0784400703044d480340c0e088440050720240240000716000b00c448061600e01403d81809a55005245591142c00316040210781500045001d03084102606c00094121903100140e0050509800501d480280440d20b000b00c1e9182500c0d08501c28420342d8645807420b040002d01041d0340705580000d50002602411204110b465401b94100100384000801c6e4140d4032030003142954810f0304041c0010340c1c908004401000841c1010f078203c0000d4030030b40078034541500020015003500307000000541d1509101403803881e00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 878826978 1250 878825728 878825741
    0x6090a0510180b18011505060a0e06090a0311090c090a03080c011103090105160504080a0f020a170a05070f060f0c0314040f170106032103091b090b09091b04 69
    0x4084885000d05007080110784c450002c40c0800314541c00c004030b49500102d00d440c4502110f501071706150818107010b03000d079076501c5045c3c810781e00080244003a1006076a0901720710011402001c2110000c01d01e0004d002540c100201001c80800d030400102c07032181c407010000030481b90482d1000c0c0d11500b05100315405001c44445030016180c011052040c501ca0660000b4002d01d1407000c41c2308240c603164000e5800340258407c0800b181c000c1da265101041356062501c1000340300810311400151034401c041d44d07803542c0c0145640c490340080c100004111040201801400e0b00980103080a460050020038101c01c50028000b000541d01158080500800c0070031918010301e002292610703140d078104d03c87c100c1c0b00d1103041100f100704596581c0c40304041c8681c2007900d41040b610481c030b110020780300c8010100304c0b20700010141d8a2103540045110060714041711003e140c40d2068a901d03094205003aa0843d40505104845480074840540030015201e02c0800107020380f8204c2d1488400014001c02c1d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 878828228 1250 878826978 878826983
    0x91518010e240f0f030a0b01110d0210111b0c18100302060d0b180a0c030629040806040b0109050a1b1b0f0f03030507050f070303052809020306090a051018 68
    0x401200b0f110449141f40c101201d05042a039400018100c801c9005503500e02804100c1d0250700301560040d8400c0c02d50f00407114100341c0f05401c42c07408020b4002166540c4c030f411041c000b160040100b000c2d07280b40c405252001880c170b03075440d407031207040800d080a00340c00e840c400248110000208519800300513006111081c0d002040117040a0080c04151440042250b002031070f41d141403090200b01e40a4400d66050b078441000d8030010301c1c142c400c892884075418440c404d000b1020300000910100400ca0700d48154440d04104446500d030480e01015a0030103010140e146050491448140ca810200030b850b484051074009910f040c80303011003281c9010308002078403940504d1080d80074001c0405000501500c02d0b07030100f299944010085681303026110300c01480700010001c010100388a40c100c160042191005800040d480b40401d8241d0410f100c600d55100b501d44013040c00351324091080036441008071014002c5480c2c0707079540c103484042d4440c0100031540d880d04903132201c10000e03106c2d04520743d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 878829478 1250 878828228 878828257
    0x6060a031208041e0501050a05180a1e1502040f060e06090d170705010504020906090c03011a12010612050609100b07050f1e010b0d0308010605091518010e240f 70
    0x13481c01c010b8042c3c03c0c00c8030041c410504140100c0c41d0351404891100c58685040e019000c2207c0a503210005404400346024440c0c0c2c002d403d0802150120315000030709088413800603581c1c1c3c0346c0004480310b04525408072040c400020803c100540300c020031182d000034100c501200c600300515000c0b8142d5140300030048401400702d050030800c04154440e030b008032700031650071f6a281e40c1c4004020058900b103895040344441440100b001e04900d40c0d103016251078074100c581c20101c282d02d0071040503100360300c01310000d0fa112487c041032841e144141d9070007640c162a80002444c00040360640c100c024880c0c00d003a1040042c021003400303824406540782e007210300140e0b2400004500c03450072000042e4141c4007594a000c460101c43c1c1b03000110600c60641c141c9a09110740c1c80e1000907202a000f00a109401100800e0b08000d4424004010044002941c142c0085c190807a0001080c1c0f86526241d035008000c01032000907201610707030250151340c1948030f0495035045440c08205641c01080302908022 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 878830728 1250 878829478 878829533
    0xa1b05060c04051207050303040605070f1b150311040b070c08061510020c03060c0702010c30020304080a0b0403050d090c17030319150b03090f06060a03120804 70
    0x150090700007402103070741c201da80e0249038005031051030701d543c140d02c22503916920402c010007115000794080e050a5004514807000000c20340c840ca03844007180200060040300404082c8a807810070600d0707240511303913031508100301e600b00b090f03c140c02e100f140101105501b004c01c2c8203041014050300308026107551002c0e0351142c00c0c030707076035600402030500e06541c419155407042c0c5c0c03810307803000445490b8600001d000b0091f685031804d0315010323139010301c0040c0c1c1001901441440411001ca082c10711070715942c0340c0709403003110f803140720448039201071540c601b1500304010402035480000f0309003030341c039402031b55112842d00c50349000c2ea46071181c90ba502d5122400c02e500e50303042c00102806d40040700d200c040c0410b50100342c0420103490f40703c100e40420003030040001032480190560b102c2902c503200543e042c01c52513207c4047d07040d20b0f002101c62105130b910691050000090034444943c000100b542e00c001250f081d65a0800340320051100c400c20441040c0001d0240850f108036268074058204000095 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 878831978 1250 878830728 878830741
    0xf010539010608030304080a03050618090a0209010f030b0c0d0b032a0414130203010209031213060206010608010b0c0c122d03040504020306041407020d020601050d03050a1b0506 78
    0xa802003410155034a52074204000b90141000c01200e210f03036840408540303014007852055004217005440280c01118244010000c040806100b074010304c1800028151441c1a2041140480c4160800c0c40e11545602040000410982d50070b5000300f0200d020076180c0881500c05d60003440610080b55061042c80003001078000244801d07541c06a0000300e4040c018506014802030312641c40e00b0641110914001402d11810082c4411881c0c2c8000d0003d461300d40c0c03110010346040941d0104640c4a03000080740380c14031610305200300042000e0700103840b01c2e624041e000307032000005100f518403801d400034011200850501c10007503030304130041c9000798483d0305540e1b160707841c00c4c90703603840042c03014810842c0d405614030100a0120050b00c00154038180c1031006000103508050105a0025120a0a600c248440790292486085c882d03009209402c021700c0700a00e00340041e807150340a0020505aa4013013a40001100c028001c0c500348084168803c131030a4682040004010b000340c0148000c1c0030700d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 878833228 1250 878831978 878832067
    0x20d0b0301141603020a0509010c02030f011a04060e070507230312010608070207180b0a031502030708070e0a06031e09150b010207120f020a170a060f0b0f0105 70
    0x146440c40f481440c0c40d040700001e60884c4185200600441c2c824403080d000c0d90700c242030300c0c45032500c081c054508200e1141091030950300c06544540060f0740201c184111404c1c1403140303500502e4400b100f550b240c1041d900141c0f0360700c14980080c128801010824013950a0740c030a1105503444541266030350030b417207440031030310400038042d14000031220004118010701c005094020b4034004038a04290003141c569100003003101080c5150030488450000003c20603051004518214850f005039491a0400f0010300c0306100400c000d05000203481d1684581d22805c52603801e450260600203001d15003980c6a0001001e02000e56600a040050040401104c0504c03980c95214002d002e20000c82d0050041e600d42c0c040d8015008150144030808020030000700c02035070f00e1400030346514441031b214041c0d00c1128102030908440b56018000e010100a06c034460044c1c0200010703800c0099144490025a0022140403124100b00f00811401c4c0c000c2603000000009554000c00ca200c0c5070802d000b43c90 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 878834478 1250 878833228 878833231
    0xf0c060806120a0b01051201060b312403090204020c070801110a1d0105070203070605031006110a3c02030c06120a0f0b04090305180609030d03020d0b030114 69
    0x900a1039820881140b010002036102c445580c401d641c18401d80c28a014001c00b40903e48440c501c0d592101000500c90032010010609143c280301b40034240c2c14503690005404800a0070f145003200780703803820446142100c2400c0b00e51411501c0290102a0829046015040e145c002941c40b0303100003034003244120001480000c4904800080c0100c09410031035001600a82da0300d036011034102d441e800300302c0c2c1404000c4e070f07000c83e414148942400e50f40d8000c41d250041c15003000f00411000818010100c840300803ca004200d240b4050301284c4803000c5168680002d564010720f00c80c80306c0c0c078484006480700c40c0c41907524043c858402c807500079000707007075251059a0401d80c081e0007240150415800c151003154a03074202034901c0450f0382c076104803d1b4018100c0890310303c661980c0c0c10500d0450b64940c00f48030f812138080e55407903440342d140d0a052001c035183d240000f80f094100300309991050b00c0110746400440c40c1c50070700507121003d0410713200c081c0c50524800341d419480c00c50807146101c1400c1803603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 878835728 1250 878834478 878834491
    0x14031807080c0d080c01060f0b0d060909171305130b01030614010c0f030c15020919050f010315030f06021b030301300501110315040b0603060108040f0c0608 69
    0x15030305155100075407034079040680030042e00408240036001c042040d40000b0005089820b0000030b4040e1b80300300c1c040207841c09400041d0f40b0b06000900ca04000300380c2c0110341c060500401c08200301085540c0c2c0344c1c1e000d00740481d0703045411800300d101c040c4c0f070b051a0204c200414001c1c0111441050f00e940d56801802026a21404640750030408030f50482524100c100020741078561a4428a07a83c5031245a00c1f000034049003005501606080000c50320840c0600c42c070b09501c000340c0c64007100e03030400050a00094880020808025040009640e4242e511140810038207000030784440c0481c04038011001c540020f000445024218410003140303070b004026544044100090a14441408645900c401e1045400241c2a0f40d204801c20352030030319400e201c6610070112161190165101c43c01e4030301c004a034042a0901204010398034950030a022a80d103001c88080101c2d80112001503100c0c007011709131604114100c0000b60410240e00060555070380c00c041003580c1580d4588008007042c2c01110078 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 878836978 1250 878835728 878835733
    0x30f0e031c02120a091e1b170604140102270f010801030c0b0a0c060c0801030c0b0a08011e030215030a060e040f0f030302251415010b0a140318 63
    0x268101c14080c0c800d9841c00180740a41400c0f0b40c0b1407071001009440301c0e041c1500c8403042c0010700d000304460083d030004801d100700c0c103031840341134001115002e00070543d005070010b0120503d1021000000301d8159405a405501f0081e4001c44181d65802402624a4a540511001c03210801003007000424800d0400444510038003450a0004484180c000e210060100b240c203c002e02005a24401400805900e45042c200c11481a21000d064807902410240802c02141c0140184036490401401810071400c17a00c1c6043d003042d0000b401488144034403101510840004a02e554202d101440155001048034000c1208904c044030145c0c019a005030180386018000990f100380c181440e40324980107003a120784048103485104004400c0d100c21400c0681c04c00242c0e80c2054420b00055807107801c0c169803d40e0b4111850130650840c05082d0401d06603000b10200c510803840140201d05603401217000039101c0d40e8451007034a10090340305800d00745d40808010071410031841c0003615a500d144104 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 878838228 1250 878836978 878837017
    0xf09151d0f010210091b030b0402010206010812091203070512030115090617061201020406210509060103082b0f0c0806060301050f03150708090717060610030f0e03 72
    0x20054290007000e201c60150b0492002e800c00d0341d625500c001907481c0104030883ca0b211440d80c400010226603081114185002c10500095581c100700baa03001d401d00030014001404464003040312800343d10765180c410300c00190013644440044c0141c603c6564000c0c01c0b640c0030100e0000140c4180c000340030b0307141900c2070a00080040c40c86680300e4000c40740503403140c40c1707140c21a1a00c1c0868510090203e90808281d142e100c511100134402040103008650328000d0500081042804c2a100480c3c16603149007002c00740690aa00800d010381102e0b40300c490b540d41d500081c02e01409114298bd85031081803014070011141d800d41d500007200d449545102001010500300080c0c03032401003542e03150f80211041c801482181000101000385001c010220b4040c0c0048005c5500c1c01c1070112288800654002c05028100f2010132500d1b01a090f142444514812010017481c4e030b9901c0101031910400c0c0e070b00400c1d0345040c000d5000c1020b040d05200e003845040b0203038104640da580410b100b8114100f001a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 878839478 1250 878838228 878838287
    0xb1305090114150117091f051902070b070309050f010c0e0a08160e060f1e15040303120f1d060601120b010c02150f0d06050a0f14010f0915 61
    0x103d00894240503103c1183c030301c0201d081e02c8a000c5008040c10030300d11a0107000d425111030403880e10380c00701540c28085000e283c026060080c111110403040c08080c018000d100000300c0248200d90301070004d140024856510741846481d003003e607c0a03040c0340d46040c8a084089900400c28001030b6001d8402c1c484007541c0d800d026944082144090340040c0c0c3d207200a10a0b05000e84a03e07411000050000718540510000501007004e0007114000c0c0c003107940e4100c82182410316000d9403601210703d11a040519644018264103d00b000c0401c0070390f5180c0a51031000c0705035124082c2c581003d015400343e0740059007a50b43d140401d40d40300307022580000987c00240711130301800340d180308107135500031840f06241e0900007060401074540c9030201d002c3c0156806480c050000c1c1c99519602c1d00e011a91a142800703108100146800c0a0310f45080440c1c00d00a40240c0c1c82d220f05058001e2801031a542e4a60328110345080703180e04000003d80031940c1c4013024a6200143d07403500706044814942c1072400c0e6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 878840728 1250 878839478 878839501
    0xe01080a0201091203020c04050726180c0a090f060905072c28030503030c07030306051801060c230a03030509010921110d05070b1003080d0b1305090114 67
    0x24013000700164840341000d103950516400490b000390706420900700400e031111040e1484c0e0340c01c1802d04403c080c03c008002540c061b007201078080785440710141200300c4429000c0b85041d0380a0007183d02e1a612054a44060206030384040d00401242108009504180000034603403000b940d00703090010040c803908901c14009540740d10071020001c0011210007400681100c00e00c603c0c920840a080c0315040000109070103200444c8102181303041960b41701001d00d400b4084a00c1a0040340c054004584070400c0341681020060640c0d0350381c00c0043d0030840074034003134840340300c4070100000020320b98010b00c0011100094100d0694481d441c20310103035840b07046c440d00301c4804010181001d00154811705481441070404e541021007803612802520014408030b01e806c90b48240b03100003c1d030001e00340090205580396203400424500c00d101c080b518549030084980034190350f8500c80c40d1340d2082042c80307946810427490300011102080c4002d18112149130b000b0508100004040b07000b100001e840850314 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 878841978 1250 878840728 878840759
    0x303050a05100510051603020c090a1e022a0d1409090402120a0c03210806030a080d020c01050a0b03070b03010608070c0c0b03250c020d0b0a060e01080a020109 70
    0xc400e5004040c501c0c00080040000c2d0910166080c03110810000c40c00c6c003040240f10398003a00a4000b0550403044a0500581140003490702c2c0c1c100303103000d17a208059000c034013607154150300e101800b5071501c1e4400941d10001c02004c104200c5454003280d80c83c0e10020105054501034850784031000d002030001e5440520348955900b81d0b910070000780010300149054204890b400c081c039411542d07041039990b2900c80100304c42d00203452007596003200c03840813102c04480288894091070720b1640d0342007450100755070b0105500b0040c0031b05030200382c1402070301c0182d06580200035090024021030603c406003030000d0210a4400380240901d0101007001400d5004030b0741264190786d41c091301e6540315642240c9810171502c04071a403a41c0d00c1e2000500c0d10900010f18040c030884609152007140c402248510210042c0e201800d00c0501406000907a80d1512180c41158226242000f1540c800c80c282004002c190400f2442c0d408150001c181d0b1403000030b1051000d403003032729843d10f0a501c039070400490082 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 878843228 1250 878841978 878841991
    0x3070801090c051c0f05071806060c031202131e080d0f03090501090602030c09180907090509011103040c0f140906060c0a080a03020c15010e2a160303050a05 69
    0x11900010030850601140c104d0348550400102e20b00e80b4020341d50103803c07a00192080d16294424401405140c0c40200000203080320034a040051519002001e003042c0c24800c2e01605106c00c950342d0b074001003020380450346035003900003403242c50b1610356050b50040c0e4001a030b6000c164020001c003064004002503107550f10241a21082052882d40c2030480140c20401c2c4115050354a40c205217000622074009140500c1c40c00304e405480f8041801030001007a1022039580c5091a000c00f8842641c9010842c10b05650a8440c082070300d0781ca00e01000d014000b41d201040c1558400005c0100784510a8841e0050703c651080c1150703041c0c2d80f845021841101e80c040c03d50710440400106a192400b000100116419201034400e030740340c1903d40805541120f100b62000c01c0e00000c0c0d800490700184146040e170303100f00900078441c1d410408424203040d8010070041c0b100385002000017a400b80034800c40e0004188550b103a50303d071082103807a18a80303070f5a00100e01090404021801c480420302840c4d200f143c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 878844478 1250 878843228 878843243
    0x24030b010506070c0302060d020d141b09010e0909060108070b1306050d0e0a03080a060b07050307020f012007091406010f0302091305090706080711060a1505030a030e0307080109 78
    0x1d0a1008000701e540c0b04900071141d4200200c800001038030713000e02405841c5509000140c0300d03020826903400783c512601c495603a10440d14200b0500303141c1c030f00340d9124090307d03020f00b03640341d2501d1801640c04000c060025680501d071301d0204079141c80b0018249041c0c80d0500d00b600c11280d60360122003d03d00614110000c100e211700000c0c001144074a000d0f28207441d006d4004114294103449075424803080c080141c00080c0e80d802042628680e0380602002007030540c10091500b0000c1d104c180e101e00070004c009210780481408a00320b03078400c994420300c64260205c0f00d01360450348803003203139a0030043c030419075018106107c041a481c0319800c0135209400c103844600740301030703040d100300e009503c02000b503a071224001a208035089080c0c0310305032040525800803d8058204003010f042d601004107520b08100a02205440c4480d02086458011061803030200301c040b00c545142e544002543c0042e50184964031580051662048540c10305000980950b0551034880c1c280d142a03601100000c0e007100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 878845728 1250 878844478 878844481
    0x311090403140313060f0e0f0a0c0b28030c0e01320f040f03021504051f0c0b0a02281706030102163e060a020c1324030b 53
    0x102e10302005543c000c00c00c0141e004030000940e40c0740b003160b0b084d54113072005654460007032101002c2000740311260b0b1210801410603819070750b980303002c44445010b241503107000400c0c0031035001c0c5039003101d2004410b0b1094519040c40c03842d8008000746816040040040c69850142c48194041c00c4012421200301310390703a072081041e0343c05500c01e0f200200b8489441c3d00411018050000c01000ba00103400038422000e44580365004002050203030f1240850810740401c400c02c05551034a003004c80c0c282681e81909102c0c2c1c0e032014243c54000c0503880103850440010100524016682e0041109150504011041d41b40c507441803401c1202400101000c109030191501c1c407040c001d10100d42c40300c3c000300094503000503003800c0ba205800c03802d01100d41da2048241ea02d52880070f41421405c86c0301c1b544002020560803100352000f10204103001e40550710020300d03000210b10a001c250544000a070240c0c07550321000e1507d400920000c0140c180e282011b84088410b00003031794016003203130382000000146 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 878846978 1250 878845728 878845757
    0x203010b03151e01030e0705101106100f030311011104030f02121c0513051201150603090203030f0702060904110c07060201050606070227070503070305160801060806010c020d0c0311090403 83
    0x46c03800e800744140620400394009141e80d180e00c0c0c2540c4c1580c0d56036400b4205101003131454500344018001424500c6105424081c6009460441045039010f240150400b0344090001e401054a440302c034465400015011052040c080c01101d1118800d5449046826002c03101e151a840307d01251045407840900d94581240704001803c02c1c10700800703091444030741d00e200281c4941c0058000707540c00c1c0d4413080c0d1a0030000d007e03880d400c010702d4941424014088030b0b900003502c034403e50404c8603240802041607c1503407a01000c0c2d6134100ca026104110032400c10b581d4100c55001400203000314414080081040361060007164080c0b180a08407506001da50350800c0740e00d03540c01d40003514034020b04603a100d0710441d50822a00522035600e81596a06040d68000e060b910000d166192074270445904180c101c2d8040e8046045414034a007081d41500c41e03400480303900140d02c001075401104174036144284040d4041e890201e078030590144004006c0401403084450007118050085121083c00544 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 878848228 1250 878846978 878846981
    0x60c1e0503041a09070801061d09210a09261902060d05070c0206120103050120270d081812190204180609142a030705040203010b03151e0103 62
    0x801441e05025601d0301a10361410f0342c08c403400307a406418216043e801401480b044032315866000230100018000c10b007400c40c2a9a8420040b0140b040c04100024408041c20f00c90340e00c2d000904100b484003c80340b0381c405141c0d10000700c54160280240500c48400100f459800c105c00c10182e405001c06080c4028019200b0080000070040024402400c90582c0165100c40090000d200011540085941541841402c403600c00100c03800700d2802100d0445800741c02010b980d0814019500108000d240c00741d103000101c4508030080c0c1060a00c0200703010032a003800074140c010107580b40f07901454107181c05c1103d120b030b01c02030803003441d000b001c03500002e01040e411052076980060004220300400384814400104c0301101a500940d0fa60f0002040210345c070708400040d000301c401400600c001e00c0f0039402020003031084040800c2c0078150303820641c405100b050700600c0d006004544039a5509440f44c9541c3c0225406060000c000c45080703035034a0154910013080d88000781c10022410900c00540 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 878849478 1250 878848228 878848231
    0x1020d2f090d03270b1806070305030a0510031b03050c09010b0a1b021905010206070f0801052209030f180b030615070c032102010501030f1e060c1e0503041a 69
    0x10040038026400c1c04041c0c11413100007451554901c0d0b5856030030060700103108641c07051442c420308003003048001180d0f02000740ca0f0040c0c602074002a42d80c0b034140d150138500415074802402c00c1c0583c0c04440100150000050440e80540c0070b440c0604001c0c030410510782003d0050425a00081c042c440c005413103100c00c640412040d0f0600035051865400007020308905401c44455a00d901000f0f000355641408800d400c410340b403e06404100c1da4000c040d2058105028a038024403150701180000c01c03031a0309403054001101c100300914034041c01c0c001c001c00c11154500c1c000c6a14510305403c0c92016500240c2200c075031301f40e89421138458504000342d041c1e95510002c0205070910101021500000e1413500852041250064100300c20f01c505c0c1442850310505030559161070b00400c041034a40c40e8181c900342d070041c45d203d51100b0446100c001503030944c0019000c14608907424010603000304400c2c03da01c038000d150140d0091003c0013140c0910040320700a01040107800d5202e003100e01e2080c4203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 878850728 1250 878849478 878849507
    0xe0103150c021005090318013002090d0501050103033510180e012711031203010305071404020f120901240e0a020405060a0e010201020d2f090d03 64
    0x4410f420a0048040c05903103007610414000c0d080001e5410003240005210140401c0a00384400c075040c81e8140c8400d45030003081c075000e2200004000400030304559048441d40207009004040241c0c69080890007440240012808150452410b00c1c1d0400d01c0402ca191135071354124142c04100380c500c030141c9a80000b41c0071204440c10b01c680800c42042c254038400790103001c1c007000100701d0112140142504c2d151414208c0b42c2d070000c0c500c03804c00840d400040b13007070715007104400320380703e0741d51000c203281c901c1c210012a051200440003008028005c039120044401220220f140d021900003004106d200e941c3c0d0119207040200114a04001d080403100d52202c600400010200f4800700388803170610220150021801c40b06c0403e204000704e07850442d4000a0304102141424104400705007148962295130081c44000e4035160a6071b13100350101c0e2030300d152101052040184c068030350205000e1a40e440152103c61952690502d074424007528601e0800400740100003945071030a0342c3c1c00c5410040b8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 878851978 1250 878850728 878850733
    0xa031e0606050607080c0106060f020a0305070f08030c030901050121110d021203091906021203041e0b041a0402100c05160b0a111f0f0906050405160e0103150c02 71
    0xc2c0d00e5560030f01500c10240201c200c1d0790f0350030814500740e08568103a084081441450712502000c00e90000d18240c00d9613141c141280d8405e054104070b0b186c5140010000c014403c0041005040c4074240061030041c0b1225009000320b0340c890038005a18100310407900025032001020001140b45582c622544000140c0349507000003494001c03c42c1c0910800f003e6400d0b61000030072494a041003403c0d50912011000800101414200300948805102801c20202c0c1c0020001c00e00748030b03504221010022072a4140c001107211382c03a081641d00300480e4182c8802031520741d9401d950088181c1c640c40780da4000c00d030f20103d4440307030000d031011001c0010a0f10315100d00d580c0e14103011030045224014003c060b000c0390701c885100c0d0009200d501d00d1034078070605411071010340198003000d89098000c0503a80c5004146400c2090080c1c0c0200381c0000702500041c01c3c1030501c0280b020129a18240d01d5008000300700c05516184180d0a409082c800103040e00d40640d0701021942103036000e032984020b607206 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 878853228 1250 878851978 878851991
    0x106211202031804020a05190917061003081c0903091409040c0b030901110c062710020708070210030b0108100608010e0a06030b01172415030f01060b180a031e06 71
    0x11a61845c0c3d030252381204c08104000e07000c0c401348101d000f480180c800c440008140c2882d0031410b8844106907440003c14a0101182180203510918148070182c41700540401190206081c0104500210310401d04402c3d02c031104460503040c480c1701c96208a4008079a41c5000d858501c0d1b0006075413000b041206555030720240300c401d0020020017028003154003c020100c9003402c000820004658095003003400c01c15540b282040203002c94910800b000d0300d440140c80e420720b414014102d21a03500000e512180c032542c0540415019480300518000070390391508243e0300c0000300990110a402141c010401060040000e0100c00c0100ca41c001100c00b0080f038482e0b81c0350360749a03451900f03070017034a10242d1081201d801038100b0444112280c40110b090030303080c203103410b1900700b01d800038284242022a503030884165403001c0009002407009030000300181c0d41d440341d056001e9040480801c4522010074002c201c0342c508207107120152500a450ba01e40d070b142c0d9000c007522003801490201c03400e42d164003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 878854478 1250 878853228 878853247
    0xf0403170702070512070e010b130614070623060406080a0b0406090b070512090114010303260a020711122a0a060809010e060702120a020106211202031804020a05 71
    0x5c0001c01803c902030061074028203003040321610300416040400b200ca030a11000032458034400d00d0104035500c900340a084c840581d00501ca40e44144c003405801c0d181031800708091410110181d1201d00c4401c4804030340e0740c80b500c0800082d100f113031041d0300b019801340840c140072426140c2d4464000d4030a41d80001c80c0d130643c1d83c810787c2c42c4ca070450340c66002c40c40126121150113030b080d104a80c0701c03111000810450130745000d040c00340325040c0000317820454203100c13001850200c1002c10780c0200c1150300482003417030f05482120203948a040e040300d001e041e855115035203040141d00308140300080000f401704c0f410780d41e0115400c9454103030000c041c41d4000407101544d40310081104080c0010f551603051515100003054250b0340014282c45841d8801020454040c6d404182002d9540707078643c403959610760603c02203026048c42d03088803600b101d8403198001d210200b510030a8040388500228420004544400e07030f124000c1d00000f010b140a210700124092400c1e07402030200302c0950410604113600003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 878855728 1250 878854478 878854489
    0x50a0f050717070c060c120509060c011d0c06040e0115200102120c0a14090a0f081608070807120609050619060b040303020c04050711030a0807080f04031707020705 72
    0x102c0c0c5051a8410010b100c4051007072500d07101000c1c01d0302c1d061030000d464091340c500c0c602d02e001102caa800c01c9030100c1c040c0c00c3d5545440468000c440302e00002d020b01070303001384041e0107a1508000c1c6000392041d000907030035500b0980241c504840b40f52140d400070340e1a0021041180207034592400800214510b003c9202c001c6500707003203043c121746000581720109510150550100a01b212a4100040c8140125180d00200d2840187c0c13172510200c0c3c0b10000074000c110b446029810a02d4017419111001c01c50b80e2000070802419009085e1100400d41d0700c5509940f42c8060380102c001d180c10000d024041168481d4100103050b21600340040c0c61401511178500b060011342d0016140820380e20130a0021200d806103801401e42030011910307262850360042e40e40e0754a800081d004a0703c44c0002800e240c010320708034403010b0305e40c02075994132400501c3c028044041110050701188002c0302103680380c0404170382e081c03095034540c4540200b0001400304c1d58119600074649003c52041100100e0181c484 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 878856978 1250 878855728 878855753
    0x5041127061c06061d1504080102040b0c011a18091c0210060503010b010e01080411060417010c260921070204110a0903020607080f03100305011b050a0f0507 69
    0x40c0000702d201e03a5891064482621859030180040011410000c1411012454900c160350401c4640c454841e18650800510303000c0c03a40560015403004c100040c08846420081100d0101d1000810400c401e1034001035507403940e420310a4200743c100710f10114140c0c00e202410303001444642100e10141a5884140124080104e00340060700f01241030070580e155801107501500d81180244004e40048000801008a404445040100e014080380520100c00c240440c4030030b001d00240ea43c0c03601c071078850501d084100c0320403200390719102080f2000d0740702d0030700149131929030382e02c41c00300540c842482c074980f0101400d904814050802501d400c152400b024500f09559641e05684810f8030340100b00440d104d200100300440c03403c1001c0c00569a21440f0390060340d178100c85071a00c1d440981003415070703030142c00c40c03560b80b02c08000203002041e5031260021088a11803002803004a85030803512040c42070110313041020441c02d00440b4103550082205e10307004881850010300304910350715084030715400c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 878858228 1250 878856978 878856997
    0x70f0e030634020606060d06031a010501080c0a021902040b10090f060e060d1523040c020307170c0a05100f1401081b060906030f0603070504112706 65
    0x24101c0104481030007104600110058045088001c4510110041c0d104c3c1070040c12203100d4038000903c2902c22855500103409990000050784060703045005c030f45070002083c02102d021804140014198800b014200e50740c0c105150701419181151b000410700d031000703207001240d0254480e092030304c0355191001070084043d0306548040b81c40749060303400665a801c80d00060104881b4a400d110300381c41c1e00088070600d002220b00050000b005500030240b241883d0030214642502c0745810b07010b800c2d1001c031860101011070341000300d6001a4000c2e80d9034883c40100a000d64800e1503001c0a1b6403080024103035076000107041c1c41c8004d901e5070b1200d0810280790f10003c90345070380e00420f82e0b1701506c601c40c0084903400500210803035418029842d503103001d04c040407811052031005806c0700c0e45548050318241d9070301502607a02c0c0e0410204400c000103080b41c41500034491070b078001401c2d02c0c0501034200704480030841113103420ba003d881c0d03c4240d864085d80c80d8989050081040141d114440100843e94 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 878859478 1250 878858228 878858251
    0x504080417010b091006021209010201150e04031805180405030d020d0515010311120a11030a0f15050604121e0506070801050108040206042102030f010204050324070f0e0306 76
    0x3c4a500300b01688001401e0344000d518440d034103000c0190002120500303035605100041c1c4aa41c1c810040303014000780002165418130709100012483e0712001843d00480c401e03101c00c142540c481103c3d0100559501c2965800022503811010004170b9904558110307000704143e914240390000388034180c0c0c5c0100c1c1c0c0c4080381551402044410368900b4400d0026040904c0c0c144401a00600000d026008804c5543c041c6117103c2c0205200000c00e500c030101404e000742c035480d120300c1e02141c61002046000c50030120726080290841915800c0f030380c40000e075400106201c2c1010301b042091282d0502c081e904a0f18000081201400380c8909137800b02c00911550042520340740203800241941c1042c2d0145050003540824400144d4901d01a107042e600e814018a10780710f00900b8113a06031240c00c4003c1d4060166035010a9030440640080c001c2d60004d030204d524031071181c1c1101841842800d400c145c4180c2075404502c040d8072070800e5050415a82c03802c0c1e482209a0b40009090810070b491050b07450 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 878860728 1250 878859478 878859491
    0x25061419030c09081b010801050f0f100201090c060f020105070305101703090a09020322021522260307080405010c170f030406050a02031003111207090b1f0909050408041701 76
    0x2503900100b100c8c00750006075600f000c6002c040340461040c8000d441e6803481505400c201da0304041c400d43c85940650f8100180c4c4445540d19140540b200b02c2c01030500005508200000700000c0c003e004840c010001c030032030514441e20341142c821454040aa03052600c0c00100f1006070b1039a2400c00b08030103020340c1c0c500141e80c1c3c1484441c2c1d03030300c0400001c01917008200741c038511409a61000018002a40319000b11079490701480c07020790b0301015007115a00600d0140304041407071201c10007004842202420203200f002c554002440d5203004164004003016020031040c01154400e0a628450780c2c070903001042038070302c0c881c0420300310341000d081800410008800c101c2800124011250840400b030070440c40d40c2807034031480440c12402c0c0800341031440302421010654640d200181c20b82040c0f1740685018030f84903241940507007803040442d0311400c100310002c1c06910490b0000c81c1303112141c2e01c0d16400f542c502910716001e000024000d841c241001e001c0081c98440c2d070180709003031840078000003481 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 878861978 1250 878860728 878860783
    0x20a1115270a05120606060f0730020a0807080c0f0a0f02090703052202062214031c08070212070503090102120c070e0925061419030c0908 61
    0x40b0410f9000902c5400040c4010810600201d41d69820260035070309540d13200d10700d020210b142d00c00c03458010003030760602c0f00d103a101b035480c00b560304440c552030a0307c2c03003606000320002ca95500c600a00074001440030482a030024021500a100c03a511040a845050306c105044070304002003180c0603a201d0078816008001c6140c400b01131365019050307040402c124289012070800c0100100c0d01c1c0e40c1e20400c210100b8003590f985100341c034400b410080140004003881d0541500c3e102180c801e6603c441050342d04507002d840c01040105c3c14640c00d2140c49158080c0708070464000e18040c2c041c400790b000b040c1e10703203902481c0f0200421801d8001c80c01169598121000280f90110000d070108034000140125a03961102182c1101121804c1403960815114402e4040c1072850056124000e007600b0a0003500180b62803074905c2c01c90368181c80f25400e15070b4414a4049030b00c5081c002e841c9003a4104c0b080c6541c64020703800700e07072a280300e4500041c6c41512101032926054a5990b0480b6400116041440c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 878863228 1250 878861978 878861989
    0x21b0d060c02030703080703051902090d06020d06030b15010c02061b060a2702030d0e010203130e040c0e06010c1e020a06050301170f070e071403010b0904050601020a111527 76
    0x1c0003c0c7e54030b400c00051412500441d00c2a4902c1c06020440da000203110080d641c4041300140e8590708048215950b102981007a00100000e2008580076081d0320000ba0702c4529010510003d114103844094081080c1e41c01c10029a1021007078003084110a0611a1409810010544103d031160000109102c40d5200d95201d20b100100c076025200a5540c40001a2400300ba140f0400700d6a04118898021002c0103034150f001d48580740c150401148400034130890f440402c180a580540078190010b600d03007045584210041310114086202441c1070000904072000440303101c0300300b901044087d01d4540c006406200c15521800c0000c0e4084014000f0006e02100803074030070100c40c001c1c98810350714001d55031108401c1c841c102c10950f100d0000f40d207580c003840c11440642c048201c40c50343d0b5038442e11000300907040340c082a0302480c6020002140b0b54000640388040c00d80210144040d81c040c0010008800d194a9586051190500c00200008507441104084d000c4a141700b40c208020b02e018840c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 878864478 1250 878863228 878863231
    0x90405180a240b0a09020f1c06030b060102060f040b040c0b070b061c20060c1f06060e0906130b1306081c05030f100f03080304061b021b0d060c0203070308 68
    0x7407005242043c0b8a00035038500c001c040c110f41402c42e0140e01c61076103078901c1080b8040c500c0944c101e12a000752480082000d54010010b691182901c00705940b01d010049a481c9401c40d8404001c0741c044000c0350100700d08008865000c0d1082140d2041e9948440806070703260400141150783d900a2001d2005078075211858241e0390443c680e800e20f0701e00c2c0a0f2140321000d036600201d01140402d048420409440368000c0700c9031051110100c404840c5401c1d400f114580c03c0c42c07004242d052500f4400305da440d202d0720394406840402040c1c111a42c90b00c0e002c20810710a42c01d40000400da64000340491030312520b0212281030a40d140008110345000401400d1015011a00e15940d1200c90032120981c0c21005032034020048030164092956079400740315212245402c101032402c81c28800008104e4060021480360744100c3d0144801d02442940c504440c42084140016070000d040744d4003d40e034520390040322a41c3c001c0240c002000c941c0ca40f0b00c01c0368081144a00140c10000301e20301410340040069 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 878865728 1250 878864478 878864543
    0x411031002040303111e030d020306041413050c040c09150e1c060e0307120f0909020d02090f040e061303090513020316091508090f010c1d01050f090405180a 69
    0x411a20031b402100c079107910580608110043e030120101d075091300c49600c44424421341408120650804400c1000100400007007145d003481000140b1303a8602700340c0a1032444004546401c00c1c4039090280115804201e0141c050405c0780390340c5060800c3c0e0300d0920300c010381019807003205100301c001d040c400c040d911002d0200031694000c01410000881e404032015503000d9a1414902c540c0100c401280c40400395489044400d0010420034030405182e802000d01c80e0044503170813a100c091006010560b09103401c00502508003c002404107441c0d000002c0d54103200c0d107001c440e86a1104005002540c1d060b0180e680107a0100030071250101c13501818514005c54201a10b1682c41c6c0920340e0f15028072200600104072107203005c2440340c202003014a030810701c484000d03c03106000c00c1c0014806c000860790045c141344c000c2105000f039400340c02210342c41d002c4050721a1070b100740c07601844050b210190086100441c90741034100150424003c680c0c880344220040f103a411205502c1c984050300d0391441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 878866978 1250 878865728 878865763
    0x101d0303040e0c03190905100506010f080103150b120102030106140711062109060906132d020a18230a0c0e0d1401051806041103100204030311 63
    0x20300c8440c881505055010f075140250580e2030780e03200541c84a15003507041d1014110700341303600d0f1420400081483d5485981c41d400401580d0b50300f40046900026006450b00420305100041c0701080700c1c2010700350304202d2418085035000c150b0300030030035000d003407a00351005075400300044c4a4294000300a4101c20070241304641030600d99228111311304a92030001d4410b14002420300242d000741100e001d4122415a03d140c00d500d0003000303281e22003030101d0300440540140350001d00400040200c2801c0b00e5003041c00511520218010060281d03400158030038070316a800c40030b40c0113a8079203074660301a01c20643ca001120480c4c15203102581c41a40c01d545510b1038524604003030150b200030150740550205000f00b907440401c01d060b0b82c1c41c25101d4101d90441c5101d14200144400c0e0000103104010300350007048aa6500d0300b020b40841d1105800c943c86400850124000c514194a01041d042c40141916058a100000c10040743e000c0d501c11004194117142008103203105104c0d041500c00680103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 878868228 1250 878866978 878866987
    0x105130c111501081e100c02070e16090902031006140f0307020f06010503010c050a0f0c05241f0302010c0c0e010f0915050901120f0b0f10080d050d0218101d0303 71
    0x2030b119120505840046d20702541e4480c4401c0241c82000800020651404501d00e1801c201300d0000c0078480190300e030004990b0150000030000d00034400c5070322406903a0045c040c4c2d42d01f0941c040300e007040302c003d030503104500130f10031611091401001903006014680080507413100d142403003420720b64147e0080b44179074904075407404126001021503090350700d180303810100c02401e1003003034032246400b410142030341c443c2c400c0b028801004c0250420006100805040d4285e54900440302e6004076610300c40741100740312404200550141c0c001d000342c00d100c1c5840b03400c569101c0044d182500d600b680005078509103a40c04000c2d1090910071111141c0d518090f004005040201098107d207040c03041016254542511308144030080d1200c40f4140e0b40700c41103508a00f409213401d0f1541d5000e950b40e0100412400001551200009a0138a440a540c49250400701000d01c110000c1d00500310000380052924800c4005640d4104540c680b181c0b29100d121086031030701c4500c48504030503400030b4025441001b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 878869478 1250 878868228 878868283
    0x170c0303070b0901150603150e04020a0905040212010504110a060203030709180b0409080d0b060a0c0f2d0312020903100b03010e0d09080606090105130c11150108 71
    0x448070280e40016904030a5210314002d5030040c160403907400b040c5403d103140412155410380041464800c804035002c0b105482c0d0041d4400322030b041e20300950144a0080802c07180480d50401c41e400b0b80002c01c802c12500402003500c0c290385003100d08030340040b20380300486070707524094080c103011305411f10046055203442000a001d0346107038041e102d00210030020208840031140c119138940c6c50081c1041c062420181f83c1815141c000d60b444151003070a01c5500e503054101242551520811035681281c81a960b8686000691308683c0c242c88100c9410514041d10320743e640446800700c190409480e01d4203660800800e5884e43c252001c0421307004200401642c0d0340022500100150044005034030450500040e00410304001044214081d42443c040b640c1d800c04c480200f110381c8581034401e40d944240801c84440e80c240189a400740c80c5240325400e01909600c030303640a40c020b06216250f1001c1080d80d61404401d8420240b14051242c0140100c01e418010403400390a03c0c0b400303010594091 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 878870728 1250 878869478 878869483
    0x30c07121208090f01110904050601020118120504031205030402040c05031302151b2515030e120318070509040c0621020403030507020405061e040e0c1009170c03 71
    0x20031031074007002a06404591400b006010751805140c40340020448801340d408001a50b8010b59041c500c968505400185154010301403100ba04000800d2504440304540c1c0b2602d155110300680010042d0602c030100008044074600c084814180c0c0300d46840749410b104100680d40610404010400144240a410f4136644032031041e00b41d0450b4051340740c0039086499801c50140c80c903118044025014000103c44020072405000e805944161084041039000f040c41400288100e016135040d0140541245111340e01001c42003080703030280c0792042070f450035174011500140c82e26022004079450643ca4001300300640c00c01014103451454244c60540c4403040134203c1442950b0030301407420720350b60003c801010030080c2454240c00441d200c0c0e449040c0180180c03c1210128042d0f441e2002142d030510f01103140c0031a0345405002103403e6000841404003412140f5429605842074996018040c1c0e03558882281c03400716031740c50000c0310f8540704d40075800c22445801c074601340e042282d85d0300c07854601 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 878871978 1250 878870728 878870753
    0x301e0d2003130203030c03130f0911090d0201051204050c01031a10030507020312040b06040c020c130b010e0d1406060108070f0518030a050115080304180509011d030c0712 75
    0x3005041e007601500b43c00401c0c11072064443c0c3c0130b000d0100258102c20460380903602c10545c6e032601c85440c0c415445550101c00c580c81c40d5180031003440103001d09013083c0b529800e000e161503c11716140b13040607c43c0c0780c8240200030541d421141500460003020003541c1c14801d600b080784006651029000710040481c60703061080045104141c0c0355000942428020400c94030a1218045040c056240030305100c198154162001e500c05c504002514400d144005180c1040030f00050500803200d1a50203000020b20420038103d062118590034a103807039460307110004640d8080c5001e6421403003803048540c10701d42e009007680e0500c5641d50074480403960020040030641301c18208a55035509102114040c070000040c8641c0c544504c030482400c21106420020700007040c182d100c82003503202d00c0225103c0c00340e400352041070403000d850804910815000b07682c11001d100c000089180000d00c01c40d0143d000c800c41880150300005000200c84130410600c8001d24000207080c00c0002c6a580b040074480e039 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 878873228 1250 878871978 878871991
    0x108040206090f060d020a0210020a020c0906040e01020a03050a0b2b1b060c12090815042307080609010605180709180c030509301e0d2003 61
    0x1400b0403442c200391242e80c3e0204081200810103030311860182c141d24080d501c21040880180141c05c1c281050880e01d00a90317a0282c030f150058421000750b42c0038040021002400c00d036019880740b41e100c450300001e20050030b0554017660003041d03501d003050704502540c021030107142c0a01380350500c20341c0c03c41c03000091000c3c17500004038606204000307040c001c89442c100c0c034500100846010001030410340110134159a207201c0c0c09021580c400e00401078400c60f41c11300c100805900031203802221100741a0511340d00134410500d0945600602c1d5460851050000c08103c699100031414408a54108a01d950000c0c0050092020a0a10b804035007100d10242c0d51440b4040c0340001304189602511800024008000c00030f52000b00303004522002d08503142e120310110b031410002c509121008100c00c00b603034403100c0407584145211091280d10300a018903590700e08505001e840008540110070703100480e0711091003a150035010514904407202e442140400864078600d035100c01d07160704280c2c0c2d841300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 878874478 1250 878873228 878873239
    0x3030a09050108150a1d06040504080a050703052502120607050d0207030e0904110f030111070b10030c09050f0c0705120a18080106060215090a170403050d09080d0c0201080402 77
    0xc560ba085008800131405909511002d00003000c202602c0b1705041c0241440741928581c015240c0105000480c0d00a88020f00700d090100316907401980500014503a051091810a1508004c0380300c0f24005480c12080e80a845c87c07801040d42545001d0490b03e82c0740c1d6580001e08901c4c20812800b8110384901543c10b035943e40c0200e540c00074903020303c200304c20040d0058541c8503107240c01e1811008007000b0406036849901d071160341c0841070405224864074208490090340c641126501c0d01d14030018001d0444203800b64044c000301c00078800600340b000819200c900070610b4106292410b102310002010b81800180500440010600000760000d1403803120b04180d6450315548012508110b500c1c904251601e60b1000000b003420701540a5070888207558240c644880302e219410101a130203580147e05c40d440f071020000070440484c1500c1807008011100c42c5031541e0b0342d4840d81000861007006010076842c200c02c01c06c03000c0500c444004070120b850005d4460f960381e8000380501c04040c0000e4040d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 878875728 1250 878874478 878874481
    0x2030a0207032c0f061b06090f07050102060f18030c030306130b0603060415050307080a05010606030606050d05093f0a05070b090304030602040f090c05031005041a06030907030308010503030a09050108 88
    0x10748512048071b100203107440e03001d4410482c0046180d581c01064907420720a00c60b102c3c02e80741a19000c20110242d4205034003510781e907102c00c0000741e414140a840503d40314881d0303410201e18041007004102068440b07001c1d603140c0c503143c2c041180750303401480e0302d8074140d0802d101700e04142c1d03075102141c2e03000c5411940000c080c0894a0302c104c0400941d000300d50140f04040e00805c41980020340170780068403400c02844050b03103440003182941e00034407810b00407039030030720204500890680146a000c050740e81140d80c0203420112104902400c000e1403201c021120a181c1d00400c6241c0b40030005103c4641428508410200000c005218418001d4140c487d0000401c1a5160601c2103030002d40d04001c065444684900640281d96035a2185d1038207103182040644805000c0c00940348a0195240c200808524000920003d800f41c04980c6004100e641d000500c15076804000e103001e401035200034041142580ba000e0049401030b0400361182c0c2c8244441c00035a5030149001060700c00a10340020103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 878876978 1250 878875728 878875759
    0x6140409050a0b0c0c0106140901060f0512070e0907110c0f041b111c02071a09041e0f05060307060c0c0b07050d0e060a0c12050d02030a0207032c 64
    0x2060b5140784002c1920074202e00380896500f42e503000d40707021074800c0001c1014030f0380c4100b00803a4443d03414656401c031040500400c480d50185030b683c0c44024481c1865464070249030201009990100c03100c102040c95902202024100a80701c01d9202020b400c3c01161280c200c03403001e03903c01100307140b0f40c40f8280488482019454580080c01c00840094403986c000182c0040a011042c00e1180c0005038454900c00300d4407086102ea883e240d00d400c0f6001703400c000d42408071050306e0101c04100400718140811820950b901e0b244624501c440365100b54480d051800ca0b004419590f805100090f02820b050501c071485d40c01054800488007182012000e04081d4034043c06444010b0707101090b0110041048001d104000c03401050440d0701d6550b03000d90401420420a4070f029030b014090000d2078070141c07000050040380702c0d106031425604160b804c2c0002c5945442c244c0e07100312515020b064002c5424002c040d00001e10151000c6400131140c9400b180401c070100284030001000d200d41060380b9426003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 878878228 1250 878876978 878876983
    0x2303040f080d08060901123e0103060503011103061009150c12050a020d0e010e030d030911041806020f190347031923010614040905 58
    0x4140040c03202199035500c0103915294080340b019180403449142c0002d039a0b240081600c4d041e29440500c03050071104076100e450707882c680081220042ea40e11040f100740c03c18002140c0c44144030700800c00e80c00000440c001010355100360300c04c034000c0e03041c000d4000001c40c4907002d50741d0120301902c41d00780c2c03119104000c0f1400380d0b055200b41e4141c5507804408041e55403100c00c49080701d000710300506070b00c078010204035240e1107016140f4005820280668035000c1c401d101440c200541450940f8074401d0f000006814840c10031551400b20b99a55a01000c200139410f0441c030904045504011901c00c003016222401f64518008012940c000350008401110b11b00740e444a4079400c2040c00002c164180150083c045a658660200001c1031a90810003070603c034400d011260743d290a603040c024540c1144041d107010b01c3e5540c075020f070000c1904444419a90001c050b40200710300002c91030b000c00e600301240542007800d4400d905150b014802020342d280b00d6924074005540001c4c40500c141401350 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 878879478 1250 878878228 878878237
    0x105060d09021306030b220209190b0312070614010302010903172203112b05030708030403030c08090111030403080c2b0b03191707080f13122303 64
    0x24003526104005c820710803481e50141c400e900d001000e0000742103035850b6140d00c1444540c000c0d40095544001140b070341c000c0030140d4409a09010200700d803091000000c0c1050000c40320311913484d002091007000c1c08154010980b0006602c034a541441d411900005c1c0030081c1800007a210240a02006010304446001c40b00781c94450440c0b400e0b88030310001484041d081d144070955135112600910661881c141d6200020100080402e800d44000d41104801e16241c03d0825501c0d40414021034021402880041d8031a030700c03e550015000c0d1903440080c0608002601c41800d5a01d00000720901c080040c0c116038003d0b4050503c4412030390703071a000030200e20540c0f01380302d000000c3e6040b140c82520411648440003c00c910705000c840c00c090207059031503c940420400c6251007107840404502241204441c08980c0c1605c50b25181c219120584542d20006484030709032000281880001c07040c0c0300410240010b45141010400941c4444081a207a150801040e90a80a4900014104000301c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 878880728 1250 878879478 878879509
    0x90c09021b030a1d100903060507091706010819050601030314040302031c0906110a1e020a0617010504050103050c041e0603060203060f040e03160606090509060403030e01050105060d0902 82
    0x100d90f100c1001c000200290a1000824103100154400840c0d03031500720b250449503050b55440c01600c92035602d40c42e014000140c54041070150075080401d40301140400c0360380075401440104242c0d45484c003150b1600810130034015000c00354012000000f4404110241160b4042c036002e8500e0001240d803040600c52580700075454807509000b1108504110540742c030f414680c1d101da242c1c2da507907a80306481b007450031051140c0c260800c03400c070380009084001032081260081e1401b2003100c1144d01080c0040c0047d041000410351083c120040f41c05100481805010240d40038000d551460341c07610390320321207042000e03c10b5840c1c0051404e03006840203900c041c2c200c0108240812962828414020752080c0c501c940500903501812800d81414010001002b207102d00235450100f4421051030b50620400046400585072040001c11000e07500985000d400700c40c01516880c00c007450701908654211041160382d034184001041155140c200b6104030400ea0600482c282c5602c0c80041d8100032100d458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 878881978 1250 878880728 878880733
    0x60203100e1906050603010b161b0b030a1b0e0108070212030106030c0206090106151d061b01140906060d2102060117070b1803010b100e01030f090c09021b 68
    0x104900c000e140e59000724040091042000f0306510742080c0300703061009025056009004000b00c070145500015100d40c0c981c02440041c51070380100002e807070880c0b603a90050104c00404001c1c4842000d0b40e210312120180d09180140980c0d0890a0241491201c0100e80c0c0c10b201d200b900003541036000780002004243c1d40780d4030b29640c0d0f0311200040c00070481050310100511400e40001c0044c04144202410307642440b4660424403422841182c075640000b5144103c09180560644907445a90107001c0e140945540500d43e104410030080c00c685c20f5001003040c4000840030b218083c1408140303d0781059054031005400c030f010b03041081010103403114060384082244400c909055010030071505890040540d0b82916040070116a515840d42c02880c40603102040745c0a10031a2320f1000c14a001c101a0003c50000480c2001a080700b5040076100d001c2450b481e00760400d0740c0c2c50710a800780040145000c010b040c19503107540000c18601d014254000341d0006052420034001592241c6840b591402c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 878883228 1250 878881978 878881981
    0x160510091112210a14120a020c0f0f03041406180609030f0f0d020d0c05030a030f140405101d060612010e070b090102120c0d0e150d05010305060105040c0804060203100e 74
    0x60f0f180981d00a1400900080203c100005400104401c49107500700d400d0380300340707540c0b03501c08104000d40c40400c103c1528400d607503914002c05800d21803420301c449110059900d49240c5000e80c0203500701c3c0c0444500c01e10301000a0035015046012481038448140da0003500e540c85180882d140030807800c56071101d0b2085400380c2205000020304590410099402d841214001c0d80003565030059091004101c2d4006000700f02d040c510075801105540c3c1007400c0420300300e1010700010702203081030750152103070780004040c5c1d41d00c100103004462101e900d0001d00c2c488030203034516031a01d030340001c0c1106214100804400d02900c10940000781c0c8890307150240c45020b591420f10410b10744c0180e51581c054000c0c2401c1d10180c51002e019200780a412001400354040291804c4a1441d90070160750f13030101962540080600701ca40103002049103c000c0002c1ca035041d400c0461908a0581c403980c4507030306250300700c2c20302948480140c0e0800c2e40200090307140e880e0300401440b800030760380040244c00684c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 878884478 1250 878883228 878883283
    0x8161112010527100b0607080304030f09050f010c0602030417030c0d2304150609020309071d070c03080414101407032a09050303160510091112 63
    0x184070a0084040000d42848214401c4401c044103c0f4041e90329241d80001600e00740307920150b00f2540240030020201e9240803030719038074541603410a0301c01361300184407400050324103600f080d01c1c100608811100c410032694000c0000700304044070344d80100700c02c0c0c0100c085800c000010f003071582c500c0c205061058407481c080007440e00f9138000b00c0000300840e00300f25491950441c07010703c110102c680324001d109103503611340304c440c0051003942500c041141d880c24002504119413018600900c00300000d031150515104100d0640e5880c040c0e124414a44041070000f4503400441104509500d030910048945e00d81c01d103a40c03a081c4460b4440718130300600d040b40c40500e100754042d2200048625036808161643c0000b02c040784c0d4505d0503020b180b0940c1c00c100001c4036070680390281c582079a1410a102e59100ca000c2401c52704400d02d6001442000f0800800300b2005004488403000c0c0c001007004103c1454452122441d613008019004018021840442140902544102440801c0040651038040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 878885728 1250 878884478 878884481
    0x100e01180b100c0b0f061e0607020a030b0105030f03041d040312020304060203040c0e04050717010b0a08071a19050d06032406120f1220100b0a030816111201 69
    0x100781104d21207048400219081c601d24a500c1c02038602810300103205e880e00f1b9901e0014611642042d92045041c0440e0b07005a441c0c2d54100c02039840780f900440954545414146400501100000f581d0001d02040c4103601780104201d04124001d8040e011a49072414141c4680d0040c03074020240d40d0000041105102040e0015401176214100000a4543e0b40e8500b00c418002541d004240e038012031f0041001d98500c5c501c0c200c4240c240c5e00001903003e1150005044201140e010411980003420200201d038043c1161441a2030020000c030719064000344820326020b00c4c7c0d40c042050207408102d08045d8005a40564055640040989184403c07194454015400c01800c80c2599041440110b940014840c0c414401035102c0642403c14103d80d5404000c00351012592040140e06940741902601c00d2825103452240b14010303144a802c9503c202042d559440401401450110820400103e58108849050201e8011110300c48074620b8000c040400c1c0307582032607020f41078441d11310b403c2006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 878886978 1250 878885728 878885747
    0x50d02010e1e030d050a061e05030c0603040f1e080d020310090216021e09011e1a04050111010e0609010c0912021f0201060e0703060806100e01180b10 66
    0x4a0442d9030103903460078225400202511080700a400034441c0300d1316040b80341c0100ea00b00001e190b0100f0642d40701c0b9060b060350028162044020801c48030200040e0400707201c2482e41c0c060980d801d601c0c0d85007035103c241080f0f03400000180382c0750003082c1c0700081180c00400c034061550300503110b0340d603441c04402440294000352050340d19580307200400907441e05c0701d1007140c103a41d00c1d400a5242c141c0190302000340105500c03010340d0400904050181040d6650310809001c1c014813045406040d09822082c405117500d03401460a490f0f40159010743c004480c004e48088600910300b04440050f22851503024000e01c01c0c4100c11482180c0900195075019001442c1d41d0505035a10141036644400d005e810095400010350408044c0701e414842521404901c240340d1041d00004c00c08680c3c590a1060306c00c022500c000000343d40d04001d02c00300800344041c0d600076100e0000985100c0c1001c8060700c2c03110062007104404a0200110107400606070405041c213117000b001d4485240c03150b01c2c0903100048 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 878888228 1250 878886978 878887001
    0x3060115080633070b01030515010b09030a110301140708090d0216050f12070308040f1d0601050904090834110d240e0607030902010c0b13050d0201 65
    0x1c00005009810440841240502250355201610146080c1c49000100f0010080072800c0200701d030750007040082034017a0003035100b40700800d003040204180c1d090960301030708285040e800410181038299000511720b4110742d00086c420302526038000009004001c2d901041c148021104100310245803c410241d100b800000156140f61424142c101e0312114603030782c4005683c4003c2c4081c801800c0c000764428064002400342c1e900c440d420600903180001c1075100325010080058240301159801d60790300010040d206640b00c07943d5030484450100400200750504102c0081400901c9580c0c540082a030640c015034032a03540d5a010401e981c0300801c001c00145281d194001c2c9000d075110003118000300582241c1c80c00021202c00042200d00804604180c0c0e00b4040c0703000300c04c2c0d581050010700c0d011007541d003000254001c0d038507100d40c28204000d14803800d15141440840c0940d8026041d0100f02c0c3d80060307100ca1710f41c2e40382c4007140064402c2034003911703e00c5a0b441c545075164055019840004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 878889478 1250 878888228 878888237
    0xe0a060b04060503070b030c0c0f1b010509310f0e011b090b130b0c011401060503070e0d0204020f0a050d15051509150f0a09050a0e060d030c0203060115 67
    0x480003801c0c402500c070742c2d01c00d29415a0040c40100309080c180b6000e141c01c80306950740f00d490159503c07081490302c020302c01091120740002c1d480501040302c410300d8a4a4401c02e0038000d04224040340043e11000d14804010034241514001008040710820303117480310f200c040701c20410038041c81180c1d002007070b002d07094108039031070412006126058a880e403030003504a42d482194613802d0031000c0100b500001802c1000480151021138440103440c003806180c01000000241c501e2100310105001034181d0081c0e0910108009000409501450543c000e05090b05c204030350303c240e44040760081c45500c500c1c0c41c0c1418085411344420382c0c0302c0020003001000b03400a202c0502c992300101d030088564030905a1200140c1d000240280c5000c3c05490141c03c01000b030342211600302440145517118080c1300881d5480015908501504148950302401068416614140c24007040c83c41490b00a084a8070604d40c030054401014480c509030200545c0c05801d07210a965a207811400a48d8420a09000714 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 878890728 1250 878889478 878889491
    0x60608010906060807050603130807050109030806240a0507030203040b030709080d020303090c04051f0b210105130e121614032d120f09060c0f040311130e0a06 70
    0x2c075400642d050560346c000344071600c1e50302d0316603075040408250f4404841e910418494800810b10038440c40100314029242c00785d90303161641c00c105851207064808110aa01a12001030749079501090346c0a201050404940d118103504041e407450145510030b59418100104004aa99200707010382e0864008400f10340c03e001001c001680c070307400120380000c825800800294018501303900040d411000c180c01c001e00f00c21103101680d4030b44071143c01540c946040028000c1003000d20510b030018400e240c0c0f042c00703400e5051070700051511000200001074283c445040c01c60022050107007040c076039074004000c0e40d0fa171081c0f242004031800c10344013910f449000803c0441610404011590700408182c0c0390304c2a03150745600c0388210035110400e01c1c0c41045c188145405213140702c0c0792a0154406002911407442c005104a280c9040103000c8404504288a424054a841e00541d03080d603907c000c0000207940444003180491034101940d0149a0800c2682c0a100001052071203446000320401c1c01807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 878891978 1250 878890728 878890739
    0x1103030a05090d080417010e060603301201061205070c0b1906170102091903150c020c0a0617010905060d0f11090907150915080a060306060801090606 66
    0x480c0a1820382401081c010845540076281078806501c145108403642402c154070345a00340d0394101000e0343c82819030b5680c00c0c05610404208441503100108130300074040c6d03207094110000a80c01501c0e5140d0285515604176000c41642d1060710f001065030002c420b050343c3d545a00070160040954041442440e080100e0000b91040d43d00c1407486422071103d40040c5c40b804108050340034001c0da84a40c00d56a0032001c0780b078480521000109241420001d40c541d20138208221102200044144403080028000c2000482c8425002502502c03c0000038000507110821390800841054065200d280b814012881e1364001c4070441300c84510320560030250313072540500800c564094903041c0d0f0240003c1c2402000905580810799924464030540d40407401c0000400c0106000f540c000341c4e9a04034a90030301c5940e03040c425000c0708070320718944503211510702200020a2002d115010f0208060301c8000350f50300206030041401180d015800b00000b42e502c20071700d0300030b11100c4011180a820000005070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 878893228 1250 878891978 878891983
    0x80a050d03060b03060603010302010507020109030c12060e0303091c090e0a050f0601140d09020103090c0e01170a11040506060910120b1807030207020117040309090b10091703040f0b071103 83
    0xc1000040c141b00d103540d08540065615411041c070490402080c0a404000540c814814000500a0782d021403c80d030300a182030700940d2050504501a60b00600400c03400300800121095140034045600310fa04140e0b800407601050a6000f54015140d402d085c03144000c0a40c0c081403282c41c0c000302007425515080f00468402440c20b020404500b411f000c10002c01c03038240e1000e02000c1c4141400500c54920350f58050f280c0d0106c1d440101c5804107040100001c1c0024028115100c0840015060231a01c0ba035074900d48105642c902d6008507560780004450342c50385811205141401002c2e07140548843ca0001c007608240c80c1c0d0302c1c01d06400d05114010350f0800c04400b1000420010050f43c0c03503503582208070025040008141e040000e80c40e44400070380c4244205a0007140030703980d01e0350071030708102c0c15500741ca5003000054000d8440c000e4019000b40d001e803130402642c00001482400c084803c2c0114a140500d070484040e842c0b0160700001c3c0c11462030f00400c10b0794440e0322942c070564152009c164 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 878894478 1250 878893228 878893231
    0x1080c0a140102070509091e03120108060f150f12070302040c0903240204050d3c0b09240f06010503040309141809100e120a1404080a050d03060b03 65
    0x90244c0d014180078085481c0060700c003503100210314100c45401c0c01400111101d00201402c052840e0000110b08550040080c400390241441c880142018185210403100010000b0803404030040d100d03c002c4802d6580740007401280e04010440451a0001e00c034481c0c8420321803004030b120740d1404400b01c941c1c13030084c080c96084030b400c20b030a82032602c2c45290501c1448483c1e015015180d60030403021480d80d030342002d05280380740503c0d00072101620741d04a1845800b1032041140030244104c103113064050083c003440410076400b80003541c851700c40010342842c0c603c1c8481c0364151050381c41c2444041111800e881b82c8203034003003034000300d880c2c486500555403480151005000142655004c0c096011504407540303d1080190600c02140b418014104621005a074181c00c1a0030102030342400c02023a0298806001005d0041c0c0410b08102c0c401c000710f803003104241f6003400951800e40403441041c10a42d170041411006868402d02c103407030300580b111002c076011000310b49000c2000c42c910b001c00003079070f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 878895728 1250 878894478 878894519
    0x140906060609010509120f03040e0108012702240a0311070305030714210a0b0a05060301140402120c190305060f0f1914100318030305060303070b01080c0a 68
    0x618001c40c0b103004485a80c000b1000d80e40101000d2a01d004000742005450510380b02000075540712070400c01c0c06100280c0607480003500c0e078181703078085815000c58202c5440c42c40c0503d04200135004544081034000c3c901080e110002e0039484010f15040040740014900c10941d540c0400c01c070310358016035403030303134021540060005802400054003590103031030360307449000c041e84940f401d100850202c1003441b915018460704203520001481490100390081c85444041120703400c2c0000d05010110700d85010503c5005083c0e6180c0d140d60465850715811101c0d500e0b10746410107020b29041000c0341a41c0d025800c0041c0081c2c1d0302035112a200c0c4a4800ca80c01000000c003682c005900302000c10203030a05100070b05500200a414200c009481514484010120700e04016503080034030f01040640402d251580301454207004100284400310441900e07126494200010140c4504010928600440070300071302110011001140c060b000056110110034101c800c40c0d652910b514118071140d0310018070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 878896978 1250 878895728 878895739
    0x1701152d0f0e0a211a0a1b0e0904060203060d050106030f020a0605041a0f0f07030206060913051207170a121d0307170c01091401140105010207030f022214090606 71
    0x10300340038940110809994500517072421100f070000c1e10080510320030070b69034884643c0d903d00c0080362014030000080b40107400b6092440c0100c10f454042490803400400082000b54000006202d9540f101d11808010b07811070001c10255031645040349005092420076803285100c0b0500040c81440b0740102d405964032030903007401321155010401480d42050742c50b02c05190b41402440301401602e406051480e0180d40206107504003502400300d40030020f80400c0d807400124504c2c0700401ca0005410504007018048560303500e00904054104880c0c42082c4149001c0020301e0754506a07000c006c58035001c1c0c003124104440505800e0241010900741404107040c0c00c00c0c072a14011804030035500e810030102c0415203141a80120a003801c4402008048504030004d01803680120700074426030065480c0e140c40d1600c25418800080c1d510580c0c1d100041c0f04415501025046449000100703198541400c080546607203480c400d00d01400400c1d038203100c0c030b00a180c0000d072020b4000603482d009503c058070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 878898228 1250 878896978 878897009
    0x60309030703080a061737200604060503070905030703030903110118180b0d0302150a060308180102100506061803030f030a0c1701152d0f0e0a 63
    0x6058581510080160a88642d00c0d440010042210103046c004100f181d0090305880403840c4122000307161001c848420400580700010401054152a480c616040344115480203004900200150103421401d0381140e404a4002500381d0400061400740e081070f110440c1003620303101810b036255464400500051400042000816806415a0720303100041c940b0807000700340104407444004280e400040350313901d00440b0115505144c42061800401190301803003004064030b009664603940a40b4101e021203250102c1c000c80c0465000000550340210125182d6040311220340c50b48408000407030141c020141490304103003462040d0b900c564401044d05081c001810700301c3c014040c2c0202d0071030b0513110400c1440c030b06e1219000654824442d0041c08514821011380c0140000960f44401003255480700040c810b1800c40303408100520158035100c42c0c1c3c0542e9480300c3c0e003811400411407a0204550503254142c960200c041114040701e503d84018441d0a442400705d60341080c4035603900c0700c50540 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 878899478 1250 878898228 878898233
    0x2409030601060507051e0c0a1e0909110405090f0706030c080a051b032d011a07050a030e130911032a040b1206010e19060e042d0516050603090307 64
    0x6004041b40c0d4040c9044031200780e500c00210783d800c07505400c400c0c408d958030904007034111001000c503c00707003d101c130052205040039940c00061440740703800c6500c00c5441c1c0c800201280410055000b82e00d01d4035044030442580c444010740140601c000560004503680f0001e101c00708603008050243c1c104c207032074110499140b0550060303900f0151044c40001d14400e03d81c40c500950700801044200341c40c0003080e4139450541c103c0510309144500e00c00b011010301035500031500c04600d6031552909401c2080045030120300046001921070b284585062618508000340000311744a0000c05c0400d41c21107030301c481d103503181c2c005480c03290751040c16032600c50790001d00e1400c05070002e110350a00600050003940b0801c1455003040d01c260001e80b841d14281080003000302003801c80a082c403446010400405050205168480c1c03c010300c0174126012808264424800a400e828100203200030000002c109500e00b0703d49515a0445111000034000c0012600345008400c817402102c407940218074040856 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 878900728 1250 878899478 878899513
    0x503070815030f0706020313091e0903050d1b030c1b080c0127290403030b0d140f0c120a1202031c0b0102251202240903060106050705 59
    0x1071154250281200309031003484100304a1028000d960095510759410000c8011088410781c40304600504000a2580c82d0b0494040c0c0c61514141090118078040f060a060320036103e0101c42e04000340c5407104104164611140022664401c1e9505105000102d40101c034241c034020000d20b02a00f0360000c500024050b4401407032403450b008000b003604007d1507948103c00c000700b00700090801c0c442c1d00d18000c105c9800d04400c1140000030800780551802401041d1046000f00020189a51244143c40075598485548a0b5030b034016060018808440002515031030900320180385407090500c0c144091a1000d4512489291176000b803100540e00c1c3c8030841068120400e07401940000c0190450005410500031040c1c103c2c00004502c851108000924051003040240d00007034151012400350300300c01035048210b840e10340500601910314000034a02124441400a0301101c0d035000d40c400c8080784014040548084040e1030042e0307a60742055aa912880c04000c0141d002000700800c1107988 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 878901978 1250 878900728 878900761
    0x70b0f1b1308061b0910020c0901060c1a16050c030d09110a0807051e0a33030c350a0504060c050f0a030207030c0f050f010f020c0c0f0103090b13020103060605030708 73
    0x1f1310454480400403400300b140d00e08281c1041c00000c0403500240140f010041641c20304417046139900c0d849141c82e10f4145c0b86a00d404001c10300304040003440c0c00e441001001583c0c480790040c001049801101d1420406285440c00241e028038110ba00008502102044031000c0b44e6001c0c14003d5102c461130603012498484c10306455001ca9070f1840800d050305401c04142081a01000c0540340850101c05c1034104001940400d007014100f4100b650741c560b00c4000c900241812001000100e113541142800981ca0311800302c0180c3c5c5103004203c0503a00d15000700d80902c1c040d80081180c884600b00c112400d208010000111030810805000c0c074621030fa0003015454040d16000f03001080681e10700c1d0740c0e000880d40c1030300c15500540d0f0121130750a00384103402085600c3d11045207008860141c19482e407030245101481008940c13040719269000c0c1d080304180d9030780311144100f00e140443e142056011640c1059000900d4040b01041d0365014400f2a17005007101e8455051a903118400d10865000e07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 878903228 1250 878901978 878902009
    0x40311090703060e0c071e0f030f230301030c0902030103020a0b03060f040e010c030e1b040914060108030403110103110403020603091c0c1403070b0f1b1308061b09 72
    0x103031400f0028042141d000c0d480c2c0604003180e5210b030760b002c02e8140150a840c0340440390300180c149900e1140090004401d031403d030740d894100002c60540c0b600081d01c06266801501a941d40d81c41030700302103402c0c004010f5050740c0c815501b0041c20303511072140008078007003400009d400406110040c050721880c100519801a0018010011140d4030350118064501074048000d2076911194600519509801030124240703413500103108a00490301458000b10f18030b030003a03000329907984140003841800300c02d10a000d82180b0483d00203594805025540ba4400d20090350b0303400d400f50b0855183d40c8030b80185403114000101c0c003400c19045400b004001d60014040301c40c18803540d2041200c2e19001503994503c12078035210305040038414107181c080e40b91020000501d0360400c0000c0000203280c002426005019611060603589c0d070001c030746682c1c15406005100042020404034107000382a800701d019a040c0b5002c2e681a91288081c0003a03c04001d0a0000445410300001c641ca0504030f04602c645207 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 878904478 1250 878903228 878903231
    0x405010906060b04141e01030b0f1503071d01050712050702040c050309010e06010b0a0e15043f11061c06062c010c020105070204050f010e0606040311090703 69
    0x9240755118001c03180a40d000003200040814100a20800a252005100000c2c1c910400048038440c403040c2c050203c0f80b40b41e06040d80c0319400358503500c8001d0074400d4190058160b513001045400020a580c01c00c4078024002100103141512000a0318080c00d0b0100040c2c5820381010b40650f69480320050b56807044040203014459203025907105c1c01010042030154a03130f2030343c900b4030002c400d0a440800110240517480507004000c10100340c41140c017056100c0c40c092412000d407000003544110150700b55007030004040b402190300815145540c05d00e48400d02c590500840480d1884c9903009801d20422030030b840c5481400100b410228402d0079460003c210614203121131426003a440500c2101c0001c07103903162414420103804c54103135214010b00000e1b03281a0002016030142c80610100e401c0d04205501e68140116401f5800f80d42407607034020310a100f0307407804498a402d403990920850060070090702c0403512900b48401150709a980080c00081005030107010b0080c50700000e4118000c26 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 878905728 1250 878904478 878904491
    0x30806060c030310050a080a02031b04021207080a0b01030e0c0108151003020c06010803070f0f030c061103060301141b0327160e160804060e0d09050306100605030c03040501 76
    0x81e00900007107108001104201003a103003480c0030b000b20700d9034a07003200301c19034809002000541c0d4005031054105c40c00d00d05164903206a2004500640540c03d141f4520071a07450078070030710320b400612207842400d009104124900007640114250b5000700080e005540140d02c801003654071800c4480e0703101041e03c06951084036000003181d8064030803181000040c0d40030581900403501403040e01d005220a500450600311161120940070f041504010855084035010030201401000351140c030f075400c007500b008101400800b080540d441290300c240b01c0c3d40b810004904103042c010600c1d02403c070000c10044402c038108200900d0341d0001d040b4000b150665030030f2071a038800390309450810035407490241c8401907012280c88828002c0390045820003c44004000c4625108140801d028115140c015050f03211811704400801e50640860003a0180003107000300940c0140f0030204480c4140c0403200943d481a180318070036071003402008000b54080000c60038012020015582242c010343c00013400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 878906978 1250 878905728 878905747
    0x816020a050d0f0810080c060d0f02041202040b0a03051c0c0203030d14010f1208030c09130e0706020a0f11120f070603050a1b030f1d0c1903030c03080606 68
    0x2d01d125034107204005076207150b03503200055000800540100051a200c4615400c09480e10b0b12032808180c154005c010105281c805100310f07410851120007405e504540e5282c03503040305810b4041a20040e4000e07402c0449050f030300e0600301c01c0441145c4d0007502400040b02111103800300c012000d0400d03410420301110880140c0c1d0f0500c01170840c030566000001d298901034283c000c503900140c0c000400b13052044802c00811b40c6802a000031145c0c8410215502e5484580700951030045411075a000320b005482581d84540c2588442e405d100140300b02e804441c0d030341c0800c99803100d0030303003000307000e0705052502900007070500d880b45100c410014040c2c040c4040981d900f0b4070b0314800e40d9a0340100c0c1c0c4586c40401450b034051141c00c3c0c21040c0c0901c2800304c4101c591040d0b46a241c103500302004c05640350a140603403446c69102945c250000070b0091490980f680e0300750354070210684e0f194801e608403130406808086d950700030760480723034180c4820f40c0041007502d041c0d940180080c16150130202c10800400b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 878908228 1250 878906978 878906983
    0xa0f0e0105010b0702040507090602060703020f2b0b0607022404051801030605060d0f11010e190f090b1503090c0d120f0207262e14070816020a05 64
    0xf03801c510502c503481d00d410340108025100c01074407503000d0104200f01030000643c003284160f802078141c140940d841c5a0031060440703d205030318210b403074103400300007200303500070441000f542d101082d02e401d000080700507041051603c101c405c000e50041104028480c0e04411409041c0302c513864400d036906159642d004070300300410220b402000090b04400601c1000300c1407241c0c5420a10540d5607000c5081c85a4820003c0c0b600403c01030840c80306080d03811450b030712803210401d00c0c0c0340180103d290507240f8546140c0d510054040c00e507080c120090007081d071f0901d602c141d1f4a0b50a00800403030300005818920a441e920180624000d409000303482c2c02d250302ca428080007090304c107120a000c02c0e801c4050062030b40301102300d54811504100c000700400c000b2403411b01c112180310000c10142d541e0314640c4034940142e2503030003001203c01d07230968403981030160192075491109039814003451100105004c24400b0464001c03010981010105040d02c011461404100f45030780115103c800042e1905ca1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 878909478 1250 878908228 878908231
    0x180a050414010e090712080306150a0203070302060609270120030103050d111c0908060c090307120b070521091c020114040b0615040e011a070b0a0f0e0105 68
    0x7035904828001042254180030085038000302c0b07507015001c4981850001c51540f6080c020103480400b01001040c3c580d0744143c83c21f95000d050700c3c511a510041024003070344940110702c2c05d50150140d00c1c00603c03a4145418a28841c0c0015403900c0e00401900d800107425141090540013250f50b80c044941202075400303109000c50300b004149640320740c07642c0380c86854805164140802c018000c0340c03804402c1c00004501403440000e2005070351101c654101100c3c4c0d20180e620904480c400c0074140210316112400801c003a00054003607600c160344a1289480b90508030308020843c4511800058049100707001402e40c4815101d01140000c0f01140500010076064403450410b4201d074420080c400c081e4184001d06c030394140028410055a0500914080ca00600140000000b14000b8185507074108401100050702c4034000c1c3c48580f5001802103060b024007070741c50b809a00c901b40c0006440710900b80c4602d294841c0c110007480c4e492410341005080701404803a5082d071281d5000503460028040c46 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 878910728 1250 878909478 878909501
    0x20607110f30061b0c25170a030e09070302090d0f021c0840060906180b18060307020f060a05040b1501180801050f0a0207081912092303090105180a0504 67
    0x71052903090122071f10651038040070b11051f035030000b01c2c1140001d82222400989002c210703400c1603d40c2d2107403025400392140c0250640e202860003c0c100c100b120100602c18064001d4903403020f00c000200d440b0309021044100a4240d5009001400c0a43d03040d0b8801c1444c1d6040400034940c04020b131040508904c1d40345458818001030900a108803644140400020200c5280650b503d00590203400003007002405901003c00b000940a1403c00800d18031542100300038010a40d01c0c500f40700002d4070b42e0707003c00400c0c130640a03003004608181c03000c0c0200f60085402004d50700701c42c0c40c0c00c24085003101070a0342c074a0501c0340590041000700c02d281c10a1004108420000c280d41c54038040180d2b10b80b000901c040042403050204030003041c0d02c402035968640c4041d8101074440034261050300c03c1d5401d0305c8051001c03424407184c03504001c90050050070b1074642118000805060701003551b26801501c15190000c0c03c14409031645081182d020445184040d158141068841300030800351074019003903 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 878911978 1250 878910728 878910793
    0xc200d0b281506030f021e07140c130902220f0e03040605041a0403060617060603073006050a0b0a0602030403020607110f30061b0c 58
    0x742000c9585114031142180001c0c4001c2041502a49044440100c10b005a10030190f90b4000d0140c1c10190341d0440d4101048980b1a40345050500706482017a071248204540c01ca80e90307424840c800ea4002115803a5590040c4105001a5409010002404c1d28032060b41c0c03004647e00c110851004503c0880c203e06403401c0007107641100003049400342c0d104200140502d5208101c01c0000c0740d0311106460a9a002031002540a149640780961034002c0d5000900058905080014400c4481800c460a51030070000e441080c0d4450341050f0312171403544201186108813218544042c180002c00241020310001d50303d040d021103480300c00c1113580807645001c0307241c0d03101c0c011020f920f4039108590041426100561605081d81e0208a0a0250a500404a101c01404140d0f2540c6003410703010301043c0a400b40c480f41c1c101c4807403c0c00c580c0348401140011341d075204039184800d0313001c580d076032207171b9040c180301d181d10366060507120381951100c041100d030390041040c05105445540805c0600d44d02c0c0d80300 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 878913228 1250 878911978 878912011
    0x4020906091305090c190306020f0403150203070f110d03020a2f060f010602100c09030b1003110f090c030703061208120106172403030a0804120c200d0b 67
    0x290b0500d4100601703640c0d0701c0343c4040050482406d00c0e0030310707007030176254015009a03c0b01c00d00b40c914546809150002800821000c10f0b0602121865020b54400c203459a118030781d410603044142ca0141004d80440f1351074010b14201c07101940039800600800c9011f11308000c107240300203a06086e01c2e900b0050b8421911000f843c654402c141081450780201c55032070640801d516090001c0e60382d0700e0422a00c48811703100c40b4030100c2140104c2d10800215040113030700007146000010006c004030140000c0f208000070003104401400d01d81251f29101c5406044016143c80d070310f00b04419608010100000c041e124074011840703520850130341020034401c1d00036a4a86481d080000c156883c140c12500803c030417640b0f0300ca008680c40020580016070007a404200d1001c000307400c03000307800d41c811035034040c030001500102d02580900403074401d50150342204155920501d08071002c41e883c0344054a500d000d400c1c02240912942d42c01c200458000707100303030f0303000000e50389000c19102c0854491008405000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 878914478 1250 878913228 878913241
    0x20f070204050106030510120c030c080c01020706050c0304030609020d0203031306020105150d0803100b1603170f0f0a09020d060f0e010b010909110d020d0b1201050f0604020906091305 81
    0x1502d40549201e013400d02c40740c0340154207429511020f211b2a0f055404201c116824041c100c26603070040c0d6002005052582d4884070240d540d00d10b80d40203180148141c940000b074952050b0f0030b446148200c50302552805155890b1003011b4410b034041039070300600b082c04d02401660304000034106101c0052050010314a07002020307084400c018400000c002e080c80f406546503690a150810352039002540d5a1252030344144050710040326042280319810004108200e01906a000708519110f81d4403a034030003081646c0b1400d8140c0584006000c035a540300810740e0700004114056022204800c000ac8000325031f00090b40b2010200801da6075a035032a0101001c105040c02041070194844000f44481054940001c2c40c0002c18441d540900382d44064040e555040d240840709810f44071a000d40d01e4101401056008040295496100d5070000048001001c0e060040714440d901a2684a50310358500b0f09000c044d500540724940d000904100c41c841599032491044282180780ca0300003050326119 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 878915728 1250 878914478 878914481
    0x6050d1b0206040210050c0c0918010c081b0c03090904080d05040f0201030b030109050616090f1503061a0403030f05070803071805010302090603063010060e0c0d110d020f070204 78
    0x6441290806c10f0400080e80a0400001c0c42c40600c0420b6802819030b0b0303204544804030b0702c104103054100794241401081e2a5611004940c001c3c0440020302801c01d00c0c215100c8002c2c4a8109614019001441450b200e480c0030014194024012802c141c038080080415008642003145c0481d0380011100d180d900b90350381803260683c800c00070350003040007035401c0d102d0340da03280d07801440010440c4150b51504a1540301c3c40c1440014010b4440c0241c3e241c0e02e40300c240143d80e0450344024006032902c5c10000d8a03841909404c444061000001442e281c20340d141241c60110174007078001400800c100b11000141d4800007140b0038401c48d50f820201d0803d54211034010102c0c3d40c00141054014042d05589645400840750402d20442c2d50505200140c551690091421072078094003004980050941542c0030035038490459030042c0030810b135600c0780c000d034031560750954a9058108090101d40442c45d056071000f00000201c401150500c00c1200c4660166030000d92801e108138000301d030403421814036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 878916978 1250 878915728 878915749
    0xf26071b050103140f25090305060a060e010e06300f010c02070e102c0105040614101809060807141c080d020706050612060601080106050d1b02060402 66
    0x1d2070140600b9034142d510783e40406018120800c0308854101040c4415400d0503050b4418445800382906c031407500708007400007252803005581d1405040300041401e1824030600781541c0703007440b0303500c0b0070303400c06201e440e81201c0140600e070040c587c40003140d050f00940f15100c440350000581400001240748000d800c00c0b07281043c20203168100710240c43d031a60003080b6642551642800f021040c2d584403801012200184d105c64038031a1074920240b030072000710f050880e245005030555082a41d942d018002140c0b440d100f04460003901410740c41440c9001d002101700702000380303072450f800a0f41c00c4070700b0940040c9520500c1840d41d1900100b0a512090107070600401d041441c1d510074904020100d40c9100400f0359820004400f000e00504100c1041c082c0d40e00f20750723079000864440e01c032840d18030000e10040e00e41c24802e000030210507141c8600042d0f80d5100b280181e581c0903141c1d117888030984841c0c008070302140210b5150b401200144e19001c0200444800d560f00808403400c050043c4005a41c4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 878918228 1250 878916978 878916989
    0xd0b011e08100b0105070204060b04030b22030e01030b1f030f0e120a050c01050a050609011215020901141c0e06010f0501050315040203040f0302190f26071b 69
    0x2944a0104128074002c10410100c4009140c0415072000450040b0713074500c41c401001b0350142c82c1100114895482a002c0d006403807250000340615101ca00002c003450400401e00c0c5142c80c4104031090009218800151a441041c140400c2c402e0340d0030300003000c1440700e50032002200701c00f081e400c40a5615001d10300000c00b0b401c2c001c1120700c03900c05595849070410300e003441351400000384546c5110f10402c00c46118101d03600080205052642c6030b0405042e007900c82520501d801b00001c285034032617a00f906800341d8000000d84004000e0301c81400a90003049005050101072003404481e41484c0740100201144080c5004101400301c18060842e4a10600c1c0261075001800601c00c000c0744400050580c0c4003420704036200d40c0c1d0383e030b804d00030f420280b014107400600210602040141f4694407250380c2d442030702503030b00b0300c4500251070084111600001c1c0c895801c055821010500ac0f250319800ac420201202940d07245604000c0b00c039601619044500800c8050394803919408803002c44090320 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 878919478 1250 878918228 878918279
    0x1051b0c06060607050a08040929060d0f0213030f05102003150402040308070506160e090405013209031c0c120e010204140406030b040f0305090d0b01 66
    0x2003424015910440144800e010b443d0004d110f5080c843c0030069510304d0b9900c1241c6036600d9444103801c038060300514401280014170342c0401076030300c81c88078505c818800e000760181e810061480c5190002d0402c40465408465080005081802c80d02d407603403010318001c41100c244501c851911030301d070103000002600070f14900705500c000e01a440c810b0b04480303400c80c1c944685940700e190b01030380041c521031a0143e02c2071001600000700507103500500312150241c0240c4040c0d690780c003112141312008882c0da400090027020400c070146040350388070ba005406a0000912525400c40040c51103405141000900d40c0c0d1846001d40c02152800385640300d5849006141070050040e0050005e82d800d4807034400301c40e101c60740701c00036900c640b6140d2164407111206012200c407207420079000394800d0103403485010501c3c1600449003014040c100813264070000d81d0000d0b81c4d658641c008640c1603042c00301d0400c0020041500305503603c0254021030b50140c0f01006955140c5401001c11124010040c6c5102 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 878920728 1250 878919478 878919487
    0x60f0510060e3010140f0702010c05030a0c05130f150e0915190b03160c12030b130e011a031f0c020705180105040b0d05060a091e030201051b 62
    0x4520304501e00000d40a000d800120303c4118051683c10000b0400c0603810052070820745c088504e59090141c1c0c052010003000c42480e464a401c101e00340d4207038885000110318100007103904000075030312420b2400914684281040d01300f880c9a03600388c0180e8094010440004030920580c2100d02d8544025151807e103604818000c5001c05c1c202040200240a5140740e041a041c06031210140f005940400d441c2c80901c040d10b5540d940349070382054030288080700c10030140d205100e01075000075400e5900559846070504281c54103d02500f800400542c0200d40c200d240c0b84000d45601170030b01c010704042c0000c64940c02e0070200a64451000a00758440d90150103101c20100c11001e40c1d600b002c1b00705001041844101c07500ba071a00625a00c000c0e044000c0c252070011060300540124141d0b03400300d6040c8030482407201040020b4580f4903000e440b50300144003140300340385694010121644654050034600d40000311a05202000740800c1d03015075120003c00c41408240c030111210544100115800d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 878921978 1250 878920728 878920759
    0x40f060906091d0406110a021b040608071a040f0602011a06032a0f0a030509060903030402180910060603051f1a0706181209080d0e01030504060f0510060e 68
    0x1e450f0440354102e094506480420107000c002d0b00007014200046081658925007010001d40d00c8851007241c005248500e080c119442c03905e070046104445070240217003251b03424140a6008a0401c4000385110f410402c03000400c89000d8540000403c200d0700000ba002c604841d502a0031854240101e1083e10b00b0800c00c0590b08100d1440306c407800041040c0b090701108254084440d11030070a90a0003142d0203d900d8082941c541c0000740305100880a81d03105072690407600340d0700e00094400a52050511142a4a046410003c154441d078850300319003180b0311680144040380c00c1600a5400652030b24104032416001002c94210000d280181e4044030380340c5400302c0c5600329422a03209078403d0006948080c40700e01e41002000401d0340580f0030142626103041030300940943c1048004c10f5040d0300000744051701003141002640d060b01e600748000e082600441c01008020011103010740d40d031200601a204500c01d0512a0707500e172181d00051420807030003805600c50102868415102103040224 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 878923228 1250 878921978 878921999
    0x10b0405060301090906060e0a02090a090912050a09052707020610140409081308100506030606100203070506071809090809100504080307050706030b0d0b07050f0d02040f06090609 79
    0x110b0b59032480014440c0b00901c0d050000e800548d0002d0b041c0b4a1200501108110580c01018801401c4804012081c1c0d511441c0098541c8400b0191460b030120303256a221a02400041c2010a41441c010301400e4032940040c4100d50100c1100c100c03801c0318200b0f41310708409a400303541c0025040c0002d020701d1402a0044010052601840d002e00010444415031503c49410800c0e40d00c0e40994000d842d4901d0320449514001188140421403144c031440031407900c0035119040c05210090040c4c00c3d03a560700000d10010000c0c8109a0341148020000c40f80443e0060200f45e00401d2540d4404e40c0750f40910b0300e00030781200d0740e8110480780e034074003c000400901c0d5481100c40261003a103540010080d000f0040d503040c011913124540360701000070100704021010400e40d06490702d58400704405050f50b018003142802046008210300543e001091260740981c000e05485500141c245142201580d4107030240d0b00b1540c04142c01e212030b082e0503c18603402800180c06088540340c21100c60303140070142d0a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 878924478 1250 878923228 878923231
    0xa030c0c0f02042f09030114040c090903090503030a0c03020d05161b0807030803040614271002070c050a171b0105070f051f05060625020a080f0105010b04050603 71
    0xe105540d1070407070301e000c8042c49007645810f084c1e1510114554055200b00c41840c0e0000d0750700c1e8030130751a00040c030301e0f6090721008040c041e0307403ca0884540603081c058020014501800e081c0e0902601300b030300181c155400c000030941c5040c13580e1b03800c5019007546000b0b41782130322510b5000103101c0d00b4045c1d51060054084840c0801e074208040c5040301031403651040000c030031504000c0290007171100110078882c40c500114040c0384140c0c0704100110080e40290600502070358003504d698031090380c0d00d013540d407840c2c00d031841c070010542a900b03032560305003042080307a00c410002c484420b0004c00803c01c51400558504c000c042c808031184400c4400301545880f00b00b40e00800c440101550020700309a44540140d80c0450b80c808400f232802203803420250f41c0c886d0101c00280b00707600803140c80f10b142000340c05440d010b03100140c04542080d40c8601e640c0d88418a421300310302c2c042d00d0341d0201c9015988440e00b090041103c100603140b080038581200707007034450503041001452410032040025071203080c102d0707 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 878925728 1250 878924478 878924483
    0xa0516051b0d020a110301020702010e09100b03150f0609060a0c140a03030e06151309080c0d090305150f0435030106030c0c050309040e15010b0a030c0c0f 68
    0x69988040000030448040328008503401c00e4441c041004030010340000d007008190780504070350540c0c0401d0104140c243d00c0f07140002400070b0304000340b00c506810036094440d0007a201c4410210825103034103004405130012a0550070707616809216200a08008400340c901403401d440d0030340741c07a62000115a040c424038485004105a07041c940f001d01800820810744c1c4c1b0462000c0d10501299800d00501a1503010700c41d0703215009510114450f540b4a60030711030400b601070840f030b01101045652800411145000f40c0e9000350412402c0c40d0f000d014480e04a50900130340303c1c0c201703450a40c24002c0c500b0881e030240c6220100120240500848a188075030380c0541d03c59000000501c0011a0140114a240f84d9035120080420340700b5080e03c0200142d4180c800741d0b58208112100d0150490700c250b40b00d94050055003003080b00040d107040036000505818100d104540c42c0c00310312003c0000212099201c2c0300049808500009500d6160003401c2000c001e81c03409403269000e985502981103032441b0b00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 878926978 1250 878925728 878925737
    0x2a02030a1209170f04030b0703090b012702031810020d110f0403110409051902101403130f02030307080306041107050c0409050c0a0f0f09060803071205090a0b120a0516 74
    0x4d49111910000f22409594001c1c480d5407170303041030740d07000e00581405041181c0c040078203400460202d02000c010740780c2c03c0b1000c1c0d908165a001d015030000940c00600100da00d80d200c1c40c000314401c03408001d02080c01096410050740d80c0892030ba910115003040755000d51901040000e042c41ca000c1905507410f4070340128641c1c080540b6500041d0040c406501e0082c2180204c3c0c2c040c054102050f009129514000c0d150038030912040d00c4202c485c803030b01030000001c0074414004128011082800d2000c01841601c2440d80ca1a4640000c2c0c82c5400040083724441030020400c4107030b003820f0007081c0c0094400d05e4143d0800ca070386e684154640f1012a880e0780100e59507600c900c18040300b013000c21991034021300790400d184d8507010383e00e1001c1039a010354174a80300d401800261071001841404100e8103508007031420100380f0b503a020307503244204c81c44001300a420300c100c90041d500c213540c440041c03502410055481c14818103800340b5610046c40145450318080410040c40d02c50210b41e005804a440c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 878928228 1250 878926978 878926987
    0x3030f0306090f0b1e0d03080411040510080f01020406050a0c0c17241605070c1a09130b061c110f030402030f010c02102a02030a120917 60
    0x24224000e01c0c241d4440400c02e800c01036040411415035020203403181040c1c07400002822041401900800d003c0350650701b0840d41a802c60100c2c0c4241b5000ea041340c030401c40780452008040015050700c00a58810260000d20306080151b00340400840160b07005220095080500e480c10103401c602030140c0c1c1c44d091100902c0d1200c2000700061802000c0c1039124040c401c0368040c488100e035500e5420000703140c0391072014480c000d001808103083d4816410380056070010010054220380e207401004046550491a04011401c0e1030150b0502041001d0800640d40300c200c040f042105a09414001034030322441d0450500c1503803504c4007140d448020103003202c042040d13002900c40040c440800741c000e01c00804507020600110300b40046020358000c60494031080032800e9042d0032030b82c031051400c01680c0503909681f01c90700d4030f82058150580c07c001d042c0d80c400e500c50118008040340540400160000102c1c041c0682c8c000310501480780f6100020000000655500d1800c901003103a02d0102da41c0204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 878929478 1250 878928228 878928257
    0x207081c02030f180d0b0619140120030c150c070302060a0b03071802030103060e030c0a060f0e160e0a11031b04080d1e0c02010206040213060b04230d0302070303 71
    0x480900ba40300f0068820650050745d820300014800d030541740c46108110005040b00e1142004e0b0307001e401c0c3c4180c140017905c581244030054800740c28040000c1480c000f44040200340719800d00107454055140006000b600700380500084030658001d014040e2044180107207404280d00140a680c8040d07840e10000d0f4500003000060315100b107e900c0860b45004c00c1580300c002900c1a005141202d00c030390000d001d021500100c0d0b944030702500076804841c2c4c1c051004400454016041114034405070b4030700050100c1081c0314942001c000e0711020344003d00c0204108203200c00c41c400e40340d2104262000300700d4000400007550003448003400348202d0744950243c8100c2210f400e002c0301c005104030300c111070306444d44a501410700684007481001103450300e03256003111801800115940755059028000c690f682c0c0c0d0800c4009100c051b1001e441c0d83c1da8600c00f1175a0405040248054400c9541c0500c5078030800c65140c8500344414080380c0030311404843c0c0f00005c3d400040510a40758035050904917480c484 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 878930728 1250 878929478 878929507
    0x60e1009110f1f0e0f0307120609020f040c030504110901140108100b030106020610091a061602031e071401171f03081c0606091818030207081c02030f 66
    0x81000c00c0c0c5100b040340f0700d81c0e0640010121340841015120020303031100701c4007056181c02e4107204006241c0d031203210444c00620141d21808000384028007603090002084041401c58680e01c68820110f44e0303070801d20040c40000981d40340d050b241210042c00d5981822081603801e0b0000c0c014506000a00c000b14074100860405240a49006141c5940780d69549500035550301b404e0b030340c80540d0824a5404130741046c6602821102c124078003a0350302030782100e4040c428030754007580d401d11004041003503500060b40c0522042c2c03144000c19440106003004050664144002540150038200c2c102507039441903600310752901c1070380b8024147d205050f80c412105180310007254050110105c51641c0220030000c401c4094107041c030012035100c001e1401e08600070119446402004040340643d4800c010340071841500e420314900003107002c24641600d50b50a40d542c54082001c0700941c200d208240f10b66203003000385203803503a8036501058828140c1040a510b85c0b0550306030504680700052806081c1c2d401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 878931978 1250 878930728 878930749
    0x261309050a0533030a03030504031206080c06090616050c0f06130501080705070501090b04030908150c0f0d060b03090105070203070b06090414060906071404050109051309080304060e1009110f 84
    0x1134181c4003841600d2a0040041c079040318110042404048030268000341889800b0035241250000c0c004d0369148010040e003500012021580200d00b000054100b0480d03141088106110780e0042010240c81010866415411140c0034020002480b11405000c00c2c40e4900702181e00a003130920003500c1c0d02174202e4141c400d40740090059030a02d4400001c000240f40d10b984110300a9407079004982c0c585040544030480c1030403101002200c4c1020071640d44c1c0010040c0140c1c240e05031032928200d4840c072003e0039620540e02140c42d50602000b0006800703001c1c018141d01011714406103183c1b440554510b006c448002d442c1d03d00a03040e41c2e0000e010445004031181000c2550303002c658091410008040c2c0d1342c0411210342000440e102000340d4080da1800980d4180c8078143c4800d885103081805101a01650381c4403070f2152501c442000c07010800003001940500e0081c000400c0c460700d2040d90700e00d44072000d42d6012400e40340c17024840c08100901c00046000b4000c807148890803000d6800144460700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 878933228 1250 878931978 878932081
    0x903020a0b07060b011716110724020c0604031103070302061603030b040618050901110a091a1206040518010e0f06060303090d261309050a05 62
    0x2801012410031007240180c010b03140310341400d01051103500c00440e2003481c2c090703513580c815484002007000310f507110301d004079805440d1801d120400ca000346054a00301e0140e100c051001d0030006c0006c40341101c22166100c407010f500042c05040e0401c80405c5151185104c06048842c040b60764081d01e0b54184810001160000c1c001a1a01c04001044041074407500d0100e020070324001d407020756420b05025070b8046172070f450f800300c400c0301001c400341014160080144110707540c0c444810b150785c407450010b03102e80b258558400f0781c014182181052031841c54440114444018042651454995500303a54820360035140130a413030302c50010400b82900301c0a00410301c0c0d400d041440d03200c0c0c0305c005003150030002e090341200c0854035a9420306031a4031500720220381020081022601056038000020000e600d46a4110712441440d6206d070300a410910440b8003c04000c0f9041120240e03601400703030042d41d14401003046041180b40c0340d0070882d00341c28400780b4442e5600c020b62200450111092a083d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 878934478 1250 878933228 878933239
    0x11227060207020a060e01180602070b0a0309051203060a0e0c0d0f20030a15030506060d0201140c070e180c090a18050102030406051308040e0c070f0507230a0e07090302 74
    0x103458005c00341c01c850884140ba800911102c500900080502032070904a0f400b9401070140c04d070a000c0f4046840d4083d0100100341034540100d040010000c1012504250b2220072071500ca0078803a0810141c2d912a900030204080040c1c148604035030800215488001141e43c00240403550305210304c0508040161881c8810100b265101c200740580001e510401d0100420000c94035101e1003c030b030076280d90001400baa4060300000d049824110601c0d504140141013500c070035a4406c8030b420080e07000e50f5030100d01d0f0f0019802040f03e00882d10306c039a000448207208201401314404100e036100720700741190b4802c0031030340d02180c240c0465a120f5000c01048180303800c8030085e2418014040d40c0309903001c030780061521000510f2840b404540c2e04903c0d42c040e2450707191074646800c41e2417811001e80701159041d01000043c00042c050392142410911600c05004007601d8804a050805042005400b00035141700100105d55100c1000c002915041c413880841d40c0c07180b4201300c810a003a900002e4001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 878935728 1250 878934478 878934499
    0x706020615120d0915050703090b130b0d0903090e070e0904030905131d031e09040f0c03090201020105100f0b0c010b0a0303110601050402040f060302090f031b01122706020702 77
    0xc544c0b110001003580c031000d079091818441440d0455081c810302030040c0004030742d080140546110742000300940d14101d110b03820807584840303241e8095440181103260b050f9447c11a0810550000011001072070202054a020b203031001c800340c17241d040a00214404d801c8480060201405041407401916000e05034107454101e894843c0014000c1d001c11822060700c40a4101c04440000110b90000c81c07a586070020030f00d84011103030a107070003400340b0540c0039489180d108440541c9103d00c40c2e1841c440c0e030300400d801030a40006421182c000d8000074404800c80c9003803001c9000030410008440da1540e04175500c0140d03500c000c0c01800d00b69075007603105d40148000818076074040d2015802041640a0780d0703d0340d03a40c004000c00c80c8190f10441840010103c01081954001d034060540310602405040b45041c0300c100082c01c2c181e00d1070308002440244007090380c455a00bd5070806190103a010100320055070000000c0d18200108084041e40320b48841e5a820411980c05641c495130340a441e0280c01c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 878936978 1250 878935728 878935753
    0x1b0d090611040602010e030301061e021203040c050915012007030506040507061704020d12200610050301020319090c0801020d0f1116030810120501020406080603070602061512 77
    0x740d4498403800e03006600302041c0e03148450b4044103c80c100d0303509440d01081e902d441001d0b81d40c0303c0342c541c04034010f5000d8080d20300850070800004510841c41154140421810141080101c1e14003418a085d4100c00c2080c0001c80c0e60007200c1580300220300e05c4401d40d0954074590303480c034201444e0002000c60154200780700c00c01100058100c03c0e500c00c1d0302c44000c600460440030040c4541160301a5000c0017003d0100b02140380101001e0b18035002e031038100203014a50b0510340c089202d00c03070004400d9005004100a4491180304a8041c1404400a40ca5400c014100380500c00c0040188040b807941c6415520400048202c4a0010300412000b5500c50010031503400c0280404c49105490b2824880c0101d03003c070720042101d00700201001040f051707881c1d9840c101c4a00300d000349000a400c8106801003200704940281101e454481c0c8005a030b15810084010040304000d0034950081d4014881802304a4000c0b032225448503483c103007040402c5200780011031000041c05408030501400d1100000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 878938228 1250 878936978 878937011
    0xc0418050423070540060501020c360f040b0f090d0f050c16090605150414030109080a0e031e07170a0203010c080a141b0d0906 56
    0xc0380b03000b1494050000d20303441c512026080c034440d100b031264100301c50620040ca80012000c02d150b1040f0503071401482c1c850760144002070030700741e4060051348008074240e00c85ca4500940703024240a101402800c4c401c50f000c1010900042039200d4940040001c0c0140080c50314895000c1e201c140c100529070341416800d0b03107020101542c00f81d940c0d07050789000070a650b000d114005d00800211000389400880c18208480003000c4004c08400c0040802603081c485c0d004000241030a001c800504001928040450080b20441c0d44094010b00e4181c0d205045c43e200b00b0140c0301281d46035586c103441101c90400090040c08068401001080007146003076102d94060a03015990b2002e504480d2800000c1401800000310040075401d140e10205c01800342c03a030314844040d2030110340011074411384641e50000342501ca003003101c980091014800c00c00c1420050040d403640403284003149800d0b003440700907903086c1d50811000e03040011000070012420b22503070740040910781d003043c020130101030001d00c200d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 878939478 1250 878938228 878938231
    0x310609150206010e13020102010e0718200415050706090b0a0b01080c04051012091110050901120504020d15410c1b07090f020c070603050c041805 64
    0x440092900c100e4040c918000078105042e5100407594900a40d622010010668074110003241107540742c068003031416608000310700142040e80300400802814210000854a00c40140c2c0c00581c040d002071031403241140100e074141d03800340c400c07074904902c4004203503104c1c8500c94008000500d0504003d09203c0d2500402d80150048082404400c0000b00112500d02081d0303000300701d225080008001714503010110203200285800c01400c1481c9920140c030071039401750000d6540900e003440302030042c68000b0b0740030110307003542c01d2481c101818000002e1004824400e804600742c2d9076000709095689080201c041560301c040c1081501010000a60103000700d0b015180101181506c82c0c8030100c071541000480402080d080a140482410202c8001c080500b140301034540401016401150f044441e4402a075210010000981340029407000c0300d2980c40021040c0c5d10511044480d202e01050140c21100185000b2440e900d0311650200b080c40f85500c020615500308103100c651011503000175 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 878940728 1250 878939478 878939489
    0x503091c02100b0f1503060103200a300c0504030f14060604061d07050f030a050106090b281e021609020403052104050411070204051b310609 62
    0xb07105194111040c04281034403600c0865000c60041100b07a441c5c8001009168400f40515010403801c056000005000e08420350a4009803000905145003942014150a0106203001041064200095103500ca907084121008a05465509441d1414403850942d00650f400401ca449c0981c41403400a0040028460000650140400141c050320345441341034121040518695100840c54035100044640203007100140302062258000045850014520480c5441c03000549035041100c09040340034568842c2984c0b074000c00100450f030908401d40501d848068039000c1c1c00300134414084d1000b205e0b40c0001800b440440e190298040d90000318180c400c10604a1101c1250300c449c1094140c1c4250700020744107901c404440140c103001c1011000204017100003140c14aa03c6500040c10755501d00d03040d0032440d1010400300103526040c89640d412070381010503003006119803155405507004200003200c9080c80f00b0700c10861000d8828550304410b4020f0036880d40952100c1c00038240f621940500c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 878941978 1250 878940728 878940731
    0xe120c0a03110f1024030f03030b0d0816050a0803091011070203070e1305060a060806060103060e1b0d051023030c060715050103050d0f0305060a03030503091c0210 72
    0x32942c640c00085089189041c9100c00350035a030190014880240c24030b40c2590102010030010100301040e007410303c20140d84644000300c407100e45401c004007130302d4000341031500c1070b10354100e0740c00003d44110031220594064410324500f00e946042c1641851146034010385405c0c400010000b0100001c2484017120034a42c004002d1494202c002c988940a02d000c025099485040240140d64071142c8050340050600501301001c6203580d642418070206071107054246440b8401800040c00c14014158003100a2804020765450404c2600202c90090300d6900021000300011500d04140c4044030072008403400709100038240f0f900d4006821400b4498644012800b17690202850700701028040100c000500074034030388100c1d108000c0150b00620003102c011030f490490250032000c900a040c02107000b4005400440744840002e8084110420f441c1d04240c5007904101e8140c1d40e112104080e2074151401a8503903956400962402c140c42c000d00b0000070700004801d80e40c80d8000f07691482c4100c9a01c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 878943228 1250 878941978 878941997
    0x40f03290916120b01170a06111c200306030109140d17090303060402130e04030c0303050105030703050709050916080a031e080403032013080106080a0b0a0e120c0a03 73
    0x55503c40300c0b4040300002c06006840380100420792080e550780342c07082d05103002c4d00e040384041d94941c01192603601e00c0e0303e40d44d400405d80b282515007a0200f40c0044001600520542c90032051012100345c030812291420000031000c508075032000d502c10750207030360b1004d003010b80d407400c01911640e01c1020000880c00074000c0082102e0840da544c400d14019182d4000440c107640701e42007040042c0d00680c0522a04500e4000d002801001c0014a94040c50003070b140d1155091181c10002c042e110141c000d54080e80c000c1030100000380d400564a81240c0c80e250b00051140c40c0da810f4141442540c082c1c124200300c2d203940110300d12038049120b804591090312a441c0700e4002505146140c00040b4081b400324040b0000900801d01907040428510a00003110f002820f5480d03486516400c03111590500300a211810f1240720b1003486098081c100702001441d4050095950183c05c46004020ba00340d0703070311040c5086544204000d00c8503941c0414220740d80310003c1e442459692003c840d001d60000707001ca032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 878944478 1250 878943228 878943239
    0x5130e1803070507291920070504020906040e10140109032a03061a0102010e030301030503030c0d060503010f02070b070309051024060320040f03290916 67
    0xc030752460794410f001c2c002180c502101240d1402c0400390102c180c002d154080241500054020030120b840c541d0b01071820480701d44014540880c94003442d52400f00b01040c0030701c802c0002584400c540044901503a5401e80030302140c0103001c0c4c1c1d40030b0f07003058880d0302c02d20100c00d5144240005441c001301074411007450707110045403800394501c0040c0c20b22800b03035580b041241e1071028a1000004400680403401d0ba203641c0c1c5421540040300000d90f0111442c0031180c59a03081c042c0e0214240400025825035040d5101c068581c44050041080003100164400c10314940d078110500920008008020540c8900d64180196201c6402210100000300000c4d0095000344520116690003c1c02010410001d98070400100600c3d80f6203104504034440c0080b500000041c48000303452103a601107400d02e1600c1d0f05001001c1d0001a1500244083c00244500102503881c0c0085903001f0350059848086071b200d2104011403070f9042e01048142c0310400056110011703e5642c00c11a140c102e5103040d941c1e0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 878945728 1250 878944478 878944483
    0x4181a1311010c0305071b0815040804360f1107030c03050310032102062404200313050d11060a0e1f0906050109061d040305130e18 58
    0x48200074409101c80701e9400301544100401d0b01c10301e00c681007584c03411549032140c00e1444101310600c80c2d00703a10f00c213003400803620601c451030304903031000480e800303500701955452154040c0d4001e07032000d1442420901c0b5205050002c1d6103030344414040c80c070285c100444105d40030346031900c07030b40f1280350400560260300ca41c14800c503403010340c06503564804034810340d0701240d4980c0040d01000e00c40c801620b010012074440582d203404514441d02d0b40f000d00c44102c00107802c01200900440200755254021202e144594858170494001103e0004501240144125114400c562003240b170300d00100c1040082c50136009144000d6001c1c00c212600101240c01c2150109056040707549640c00003008a00404940d401c249100c0c01e203101030ba000901078200001078a24282700444466484104030000d01c215885a1400b6201c94a4180300d514101150742e41490512003200360409210400a403d042c442c100350b4110304401010300c3d01182d40c0e03140070346509509458484680c0841c01c0b11501c00b2400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 878946978 1250 878945728 878945761
    0x60215070c02130b01032316020604050d08040206070b0a0f1401151b05030304032105070c0b04060608030d06090e0a020a0308032d0405011b1d04181a 66
    0x24011440070007240f003848050003441070400d05050300c0d004000343e000103003440003402a00c0b404094007189003100303040b8030740c0940b581d20340155000314042c0804503030089025246c070101781c1400d074140d07112072021800030301c5491000303840c005148040c032080202c15048518001d100500900094107c14411003d0101c288107580300310f9041d00100c0f08240c01110f1a004a0b03100190403140843c00f030b02c030710381142d104417012000100e80d800280c41ea881080e0741d0501d51900714408004030701e0000c0014001c8488941d024110180e00d83c00a0304100c80f64001102509044007500d84800b041071004001e00031a000326841203040c0161400c01620000369445601d400a0943d401c1a2a5803111035940d80302800c03402040b11084007034401548500c0092175204032441d90184246403a040c07042c02c5541c40340c44141803e80400a6a100543c401550b00500001211501b440e84100340080c0080000c002005080c0302110242024000c40c0600c103c044211740c2664246c5541f140b04141c960b00c039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 878948228 1250 878946978 878946983
    0x20f0307060e160f140303040f0306020406080a14040b15120c18061309031b03092c07051809010810060609081f0f05090a060e03120a180c060215070c 66
    0x1350001c1048265540c03080312030301c44000350642c0c1c6010745a41c009070b0307441d13980d410544443d500010100102603002c41003503800280740901300401c8800c81c111580c1e440b4080d2018002590000c042280042d0052414450500041070020001c030301a5509031181e40074400341e403061120981c144032885010038414810a00100030250040344a000100109240c0c01c056080140180c2650310801c0f0000d24000d0542c040c0c0c0f9000c041354502100382011109a40312032551050341c4180c2c00c80ba40300090303011b4000746181440d82e2200820000d0a1a140c80c0d0144281e000185100000e42d10b900441c2101081d0b100d1841170200300c1e101d0605a5003c0c01501c6a6240b940c0850b6011020b4030b1404182c070702e440c4807120082164085442c2d90b00130745100307480903000c9410800e000300c00c1080d00e200709051100c90380c014500b41410603a8103000e0440003004012441d0715074082c038030b510001103424004140c1c44800084550f484240c020341c2d961003208140300c000c40600c04201520700a15282d82d910340d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 878949478 1250 878948228 878948249
    0x91403030711091e010f09150b07020f0609150d05060d080703050a0504050a03050f0c01080112110a0509090a06060614071124120f0417030403020f0307060e16 70
    0x1080102842482c1c80004c0ca20890075200b441c40151903403400504600030950354412400f802d052250920840f800032281034011202c2c05000c21517000141c00703507104a5011580c0b404103400180c0481d0151148802d0303258030000c401d444a2460320031502030304814a4204040060780c1d10182405141012000c01a0180c0d00074010f481c000b0740700350300520f490111031030031782d04003540c50007c0780e04403259800484071134104d07446c4040800400c1000700b01c004400d2034580255454800219030007a000310000d800001e043c0c1e400c5009840316080c010050030003811101682ca4030395941e540f548284c0c039040ba003c0b070900c00b0004a441c40b0306454070700f5000039440903281810b00d82e0340c00c007601c614880a640007040701c072070154409030240d55007402d050702c062500c9d643d40c0c1c001d0a003044880b0090004400d089517409001c00304020041c182d0710041c001d041036940381c850741000d81c82e051640e203990600d4400094644200000c1d41c1010b807500c64880d040341c1600c5800c85500305401428001d21040b075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 878950728 1250 878949478 878949503
    0xa170903090d062007200a12060b030d051903060e070323071214190902280302010f020d0807030b06040f030602090a05100203160602040503010c0914030307 69
    0x500d02603035406100c1e03100e41c41c0003800c00e664000300c0300003200062503c0741c0e00360042605000c3c003a22103441c40e4800700e0380d0f00400c40b001016000940c42902806140060230700d1158600070003415501006c000740000301180d03000c030202c080c02801c5501c00000d0310101d01c04540b05410346da010b4062681510055a4441c1c0c1035514104220002c20020a400e0030007a044602e050114100418150240c43c0c0d9507108042c91904c1d482400c190b070903800c17010100c200560304001c02c0c401d01c01d1884902c1a001c041c0032450821600020701d02113100140115038110059050590009103584170b02124803e032103050740b0f5001c445d4242c0c0c603040c40e14403000204d05144001902c03240b195100b0f24260b00020100d03070400e602d58201485079030107504100c80940d400281c007d080c1c50328a50020060100b1100300b0140c2542c4c1070001e440c0d015450b600c6160000c01e1114208219660f011381c5d02804018000708640c050202005242c402c0a1007410100002d50b251180e10307060200c00c444525400000300440e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 878951978 1250 878950728 878950747
    0xe040803010608130602121f0b04090207050102040e0109020d050c03040308040f030318030201090209090f0715030908190e0a080d050c0a051c08010b0304200d170a170903 75
    0x32001440d003602c0300026401c103130000350701d48003601c000c903190100d81c1c0032440c00c0c589140202030309280743c0790404031a280400014003444122401d454908001503203031103591030054060b00070354100303c01c0d9400b84400421301d440700798060048003038520424011515005142c006910050382c024000138a81c0c0300040c00305080580740ca514601c031b4900000d01c0d5112400c544806a540700049005075180c114440640c50115540781e0880600c074054180081407003082a41e41d0310a12400032102c090450550480e4001d03400341244503003080312346607a0b41c00c0424844001060b4522080450f42d061001d9040e410306250441c2038982140003800c640305d000c04159029008107004464510801400380c0000310144103642c9400c0c0365181c00b400300d400a107000f51480c08141c10020701903a0a00c1080007160046030701400310700360010b840c280b82c0003400100c0e150b01340e00403018141002c120000001403140c0c000038100300c0201c0c5d60b10000e811044100424034607095681c0300e143c0e84107008c030009 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 878953228 1250 878951978 878951987
    0x171003020105071403030c04030c050913030815180106030e010b010527060f0715020a120b011e0801140f0a03020636150c1203060105070c0905010f0e0408030106 71
    0x90240075202c01c11105013003000c1d2518503481205c0070004400c01250810401c5191904113001d0001112200740c00d00c4d0170020340c0c40c074003100a405401c0011040101c0c4600107907800c407004c41d5801038050109203503008c00000d0407510030b10a0b400081d02e00440c1200c0104103214964410788141e46107460b2400944104462654510030500c4201c021514400c00390b9940c0003c1a00441c540700d8142c0744c0d001404c1420183c0c00e80034900c048079004202c035002e515480030b000b485007200c50300300140654116004a46003000843d0f00e04158a641440082140e0400b002504980202c501c0c0700c20520030105002007281d034601c40980021394003100380014907004014001049211010401101c03411254528020031104221070303544041030103ca103818168560140584109031030345c03a00c652491680d03500d02c025200c001e0140000b001240460f17100303108071420180c0100c14641c1c210340b5060740d41c00801080c803454440004001000500f968490072451040c0d03004440142507070b191240985 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 878954478 1250 878953228 878953237
    0x100c02011409120706031803120c052b050105030c031509030715060608010504090b07030509100f140702071a030604110a08040c0504050c0d0e0309030616171003020105 74
    0x10344000380210b0419440d154450401c040341c0d88020a0790626000024080f2162004d41c80320705400f002e4010042a04041c0e1740146008281000401141e0034408803854020020b0603500c0109610680e5032a44040036195007961125400f04416660b601c20182d0741c0140c3c40c016600358104d0701e9990900451740380001d0b8000e41d80c01c1528945095035403922041e0070640d080c0d41c06130b0396501c0c2c1070100c5540960254090001520104155146504c0f250700b203c1008080104058450300000d0f03003510188142c5004000e0a6800d00c03215060310703031060203401300c50140104490b101c0c0004145910000b850303c100c607000c0091140c000c800845001299200500322071b0016118584881c4141c14440101440034156a800700c00d400c1c5450502c4011100b50701040c415401c04081c41f00d000751101c110341c40401445000143c01d01950744040c03c5004285950398540181b9040194038000c13034030900d0b0424901e82e20a83c030782c4141800401c2002040d03800c01c0100c81d1044003032006500400042 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 878955728 1250 878954478 878954507
    0x5030c100e1801120507080109031704021503010b0405150a0e01180506030c0c1006030b01180905060901140a06061e050c010c030c02070603091e0f060606021605100c0201 75
    0x100a0b10b00300d11284000c041d001e0f40500c446400032a04d060034450300340b1485001d40303040c0c0b0003801074440f2520020440c004103804054a401900042400c40d41ca186801c840b00c140010015101d6070364011210060304240300b42d80c09070503180c10203c0d40000d070700d048554a1f2050340711d80307281c0340f03900c00112012900180c10104440958501151b140e07a0700c4050f5109070310354015140c5c0d0381d861109035818840204803040c20709050401c20b100040c80c0c0075529042d140e075407468080f4500d5201d0040d0151040e11000303056401450180070402c14113405c00400100384020519082d11420044070840d450351041074002585210407604400b043c0c2d12808034080180b0b0910708188440f407603a030840380010304017000f203991035488190040d018800c1600401c000e06080000c8000760321507100c07150166101c58070081c0c94504c28010410550b004083e45500400104401d548400020f0364804d014051f103502e0301c5006200080d10710f006400e80c00b00c2c100c075070b841c4c540480b0181d005540450341d071580c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 878956834 1106 878955728 878955739
    0xb0411030610060e0a05040f050103020405060111150606070812071b08030a0c14070501020a12050108100e0c040c051e030615091311030a050105030c100e 68
    0x50382c01c0343d200f403c003803903105801030010314001c4168104540c441d00c3e1118141c0000c01c254882d605030780c407d44040100380c0703443c0010746d050104010000216403240c04084002005140c0301c542004000e07001760b085c4409a0f9401c0b0030794110b142c1e540c1031400c2d070101f00408070754003496134100b040113030070781070404074003529218914480104900500390300c40003828112440f40190b00b216030090b03d02d43e51549001d02d8298081d601110780c18001989540f910030b039101082c8078190484031070f040100710084401180001401e10442c140b4254062034050002540300c90284980306034496803216600c2c503190050000c80c0d09002500240b50005000700b10450312507460000006445100c000c0d16180220001018030800c80007a1a049080100c0507400c0ca100740d0185026900b124070500030707030381c0f601306140d901c2500c00b82e50b550041100707413650400d0b402602c6000647c2170141c41d = true := by decide +kernel

theorem cover : BRFrame.Cov 878776978 878956834 := by
  have h0 := BRFrame.cov_init 878776978
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 878776978 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 878776978 ≤ n) (h2 : n < 878956834) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
