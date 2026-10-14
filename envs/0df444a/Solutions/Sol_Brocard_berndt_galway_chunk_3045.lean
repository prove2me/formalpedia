-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3045
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:30:12.81988+00:00
-- url     : https://prove2.me/submissions/6f0141de-64e1-4fc1-aecb-0e3a49531080

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 547482014 ≤ n < 547661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 547483264 1250 547482014 547482037
    0x908010608100c18090906180b06012703110a121109010f0b18030c1309170a14090a0513021c111218070e04061a090103031101090206 59
    0x107115802e007181482c012040c040029083c405200704500055540c3c0102d24003c05003401c2e1a00850301c00c001c0c0c03580c0411070016228006003034003283c0b0b107840c1044080c1a1010f40c00590002c603103540c1e02c20031051900d030b04ea01c1017400040c00c91545d40c404010000850707235164441101003002554080040b030807500c2d00d205120101048614400b040718000d07041c0c11200c4101603078030040c40700c410802c0440d1040100040c502180040c3e08000a180410007901c1e07903007022280035110380244168208040d1a84100e68007843c0d01142a1022140d004661890f0b0004040115000400140c1c20040880180203011108203036100c801081c074043c2c40c100540d9501e60300245160807030800c00c544011440c0400c2e4180185400c3c2000c0c1003a030b00820141c80d40d8030040b4400f0034011512001c1041a41440a0503220130719943c0c9a0503c622000f180c2c155025030404800c01c402c601c440800c00c01c400e400a04603001d69085440c11182000d0004c00c0791000d6584126602c096902c00f03000c0c01c2d525140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 547484514 1250 547483264 547483273
    0xa030c030b0106050a0905060d1104090e1e150711060f09010c03060602030d0b0619020601030318030201020d0c1a150f0405090c0d050a0b090a031b0209160908010608 73
    0x21071030448424107050303115078100101401000802980283c01c1c0c01190340403501c0507100c0c0e5444074054020503242c04480c000010006000a809800760450401404260309440c91428541581403500518203030904007030b0040c4090020b8103c4009129800011510b0824000c1c00228850f070302d440c2059510000038101e6400700301e540d0800f4060303090046018a803e008a03440c1c400c0180daa0b0054034246a4415110b81c019002c1d03460f4002658503c0360020303017a60284800c9003019454900c01e002c10740001e0111912286220071542c0114200c2e0b0703042e8010f1420368a03d0104075025807584000b22011072441c03114401e010020700c0307000d000c0c24421b0600b40c84201080b04201a0302c2070a55450b000721304103070400081c2500403508810001d810307114050414101e251180c1070045182c07000708072401400901c09c8004c400a01c000307003184240c541000140f100c0c00d07041010800c030000251301081d03403130003c0c455450b03203074960382d003044d4905040300010703100e203412400d40d40313540c1100056030301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 547485764 1250 547484514 547484519
    0xb04091109041509051e15071b0501060e100e0c0f09060f0703030605030c03150a090305090a1d0604140402130b1005030610030605030604120207091103041b2d03020a030c 75
    0x40b02c0120190f03030070064000d2042942c056010300e0140e0b0010b03e0340061081c02d10300e00032403449c802d040419039035000000700511a180c0c1d003036681d0f100045e20204e503da81680b101050f002c400181e4507015048005034103041c40b00e04d0001a603190b00410b255a00407409220b20152400c82002920104e4440d482c042005030410301858506507250700c1c0382e44030358032141a1100301e003244400170350403844203880490880c840f41000d91301440b80c149801d07045180b00100061000c24880b5103401230112041c09039054480200b004191103403240c014060301e400d6401b240062424407a030f00e481c0c104100021034480c0038040010086403a0b0004034003c142d0002c100704692611518401c0406240d0508101d80c078141404665a1034000700010001740002c4044884a03000700300303800040255000500002281d80c2d10b00c2c3e42c54009407400ca40032403140c0c0081030305290050307002c010f568180c90b14201240a60014280c2c1c030500c5461491412514580440542c03a031510041c007079800340718120741c0e452 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 547487014 1250 547485764 547485793
    0x6060e0604050c160f08040308120919030503070c030c051c020f0f0a080c1005010b18010e06030c0d0b0a03060b010801081207080a0e040504060c02010b0409110904150905 75
    0x440c01080344500f85410040200b011141211408205800028070221a402c81c9005080c1d845140c2020300000008074210b48090b40103c4458801d0400f41c09444504040781c15000c00e0010004000303021030010b000145410380300300f041400c418041d250500c1e0644c05500c2c1c0368140700d504070000883c00c90142402d00c031180c04000011103440080300400142e024215030300c2e125012004003c3c44240700182c109078244081000550340c051407a01003220b0350b902c0c50b0001966100000348410540000c20783c1c445036018000005e000c10015200c94a5039031920403210303039507120f81c4011081eaa91440c0002040e151000300c0800b42d03129030000039840a8020015200305e00592101032a82d009000907200c42e840041650489640500d101c0e840310b016040941700085801c07070031500146000100001d0002c147c0041c00c008250b600208010300c0380c00180019542c100c41d000d0286090401c1060160030481c0d51503a03c04c0c003801c20400040c50502c40c034402d4640d0801e05a550340e0120f1907580760781c03 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 547488264 1250 547487014 547487021
    0xc1617040f050f10030c140c07140402070c050f03030d0e070608090a051f18030e01031b02061909050d030b04060e0601170a110a020303090d0203070222020706060e0604 74
    0x42c0811140e860404003030b0400038502a8030902c80b40304158980080c2200030b4001e80303d007216990484c034031a8450b10303a4a500e55503505184504c41d44201511011000350401d03100303c5115a03002203078511403908181c00e00c1a030010304404150584020803510302d4820301840707041e80c188000d00107058032030b24100d07004140840150845219800003c011000a800029005d0b005511428030030006005c140070319000f080d00c075010602c00404000c07d00704244e484000f842d041c2c0c1098804120410a480c0242141c0e00e90400c0e4502503401080400c213448003c6a110303240f170b2868103001c0313900f400b9640d83c503040008a1124101090b00c1d42007005503403138140900f2003c0c0c202d11384d40f03810a1421400081100701005045e0f0403070058000401c4030103065411207003a201c14002c1d910384e02e0f00d40200080d03403030f0700c11519507020703014201985414610110071201c941d034008202c05e00d03012124101144182d0000c82140180307a00700f009c840095101e001d038030002c02840c1890203040c03a00f10700340001d8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 547489514 1250 547488264 547488269
    0x1c0602040f06141606060905090d140c0d1407051917070b1f051509010305100f06080907050a1203030c0c0201050f0904020915040602240c1617040f 65
    0x601803c2010115810040816a0000c1099155a01d080101820035100911440c1c0001c2c0503613003007070f04202140303000040c029000c41d01542c0d07492030701544e6401ca100a000d20300d00400c0300d402410400c06210321070445448010300417441a4036014083d5a140d1500b24040d1450340446444d80380503090201c01c1c8844a5a200c900c2c004a207000480d40e2000c000100c02010502d200d03840508030f80001d9540e1080c00b02400000c0d01c40e00310581898030100b40e03a0815029180082e0070840003d808043d01100311013181c400d240b8640845007403080c01d0f501048014a82070451003032800002c0c09036101071020300241000c3c601e4120b102820704005090b00c3c1201c0040d014016000600130050740d01004907802d00d1095558180c0766011000000d000c0c1c8039901c0115030104a841d0a4600075102d080103208480183c1c088410741e05504c2086500c102c240c140c0011030039500c0c1d000070300718014035000f03216280f016000c0741e21520043c4e559540110460031007120455001ca8103101c24131921004001 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 547490764 1250 547489514 547489517
    0x1206030c05010212030702030d020a02100504060203100807030213090206190801061403061f050913020c010e0703110616021903150b211515040c0f080a0504021c0602040f06 76
    0xf462619140288d520711820400d149400d900103129032200e8420b1050304054040c01c4001c1c0a0750600381080400303904150740c4508c840c90045d000040700b010000e0140704686d405000d0040c00f5807410322090081c250b01c1c400f6a000764041040d030703a060015900c030200032070b00c82e244d107038503135051030b02c0104800900b82540600d940d08006010507680c070a2201d00d60315160f42180c90311010800b904403003034011218647c1c0c0188030038849907011030300354000d0206480140000c102000c01040d4066548013140700c081c101c1e40111640342990304202000340260b4140c0c00c0c52440d004050381c003152249449400e400190340d050ba00910820049070344441e031092489005000328400d000000d560042401d80984003800d004d4110300c43d803881403101703000c0711070181c64004841c5826030072001501161504a8441d501d80b40300400103a0096140301c10745801c03946ca640007503841032a400000d01c4043c100b0303a40a81c0c08280c02d070720b50000207110780d0031074440c100c09030f2514503154000c000036429402100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 547492014 1250 547490764 547490767
    0x80d140406050f07050c1e0f0d0305180c06040902070519030e0f0907051606110a11070f030b06060a03060b0c0c041406090f070e040207081c0e0601060f1206030c05010212 75
    0x60f5a03070000b00785c11f000c1a4006155101c0005c03d1059181685111208038907004940c0803012480d0150b0055220f42d6001310b640812a100300120360b01c038009264450343c03200e024401072141d424181c0c0548081d5100c2c0088482d4401142000300307241c418508110001400e5050301150340c00c001d070900103003a6064403501c0c0d49003040a005001030107489000c0c0041c000020487d400c3c0b00094128004200102040301d564a001c4400140404054000c031441031241030340004071201c0300a070500440e50089054007190b194081000b22552080c08114105500c2c3c400104a01650303030024421148030320000c000e0b200e50300050105031510300c6100f0600b19120000c00c44039440380c0e54415880f1400c00300e01403032603980b85415640c43c10080f1140e500648041001000c2050b400020445412402c400903a26240301a0140171b9a406030b610751b6280c1c120400400000703010f50b8001584040d50b041c031400c804800490b0508840c5254406e682050046000300540c1d41c043c004440c00c244150382e1203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 547493264 1250 547492014 547492027
    0x20a03061d150a0b01020a02090c04150f0203090d060b090f10050901050d0f022107090501150f1d19030308060315041b0312020f0606030109030c080d140406050f0705 73
    0x7041111001480ea1450b21386510142080381e10903c02414403035801411003416040400404007190064020040070501322040103200c02e0040c440b09074104003070360007185000d00b50014400074000711101212215102c0b121041c9554580b04614032841411100c0002ca1138442c2e041c41c03e0301e0140d444180115840700040c0026102d18818002141d000b0134045002e80080c40824030000243c40c620021411154004011007000320341c1c00c0441d1007501c000d001c0b0b40d0700c69940405416810040d10041858400210b129a00541005445002c0081d100104240703040c0442e113040e08102e1019a59200d011081c030405400c0a030710740e00302000303800618850b401a00d0101d10312401030006490640c403049884001e0721a882208059031303000b01150304400300d400e00030f5540c0135200800035140c080c0d41d00248403410144213804040360507a851460354a829115901d1560221034880c03181a29100080e03400d41500c008107004611031203002455141000c0c1200041601608110402400b0840f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 547494514 1250 547493264 547493293
    0xa080a1e020c1302042607150c050c220507180f0e0906010303050403060207050c1c050f0d09140a091407020601060309082502120c03070e010b0307080a0603020a03061d 74
    0x5140c498040c0300860074032002c98880f0305d2400400d940100d207090000b5008c1000e5540c0003100795012441034040356940c0c0019410811750001b040703081c0c0c1c02040200e01c0300c45030780700b0f0350410307034000c011400c0180304c0ba03070311303160040028105410240e00c55010040402030021901c0401d40d2185500001e414035504682d002040c030312607480b01901c695004540e44c42484004e02c000b420001d801802c1d00c40c00598000555206440c04200b51102d004141c4000c422520124003100b100180d0f50310401c140d402d1420f1b640e100703200700d01e00c1c54000640103408100c0c1000c5100f400c03542940d2040e4122545040a002840c2a9051b0000010181032401d580005a084005d6413082c09007210199100c1e1140c80003020400440320000c1d503c020030014600700690041108010303000103900740d0300072603140c80c00600034901c284201d00540c10300f00005410140302c2c541090300900203500100e0080d540741c0018502041c903800a44d80d4507a140703240031034180002d81c00707405403000d0740117418032080c83c608 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 547495764 1250 547494514 547494539
    0x200304050f0607080d020a0c12030c080c1303121812050307060e03210108010b06250f14030306091e070e0f04020403140607110a080a1e020c130204 65
    0x7600340901c40c08140e0303204011205068841481d0318440840d2034280c2507800074032401c803429050350b000c0099017010f0b440610170b008034048803d654603480081d4072400000b01c0341e9804921000b28060700640f02000081980029052200165a41e142020a5103031120b03202c400503404101184142e078031442c0000e01c0132095600d070b00d40203040004e8080c11140500d0851140101c036034281d4400514150350b0742400b0804d28180c07004d410081140080c1c49051010501c0384032516000d24652062080761113049100410215200726050480c050071f81e510f00b00c0c02d40c0a20411000c6800100400c00f09040c0b4103a100c0e4480d01c00000290003404c1c02e0640200c02d280035001004001c4201c054030129142c14040f82204040a807045550f076603a42020b1522060f10003e04916000340710116030103034800c03099219600c52040140c8021003c0c3d90b9500302550207a0200c3d401e2048550f0b6802800c1d07800307101003041c00c4168001d400e90f40000401c102c10214040b846584030352050009210904c040c4c207 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 547497014 1250 547495764 547495789
    0xf060f060f030906021902070f061412090307080a051215011205090316050105040506060108010e010e060415060806120111040905091627050412050702010c0b010620030405 76
    0xb0002141c6880d070030090080d12604210b00e10301c4540301c0e0a60351607503000170640c048036501a42c0121607501c4007006c4034201890031142800703082c00d0018a5860f000160b1840e0001d25070300c03c4900e0400c469680c2a20f6400640c000b1000c02c170b021910000c07410100c00d0507640b20390946050f405011403180082c0c66031241c0403a14031296942c2c00040d00c0c000003001151001802042e40000154851030403d010348011141120a03010b0100855101d501802e0041d0680b88204600380d040c0e800e03c0c0740e951900400411281c3c0c007a449540c100031000c19140400302034600c6596000a6280c180144aa040d030400034100050707240148988101d5906411703502035851a000100e1540c03100d120407494240c00e0b0b01000302d001c851480026a0000711800301a0601000302501c406070210803004045800c1240c007d001c112815040d08501c2e44200002c0204c14414140300c1c070010b0030342c0c58410f8442401d801c81c101103050030102c081e4860b0401e02c4910b40b00b0f0580011840e19003424041140c008102 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 547498264 1250 547497014 547497017
    0x114041e0f060b010e060301090c1e09060c05101a03191e05071805060909010902010f0c0219060f021506030a02190806090106031101020105090601170a150f060f060f 73
    0x449503e94140e208114400c9041070081c0755640b656182c81c86140108240d002e1040403542203401903240800c01300507040c015001c3d4403102055858000d0980e62451000303c100c40071300075410040b40a240c640309030030840050b07c00e0400480722080903d46407500400700340c0814407650031148001200c0d4084003404102078050b9503c03405c51454058544201c541100346641da07005205040120307a0351000d0b03c43c0104851b1800c007520b51888c1c0c3e508076064005e01900003849508a9003a0310300540c048140c1910160041203411b80a40442c20000c0d2550048400144011414070f0601e504001034a030000c464005001c1a0800701c000a584403000e10009014141c441070345510442d0f85410300b001060ba49058641310302d001c2c010300e4000d00c0300380000c03200207280400d2688503510512850b445607240e000100810f07401c04284254581000340c03201210710030400d000d8001a0003008540990011740710100d8505030f40394002e000e0701c980c5e4021501c0b00d20024820460264410340c43c42024456 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 547499514 1250 547498264 547498271
    0x4140114030a050f0a030f050412082809050406091401031104020f1206090f1e091002040306060f092313061b022b0e0f030114041e0f06 60
    0xe5801103030500294480c0074007180903204041c1c0f81800c01040d85000c00c0d210340e68580c00d0f512505001c1d5181d0080f8028079101c580c1d800e4240001500f100020300f00300d208800f024440140e501c42115101e4444000c0c2000100070900400c014103043c000d10001d0010444280913000c041c0c41d0300a050841407101500c6003844075021030321600d86074100d030400d02c80010700c0d070b5440c001c038000003001c0501520014001c500520019000c4400100428001c02c0c6503a04d008071000b036410b99460842e805400d107000c1e40680c2c0180e403a01c010070301c02400154071421f00415144e2602d802124031440380c0c1d10040c1d00e5418600c110048203400d804040307425072210020021a21009008103188140d108001c20162400344181c0c84040c0801c07092800b41c48a60840c0c86401419140c00988100c01043d034041848030000200305c2402410150080000070f000180603442e8000040d0944080c03150964017141907000b8401800a101825a0304030b21040c03c0b43c6805002c2d0f911030004c450100009414280e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 547500764 1250 547499514 547499549
    0x209030d08060f06041d010e0f070c0320010b0913030801051306030807060921210e030301170f0604050712050316080a0201060e0f0105010f050d02040602010b040b041401 75
    0x207614002c9003070030401810645d02c940d294084014420310b600305884444020f807000103004446a2240d52103a00102d120100c651160f0509035030303121591030103c0074050080e107442869400d498400700f05807035050001c28075104000500204090141c02c2c2c1e84071105824003000481d0b0020101811500180c8407a5030a001200e1820000d19071034000038210400081d21000f071108540080ca40c40d030283d8400410040f5110b40d01c02c3c3e08140085400206912502c0040740c02c1c807031070b003841004100000100741201c400c1e46160456100f40c101d030118402e0241003051a103030400a010300c0b071030000002d0580f4140b030703100c269a4103054403515003185c1c9142081401c1100a2068500ca4000002c0c928800249e80c0f50407403450304100b008500561802000080f07075420000074a025000140455400741d080030011200ba410b5038401c0004d0040c104500948203041d4801000100100e50002032034903a184100016140815034543c41141098000c0d58a0458800500d04480c1207607161130b010803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 547502014 1250 547500764 547500769
    0x106031d060f1008100506010305060105070507180b09040f03020d021b0607060204030b10060e030a0f0213060302120732010f120c09150507080d050702071206020a0801050102010209030d0806 84
    0x145900194824014100c0174490740d001600802c3c080c10003600c1c14402a41c600004440c0d5000703da5002e0540d0344145002c10540075424403008180c0c50704400030500f854403c2c00300344504d80a42d41101c100c5c07030003c001410f0643c14014000300328403d102905c030000344c040c07041400d00341904000c0c0c440d00c0e0004401041000da07074100c0c0d0085620003102085854032000d500c400140520801003c18502d100384455803602007980740603950f0141e02a14002c55507000d10480c4681400c554500958030203003c000760b596900d071542c0000e5207030018400c003410036043c6c10b804002d41c0f4400340f042d2100400c10040c1140322101001c0c852003072030704203c2c007107060104580c0c0341100840054050701e0b1031502a11154000042400c0d00c80c62280714000001c0c9420884941c4a00c0b04064003114060205200320302d41f540145e5086031440c03048850b070300e444200a0384003030f001d00340c00c888513580054103005480c0c05c04c81003801010240000c500308000748010a4a4106201481c010842c0850010700303180e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 547503264 1250 547502014 547502041
    0xe010207030c270204060504030f020f040e0303090c0103020304030804020609032e150308220f0b03060108060a060203030a091403070501060e0a1e05060105070f0303050106031d060f 80
    0x668120315000c0402d540d80740b410003d000d1854115001506840d440c480a8096000715000c8a215030f0700c8524080c615280d400c43d0340c0040c0700480e400394007003180c0310f1555518015042000e0000014641e681004050903103040c0c10003840c50f0501d0f0060081101103a040000396030b00c42d4041d2503c661316026440040c3c14000e1090380c545000d90349000b000c14507210000440b00401c1c030464208088100301421486644107807000802103001041107200e40c0c04e82c0600111300e442024400c01070380b41c80f00001602c44a0715080000d03020070120420501d9070340f0050700c9400400c00d440c1c81e03105078185480251a03102c0141a51002c58694811008010b040d48216031001c07030301000c1e251650041c0c5442c60284c1b00c0d6214a20b401031360103000c680a02190704c10024069607040028038040f106c0b90090340a410010000c40c103016041c0400b80104040ca10803050252003035400040342d604003e40034088402e80301e2013092004032860000c880900020b4003903004002c0c154500a01d036900c00c0301c00c00c0b4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 547504514 1250 547503264 547503269
    0x50411040c03150b0403080f0705030c070803090901090b0d0b10271113050f01110d0305101406070b0a15090911012d231806090607030e010207 63
    0x11514006201c0c20300c80d07240d88100001040c10f02e00b079500c1596030003480e032540a01d000c00f40c1403c008020a40c81c03444032000a20b1064030460583c2c0c1041000da0986051907000c0e40310f40e04a03040064004514500181c0395070141039003480401580001402003501d1000054004203044915400310f42d10403444a558401800c1c00c2c00d001102c40018010101c2c24860f41030b9003409e19040010715a001c4a801c800e454034010b0f000040c14020b80f4280c10070007650b800001e8241440071681c0d1446000c842482020203401c3c440e1070209403803c01010320000c954441c1d0002e11854810780310b0607141e9444908a8109540020400032503450b030f00d2425000f45101c1c2804550b885001d03034000750744a10754100c1c91800c2d0140c0e00600f5052001e200540e540146060850039a100315806007200c240c40c20f50300881041c070b0f0302c0c2220240103560a000c46051901491055450000c030b0f000b25a000d40350916060280162402030611170584003089c054090220001c06200c0c1035800780900b64420044da100 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 547505764 1250 547504514 547504519
    0x2e110d0315090e0309181b03070903080c0105070908030406020c060304020402091018050405010f06031e0203090a020405060301021612020a1509060506010806031b0102010e1606090905010b03040204050411 90
    0x800a12843c81d40e03952062105a0203400d40318541200e2160700841e05104100b04c11640c8015400a14140015070006049030140407140c2008004100401302620310350ba2170400026a60811050190245646a1086080d03074000c02050201980c00320700001da40c0c04c103444540d1280c80e28130009019000c3c02002c590028880c590039001168400b0030030304202035200108074180d4031762050000b035890900443d000a024128100b050610a0b403001700415003241c614000010056020010380c0d0055030140580c0d40000220f2041d0319082c4a11500000200c0c02185070081080405031a031402c401c01405031040d000c0c040030f8482c001e101001040750700caa0484d00c09680703000742d50018008280161051741c50800011055409054904e010344030050052026185812949040d042403900c103e045540f2100e98504901040104010f040d40040a64400b07605014000b41f40341c10591008407024241001005900c0c4080100d98101c4e4055030041915691810440021000503043da034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 547507014 1250 547505764 547505771
    0x60706091220010b0a0b090402070204240602031903020f0c0105010603060e0c09030a060b030c06030c12060613050907090e3103080f04112e110d031509 67
    0x7160341e0140000c58000a58210b042080407201e58990881d880340c5455500191011803e0000d0b9125401400b07007604014805890401140d0104064030000580c44000e1005290600d00c11440c1d0081c0710046d291510055042c03229180a000b039080a080200782030560003e00801072807200b2044440b4011610024010b9580d9014014000c00091040880318070441000c02d1409030b401007212440800100108903102d101d13100d510017080203840d210341c1441040054a050344440018622545500b1450380d10707030302c1902d4070800c4c003d0020040c502c00c0204111000b4000c500d1100034050301ca0503544c1c44019600c60340141c0f14040c0903007041d50b40c1e00c0043c00b00401c0e00401e070141540b038001394100359103081724482c07501d5854451100060114204500003486011010200356015011311044020344140e10082072054408681c0c030300004050000320200e1500114412490303043c549005d05141d00b48205061302e0300d45034021315003010307111a92401c00366501903131000600b08200041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 547508264 1250 547507014 547507043
    0x1311030108100b090103120e04020c0a0b180c0d080705010f0e1b220b15030405060403030b01020c01141b12040e01051c1401150e0609060a031106070609 67
    0x155542802901104007542400072540d02410000f490718102c903449502c4a100c100c1f010403d5405030280011550455401e100105248804019200202c1d028620300182401d03c1c0e15506100312403607003460f001e0341c4401c51210850321114455208180c0200c61a9102c403a145030041c0548a505484888103040182c0e00885040200d400f920264819680c0d00c066400201407203504504211101d00c180d42484411050606681001c110220010310b800e821001c01b8281c1c0680da00b06170b80584240d4000340c02c200406405100d1011410b10900080603038a580000080001400c03800c030074900640030813500103515142d60f55510300001c100a07213503041c896a030718010581242c46500c3d01810004000502c5051106064518000566911031841700d039440b041801c200e070911250722036598020b9003d480e903000c2d807000c02030420405030040364100f207010040340100180901d4400c40340204200b00013170704501020302019064aa441d00d403501400d10000601e8024406040000140900c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 547509514 1250 547508264 547508279
    0x20127060509030d0f050a030b0409080714190203031b011503051c030207111c08131d091e1e0c040c2c0a031b06030b190513110301 58
    0x81c01d142c2c401075040381c3da2000d14010032143c0403a0f02038000c01140041041c4103010f442a045005910340140011541920994400d00c950740704101c00c1e10142884400004080c00034803c0c19a188404005c072002d5a44540009890b80304858603208845143c0c041d9501c055429003003441801d11680011303613090342d24144252161546100402d000b428181c01388800d034040e100380c2e00d5846d00041900051641702e130600c01404882020341c880c0600950103540000e030080c005048648203083c441e030b04580303400c000160000a0810a200c03010311042002404040000e05c2d9a00d2041180602102184c00d402c0314103001e40840c204400c07441c81c20800c3e4010000180d8031500791403c0c0c03400c0007400006401200e000044c0002d1825400384a59800c41f4003040201032515510020001e864113543d944c2e4014015034400c10020506040c40780801110340c16114002e0310302c00595088014806084205513011168001c3c107120306680300b0a4052051190300040f03c602c00042d00075601c0d45c61b0b800 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 547510764 1250 547509514 547509517
    0xb040906053f011a03010b010906020604080a1119020913150b01050408030a021b030a030203040e06010527031b060409230f0405070503070f0e06010c150221010b070201270605 77
    0x1428006e6080140300b002c55442030300040c04035403641d8081d05c9035454a5070755030200d5100b514400100302c0c2407500c440743c0a40030b200070000341101800302440b201c500d10602540010051818481e00e40b100d024102103100414104c4a07882c0c14000045d0710002c500050340d1030b015a801407441c030b100110b0484641d540010310380128020340c1000d10519501c9604141d40c900484500900580060104101c01d8600e0459643c203c1d005060290030250a804841c48041000b030756481d8241c51030b40480040d050600102002c900b0841d80241d2210303c0802080191040d44650070b4055540c3c81404200c001018001c0e0748146c0f505020036079420220f807034144a07030b01a03d007a2442d02941c98001824a000100300c03080726a581d061482281c0340500c12940300b04000d00c0d45051000c40903119000880c402c411100e001000840140c44070402e01c00c0325849402c90039641d481c0311044005004282199054880303195092801c40c1144039010365089020085841125500c2c9880d90301140442d007010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 547512014 1250 547510764 547510811
    0x904200d0b0f04050402030c010f500405011107091b020d050313020409051f060915290c19030e0d0308012d0b040906053f01 55
    0x250302c4082241000100400c031101954002e5256000140c1c403c96540a400c0202e681c404034101400304c85001000007a1591601d02c10f6041c01000304c0080c110740e2501c00400740807200a16540b0348200800001300c0341c81c42103004481c1807040020550300d948400b0480e40d4041c0110510911180700880701d40802c240600c11084050b006000001c40301c4c81c4a5800d80c0c2c42a0700ea50441002c509e03c54080c0802030941c88802e440e0b500a40b400d8214040c0036904405069005100c0068400c0c6440445d504840180025003500d0316084803c00041240301540e80030502d05405801e005072540107c0141f52040d0400401d4600440c400090b450340a0300c0e003c0340d00d0740030340c8a021140b000c55041002e60552004010041a6000014402d0065440c01003030846403811340502c070b440502518442c001c00542c0314107000307807000500748400141c9014980c0100410b8580b051258200001c804902c00d10168129151890300900201d007400c411000c04801100c0008202ca100d440740140030400210 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 547513264 1250 547512014 547512019
    0xb040308070c0509070c0b0705071e1205040506040306020a090302030d080613020412140c0a26121801091703030615030723040302032409030f0904200d0b 68
    0x100c80000c3c03a820f1609a840c0f00d51410f96030344000b4800c0d0b964240c01500042e00ca802040001e0003050300190004c1455900040c5042410135107580da0703d010168042ea050302c030400c0000038070081145440e01d1003a141079030750001c0050784035008a60100c80404c695407000e0f42c90322030300c0d50341003000390044a0309000e0082511000316440324001500141d2213203110300c00000308401d190b880412000704c5a000180000b00a550712002c0c0e001c00240300350301c2070700099803a100c00002101d6892609030740c0c2540b00306010252696900186203045940155005580e08000c0100400c1840c0e2180c000c420103841500c2d20969076410744201c190b03590300202c801a026010380402a80d10084540030350344109156038600141e44954855100c6100c0506e41c10080290140404001a5400d00540c41c02d03907048038008080000ba20b5600b0602c03c80a00071041942040003140311010042d4121030489409640200d40d5841d0882c5403101082d08a04410b08035002040f42c0e8620307000e80d0805106410304 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 547514514 1250 547513264 547513283
    0xb0f01091401030c06050d0b060c03040807120c03030f0c080f04050111120d110f040806042306060603060310060b09010212090901090e100f0506091806040b0a02040b04030807 77
    0x801c00c602121503000c2c00060981e450071502000510311402c01841031000032800401c000048102140c02074000b01c05020b5140c00106046c88060360400c9100002c12441512074800d500750380320b42258554901014003044443d08046d199180a9280340b450380b81e0102c800c0b0795442d441050840d003a042805903900040d118010a0891000002c03880483c1d11803c1c80301d842d1403103010001000341001405540125814441b405480c42280007030070041c050070700030381928545480e142c003031017500c2c0f0b5612a85840709804d524414100040d45580003c065418954a40307501c0002031401800a000e1808507091640201d04843c0c4540a040605000c3c0c017110608090341840b4000c60140541198100411000407c0b01c3d02d802d40042d510a0300b0a403d80e58030303261100f03c14095503d585040d00506850380c050007190f081444040307900440104000352408820441c540c4c41d0003019002802d040c09000c00300e0380c0400a541110010090302030b0050f511941d900d040903081d004110241e54600c0c0c1e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 547515764 1250 547514514 547514531
    0x1a2a0a030518060f1005060c03130e150607171b074e03020606010e0a0e1303020c0a060e0a08010606091809150504171c0b0d0b0f0109 59
    0x4041c048041a03140b000241c0380564503404220b000b42e0f801803100341428407030070000030a42c035080000c210740e11407070001e1503030340f4111000c9a185600e40d910881c110504807040044556540f5055404901d00320b07103c95450042e410f003e40b000c00d44c0400048464000035488a00004103070110480f00303019802d48007a1980c4034640841d1030168180043e0002e20402400310048014010b01c00356807205103043c0056440818000311400c201e04101d001d81e000c6810301000c1e60300240b0046800c00100c0b0102ca9590800b08003052601010f00398203543c0030340002d8101014024080700c4031165019101c440c1d400d564401c02010a2000743d0224010300440d0004505440d06026941c203540e01500c2e2014003915201241118458284044406a41e920b288900080c01c0c0c0100c584074514800d404105030405042803000e03c80c02420031601c0320740400c140550110800b40c1d10442031040000004c40c81511808030300094502040201500c0c0654100440c128800c120b1506030740c0c000000f04507100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 547517014 1250 547515764 547515781
    0xc0807020c240c06010b0c10090c03030c020d1506090506040b090c130902030106110d03050f01122108090706030501082a0a030624031a2a0a0305 64
    0x1210009504480414032401c800442c100080c1e07202200801018508140036001c1402d102080e0412403510f070000405102010041001280e20440004200407088096480955107440303440024144803804400206554924540005c115040b82200501d400328020a90040480380102407400785080c01041081c10a442100704040000e01030501c00c0c2c171214402a07854115096080c4040c21500010902c080180042d42c001e1645841d41e1000400d10390340141440200c0411104061801d420001881c5041070f09a0456090303401d003100310f840d2401e055040303000d800f03e01c8843d55412862020140c2d40120520302c84c00d0804140c0e02c083d520f4038001c4060301e80c00c2c4145d00140c0c0c09094865001208200b03070f80c3c24503c045000508400e12400400d091800030f03030080e00d80070340d503801100808100d156203080c0040141e4050341000c0c2580d0781d5403141360207035095000d8111510009144509400307951f050020002401411243c01451803d956a02c00c0c060710340043d040002040018 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 547518264 1250 547517014 547517023
    0x11042406021009050303010e1810090308010806091c03060911040f080a030e0103020a030f18060e1f0e070f23060c030a0c0c0f06030204230105070303050406140a0c080702 75
    0xc0364450080c518591a005100d4040340c4080d1200d155080b03850084120488104428034040d0ac5800c1c020032a0304c550b00b0068035480050340104a550800d500b00302c11b50740c01007000c6030700180c00d50502c01460b41c5130400328010319582e00080d416505e0301c0040b4203181d800c04c010b41700315802141001802c9445540c4c81e070711110b103100d00030302040700c14120160660180d0040c090b15002407500113207201c00c2640c00f00c00d480c81181c02d210480c02803d03e000c00c0c08402d009004805400a009000403081c1c510003480f4032800c4484400c1d41552181d040d800c4610a20903c00100814140303101010344070044032225120b54114450500c2090100751310f02d00300101a150503409500c00b031410034440d8001580c084c45000000c480340112558082460f601490050000c1c02081e0380c01a15a800c1008131074400358244520b07081e0903008091401581c0e03200c0200c404803945071034045802d440b14078050010b00030040301e020100b80307482c0c1082500c000310381c000000c080444d079500816440390003061340c4a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 547519514 1250 547518264 547518281
    0x40c030209030c0a063c080402150a0f0c080c060c04170615120c0a080f010b0a080a03180e18060609010e0a090f020909070305060c16110424060210 65
    0x700b00c549903601425411405440c4840c95606207440092034003d6244071070790310405101022402c07003808c0c4401e60900b001c41c140c2d40c2c0351f416a05031a01d000d484024110900e026102c0007004001d50302c402c01c224000c0e040d255824440c030100c0e030207810501103482c19a081402010a2002043d8524a980c032000030828003580755a04200d108002c80300c14041e141c01d00800c0102a80701c0d4414519264403240d10b408000e00c844006068032840511855080d62840320b10769100c0d1499035014400c460300030504840d029454244a1103615001d481502601f54591007138900c0b2544004211401912440d455511064681980c11564546e800c100c00041c080c040c2030014601c0f107000030258036544d07001c00301c1280104060a004c002917400140b0303201d030403031301450950450002002080402c001d01c90b04815207516007800c044181c144420885070300c0a0190240c4140b02c0454000d44407a40700011001911001212041281351701d030810804d907100d40c60043c803a21000d1405100c05120b902032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 547520764 1250 547519514 547519517
    0x80f0d180e040501021b0303070315030210080603070f0608190e0c0f04060e0a0207170403030c0b13050a0b070810050a1509170a030f082e05040c030209030c0a06 71
    0x40da40c1401114101244020002c440035035081100d620080b203004a844404040c58000707554a10708903c000f002d40701c02081d00740d54805154001d00c0107a0740c0a801041b10006441d0500319543d6105c0002e207404100c0d4091400d03004604408108154081a4284a480c140c002900350031040d5000d103045801c58401c00c1c14580009072010f11a00d0321240c1b1000400c2e0007000451125264224400422001d9600815069002a195041010b0501807848540c00c20410354201450b64501a0525204801c000e1075440d0807000500050420b0b02800180754200742103400800c0549490729110718103541c8540070039030000c0010110204861414141c840c060150f03401245040d14541030542c84002600c184502c0c40e90108102c03000070340c0803015003800e000601c42c80c8441d0030f0180910041346070a004208000342080f2a4819500b0070f6841004039411190380ca022400481d0390f05001c640000d980141014508811280e050300034025800044040c0c0340450608010040113604900c6900f0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 547522014 1250 547520764 547520807
    0x50d0315210201210608071a030708090102070611180f01050405060d200a0f020a030c231204050405060a150f020f070902070b060a300b01080f0d 64
    0xe5a2003407480d00036841c0351040c18065a022010000103100036501c40c80c00f10003035600c00041001c100c042105000400d0701010b440300030506940348910780c0c0300040608083c48244004a20090b000f541203621658108408100700c3c0c01040240a4580c00100d14540c1010100660010340c5402602c030b421400058481d1407400c0e1501d0180065a003168808080140d42c0341d400c00d8200441314030725104805d83c2c8420700d03568038025101038040c0041e41c04501c11544650322074400250401d0386944950341000c2952a441055008032441c40140d071046809170192580d40501a107201018005031481140d091103107680381d00500800c1e00300c62082c009014071411140030b00c20b00800c060100c110f1640b055504082003020020314008039a44541c100319400220074003407005010100340c000c04111611000c1031701c1e0242c10340d0164407082e0006840f022800d8070b0f0580700b139866032186080341c0c008408001581e440c001075455800c1845481405e000ea040f00c0303001140320b940d1032081c0c0d0380102c0006 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 547523264 1250 547522014 547522049
    0xf0907090b01120501030c0302150306010e0607140d0809010e1f051e1e0c0306030706030b0102150a27050601060323090609070b0702150a03090b04050d0315 69
    0x1401601c0c1144940d41031201c03400c080c6491408a0060901940c002c0030b031491840d00e544180001040160140300c817812041c0309002c116a480b4801c0005103400700c944035200c04142c1403a020340c2c0040c0c4500800740c032440404000d078036009600340d0f204094004c0200410341401c07d6058441c1100c041c45050300c502c0c10301e40440c101c129407045d030304107105110302c0d045400d100324072107034082c030a440b102000310481c200008019503c04d4520782c80340c0d107144298154140800801d40d140b583d800341c84145034a03810a000c240c1d208000c50307800b000c1c042d60000e0250402499820041055070078840d031240075111707627418030f0300d05884241c0d02c60340c0100107118980c6400341c05ca0042c4050341d8581d0224413840c1c0074002030100901701c14012030318103001d0305207414412441c03460700400390f01403009241c0038000b030b0303001d0307a184c505009242c1010391215540d8030b1175410407001001e06580c0109410004c80c180000e2200004e2145554070403074408102281c0d00540e6041101a0b5102d40d00b501d13641d00f0b100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 547524514 1250 547523264 547523279
    0x5090439080106031725051507030c05070311030904020f0c07050d1a090a060f0b01080f0702030f09030a0203010c090312080123030c0a082b05040605210a0b090f0907 73
    0x9101b000861010121448443c54500da180d814000b016681d5030301034003507c0011070b04003120030b420280c50308041001c0d1140d02c0c0090118090000050180081c1c050a481030303141c20702c100c40c5d003502c0c000c2007190786502c0c1c0408405c2542150a0740000b40c468070102081a0400c2e02c00f003400e054100704900070540f1000c01100e010100100404000d0084c0d58403040000c000740109100b440b5810008600c40740517000042c5090401801c0740045070b46075042c04417080c3c0101c100c0740803030080340c100359030b038810800440d103041012a002905586001143da103038070f61203407004c400d90784070380c0d0740c21005240b00703204545000003030240f0b00c0c01045401039100403001000d4001207102028064035001214000051074080403940002d00e640c01803101c07640c0940d019542c1603106814040c1c0301548041c5082c0c001c0250146002e090248080003550800500791a030700c240d010724500364481140d10b03001c85243d0140c109007072414060501c100104488440301d418a62240c4100c000903d109450181c5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 547525764 1250 547524514 547524517
    0x90f07140f0613030209010303110105090606100309020a0b030f042001050d2706020a0e04150501030b01050c0703060c09050609090a020307051c0605010e0306040c050904390801060317 81
    0x10f64084100d50b8110000068941c0d480b500e00840c040d441b00b01c62203508500d5103003511801414683c003900038030104281640c903100d618a104845160000710301040b0310100d070004407540c00ca1a00ea0001004018094007030541e0103208510071444100c4404114401c4a0055a0408100d011a03824400050201196031041081036103072032040c03c0542010b0075400b40c101c0a41c00503a4600c0e00066000302d01c41d000b66141710003031420748080080240a5a02000c000c0701070040d2410140c4503d000100c1d07a12403004d55041009240c00c0d209180d070740b8079109000b0b05102940f80302107146140002002d140100c00d407503084402815401099807070903162402580001d100d41d0600c6018003101604801c0f585400c1c0b0a503016150001e412420640090a090403905d15140300344e00040800c00020944018001102c3c020b07a582c500e140c49902c0c108811a000407807801028451080d5081c0107920400441580c5e615048038100c802d495581540c01e8a0312404094101402a52001240341c4500d0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 547527014 1250 547525764 547525777
    0x1020f0a180b0313210f030e210a140f0c0118080a030e101806201903020f0d050f01050402031b0f090411040e010b0a1205041109090f07140f06 63
    0x1c40307810072000581c0c40780c807030b54207508080c00240b00c0c11800b0f0306d00b03030988035840c10402401c4c0100b0301e0100421404070700750b540809001894101103003480c0d50300c1c003e401140321680d40e0f000e95a01c91441d0441d510241d0403a0b401000d8a40c00c190200079018000340d810300e00c043d004140380b80f4203010040f09402802c194011248184900241c15408040c6441150750a142d02d47e13038168a840e4034105501910803203802140504096140d00003c443c030301084801d4041c940450302d10721346014800741d000340500101d00c01c200100080641c030030091584090300c9001401c02d50281c990300c2c1d00600040340001c8441120b8201d500c41c04000b48810709000d0003d1340e0754a9981490410300700c02084c16901c010440c0c3c807010f9408102072210315050360b0401c1c090f120070581203082144a40004010709141400500442d40d540c0c04241400030082050f4072060300500b1802c030a0820756180350391403c01c11801152030059180c0426046185588030f40842801440d52084540d802f080118030750010 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 547528264 1250 547527014 547527023
    0x209040b220b0c070516060c060e070b120c09040501031110030b030c19090603050102030f16050d1107051b12071508180114100506070209041407030501020f0a180b0313 74
    0x609441124030101c1819025021f140d84280744c4a0161600c4010740e4581e030003440a507007210006103e01c410750003c0d1040a130380c0072100d5800d903d55001e40710740352049c0540650001e007890008828000ca0001706845024103943c03800905284020450840752140580c541c10b07046091f802d050b9117420700c4c00d10800401020000546555580307040100c82082e88101e916940200802c1400040c0c0640c09600c09141807941400420845004016118481e400c4080300c0d0b803044910b141582c910182d40c42191f0020440e003420800c15480b0101c3e40020391018464801149803c080c24400b0a01004842c4101d42d81203800c1e030007500550f003150004002207071a103110000e51080c0c0800b4043c00b00b0b004410100c07810380b420481c0d00360603007140d240c0086000704010000c41c0010780b1041c1030a81d1064100140b03503e002c10388400ca5007080e01c3c40d03201601c25070001c13826200304031880340109040c9035903485148822441c1c80102c80044514400c40d00030980900011314840740a02e46006228802c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 547529514 1250 547528264 547528273
    0x1e1701051009090213030b07170f19020a090305370201020c030a06092102100f06050d080d18150203040503040e090606100914040e0a0209040b220b0c0705 68
    0x441000314201c5c1c12400e2200b0000310f0310001002400407a94100303820070f41515201d1382d40549440081201d040c09800070000c010707018006001d8a1030041c0c20b03602426160380035540d0f401450b41c002c080e5142c60006440c03030301803801d1409070b003100c010b1240e88468040d040000c00c8a50003007100000b02d980b540990640c000c400716261b00d580c080c41207508681c800e040c00a00c2d400f03582416800c0c0800f80744001151301c50310001018140d00042c00c120b03c062140000b1494440d40f10402024040d203034030594101d030805103143c007003104072009800f0402980904003c15921000c5c00080500300d444043c00004d0036840c0480151003907002142c1c01800383d42140d2501e80d0710400d9031800c0c1411961859650410170500102c0d142005983d43c0c646001d1078100342d80c80c140401c4031280011194280d105030798a10a0754030a00081c0106001c0070b40061468003645010b00300203018403022544580e4211284a14020700a48200c03c41c200e56045004c548103540c0b5070070140300c9a40241130948a0340314 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 547530764 1250 547529514 547529519
    0xf0a0e1206240f0910090908030115050f071e02060f0d0f02120103170903060403030504060c030510060c14031b070b07050d050d0b04090615120803062701061e1701051009 75
    0x79034011007c8151181000329135035850310600e00000244600c990013000b0040040a0041480200703403403c4540049142800d1442004e81d81212104a0720094000f00302144130407903a02c00c01c002d4034141d100c82c035041c03200b02c60150f01e4404a10814042c1a0851080c400500101d01c46041010090f00900807185c54469602c00003443e1030000c9600b2000680c544080104000c010b018042581d121800c007072000e420015804000c007003082c0107503810811f035400c51030240542d00703402c007480c2d03200c481c01e50369216802c130380a00e8854100c406400b445d00c40c0500000d4484030380401c54000c6c980207405090009043e03001203071503611560f007084000341c03285080b04090361580b08850340c181c465100081c054900ca04190f8501e0220b9010003104800100310401281d4020212a4010b000300d0303580c102041c02d4020b840840700d441000b51000340070a0000715116400041004131200340e400700300f8800c880c15000712550180201d280d80900c901c80e0040000f07040508000c100c540703ca0400d18400c54 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 547532014 1250 547530764 547530779
    0x916050a11030738060f010302090a030606031209150c020607060e07180e100207020301180317100501050702190b120f0f010b0f0a0e1206240f0910 65
    0xc01c86074003665400e080d00302d42e410b508041400c460899892492140344c0365408610b0800200b8028421801651200701c10300d013a0b8480c0d8125060011f00810114540f03440c1e00704540103044900045810407010380c07000602c9070056140c20201c4104480102046c0d41d001400c5920070a4000200d030840401d108680020b02d0600032400071071000b00044c0300241c41c008030307010030018a84005002d541b500d045440c00800200f0042c914004208025981c0c0307082e440800d0040010090451f091110071020100f0154004160301e901c100c6030310500040d80314962036190344480352140c035020a004020150060903c40140c81c55088107a8402c4415565041c00500c80d80c0440001159011840304104000c3c1d0302e44540ca810481d032040c05052503042c01c00340d4800e40300f91401c018650101040e54200c0c984181070585d410176010300951244c0822a190079074807901070320100b0341155581c2d40d02035024010308005450700b000a10750000a0482c0042c044130200180c41c103207031000c072001d007c00d014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 547533264 1250 547532014 547532017
    0xf260f03222c0105010e03370803010e0a0204120f06060b03070e0120070308161a1909081902030f04060c02010f2f0322140916050a1103 60
    0x30b46852480c000b02e404031400e100c05010140c00203418068102c03078403105030303d002442c4880f518984040f007420000e10002e040386159412a503d01c00e10303031003c1d141e0821080d44040e6040750411043c2d00229143c0103c040700382d000e20300800c0303200a0b418400c000407828445040c8196030058100140098517048501c1003070307004030750800109071541d0f100c4c8402d581c4008000242c1d495241050040e4004182e49511100c0c10320000d0314005000c540b0b001c0c40d2095070b807102e200e641d00088500d9507c16446800d0742180b01112903424000d0f0b000c80c9003051b030b00d45001e8541c069a2101c009440e140240000c40020003800e5820003c610040c042c070b200c0003a0600c000c1c0040c00403030b00c40302c0d44022544001801d241d0f6500b83c1c0d03020041c549088010071901102100351a0011a950030861103680b084249180256040115207020101011020304400c03940d0009a0301e42e203020012035600c40081c0a8810000d690400f1000282201c00850038402c101078100c2500525000c100c0c9100c94820a01d503 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 547534514 1250 547533264 547533299
    0x702090906060a091e0917070b060901080a030905010f0927050c2b0b030a0b09010b100806090709030c0b0c06150f040504020102070f260f0322 63
    0x140e0021040c8286890088904801801e1070f6000717210002211481d10301c840840f041213001546c036103d1840400c25400881003203842a02905a00d0741d8180c1440d5161860a50b005805164150000302e8441e101083c18800e00d5050340310090080e1070000110754505203040c21a040002030130f0003061081040d6815084000c002c6030510049500e100c1d440304807840600007403503a400c204585484011b151442807414003110503c40314414004503118050040504030940c10b014103c050342c1008a40c840641c042d101c280001c00100106006028411050684240c04500b11070b001030000c1c07800814030f42d444803940c903180384815602e80e5450f030701500079044100c540401007000003e60108000146d4046244480300e500041c6e9000402c90904010031814007079900e6000040559008211080040103003410405c0c2c003580d680142d0780301c04200e107250980d040516594507550640025103818012a9001030352030042d21a040702c504000b1070650003100628130000142c031802e40c0d80351600 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 547535764 1250 547534514 547534531
    0x120705040510200d02070b09010201090b010b0705070801020f0706020c0c0409030f080a09080301051215090304050f06070b0f280c02010e1c030e030c0d030c080f04080d050c070209 79
    0x14450b0401014001410b207110f4032404681c0081c00c9458142d6001461070200c84404d074506907500c26000040303000d010a40809480440800000074075480428010101c0d18044c40c140c489283d01c0790f0b0094240e119840d0391800d2100f050012001045907a8000c040f022062400c56080003099000b0a09071072901c0c400740e010400c113541c0c20f041e03a030300b180c2815409400076400304207602e002e58a05149000c10300600340071710565002d0b154a407200308000c1000b0581203040104034680318844a64a0380030340101070107252498144030311403e000307003501c140036072004410700d540da03510070703102140c181c010b280081d1101900e0602c030080070010101c00f0981e40c20040800e00000d40c0c40301074299000514943c02540c004006004c1c5650314001c6080308101c20700c0c021a04045400c200e40c55400f90140d2003100b801400f400c3c41c2c1e055019440035000420b00c0c1c8030200c1c0c560f43c01c43d980c09880011203010f48440c0b410447e85514405a0740b001d60700902102d040e03800c0c40015000304a0f0520101d41901 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 547537014 1250 547535764 547535777
    0x708370f0207150504020d030c050115081608071415040b0d060905070815040e070e130c0e0903040303080705161b080109020607120e06030f011e0308120705040510 72
    0xb4107100075210000c804441110b420301850619074082100c4211180e0040d003044650141d04040007400c1d00f0100a5000c2c03005232000540e1240d11064a030b402e000300d034002c800071020b800641d8040100d800e10468410740c4418185400310020300c032010561000001200c00e00f0030022a00e42c03540000b80a000105030b00000c0d1107401c003442e003003c444014020308148440f800401100040d0760840c0d0404d56810784000c01c0031b4a54140a130714110f03143d008014407100d080100181041142030828030140999030015946030f40d41d00c40c40450205555004043d0420001800484d026080107600400546025487e0581c1d001d40ca04101c5480c00c0e08a90f0303807500300401c40040070340641038005080070200030020307a450f44c1d0000310280301c0c0780302c0100300701c8404105400d01c600520a00004940241680742c3c2c91604041580b25084e090064038001941080440601c00c0c2044a41c02500c0c0c1c44107125241414010001180b020010301c0602004410000410640c8030b01f619420307049425121034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 547538264 1250 547537014 547537027
    0xe010806010f0501171f050402070f0506010e060604030611040924152c090711061302010518150a02072d180f020711090708370f02 58
    0x310b50b8180a900c9a810042610350725855036a204008030b81056a840e882d81035240394140c41c4c904d003121030f4481a8064170205814050000b4480d500d00b07028840e500703440850f0780710700d02e4031114602130701c406030450403d01c010700c002081584001168601c0c02012403c0c11b603200c2c510f2041c2c03600004d000007040c4000744155030200e0103000900282103204288030200c01c2425004012401401700c0480180100c58044030458180d144180950405480030059241980026190300312542104220380724000000d020440d411440c00440c950580d6045d241c40f280d0700d042103c000310703a20311907400140074600902104042004140541550700600002441c128405846060204c402e2641040e84031084c1a81d00300c2c003802c107095800381c0100030704807840d04107507000900001c0e101703103141c0744002402c01c20300030001c91442604104841061040d90344440c00c0320b00090a07101442541020440e41000003031a100c03040c0d8802001d00d030b035a440140310340c15000342e840d480d611124265000402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 547539514 1250 547538264 547538279
    0x2704051003150c141e0f0903300306030f0610060210180605130f050102090f030d120b0310050a0606030c1b030c0206040b0703021e0a170906040e01080601 68
    0x70010340c2d41105040100c2e8600ca00301034035051404c402120a0840000c1e207903034040d002d020070101070000f0140135450340452021240f0503444190102e00c40e00c03c03030a1202c04074581400c5641c1c1c44450851502d0a0400d40c80c60301e40d5600080e1000b5414000c4001e04c800030981003140d0781c8951310380e40201340b1140c64010003034200842c18280c0110541400155100c900c6403074407210082d548044001440c0e51022240c1c0411007403460002d00304084010300d102486030540280c1958038085440b0505031503042c0c10156201ca20100d0035002c6108040c01340ca00c414968404000d1900113025681000002e48284084030011a90211440d27030350f503018441641d052203414403880c6c03141080c2000180508603d4000540e00300001c08219110b4511005c64440030180c0e8001c000110425480306030714a0003940384d80c0c14503500039903102e0400071998410800200154a03680085207034039121064222000c1d1640140056a0482001c00c0f0016052070004960780c000c24810f03020b41081e5040411 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 547540764 1250 547539514 547539533
    0x1f030c020111070210050408060a0c1805330a120507052a010b060a0e030c272707060e010302030115080604090b011203030e030f2704051003 62
    0x1610421a0700d01484a00325610381c2c000c9440e81038045480600005070030808407401c0c0300355001030600f409041d0038005150f0441d0862120040e841d101c40c000c50103012440000c2130070500c2110f500c024029020352003050500c0d0f501510294018002401c41030000540b0055440b520125002030800c2142c4814410b03607104541c0c00028070710380146070840074031001c201d031745541e404040e04401080414290103401d5001c548000b001800540d10b556481c5c00150828605042c841e0107401622400390b8145815000d858544660020000041ca43c0c034000d091424401080301c0844070800f59417211560000c100a001001010010015603091100050440e0303002511300c1c0c10f041c01400140200c0813000c40a0580e1407048c6040d41199507020300007009000078500c0a81001ca0b20b1001040c40703583c802c6000700c414069182849684041c240c1650340f4032a900c1c070014541c1007808590084036411003004c1c5500c003240c00e18034200003031a0000301102c0e410303034140d4041c0213100f1041003008408074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 547542014 1250 547540764 547540781
    0x131e0509071401080711060c030414070605040909020d020a0b071e030c020405040305070c06020120040e0105210d050d2414040f020f09010e150406080c091f03 70
    0x54800c0720320700104129411200c0d035901e414400d000002802c0c1a1041405040c014a10402c9030042c0c01d00c1440010594420f4500340c40c0b01d0700e50405107040450000d0840100c3c0c149a50343e91a03c1e10b400c4000d0003c010256049034042c00500d08a40560307a040548805000702c12816a6201c845141000300c1d007547c80c6000d240403202c20700d404003084e0030460386000136805031400301d46680d8903e011111807040440040492508510100d00203505512190000c1030f4902e8508201d881c0b00c1e094600c0380281d214100a42058000502c02030034400010035032900d08000c2050010001130600d4100903800880300002200400c0c40c0c2d007101d8103409240041469200010713010030700d00390101010f00c12401000102d484824504003552a01c1d40155100c22a0210842d21103a03503461001c1d06030301c00c545960005003c00701c00030061a10042e174240c0c4500080141c0d10705840c141d015a5a10402802a03002d89028440301e4000c0d15101110350045105454405221007240c202804840c0003d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 547543264 1250 547542014 547542031
    0x6030c080c030a02030406060305030304141e03041401020118061b0e090604090201050f040306050f0c0316082a0a031103070c0f260c010e0c0d11131e05 67
    0xe40512000006a5007282c1c0c201d10801800341e56036486081c0000508190f80c0024558031000081006000c8105032008006030401c090324002d814403100000210401204080c1980042100b044076000c1c81c084540e5010040c0004104000c010411002d06108404107981e0b4603181c131903403940241ca82050f404000990b0800940418884010030046a0000d0907140507985d91940300003568056410740d07a01110605080d070b5940c0e00da03d0000081c0209444025a03444650040360344141c401056a1203522a0106076441444e141400c6401200c094890006d007010500c140005035420040c1c40306802030321101a0b82c0d181314680090860301d42d19403000845805100b4050010740c407151004200e40c11404c41c0310140458101031480c062240803258a880083c0f015051086140c00a00020b8015000800074090800c07900c03078403a0000448250320807003034015480080c1054101d0514110040c010301d0700000705a006104840700c840c0c61a044a528500c141845c2c40280112075124a00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 547544514 1250 547543264 547543277
    0xf06070e0a061202030a0b09270a030e0d11061324020c0f040605030f0a140d08040222050f011a070512220618090506090130060606030c 60
    0x40a8004250060f640c8207103402d0b64001000c100a0b28150300001440e0380c00400b4040c0c11300300007002440c60054103804d10a281c5100305e901c040d0020104648241d950191035403840b424000f010833001c1e00152004a4003440c4482598090741c4850026020001003403566401c01f070305102040001745206d825602d46000c1c0c404410b40172550101e40500e40480507a02d401d0307101a0100040c1c041c004c240c0000e90144a070b21400010070000107945010307507004450004805051110b07658840700510a06408035581c0c2c00071078018100200f02040d20030182001d1113482840d20181e0095034016500c604000c440140140401e56204941c0c1c0b0001c81d022650320318000c2690340321511101c804841c1421000080740340d112480c080210504140d02400c0d00c00c207400e417110b40182000550307100841001c46070344000301d0f6101d064482d641c001c0070b00516039001c40c1e1a04402403852182c00710b406404841c248100e12070002c403031460307011142c49090040b80340b5042001c0181110011603001040040 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 547545764 1250 547544514 547544519
    0x1203070312180611090a05010c17030c12070905030709090b0112020a150302041404050705031344040b0703050a0201060f14030d02010e100207020d050f06070e0a 71
    0x4110304100d048800d000804a2408500c980c440c800701d4403450003a050a091201c113041404010000303000c0b505045034000400b40e112801190003103031401004140c19815610020200c5121000d59407009070344040c00d191002c1c7c910b5510106600391a03e10200705c0c403a100b0310080c0740030310140010309a0744a08100741130103611083d000520600c034841c40302810445090642d01d4030804100a40500e408014101c0150040140207510901c112500c1280e074250418007171400780030b0a4004e8101d5951a8255203525198081107507641c07500312042c54048080c4108103a04c0c00b4524201d03103040000a1001a500100106103009550203181d01c400c10001400208841010343e20041d4041c94541d403164038100c4164010500b40d040745002c81c0d0081c000041055a80c0c0e0884c84282065003a00c80c0c1055a107411b07070980718a20310380c0b06540c11240300100840d03590f5024003030440c002482200d4402c901d0701c505040120911011460340c0000080004940d007080100d0fa0b51003050310702201d41d62 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 547547014 1250 547545764 547545767
    0x601090b0109093201091812180503010f0902130603050d08071416061401050a050d1a0703050f010e060a030303050a150f080111040b2a060c0912030703 67
    0x48940074000c40a503841e00b0f0107007011351000d04408800d28000b01d1a401400501086620781024440d0342c964905111417031803a1102c0c4900020850790004200b00c81424488044c5c4241000444001c0b0924410100103081e903002d010300010211407903800206000b841c0184044144a46c524480d564104103080000410000e030320800c041203840c00f2200d03038903005030403519400302c070700c241c0410076011405144042803038001e9010144101c40800c028200200c003500c290500340f1500c0c1c0e00648800e001c2146040c240c19654015100e82c0751141851034505145901507000e0303910760002541d440030040c18000701009a8090490314417101110301c3d18100107468003889000003010036440c0c0003c10041d40744e035000780900c0c0324085d1a40c10300a441b02c90b980c9145513a40b141c100d1542c03c0a081049a50b400382c1210242e03035045074410b00e400c40d070301103000c00b004c0785080b26440e506507035407141c1310400144a00c90054003030201865950880e80204540070903002c0140d441034108000020029 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 547548264 1250 547547014 547547027
    0x7021204030b010e0403110a0c1d04150f020d020319050603070b0711040b04141605090307030611071b1401030204050112090320070e0a020c070b030c1303050c030601090b01 76
    0x5410a6004c0b40c6241d40714503007147c07014184624600d1520a0500440030030800800040c00e444440e404134400051409500080c03800944001e0702c030900c000340d005003410302a0425645402001d901503d403908401c041c0040703920851380c1d590517020114440000c4002c81c003c10341c00840440c020030006061800508861144000050040202058140d42500e46801c007218a0310018000c01c21a4001d45100d504007a04569080c4503040101101d50180e01035802e503000d800f0094018030712103045075204001404004220202d490081c05900b0024481e40e4003140981022201014100d141212002d03012001c8680176040c140140020b02c01a68480f001c1c02c2e03032240c2d0840c041039400c45170906031003074140c1000e2440307003002035001241c0f8100005220300071540d001c1d01480d2a50b80e0042a04201e015140d060121504442004c02002020401035500240b400d101d00c0d1401d0440d100c1c040111001e40e1003118241c1140103007081030320307060040900400420200f40b062012003c00240704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 547549514 1250 547548264 547548269
    0x11a041103010b16020d03081806071713140a0606060201020a05091c062405040504080405013006032f0d14010e01020322080a0e0102101407021204030b01 68
    0x40c00f0045541c501d602c070201d510115440d0080c2581650003c0e50400a03c1c00c10219011802060703136000e40842c210000603400d02c110090b5a8002c40401e8107103005803510f40107850704000da0051840d400204403d41100c000d1480700c0402000f10000398581034080c1c450f96070004082da44180800071300c0e19008000c591034400c04803440031070320f00004050340b51007450440c09000280f0300080d80300e600100e04240782560060180702c03001103a0710801c000c01d03076808507001450303e441440b08102c25401780d140040c541200e03130030500309050315024404881e0248064140c400d62207038000c00034048065142c00400056070b00040700032450b4050403428403a41e000c0b641c0140030222004080c031240700303002d4140041620003407103a20503c204e4140031750800e031641d5050a00300c00c4c80c00d40811043c0803c04456070b0181e8100d040285000003a541d18901c5149035040d80102c1200f28042966407150040c200b52031000f0440a00b0f1868009280c90165000161283e404020500100d513081006604 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 547550764 1250 547549514 547549529
    0x30b1e09010602010e070b03220818031c05070f1b03061406010f0f03020f03010b04030c050d030f0c021f0c0506070f1409010311130e0a0218040902010207051002011a04110301 77
    0x950703441c1c0c1c1c0103a10204121003046682d80f61156401e40801c0783c0f20f0020000c048bc5a40001108280e00080540b00c032095078441805010b40d11604064900590150140c540140580c50741000c403912031030400901c411907125050007185003801000141d11419009010710032400785507140400001e003040701081d42c1e0400748100c00460450292183d0100c171546400006c13042c0d165695035849841540003804100c0d803442d044003000c2000e007000894400c00c29019a61062604440281524072110111060360040a000d00000b8209140c002580c0f5151040c0e0300c28080080700d00740a801c121000c1c0c41841000065180300d4070090b40401c190820444504041c1d50b1402c810005900626511021401d9001d001c0707082c29a402c070440c0ca00c0d00302d8450101301c0d85143c0d9017000c044128401c0180701404004031200707800203400d1546c062003a862040c011541c8094541c000a9810780b0450030460041c0c0d1101002000c0c4181c00c5644011103100b130301c0511076040345800010050005014800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 547552014 1250 547550764 547550767
    0x312010509152107080102040e0a1a01081f0f03080307030608070521030c16060306050301200307020109060e0c040b090106020715091e08010515060405040b01030b1e09010602010e070b 81
    0x3c0390107001a600924441008554469a505940c030340000201d0700070800c1494102c81144800700044402c1c22100140e40b213010503034401120319200d0503410075140900c1d0002a001c5002400d0281150155020740c44440e12850300001c002c054842c15000040b658100c107030104216150090840009040c5507a05454800c800d1b02a510f507000301050f020b084d100c1c14401d41c4402c1c00550b1008180c0f01666004e00c021500c40040c1401d85170403100084421a1400ca0003203002140340c05540c00c1050351001294555041c0c0301d007c00d9480092801c803854202030780d8609189894412411000d2081c0e4811407190714011021703488070540e114003001420f039440c0302c4200c42d12903106d00c0c01a0804c20400d41440000d03690003488440140690a0030758030300008a0b0f54901003181e0b110a0310001800a45024106024040a4a8a41e2110b4140364884140041c0395035030b10103054103482c1119061007108564004c101c50030300103a00010542e45440c5424001d181301094500a5490006000307 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 547553264 1250 547552014 547552069
    0x9010c0e060f0c1204061107262514010314181504030503040314070f030302130e010905072307030804030e0d030305060306060414010510090503031201050915 70
    0x400e1244120071900c030b8207016650b000107569060368050020342e0f01c250303a041f42020b82030200319078403486400b544031070300303c500f00800107030003840c09074072100511100391390003841c07180200380c03050701e07070381107030028a101c01c24103003e0407941c80c4510802280c2464280302d180d000b410030540e402005400c08000f9140c0d0105140000810003c00c030580d0600766010a0600c0c01d0304008007990020303039088000666855100d240c034202c070000d0751491900000d0030580c0c400c0582d13090f4002d5000d13000c2d22040d45100000000d186d40122074050090861003400b107034920309024000c0421403c3e1015200181c103880045030104e1481003642d078203c0d0b06042c08442620381c3e00b026101241d612400f20303480301120b5009000c043e80360700268000c007030650445000791962070812056440412a14a101b0f20f0b603030040203c4d2600c262041400041030400040e000d0b21440401e0075030380b111107454004100280100a03d0900c2d40015070f11031042c0c0c201440030a40c000005014400040040d0b4800e051a00407 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 547554514 1250 547553264 547553287
    0x5060307120f020a050d150905011805240f010e06010e091906080d020d080a02130b070507231e09160801050303030708010b0d0209130603020909010c0e06 68
    0x125030103403003100c103841d08080d035500d410b144905840c9400c90043c24800c00014080c14401100c2074071aa1050302c80c00b03034000040c0c07090024503424501390b40c0781d9200c10b00c0651800001140d100c2c0c1c54000c030080c201d00200f05840060040100c10300100c2c00714868204010814500183c60565002010300d841545501c40100c5081c50783d2040503500414100900a20260709401e808000003180d8060180303d40d03070440b1030345a2250201c81d10158000e0180e8010440c803684040c0d034001415034005043c100c6c0c02c030f104000c002c540d804c5540c0e240400550441403110400c0240024900c0d18040034440e03102c002c02104180000c0310540c040c446000340c2c40c22400c01a40d000503081e00160050b601480c00108018451112a41032004200e418001040508003c003c582c07280c502500c540201e80d1030140302502584c811100c1c00d944981c24071000e4029550411046001405820040f402500f5401042541c4030058850442e5a00d0041031080440c3c1042d490391f40b003034003280d4175501c031018000c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 547555764 1250 547554514 547554523
    0x105070c08010507030e0609060114010e1f0c1b0605191205090606280510050d020703180803160b06040b12012304050601031101120213090c0e13050603 67
    0x8800c00340c2d42030000f0010495032540c0030740034241251040703580741e0f01d881142075221a020b000d0701d2074040213120000c1195000b0f240600c030b030101c05491040720100b02011100000b4a4120340000114102c01c0da605011089246070140c010101418485528050001d002842404420b84188115840103081540180401d14030311605031400e00440c40c000101603210101121103034459104c8a59000c0300c001c445e10700308c60750140e654200742e204d8200f2081002e0002603450120410030208012a0b40039004e00107441418440c0c0c03a40384400c102c4040640c0c0c00322080e00801c003658000d2180e10500880e40701d565038000e07000b020120070341d110400840d000e4481140802e400c48440780c402603100078150701042940020b96800c030a0644204900c550060701520047c0850780008010310108443d1094030f43e14a070141401c10940000c1e10004007642c01c04000401071814220040102c0d030800e0141454008191415080382540c001c0005d1501021500c0c00006590341c40010b6125101000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 547557014 1250 547555764 547555769
    0x20090112030f200a0201082208030a0204080a050307020405010b030408030f0c190c150605180903070609030e090c19111005090a20010909020901020a1e020312090102030301050105070c 81
    0x2908940b41d43d204910342941c07400c0b030841c1240020740d0900080c2c83c1d50002030001000c201001e405000b44206034640707042540000c1c10190140307900300800a00400204880039415108101450715111103004002c1110300c164400007268a04104000000d10828100c035030204120980a070b480e00c42c0c01c45a03c45000307240c0b00c2c181a42e0350668021070aa0002b8041904910540000d8501c444550045080e6001c40c07040329003040311005035010340c1c681c84459990003e1180c088034200016500d511064642610b415004a0351810012003c0c2c00c2c2141d8150703100a529908903d0070700c3d512047c880c074480c3c4400c00c03801c03c4201800c4040325038040c8810500d080128100780868288007160036120480d415007122800400740000200000001c0c1d29951008140c44000f541c030301d00b00c0c0d11070103584884a15070441c000e281043d40017481c2048490b50703120f40c080c145000450248145440e0183c01c40b0b103d8055401400b005641d0780e400001c4905440c0e080c6000c0303885031002d1810038004921034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 547558264 1250 547557014 547557047
    0x50c0303030709030c140d0201120f02070809030d02010b1f0504030204150807150503070e06120f06120102090d02240d0c0914010c0b1009060320090112030f 69
    0x205100300c071680124040f080e28018681d22001c155941c410907aa019080d6103180c201d554001c414004d13600800c140c546062454101140808003140c0c0302d0100c1e4086401100c06660104040301c49080401203036030240030341e0000308101480355000484910220760051603142e25518031a20940c4035006507030007590b02a1041c00107401c6100541c801406a00032646d0b00d11607520001407106d1840085012102e60b40c841c6481e40e212076a0448040048041c001c0d007000c810011048449401181030784211500c0b60a28070b20704080e070412407203544420458800d0303030040c060080203981e0002d1000189031304075031000c40c00851210608240401c0543c0740c11325003010070300c0f0703096030f1aa410124045151f0f690310402c10317403901900342c607400110a140d40054074000150700000c0109414540003c4000748011040d41e54044010980f0b9598008960400764281c01c05c001c131402c41c071785000e0031108617803051a41d8104001040031b0350705c00c50080c04211a150109100394000c840c1e02c00d1036041e0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 547559514 1250 547558264 547558267
    0x506090112050a052d01032d03080601081003081207021504140d080c0d051b0a12140403080a090303060302090f070f0e0120070506120f09070509040609050c0303 71
    0x5440000c0c0184400c4a005d507040b000341902402584560719020840400e14150308030f16400c0d40c03540c84101c00c50081c004a00286a102c603400140d16002660603680700360b58490007807500000040805002070300601075120b100b1010300010720703810140c03032860254020a01c195998800124a4001d9011140745500071007800e000c1031041e05000c00d150206294112161062041021507450f0b404980d41444405e0900000101400d540c0000e600242e010b07035000c031501c01600f400c0c0e4155103d43c1e0302d41c0105403110b803140030f055054002c00b15418002d0040500c58a41520090441940101880c40d0a41e40d40f500340200350003584040c01a540117071070007080c0d20701120104c0b00070f0740070743d40180410141480b40084503ca402c500000150603998260741807510303000b041c1c0007290301e003480c0120b00440301d0100702d036180c031000b4003498401400103c54904040740314040110010305105841d4000f600f00740003549441d0b140340d403c2940f1500018042e50241030950030081d25054003a4103020 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 547560764 1250 547559514 547559521
    0x102251b030b0a05060306040b0103030813080d0e0601210b130c0f1e0f060f02031c0231060e031606021c0207122603040302070e01060e0109050609011205 68
    0x1407400c480d510590403240100045d844840815990311f000300c5000340162041401400020b105411440e00f04002d8010441c440480d561512200d0300002c808064403980c1d52070b8030700300c0138003040b405004018008c0108144595040c15402c0404080c0d0040e12680900b0082021081c0841c000d00b003064100c214411041d45500e000c000b1540a4410411455a0b5140e00365482801d200b42c5821100711428034460503140500550740b1030410400c0030b040d8082400000c0510b4401c2003100c2c4140111800160307181b082c107070303101c1c10000c0030481c18441084021012410546809411040e68142d00b8050028010350740003a01d4041c00c2d61000000e00c145500016845400003003000c07445200c1e40080c80b02c860041d804aa0318280e0303124480384c502c414801200803601100703500040c03142e144180322114010a225000390392080c0c60403801644856801c02512042d07691050242c081407820503940b201c20800246440954069248104000541da1aaa0380a507424415889021304113000514 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 547562014 1250 547560764 547560773
    0x319050331060908090103060611210f1216050c030d0f0b030d08070318150b040207120905031506090a11130f0e07210e0a020607150e0102251b03 64
    0x80240c814107002c6420001c010400d40c2c011800240c0c10f5407192b00404244140c00000c0442d846903103c034000c86d00c401c1220b0150804030b20f0045c0720f58482c004080f801d80c1010207012040e01d8410040200b0000c0901c10307000341550201c02c96038140150303203021500d405104d003200001c2c84407440c1c1d1945072180c075484480b04c3e17800c94002c0d889042e06131420000c1c4031201036858038044881c030004141034042d07050303075030b1340c0009501c200c030703186400341c0010300340003195454010503a03021002802140000200b00b0852a00700444050050f60021302841c50605001055100402801510f406911005100078400c002e00540c1e98902d0040a00190070b0755800078004001042d014050341041c1c0c2c20002501a80980300102880d02a8913040c0e0f10f49600d44034079401444172103081c1c209401820107030402360b501c10011b8047c0602502030205e6031811908050101e449901d0f480c1034a90050144601060b0b041c4050070400c00000c9904041b5a11450105050001e2340040c84c681c4c21000000300620 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 547563264 1250 547562014 547562017
    0x20090f06210d02100c0c0b0a020f0c07080616080606030604110d0c2703030c1704091a010309020102120a2d091a0912030d05090319050331060908 64
    0x50216400f030700e41310140204070005494005c4100300200e8500c130003040c00a414081c0c02a0303c030b1440b900041c240003015940c00b00941c0300010800300d540c40f48005001c00c02c0c05001150300038100a41280c0071614012002d005424000d110340d20a020110008107503807225040011806950344f034082c1c0d240340b08444640101002c0707000200241a0404981c2c00044c8209032102c1d0708240c0e030380200c18a14555040f20096480c040440e007610103081d40303042403070610703000c2d0000d4803000001140000651907400c201d0303800f49070b00c28100360070030080e880541d0b0081034040703007981c84981c1c02d035950303035019030568007641c1c2d05140303040d00c10120400d4103100b800000301d210103101039a104054a03907141d0320303e90010305010740926070305001c001c039014030b1400e40c880350b07480e11500040d01d041181149a0600700c4004a0780d011312904006001d04ca90029551103042420060a2890850900103116903285196035610b48001805031090510448410b12250006d82c0c0080c1c00d0042d0362041c075204825 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 547564514 1250 547563264 547563283
    0xa0216090e070801092310050103030306090e1b0105090d17032e09020a030b04020a0c1103030a080c09010c0f080d0b0105030c090d0206041701060320090f0621 70
    0x1038040d0080c00f084201040c0107072000103821440300c40d01c2c2410040907944000020074a0640c40c8244c00c48000c0003846401450300841c0a600c0010b000703407030941c05600750b4503e10032030f0007182c01c0011002020025043c05622018081c41c2048e1240301030004074030f440018400c013610b14649055007844418006008500c038296408800c4451170412412070681d2240354081810911801c106001502c0c43d58040c003c040c180c1d180100300a0072610108007282d000800e148002040034940800303000d02070081c0b038004982074000b14603110305013800078146a006000a02074040c002546141c5a1007404125030990f0055040075000307829203070150345c41e442000c06450705424280020400d600403c00e0344d01c0788590324000740c9450140700400003490021081240d0010060201080c0c1c41c2a420b920510303000243c0000420342d04509080e42146443c4080b1040c8d1866480502c00d1529841c0c240c03604100d10101407416501e0b1240010000c0e20b8000c82c041042c0700c00d00c0205040ea9000130540103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 547565764 1250 547564514 547564541
    0x12101505130f0f15140a030201140306010909061e0e061e0a08060108030a0e031501030303050901140a0204050301110702220b04050c07060b1906050a0c0c0e06012607050a021609 78
    0x414102010030310001c001b140c070010b03010401440204030b1810000000303540c0300005240120940d034036541820112070351908141c0310080c111a803900d4040c040241d0380041c02440d240b0f4561890413000140624a2040c0d07000f03103034203ca408900c62078a400140a010700b2800c8159040f540c0c40d001001e41c0e0303411102e0090300081048404030001c0c10003045807010107800f40d1000301e4aa0035034509078090700d00604940c48941d0b070361351034101144280090f103000740806403026035a82d1400c0205400c1d5860b0059035503441c00200404030059036150584410044900303048550740804050310001000c1202456030814140400c11401d000c0000c020a50a4882e0a0801143e080c082c18001c0a118400c2861400041e10406001d07c0c0d004e40f0281022852601d170000000c5120741c3c42c05c85154903035102004100c0d070902403140f15a0486010081e5102132a10400b1108485a466184000c05007030b140074044c0028072007040c2d038403d10030080203004100b144040107a030344ca407d000515a9180380780 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 547567014 1250 547565764 547565789
    0x12050606090a090209180f0715020f1501050d031827020702031b15070614130f080a0e09090a0c0501050a020322030212101505130f0f15 60
    0x9000b00c4082c415010b040341c0103850400155034900340201d01411100e60b00c0407038420803c01d0549500308103c5480548400280a2241480120044d2500c0500319040f0503640040002d1304041948464060444008a485403040706050806403840300b040800d01e2481c1e0f0006070b01144038009500003070b114110040043c00c59041d030389c00401c100c6c05020710013981600701058060388a40f86900d41039402000070310906241e00c0700034a4003a99031000008640c41500c0d40c0200c3c5c074068130b1a50440d401070890007094074044055903012000038940100410010020640b542264031420034002e007040b0140580c9038504201189590720301c600700007240c04850100c0041032a5106100792000309015030002c0d82006e0481c03420081044448150200350340f0301200000169440c06a0a01401e004102416050b500c50920741c0031703031320721401080b0065164001046076884580308000c0003840700710005240400101050081c0042580030351a036410015100c089090104c030a5086420f2124080c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 547568264 1250 547567014 547567021
    0x1a0103050d03020316080603101404060f0513060218130906111812030721080c0306090406020c0705030106090e0c040e0303061c0618052518061205060609 68
    0x40b800c1c0c0c032007110090400c1c0001649951101d0260441c1500140020b0503120f080d10007956038022030b0710004036401000c2d2000c0500051103030720320440403030078103c0c00248501d00c1c0454801c98141c00c1403400400240d4002805255110950b580155143c401010042440c442490140103020101402e903035151074115a540d02c0d000c40000c0350a0080d0354111180e03980e8008081100c24600c1031803c2140e40010081c83c00080e00c40800c15640414460b100480c1d0a000d050003080036000424902e0300303800400500009555000c14240e20692001002da03580441d40d5986050865562000da0950700345035010441c0348090300080204512031044400d01e810542c20801541d52115410345150020004030b845070a2458001407060044280203c038503900765185030480710443e0483e4064000c903000d1b90100103043c0244040d612000354101d5903000640b54081c48215140b1a28440303408008203864070000d1500f0090003010b00d14410501d41c0b0003401c1903600d030382c0211601c0d4401c520300c0002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 547569514 1250 547568264 547568267
    0x6081c030f0b10120e150f09010b01020c040f0b12011b02010b0607141e0d03110307021020030a0204080d0915050313050105070905030c030c012a1a0103050d 69
    0x600d484988014031420b0441074060013a660045030306180e0b42c10a49402c2900070f40041040300c560300385203000c1051410301c0d01a550000c00703040505050042e0341044601a00c0380e900252825060307000700d40c0043c090a03240e01c284000d1804040c01604080400d840200f60901980724440c019180d90200006040c0b00b001282211001d0400c1c0350b01034018002d1b20f001c5034000007485001c2d401ca60840b5082091036040510030295128001c0040e844920003165199050150484011a8103003641c1142042d030001f80d200c44807442503045441d07840c0346070fa845104c8030344046072035000212641d03624140b8505150203035100740078200340d5114017408500b10500c03a101c02c07403c5038191582480d45010b54001202c45500107000c00006002c00c10452011407020f03c42c15000c6c3d1722136261440c0c150710384000c1c1428a02c0c100007541c0300e0380004100c180280d8112590058114200443d0a41004200950039801c2c600c40405446291403a80645009185840c014162030154088540e521f5403040c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 547570764 1250 547569514 547569521
    0x3060a170c0102061e1902090a1401030b0406050d17040b120402030717070611100c05030405060604020c03070f0602070b0906010e01080a080a050c0c03190b011706010b030a06081c030f 81
    0x161100c0c5c0c036160f140091034030720300b5400c00b001c41009002d0143c80c240d01007001410312034040d00031135848168003803008003a60b094071074403c0c0c00c94140c6041c0700c42483e04001134140a407807100600720040080d404001700c004402102c0140440e40f03001c079100c050f825108a250740c0704940480c080c0c0b0035480081000d031b03411401c007000302441c100101819414104110b40c1d094143c002440548200d071800f0000c8040350058007110007151341c0f21501c9250034189a803a248007d00000d00480c4100244407080303201004980669802c40c2c40a086001c180c40c0c03410081c031a066010708100075840610650b6000451580c1c121452840200c1403a600d4000441e00c90301050401400c0040030005880618056800f5020f100c00c1c15055030040c000c620080f0307040c46990911101c0036113032002001e040202c156511400b500702c200710094500b00003003201e691480180507485003400040b00160b5201602e80015000d84070b100c003a2800d10681c0b42c043d003400481031801001081c01c101805030540307407620 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 547572014 1250 547570764 547570801
    0xe01052e030f0501091107030f11060a09050c091b0f040302041814030c1504020f0d03030c111911150a020c01260705090d0501021b240c03060a170c010206 68
    0x42c2c0c51442c00d000381d6415981c0c03e2714181e5000a102c0c40710300c08083d0000500c00c052140840800200300c0300c2072407400f0750400c0c05040c8002c4c86130000c03406000240d18001c20112150081e001599950f40c90801c10159600840e80003d5001e410282201c2c07401d40e4070300d5500e0364107226142c00e0000d0a0132950304d07a101c0c001c01040c0383c1c043e4402c0207484150040040126040b40c005882a10010100350114020703400c8898150b0209444903801081242c0c0901c6500b401d2620300b000d4007142c0d0804c50000203035545184c0c0600001e4a4a20f141c000c2d070f441501c4008103e02850590360b59100301ea078082c3d01c0b0401c41c190280402c02c50300c11b00b01e0381f041500920b080784820400c141c10560ba003050960341a00038842c529088000403800c900044e0702480100f60105001c00990307040545400020700d0304444400030410040250200d985d40b1b41403402c03081d04030b14000000e5480b5540d6501003a810016a0f01040b400400404801382652010407002c0b0301c40707400e83c20750f2081d41d2449044c00b0000001c2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 547573264 1250 547572014 547572041
    0x40308030a0f020705030c010b0a0f05130e0327090705041203140c070f030b010501020307050601180b1005070c1710050a0204031a090708070e01052e030f050109 71
    0x20000a014840700d940941207072491160010f003810415104c56141d9040080503143d40c0e952004030740c286180483c01b500080901c001c240c129541480042180002c0b0f1050120781281c40d00610307010f0800610658030000100c0549a9040c0080021101440540031290340610314079004124402c0c401d80480f800d584c2254820402e0003c00d40c0d0444a102c110700080035001007d20502c0c400e458103222a00043c4a02d4078800038803821401c05000e00181a03005a040d50f0003080400300203000420160304403100e0020076405150442001c00c040d00c1c446c3c00c1c007940300704030072968001190080098554213010310345201c00191106048424200042e921481684c000d80482400200fa9004554016003003440507003003581c0c0355507041d000406a2045040d4041c004100a88031804100c007800804051780100100c03481e04600d590f0540c010300545001e271b011520456504010300c0c50444000342020041d00341242640310003401098041e0190100c18141800040c04030428010b01450b5201c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 547574514 1250 547573264 547573267
    0xa0e0105100b0901022e0e0a0c17070911120a1416090f24020a1a06060c150a0b06071109060d0b0109150e070905010f030b040207080c0d0203040308 65
    0x2d009058515400450496046104124030022001003541200c000601000c50715520048014051000c4d0f800c4408269590390000e1450710200c0e5130202600d007100d111480b403001d4480c40c4071502d0f05081898011301d07a0306003400c0c01203490b004510000c182ca51021000307020313a40c80d400103200c00e880440d11040503201c00d80020600d00554500302c041e116003a410700705001ca55070301081c034600192364007061503503480c100e640304116218554031400d40311900c00740005c1c0101e40e031050304a50315405076076207080c008000140161220360481da0030440d50021507040e241d8805c10400c0c0d0304411151100aa4281110003c0a041c4042070302c140135400f54440b8244a441c6051080005004050580c8003d80b004880c0c046231905019a018155003900401c1425241301c03c0300a808050f030104188942c10010002010303849250302c004d07500d09181c90b8440001000b800c5010348080443c0365407040c4000340304410801441b005051060010064490080310054142c4c1c13240035521014202810 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 547575764 1250 547574514 547574519
    0x21023220602030c04081002070c05150a031805060f092e09061b08100f0b090d03110f030d06080327030a06060303050d060e0613022d030a0e010510 65
    0x15000f555016036240313030030f50810780d4403c0514030b0a88210101e0f2009a400900758043c8880a48018040c200981d07a0681201950b010325010b840384880403001c05989003618901488854a0600c0132900a4221040ca0615120064030404280c9803900e4034484d44198034402c664012840c0c0d0081a00826a420b01180c1000480540005442111103607500c000743c081d9048031074010903440c212942c403151a403800c0030f01c01100482c10707041020300951899003081145110003c40e5140c800a640c4c21501e445140f07001d960803920200c0440322401040e4900140c107800102800030782082103402e01c030316035030b0b61202c1d91a84541c1c9811481d00840415203145120400c0c000803003e840902200d2100940e520b40d5000c50350700790001c6002890000e10030026164600a0030090070541030210500c1c02c0550000e288144c040c1100500140c021542c5101000c0b1b0030011108401c00500c400a444400e217809045580122850580b0618015440d04210014810203114103d110b003036000060 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 547577014 1250 547575764 547575773
    0x1106060d110f04240501021b13060b030a020703120e060112080f0a0807021b01020606010c11041103180f0c01050d0b0312040f060503150f0102102322 66
    0xa01103015650015000d103503660301603c40d40f10750954880302c504141604403070328040b00d09020095100e0f504643c13012054aa40d03c4406a501c100240c04451a00343c0010b11018540030740115880805021000b00c104110381c002c1d41c0041124501c2556125500210b00d04001c084a0710001032660350b07408100141b140c0c11918000d8207186000304880307401d00f21011001d04450b4012595034001400d08414404515010014804e00c040c58455032000210304000003565110010491410040e8155440e400c2c07207008020116148005030040c000022810011401c0740d0003541d041601c0d0a103c42a10102240800c480075038103010f201514500030007030011500c80e0031013101406a00d070350b070790320055980c0c042182108800300070140071384503403404c0c00d0320a00140e142d1110080c80700410400c5290407002ca0040d90f1a5401c44800c8440030717420004038544041c103107500050510300041c411032034261070b100030f51044403603520040a665801c15800c10006e030303003400b80c401e400f085080340000303 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 547578264 1250 547577014 547577033
    0xc03030507021504090c120e0d030209010c050f03040e2404090218040c06080702070f0510050c1504021e100f0201110714120405151e0705010c1106060d 67
    0x354002401c01030b05036601003011030103901903031011400c1c607500c80c6d241542c07540040a11401d000650340c10000080c02c4403007151110302c054103079400c242e0700241c2424580c0c000d4940301c132216007260072154885e5403c8841a9039034890f00405c2c00b03000901000a0541122113510414030b1301e0340101c07900101141082c44054001d0381000c9a1002c240080202d40c2c845102c515407089014a01c481004c03890b0100141c1400380280804045400c640720500031040d90306503c0049680c2a81ca1b298840b12801040b90079010f0810240e0080c004e1180d2600310f101e683d41c00794003e500031101c0c46070b1200c11503a59103010704004036582c0c0219011402e10803041c00303a140c181401102e40008103403580a880d16200700e5214613022503840e241316035156101401000440480b00050207464582420800000d0074000100f2807075040200014880811700c09142d0381a111070328010707295440e40c10a103460f501800e080546100020f444024201d124040021001c0c01124042c10101001c111030301c40d010710707 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 547579514 1250 547578264 547578277
    0x30509010b0607032c10080417090d0305090d0605160201140613020318190c0503060c0702061309090309080c1e040902030f060a09020307080a150513050106080606030114040c030305 80
    0x991100c0d02180060741c46034100c8040281060352011f61914140ca03101890119480745008801c070148465203040c0c0b600417100030000d0705030412a803142c14800001c0c2c0403020800b402003200d81001c1c103020020784914100c1c10700500305d800900410b02002c0c1907260012089400d80d50200c091000c0703031045800b0340e00a5422200c0300030303032281c078030300b0060820700d84600c50804040403030391000c0810030301038a44010000b604040b00130b4030082c00e10602400e00703400b07900000380c4501c80004000c607100411500501c0106841c800512031103502e428082c0c5842c0b01c61040d0891400340e00002078140c42e115444140070341c01c61314849200588001400003c100f07120007203801d03208000113000c10003400c0114610502d80000041131700c803000e1052609010301548001c03074a82c80b8501c0b0a002820030500c0c2141990300030350020309984c480c04030326090854030602800d154641500030404841c045442c0d07205000c00e900034031005040100c41115203000b1074018003e011050404c0c0002071040004201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 547580764 1250 547579514 547579577
    0x40c120602121005010314040b04080c100c0804140105060102100b1302070b060301150e220807030206150a060507060507020304030b090a030f1704030f1806030509010b060703 77
    0x61924907802005145003c1d00c03c0002e002160700308100669060081c0a04600024401c000c6401c1a41c1d612100c2000504010094407002c42c005d800300804001240d200000c012052002d0035444002400f001c200341da05030717005406205000d00c038034014003030980a2007040c2c1c01401241d0180d280c80000b08079144806900034030703070500014a500d42e030001e000e54600a036403d00c7c0c9428440c01b010b00310740590980d58070003c1841420003258000c0240b07683e0104002e81c1205080e8103808124150038103400004100700e4000c00d807201417507400a0341e10b100d030940158070100010b20004000049429105420000303038208150f000180280e00a603800540d9030040383e060036180d03502e0030071098040351100071070b501c10700300d460038554031041c0c030300b03680d085424512f000c003400c1d055401c50040010000350900c00e8102c60300b1200d511904968212410421000002544805006001d04002e80702c0051560801d84840c1c030a1414608542485505031201f420144104204a800c0ca440541d00304 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 547582014 1250 547580764 547580767
    0x10e0919060b130f030206180d0c09050a1d101505030118120503040809090402031005100f14210a120302070b0703110417010b0a03030c0b0708040c120602 68
    0x1203416460007980d0140c0303040e042080c0c640c0c0c410340d01e4410488507940030384ca40180641e010400350f1500f0007229034816410840103894804440820303c0301c88a84401410312070000303070000300e0b038100d0303888a800755020120034002c0f8403510044654600e0029500382c0396400202d405901001c00360b11154010f0040d00300540c200d03076104002401c450a040d0014100c1c84144031140401200c450020001c0350a030130070b9400d6050a0b210300046c1d000c0d4600c0f1a010362100c0010609564007003011164a03c0d0390503091150b45001c0a00e144402c0e00c43c800c2400707880d5181e070080b9900300740d100686004c00020305005084c1d2100000c03a06200500b0800040500034804180042560b85400c201030148076200543c1e50b103e90b10305184c100c10020f2412040518080408440200520032a41205d090001040e039408001d24210300401008003c150700070722002c4000105600083d100804a00620b0508602d035038010064032005011100105400c15903101840320902c8046010000d03401050b005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 547583264 1250 547582014 547582051
    0x403023c060a030b0d050d0804260418020d090c05041103221704030303060e090316060e03091914010804050a230607030b040f020c030702060a0e0a0306090203011802010e09 76
    0x24200703c0e5605001f4001004c8004001c00c2c0080d01c0928131185680140d810003060f2048080106401180158802c2543d0218515044002c50301030b10403258503000100050701280c540750307402880c60321885004e41d040404030003510b0740c00026a0f110f00c03801c000300340c000052207110301c800902c240d204a0f96003940f12252034903500203d02501c069440780d100003e18a05103100414110001050001d960b0310400c89207400c42c200015000549030701003008181054440c60440c21070040070082600060702010448000c003140302280103d030165015201c1d425020401103414601c1110046d00c035522424200c030000349068014400c00150483c640fa0243c82c040c0c40314180042559004002a165418501145010b105003070542e180c0c81c00841c40c0c040008640ea40740c0c010414040d2040002040784030032a4000e0451007554900101400c549580700c1c549032004007002107091703001e580303041181b00220341110500c0b070805405840b00500d42003401c08004041500800b11000841c4201c4003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 547584514 1250 547583264 547583273
    0x30604060906060f0e04110904030c0204150b180a0e01060903080702041803020f010608060108210702101d01090b0910031104120506060303070305031305030403023c060a030b0d 78
    0x307074054a0302d17140c0600941002c0c1801c040020300c00c0c590512401c6444180400250001d00e04041e003541910301141d0100c5100401400101035071003005d0b00c240000d405204030720710207290040000126188440340343c441c22000c1e01d5400901600011445904d0f00b400800d010101624046100410101e0203103403181c9030301c9100765403140c11000f580c0043e4845d4032552081c05140c000d400c194004204540c9041400750380d4410203603150022a0804140c8801c0300d032148110f07030401d9005400201e00c514600c000408444207210303120040030500d0459601d0398400d12003030044410540b10541003418083c2000142c00160900ca020706070388218020804420703038060b200030881040d01820440d40750a1007070514100400d541c1c400c0d04104403c0340003c0e001001e0385d400c9413907103848100d4441145440352640c4a103420281d817041d010400f0964915028008035002d44083c41010143c54001d403524242c0b000070140c040d8000014402000c00300e110b58481c6000c2c117030007407000c00d8035074580e200c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 547585764 1250 547584514 547584539
    0x31110150302040515100e0301181a0c04120303050601050702041103071b0c0905061908210c0c09060d020604080d030b01110c240315010905010c0203060406090606 72
    0x60300140d410541a0400075403074140300d0194422810305021540c40c210b03000154204070155003d505001d250880d500742038030700358810700c22011548802c056160903810402000840d420400080c0c00e90240012220700d4142c060740d04490004010880c07402660354181c0c0035010091216040080603c400e0000d6a51030040700d040c5120007110310f540b401d04034030042548410030441000c00341c0820305071000034240700d0705000302e89018100241076124034002800c0080201008414068560404198440302080305d032481034200d203110400c2031000ec0e00009a0245548480c0940c101c07071100c07502d50900451241d0700810003026000d0740110740d4001501900a13030801102030340300b002034511082d010310507800040300900300716030b41007020404940d5400754034041900498413020f5425a10320328120b075000c80b080c440c60160700c900e08041500c08e0120b401c500d450004080310000034943d40154685408160054064000b541e80d5032103847c0903101ca028100d486560b00c54000030624020780 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 547587014 1250 547585764 547585781
    0x41b0e090a180f1104020909010506070309080f1513051b0102030903010207060608120c0706030915061d0604020a051e0f0705060109060b12071d0307060f090902090d031110 76
    0x1404982400b4440c14041203e03040d1602a41c040d510400090001d2342e070b1a0301090460b131049030440d079144a103283c115030700440c41d070100c1c12500c10901c020f9207204010034018500c50100030010215946d0321100ca030010203c60b000b51141c0c00116009001c1403820802e0715074140113004803032918403000301190880c1d01220701a501c1f00d41d561014030400c0030502950074040d01c44604182401e0580321100e0312800e4522a000174180e40d0354507901004007840281580c035860381410051a0350b0761144402e02c5000491281c0303132494100c001007a5103402e1080d6002503000e55105401c0a0042c02801084540040f488140c2281404900c046284c0705000b007103220320420181206503d801070340d0054645076004000c01403020711154980f80d000c0f403800c070740c4800107107444415214100141030441d0001003941c0d400d4081c101011a0607030b044003520b46404580e41c0e4039007405a80d005500100d0240c044481d0b4013508000092010a12400040c0c1302d07100311005aa40e81d044400d424401c071164074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 547588264 1250 547587014 547587023
    0x60c02040c180f14030714060703090905010b0306040b010f020c040b0607050607090e0907080a0b06010c171e04031110050c01050f0105040606030c02060a180f0b0402041b0e090a18 79
    0x10014084a0b00c40710358040000402c1c0d00501b241070414403291b00c1c0840e4602a07a000d1440401e40340d042c184117001240041c5880001005596110b0b4000d44950340300b140c0c1c85004508001c0d82c0101544191180100b501c402e82c003901c0c03400d461204000203000c450001c254400424041280494014000240a24020740702c0d40b20300d0386000f02c0d2035040e140013840c600c896003200c082003050302004284010403a5004100039419a10b810040c1c6d0000a20400906076003011643c44004032851402000d10342403924403000343e00c0309c604002115100c2d5010051030103000404081041c00d1203042e403120b07032000c0c0c18840e00304212140142c1c211403003200d43c01c01c594401070041145081c10300c070f04c90207082c0b1481e05002d01060140c0c0656240c1020300b030035040c00d03910404510291881c0d0358035009540c0c01002c0380345441540c108034440882c00c0c0c400341d220710325201d11114410382c41c0d40c0f07070019401107403102c2500b030f00181c1c20040e480c9002421000000d80f03603449000600c203181480080715204 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 547589514 1250 547588264 547588289
    0xb190902130c02070812191b030f021216110301021603030c091208180f06040801140907180908070210110d1103160609060c050c010c09060c02040c18 66
    0xb040402450300c0c3e826802500b040d04880065800300c800e03a4216258600e031105641040c001450007124011008020008006858031100c020503030702281e070940c01c006030343c01c881060307081100c0c900c45442402e41170f040706c0481e11040800130f4503641328071210701e900400050420082c1000e182030039601c01c6c1c048000a544030250207a045d0400300c4140645001180144410002d03541c02c0d240b0311568442e01180b1040300f0301e8103c03a56034082d42c000040c3d03001d08040c0d112036031403c11034041c104800040c4485844400041e243c0000090790038100c0d80306500103c1c40601ca604141c008081d1301e04245c1c0d400c6410400302c00561691031a03c01c039608180d0300e01840f00c000b00705072410712071800044410813088030b9406820800001c140c91007040180c015644909203480c0030700081c102904001d0060317003444000b0407010782010240a00c0b400070002402040c00340c00080f1980386d0240038a40225000f1404000542800d0380700080e4446035080c500c00e052162030210728141c400f9030201d007900c80c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 547590764 1250 547589514 547589531
    0x1c081c050f0708060108090c1504051302070519080c0d09030b0901060602061b0c160305240406050618010305010e070f0e0a090c170c0a080a0b19090213 67
    0x28103200d66980800d03030000020150a01c0c2d1401025140301030319441c10020211b011582422003031011701045000184800c8940d24070704c4190501c1d4000380719203486100650669800c40540780200c03242c20f03501c00b02030840030f41d00c18002d01640244079000c1d00c0703c050034410406400030422005840d000280c8402d810300d4918500701c91040e000416003140342c0d040034000c005d5a85c000071070980100e6540d08000c04040710000c01441c5010f110070345455441500c0c2c40505052100011005590084054070310104002c03415100d034005028040340b45c51582c60000300401d0003944241d800540040001c1c3e256800c810315000360000a81050310399942d250041e40109030104107540041106081c400141494800080c8040200905004141d074441000500700703c11300c04264040d0012a018a451004414050350396003071240c140c5016000084002c102d91a0024802002c6540040711014982e24a40041103001da6503050b60b540c1303070300d45d0300200060f5260145d41d06640c0301c2c228006003c1c1c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 547592014 1250 547590764 547590817
    0x13031e060c0e030c040e011e06150801060503060103050705040302030105091612020a033509043c0608030d0f050604050105060d0b0d0c06050309070609050f1c08 71
    0x10109010722051020380348141105840101d0342d088101d00481e4002007417041c0300c10701e50241c181040700c0940c405490098000038030150303102d201034603828054008019429203080d0741110081c054200464414000699250b00c280c00403940024146040c508081e92a07010030709440c000e940214690700801059900c039030b0320301703c840e00808801003280c5115038203401040c0c1607940b034000a0285500c65441c0e1a60720111281090450304000c69404094042c40390b00c03003140c0004411602c140d0500310441442c03951102d8003442490003d1040300e049040d40030440250f06102c2d0215007003034680c0700000f01c82900341701408142c2a03440000c98010b2042c202c26003290b0004004500c22403800c401401a520781506542084484040001d50041404001000720600070001480e19000c03003404a140b07540078020b94003643d0200c08860840c0e8680c041070390f2003942400345603007140f0480c0e0703440369601d440244070855a1040d02000c0001090340c407246c0c81c0d64840b0100c1c2c290004640c1c108039049 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 547593264 1250 547592014 547592021
    0xa0c06031406011803020108040c080a08120c03100e0703200904180309060c06140c0a03050a050f130c08011107030206161d031005180c010206010e0c13031e06 70
    0x500918011a0303000e50340076030815040c44c2d40806810080900005030400c00780540b004094005001102c005132103929005400c2d0b40452003c0c01844034500110702c10340b0284043c1c0b0302031a10141130550039414034104c00c080b04002030981c4101615203901c0401c0c0c0d441185251f0050b4160000319070344100003001e01c0300362012082c0b06c480070001001c049000c20303880502502070b68035a2600c00c15039910b50801e9400f4200401c000c0c3d42d1f480c2000188498604a80000c00308400251010f2107645d81d00b260002c220f80003200e88079140b031140030000d5841178200c0781c2da062843c8226180082c5035212680c0d182101c076410510710101c0700004080c0d081c90340422049610031a00103000a20580d1a00300502031900282d40d20300104117000c000b01c8507603003800846208900424100002c1c50318441403d001030042c400d0201c1d41c083e22060f40307180d51002c140141030394a081080f180702d480d200d10b010400d40c8980c0c800c8101e070a00700c602000146035069a201c00c0c0d5400d84403961181d07603504090046 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 547594514 1250 547593264 547593271
    0x609041a030f0a152a02060a1103252c090c0307050409020906040312091a090108040b07030b030a2f03150702030d1811040b0618030a0c060314 63
    0x556010201010009161219540000f0885000885c03405841840c0d807515130241d4951211102c03043c0c62041c4080d500080b0144510901c039418004c650007a0010070b25440103455114a031a207612405034503812080c81602000c41c180380482101d090210f26410403004000d90300d1040101e44180300051411600e210307000f41150302c209185003000c500c0076001b481240f1507203881a13004550500d03c0e0343c0e854151001103030090702e070202100e0311400007012003000b8069403400351050b5486210604510083d610184e0040c3c481840e1615513868040031840010140c1c0b08058490040c0301c0c1c5500c06002a20f104d40c403c000700d80300758884541c14610282030102c0c000d0304016440006c4215030340041c5154424581402030425501d654001300e08600c41c1e1010040700707509100c07000da440f5030016030383c0200300c3c043c00108400b05480f6003004255440310800301c6c4d020f5024420034a0030a1101c1100d0090b01000f02180c00c07001c203070782c0d450f582521240e0050000c80da4644507020044011070b10b00d5031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 547595764 1250 547594514 547594543
    0xb040203010506030601080d08041505191a01021e190f050d080606090d031e020c090f04030806190905041a07020601030c1701060308040b0316050304050703020f0609041a03 76
    0x4541c104900c2503a6400d44404a40400c8071389e00205050101c00c200c0e454007251094400e210615007000d0a1941500c4000c00c0071000b46814a118007545c2e01d0303001804404030580c0a040b01200b801380c0315001d8001910307544440d00413a5900134849100c1c108458070203101344660003081e01c503401d1040c100b00d0520101410b00129038104401035441000300d0f8905101100e85450004a5042c2118034140b200b403281c107415072070407407030b040740b500041c0e00114844100c42d1011340359a0341181d070300900c4c8240e4004001c1000170010519500c1d03c0c828180c2c03001800c14580d201c581c1e4071010002520409d5034240e40200c08422100525200c1414140d4402528001443d055155594100111a40e84a20724070040700a58030741e0030303c0c02074010000454006140c140c0741e549505920310254000d980c0d00c2403070312980590010440c05041604e00c50b68208c8042d00c00b080c55034003400070b4841c0b213100143d441442009840c40640d03d5101f8000f5041750810741c20f01105c0454280351034801840144131 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 547597014 1250 547595764 547595773
    0x306150e01180f0b1915021b010f1106040b040c0801020313030f03060b0c0102040609080a050a02040f0b04020c0106051201110304230d08060405010902040602210c01090b04020301050603 82
    0x24040c1424060b2003040203201000981d082041c49480c000c1c5803d0810f158080103166654000741040d40304601030b22880380d0241c42a030b21050040c0c1c2e0301c424a03c5040a100406031036819150b00400004210a08908008220140e04600a42054002c07034080303031003480110601042c0407200c52080042c0003480d00031855801c10b031308041218002a54018100142854807064a81c840d4018800030440b104056840f0510043c60fa40030b03401500601c40090010b07100099001800103980340d031039130041c1c05403581031415000e02029001029075100e007182c40d482403000319107591008000b151a81000090400c0c100380400264074075903a403440d01603041401c3d14284824a400300c130b8100e41c0c000c846444c2d50a1030244c01c03101c40351040ca0040e8034001c4200503c00560010b12442c49103008841c01c00280c0c0e00c0310300450482c040c1e4010705006034002c441e020340c4050340310504128800300c06d07060703810300c0e9580400e1802d5540d160402c48950746448113020443c00c0900425801c80021400350 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 547598264 1250 547597014 547597019
    0x9181e0708070e1021020d1a0f0306220318120c06020c011d13111308030415051c0e0a0605010f140915060a0e01081b041e050a0306150e01 61
    0x40808283c045e0202103240f030041c0c3d92074840404d504070341d18248a00c0b400c0c01a400304800700340890741c420603201d00400c1c600c0d580c06460315010400510071111003640d041d0380355010301c1a010349899440b040b402e10241c40e60046c054240802640020078000c1c105c2441c014044c03804200c2402c0c142c0c016020766012081030051a0f03085000c80d000c2500c00380c1004600303040318000941078040f20503040030692500c0050601c01c1d0a0200600d558440036280e000f00d250b0ba110304c0d9a0302e120303d114544281201e81c90216400d40309100421416203071303100260346041d000c4c141d1300803110021070072400c0340d0107444000c00b00007030340c0a42401001303003069166009240c500c0c0080040b11262129120b00c4e220700c00240e03c402c0300020042c405001400140d2200102003000d000048a0004207000c204064006528402400f0f00c40310400c540c1e144090170710b4a411442d04e20280b10111440400403a03000200c0c603500ca03900d500b8001c50182c1c402140c82540c1003400c650b000c815030064903140b102034006 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 547599514 1250 547598264 547598267
    0x40e0406091a0a1b02120c16121403040b03040f05011d030a0e12100209060d061203080108010902030c1c1502030609070915080601030902040203100e0c09181e0708070e10 75
    0x750710100807003403802c564403110607440506120700039224284564107071801042c5d01e0b00076270101440b1031044180b00300e0040034402c00317582d0b40154070480061240400c0050b001450030449090403502c10800483d0064030250b0016404501c01c80000c410351010401005d800d6024094003e0710700c0a86440a01c0000004030540b56001001d803a03065640024605038a41c80c0d000407101401984a400c0011f180c0794001d00d8403200090038146c000070b0342400041160a010b10680051950040040c8078111581c01480300701002c0c2e1010100805040003c0070204269800c0020691910840180d403880c0c650308000c40703e007010f000342041002d018000e0000300d41e403024692702b000b4941007542103580d4081c0120040e00011034000c2d00107001005009010504000d01130079030744807019030000e030b944400c02d00465024050300194440b40030318841201c800344400365500030100320f2001c6184a01d50315180107540013a01d14000003070f001401c01c28980d030311402d5050161001c03645c1e00d60301c000b0400c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 547600764 1250 547599514 547599523
    0x3070306021e030406091101050405130b040b0319060509060910020c0c060f0a17090703022404080609061f061d041a1305010605040e0406091a0a1b02 66
    0x106401d50001c1c80703415021440e00c00c0b4603480d200c0b0342032994920b0189400c40180c9000c0d081241c800950017801c1c400f0358000d2080d030341900c601401d100340408410308084044c2c1250701020390801d640305912115510140424190403000708200d00121070246000700c21241b0003020b08540d41c001d00144100482c2c0802c103071242c2c0c4499880581c43d00351503616641064411000103a2155001404541d80301c0084003801807a0740c9a10b804003440f205d02501600f42c08100c2d0310350225002000c01b4001850f1001310301d041060780601324600b00c840d244100410394040d81050220f41d12900030480f10322404c1008507804200c2e00ba142c40505911004260a2909805114148101d1903000e0401c2905080c03129080880200103021000302d1b251030180d0002c01c6e85c0054000d802200b09214010054003425040780da850ba03500345028030b40f409002c0c5c1803034094400c880080e1100400310201703004001c0913110001c403414130000e078280444120f044541030000c1003492210000410a4a5000f08 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 547602014 1250 547600764 547600769
    0x20d0201050307260702011505061611090430090e0411040c1d0409110d08040f03050105060f18070e0d0c08030a021e0a02011b080c0604030f0e0307 65
    0x200262a51140003040e40d03407010f8a001d51300e50a0b02c0c6004216404512505a4010080d40e00204410112909101701d200103038050260401c078204400404803941405600c2d020340181c81c02c2e24100c0034040000d05004080c3c40c02d84440898100c1c19101403071a42200240540c6095500a18200120080c08403607051059a1071a454000000c003441615224402d03800d00040081080181c036140140070423040000500b8040960070351640141014440e82c13901070b802140081d5010f5000e001c0000f1403140c24801c440945091000151142031184914040d40c41780001286500d402c00600c03c181c0d0141c801c1703c3c810000f40044105103500002c085030050150310b0720b0046a9042d0010420076040101d00404410010600040c0502c1c044003038004858181c0c240c800c07456902160060601392030151410681160710703590015809a280d007050608440e10091070843e2944888446030400c1c8150650358101c102000100346e1b0010009a58a125040410a540711100480d60b40c1340c0c5070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 547603264 1250 547602014 547602017
    0x705070503120a0e04022506150b0708030103062a020d081506180411040f050a080d08070509010201060911091f0909110c01110c061e06041a270109020304020d0201 72
    0x301d1106290f9103488000b810400d0000348587c400d26850f010b0003d2100300e40001c0308280d003050128035854a11f0882d68100e412040d031a05503429504c4205c000c00c00c510440300001159109095040840101111200700503005010441c00c074000c0544920002401c1d06103920ba0002054829500c800a9490040c041c035140c4096040c1ca40c0850010403900d454140c0c010808200010088004042c00d416541c0c181c490400d0310b039403405280d6a411081c100e080204152a0005180c180f00d40041c2503c1801480080340751551343c00c0c0c01d07088540b40c1507400006000007418131002d06040c900c56440c082c141c499110020328800c03004201c01e4450054200b0340e07496103d50800e550b500300a0307035841e41c540d000030400c5100c1c3d104080d13060b0380983d10303951a60145000184040c4d0b144582e88840d4a8101c625403025500d502c104002801c043d01e044030718000d40315110310c05884020880c0030700c981248a115840d50040310400c2103c41c1644451a6607004108000050f244ca180c034420041d420f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 547604514 1250 547603264 547603267
    0x8070b040c0306051305071421030f0307050d0b10020d12060503060106020c09090a1a0c4f050402030c0c06040b04030906080402090c0a140705070503120a0e0402 71
    0xa034506000203564680c07019080b03a040c4405d1001480812100180251281003160181d42e0b84100040000c44240c0b8003d500401d061080754000c00d0084004207240880b1068a20381a00182580341c81e4000395102030001c1c4002c83c1c08603480c501c0e032107a82d0090314111001c0681c5045604005d58034643c0103c1081000b0803a441002e65000e55003014000d40390080c10780e2120f607102c44000303540c4c04c0c084400300e00c5101907402080c2c0c2110301080301c480c02c07500884014983c10113141003d110365000381810a0520302003280b040d00c182d02a00c081203840603504480b00000701030280f06036032129001409181030380340054401100da03200400d0100d400640d400361b00c0b0382d546007414038103000b0b98102281c0c0307000c0c45081108108900040a109070b11a07203460312200d8450070100c48481088800079000401440814031108414014112095852601c8407107010300503034548040e0020351085900d82e1200c20180028a414030070150b121042c0450700d03081803c851001000c42c0c82014005014660 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 547605764 1250 547604514 547604521
    0x215090301230601031503111c0b04030e010f090e1b1606090c1512110c070308041d0603030706090203030d020301140f0907121802150c1908070b 64
    0x5003900001e0b421128491074561000401c2d840011420007111600c0c0040d103800c3c045120180d00904031402c5c0c0c0d410412004c000c002050620201070345c0300c00d180500450b0011060009281d14142c5441030b80b10760354840644040c1e1001401000001c0c4804c020712460041c1480310310040585960300c1420b1018024100741e403c00d0310784092141c550442d0b1800f480210003c1480940e41201041500c112035030070485031b40d11000340c0d0b458050701d80c00001490583c010302d41d180194000500c4159030103070951070070034030206107071070306205030b01c1100c04d00c0b004201000f030724103d140718241900c00c002d0441c440e0701d0240c0003c2d481c0d100d143d00007800070750780d03082407000c0d0b46080090f1604201c01c0d51003159a941c540104004a10210608a206068210701c1d908203050200e45180902c0b03080c0c079041482c01400034408040c203500e103c0304040074146510400981d864030b1621807c1e403044241e0b699684400120f950501c040c5200300c0d0040d0700f031809400d000030050000c440171103400c01100680c42c2c8 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 547607014 1250 547605764 547605769
    0xe15150d022808030c060a02160b06130f240e01030201080c040305011503020f0a03021302070512040e040201120e1c021603110a08010b0607080714030c0a0b07050304021509 76
    0x12032080034000d45071804100815003860004c020290701c0301e210200d65141c0d40384200b503001d9100d1112610100700e082c9401200207540301c03c0ea039800841c0103100c2c181c4100c240d007aa0b82100d0307048251550707940d10744407002c06000032400c50418404411030100c0c44a4101051194402d0301071000904102d2407400150040048030107440c09164000300030701c071740c000a1180000e09070b0b07035010030f070b225510703840340d101d03c41c80c01c0181b000c03c4a5001e0004966030000028141c0203411000741a41d00d4000c00481c6c00c07a6515401c000e0018000f001440d40765420701d40001050314411010001a6515001e244810b0070000a51800c98840200404e804490208401c0341012208041840c0000300d17000c3c04000c00680000280c4070802c1a10395092050f51207000d5400d83d4212440140c001c0000c020031400309101030010000e1038064a480454110b5020b8801d02c1e60f440788021224a13003007854182c00704071400c0da00380c2e000015454901c0c103604103a00001c50801c00850511050380c030000d4007884a8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 547608264 1250 547607014 547607059
    0x140306100512100e061801050112241403030301030c142815020102120c0703035610020705061201090605010201020307140304150e15150d02 62
    0x55000c805040e4500f404402140503542d1801081d090100f46000a903050419001618401d00d031900007240036407900d0010360b00f0300d00072850780011a48900f00030102c0940b14207000c14842004100c103205924002e0510710403820840c1d040d21942040004001043e00d51748041d0980c2c0c0245001e84c541c4c0c1c48500020b207210220b600e100b441d868500154085d229828240c103084524a1014440148285000320b0807403095100107503444c21801c004c0b03240021a04090540e00e031203801c0025140c0e5120000c00c1706a000800b00a0002080c0b48601e44040002c200b2140b290410100b1707444010280020115120400c901540c0501000c2c0811408640b081081030007c29028050580d2040c01c6009140020800d01032072109a0034400009855481442140d00c00c00040c0d4849070000c14038100b0300b10642c009802910905003502125115003403500c00c00d8a0340c080e00e03004003282c2c0420a81445030310001841c2c40d12604503079840c184140c88002cac035003204030740c100c0b1940340c40d800c15054010350 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 547609514 1250 547608264 547608277
    0x5090a0c05030123040501080c090c090d080d090c080d1407020a0302120a120c030e0d020303073e0f04050c040521160501021216030e01020c1905040c1403061005 71
    0x10501b8800002644130000c5030451603544103641d01011982c942d01015020b00c1143d1442e41c0201d200072520000c145001c01819101803503d4011503030805070b465540e2044210b41056103079400c40709070551541c0d00082c500a0607c0d4100c1c44a0501e619600018000786040c880031340110b10290400c09031180501c07000354015032007400d80031511075800000301800191041240030480000c1140c00038985a8900c4001c41c2d40100190700d4039005075201045040c031100080110a040c85407480c009414400703088000c1c03103001c5808005400e600400c907000107880400c602880c0340009100c5103010001c01c44065402c240c88046000080b5070761010001c2078804003103034500650102c41c0088051100e0f400803204264200d81400b8038500c51040148600226513120f800500f04800020b40100401e00c031051050054405441d0303524041001e406200304581400154400148540e01d05440b94410a030102d02e025501d070b41c0000a0040760344005000c052140340c40380109001107202e003046440 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 547610764 1250 547609514 547609519
    0xd090609090c02030c0f071d0907060f230d050c1201060f090807090e060105031912111c020f010209030a1b030f0b040b0a02090609040507121505090a0c05030123 71
    0x1246c004080c000c41e29885a40194161070601030005080ca02c0c030b80382182c2c060001c075009003910601e0a1015205025070007206001c0c0010800c01c2c540303481e2004000482c10307000003445039458034602812002c4540c0105a105261030602881d20350722209070f1010b054982d2400c01401032000b81d601500d00754440d50011115108241000c1103141144d00210194070000007110402c1c6d0300e900c101074654403940d0b10f00d40f1252440d061040402c40044c40118101002c0c01c0400504039121060b030b08241d4200000e0320b00390010b1b40b000882607410811940700584050003181031001010002e40ca035000060050048981d800b03011000880c0c0e14030050045904c1050060046180d14040c40250022141a900c0d140110f0018102003e1070088508081c801040c0c6460030001108000003007101a000d00d08210342c00051099001a070f2250304075400400310000f90341f80c50070381001b4114000500502c01242030602410003650010182d03030646030580c3c424441c5040b8034260450207500c080341c0f1030303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 547612014 1250 547610764 547610773
    0xd1107170c100201020a020a06200307020a11030105010b04090504050708030307170c070804030b040f0602160c0b0a0203030c1813050a05060114090409140d110d090609090c02030c 79
    0x4000400001e8003445800c058842d005124280c810a07800c0f40251a00007015800510900300000c89581c869134090000d0b10341c016100e20900100206600112000d102580c4a90075417010b0191100f41142c2030303582100240101e604060008403540528810130510380c3e1140c0c041020400c0901c8180007905201d801c4a44034580641c005007400c10174611000c3c040c08210110b42c525000c481280c265581101e481842e051560792001142400200140c1d04030b100340f48443c0c0010500e00003850040c0200041141d441650309240742d040d440b035849100010402c2104224103500842506d60100404c0ca1241d12544183c40031004e030f0f41340000183d0300c42052507400d4949401c640c00349019415a2404101940d1805c0042d10760a02c5050301c1d0202002c00d00c681c03089868250001200c0707621403442d2000ea1620b10b00000e2a0244112210707000ca0308000810000c2041041048490007051a01d009250f240c40350140000c800c0e40601403480c0e0720340c08040030f2603008004945040103e0300484 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 547613264 1250 547612014 547612049
    0x9010c0b09030304030824060f120406060801060f050f01270b03220c0302060c1e010b1206040804090c0509061b0d020106030203030d05131e12050c0d1107 68
    0x46440f540308440440c042116080400c0d8248035200c140228017050b144180e07205c80000040142e660010040c810403240200f02c0c1104000900b4410740c000c0d07110301030104206080109460a40d1055044003980c2e1324000c400300a41d5949010f000741126082c20a5000c1c520b102a00040c8074281c410030706100300c0d20800000d40e0a0341400110302c03410081015240c120b0381c6218010041000c184050b0008440950500241c6401002003c4a80c3c040c41111003030952401c010001e05400003004407680d6694145004a003042000004140c075034002070300d9180381503074841546000718003c0a983d1642c90180003d110b020704112803509a0040609407190103c441904648580280f2100c1d540a0381c1040c2407a035005000d58010b51368014044c42c02c1032114005240185002041d460102d0b60b22210a00424003140c3d8181c034940c40c501400e0b0f140c076401c1c2410540c40c00c01c1e04800007000780801c80b0300c2d203d10010558020440007407a20341401140702c040303140b80c50b00ea40c010602141d00c42c11300 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 547614514 1250 547613264 547613281
    0x1090512030406290a050d05031e0415020703051606081302010e0904110f062b0216050f06070810140d021c1103010e0c0108090304030b1512010b060f09010c0b 70
    0x340d1a5160485604145c0ca460303c00707006080413082c400130450307403007840740700e8071071041c0140103500070076050200d424291388000805060584c080c0b140d0240c1c0101300284280003043c403260b540036404190070301d14580f800d0b000500880e002024021040c0485404508680c0304c0e07065a942d5050040a80780d45080906000c8a00c04960a905100e10180707903204141d0304048003a903410480d400c10034072800c005a42007500c45154504500b102550170002401c0b1190903d481064960054006159464100c2025854400b001c2c164000784144681040324000c07003aa41c40703040d1070b1040b01c554130381203100e00800c8070a0805d5100a5000c0181000501386c0c80002000002c0240206100c0c0120241d4505040c221555250940c0c4a90000da00100e9594000c1041036040482d85040b24602580c0b500c440180e58810384100304000c042c240b07108641c1c41c0410280c809030b0540e6008005500341900007620901c035064030781040700700c041801c04503680140640c94000d034000c1046401854044103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 547615764 1250 547614514 547614581
    0xc0b040b0f18030102032d07020d0309060b030604050d1103040f050111010b180912031302010c020a0b07050606090c090d020108060a0b040f03050f06011208070c0314100c0201090512030406 83
    0x20100c403075051810300c52087e0000d10000030f01030952a0090070001000314012006450f003042c1c00d5400c941c0ba90312101c0c0988040000034400c81c059400703040c20350310441c001003840c0c0103c40b04802552080c0424002100e000c200c2d0b00480744242455101c031031400d03444ca4090100700d031001c1d61011048240200c542c86800c004c0b80300d590b8a9043c2e07030000c1008a120400c500003a60f01120841e0020040b10040d40500c8400c01858001000d81740e409a54012624040c1c1c0a42012a03d030303081002449111f09103003541a07048070001d044941030000140104002c4072581c031010341005440300100c4c616131601c4c48420049c00d4484a1903a40d551120302101f1500f1035448112154031800c0303a4003c44410201da041d050b00e021601481a5000c541c503485161703007002d00b0542d4130111180c0c00000080038940b1031341002000d03501600072540295080c00c11100314504003400d690519115100054002c00c40400007065054440d4030f0380c0700c3e800d0003001444002c103805121075501c2180180481d4001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 547617014 1250 547615764 547615801
    0x20a0606050109060c12020312070203120105010f02061b210114060304051e030d050f10060207080d080a11040602060f062d010c020910030c0b040b0f1803010203 71
    0x11410302086540e800111200000d40c072545000412004541c000648072000300c090700b00c850b1044900b08146d6141030104840d058980d100503a00000c0c500c4002c0e290154864010002400d100c070a45040020203500c50314020414440c028840b01685c0751070706818180d84e0107004001c102010a4070b442c44070304120f0020b019107189d40509c0280705040e882c100c42201e2207540c1c4400601220f2068000203806240402942c42d82030000f40300c03254042080c0e2003054414855441035100301c0c2400100e0504100040c2c01100443d08100000c0c4820000003540150380840c62400079200d0b81c402a103a07005103032000e40c00c0c00a03000003400180c0a5400120725000c0d0702d040b5030840e4180c03503c1080020b940140f440c003604452a40800e17110b114240320b1440d85100c81810301098006240e400a50845000c6951126207082000140305201d0880c2c0e4010207031071160941480e05003000302142c464000c0d40f0982c40c5883c00007510000349030142d81d0b00c0c070320078034041d000350346034107200f5515484480c441 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 547618264 1250 547617014 547617023
    0x2015031f06110c12070b070501141006080708160c03090e01030305040e070e09010506091c0b07030b040b0a0e100312031b0518011d090f0403022506051e0307020a 71
    0x450342646490210500e03040004e424004004161a040d504299034002d41800c0d03909540e900140611800c42c1070748244203414203266050a18140b038009020100c0150844c002c01444404001511021000426008203141403400f80c032044d6150407562040580c0060b80d0700c8801100000401d60020040c2042d5041d0b04040e41d401c0d0340780c28045611200c0003680c03a51040d100c10042000e410110010200150058200740303520b0b1200c460f950400d1911042114110002c608018032035a0600c14140c106104a9040c030a14242d8000601442603d0252048200380e81020602008122202c1c000955201d20700844130402e030344025000b001ca540407640b1003043c2410780d450083c030400490715801d408005000041062800446154411095824031a100315012520a40d100c0303001c607210304044801035445103001d150082c03c28203014902110442460164140503d50b00003e1003601c1481c03034410346a00314042e9000890b0815410b4070074500002040c030042960202e800c141440c040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 547619514 1250 547618264 547618273
    0x1020d1d0d0807180b0c0703111507082511010806010906021e01060b16060b030d170a0912081e010f05010311071209032015031f0611 59
    0x40140d152a041e002028100040e150000112101c0c000d01c40c146850064820901c5020785074041c01885901000c2d04100542c40200208200b154420014042641c00c1d0307841620700d5010440848e49000c0c6000042c141100070031081c13600b00b040f054010b00180c6e140800d41fa91103050900040e245451048903000070300d4800016030075405042c030082101c0c0d1a900620001845071241440746200002100c030654a409001035450210000343c100745000600c0c3c000103283d14900b403001c841e10501d0b41406034003e400b0301c4483c40e401c40034004040716288010841543c0e0142c844c0010204461300070030a0700e5040d42d0741c1a071a80a25128425048500c22100c00c24141c0200e2140300d100b445290707015000d1000c1840700d540300c1c0e0400b081c815a082e50990502c8050760703c8607409509011118005814181704005028021008078001c1c284003140524018a00c0081610028280305030303000d000300000414949585c0d02c40b02c2c05100c000d60060a0616140c0c1030003803144840c1141000588034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 547620764 1250 547619514 547619561
    0xa0b01230f06030a051e070e031015030b0c070c060c0b060301051605071a0f0603100203130b0c0c0604030e100e030a0b090708010c020d110114011a0c01020d 69
    0x304204141e40c500c00050006085544908144c00a0324004000d42c4050b03130403000e1640c40481a105c4c0e2400369080392585030150164006040c42c102c001c0740a2001182042d510348403195400f505030303045d40d4210249100e20750701c082e41820148240d10004025854100c4001074295014131540111392141c50a421240c0340e400c10107080e10410f40b00d0401d442c004020304514140101d000303101091140a940e03048000108030340c07a2400048550304c2801c4850420400c43d840d09015040c407031040140c045055003803601c0700f6048c0c0010b80a0042a4540030030210304c00042901c15a01c803118248120751309880e1504c1d0080ca41284206c6103401518801c652001c0d007400f8030b20481034034101400401036154503458281c10300102070304510300d900035a1004a0740010a008030440b07541c2a070001c00c040f02600340014101743e40039000d001c00ba40f509202c404211440145d850440341d180c240c1840036602c00c1c0f01c0344120710505d07581003003661001680428004c0e60350410f0140c00b001120828043c103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 547622014 1250 547620764 547620769
    0x1b030309021e3304030f02010906050c060c1305030a0609060b100e10090512060709210f02010e060d06080714090c07050a12030f0501061103090904050a0b0123 70
    0xc00d001169201c44540504043c4400c0b211443c000c0b03100c0c04600045602c240720f084903c43d07015400507a030741c2420100072000d42d43c0228a8900502d501d01c0c00030302d45400d90882c203444a002400c4120f2050700000e5009880038440c200c02d010341002000e0b07400034400c0f854200001c21b14107500301c1d803041c04c4c14034684440c504200a0f03c80a001e90b1200d000082112301007024039003c0c0724044007405007a002c0418582c489030600501e01810030000c1c100f40c1840d03840030b0015900e95000341d01e0601401d00c100c0c1d000d035080c11501205131307200c031140d140d07a03103a0300c016140d400d145c000b0715130001404180f030fa800341e030150030400c216041c0a05547d5840c0c0ca500c036075218402426035007600081071b0b1021034504030722b06005240160054007035400c50040d66a6000d000708401e2030100001e030301c404501c01c490403944609801400c4c0390410550070700070f60483d16200d000700442e00b0710a4450b040010240101070000809880c1e004411005540e110144940e54001c0500c1c007901c6110310203404070050 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 547623264 1250 547622014 547622059
    0xa030606090c030b011b08070f140714060306150304030909050712060504060803030c0d0902130507080a2c1c0f020f12070b06011112210f010311011b03030902 70
    0x40c2c01d001d5644a003070205851f9100d2a52000100301d40460040d0003110100300440c40100740c240c0010080c2800618044c0c81c20140c407681e503840381c416134041040c011280d03a100e00800780c442c00c01075080d17141c0c1d40f203060998a0980c142d200150103801c24041045182d400580000140107102003003000075111402e0204450300c0340181c800503401003002c1142c80d003d0782d02030405040d04002c042025500c603404201540b008407208400542c07224280054a508100f890b58400805d440c1042490650b4410981c4c0d0740300c4603404010b005403001f886401040030f00150000e0b0b2100141035100c8070000400030004440d050541005000f489e800019400001c160030812503039481005040410b661a6550b40f024040c1c00780341400b56031140714030101c5003400f003158406508031105840307004400d80f0208040410710807054180c194010800c40740081c000c642d05483d00300010741c848540c2c110043ea010030300030008004840d07121400c4420950705801c80c0100a200360b8480302901094581840700 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 547624514 1250 547623264 547623287
    0x605182214071d0a0b0a090c030606110f0a06051504060f050316140121051312020d020a0b090a0203101b080103051510090f0203180309010503070e0a030606090c030b01 74
    0x10031a0b5070f0f003c2440c507105900b1207103d00c00000e00d02c40803569074010710b030f044400844078a404aa10b5400401042c0d81002103d022444407601030000034105000300c544410015000610540d0740b200804c43c00c501e10a8013515050028004001c0913840f60344000c140c1d20b0760701c00e0030301c01d118a050040d4a003c81034015001c8400403400705404000d0680151403204502c421070440c4801807008007640a114000d9500a42510303619180190083c2402c2c21044812f58481065504c50702209403001e600088940b0943d0301309000c100c407902d4100c2c05a040a00c0c60380041d5040c840e07000d400c42c140559030301010010366145450703003918240030b0042d1140c0c4000d100150483d007001c11046560f101c030b107600d50382c070104071700c500a42d154407010030404a403004180a00c1103a03010040007403442d01e040400c0015003044000f5828686580002006440010116010818544034444141c0c4500b0b400e14040d640c0a0010320a02d0340710030700c4d00b005150700301655000070300f030804403c1994000c3d06401d01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 547625764 1250 547624514 547624559
    0xe031201030312020706051521070605130e091005070309080a0305070905060f09090105040b0a0b1b010c03020a0219030f0e030307060c02030913060518221407 70
    0x1180da2071900c0607900c95150061050003141c00300481070006485110300c91060300710325041e0010443c40018058030500004000c0c06070542c103500088080390025450086a10500e00b860351141c00441401c113803149544039603503000c0fa00040c45010303100817030074000b0b00200b5442000140ea400f2000c80a842c886480940035050810000d402c0e10f1181d00001e61204050902c102c006a8440100f03c2d035920171200b0400d540c01c089248005440c0404c170041c01800200c1d003c0c00811522000192000105d03c41c81c5181600045c92071031540c01c0d4800c1e801030740a404002c1141311010003024010354002c09a070070060085000140e0b10051044031a00d00e541c150b0f84244084288035001d8622034a00360102da4107200c140110030015400d03001d80715064010b940034544651220062088415101840710b00c0d460801906003c1c68486100d00320325081ea4900058a076260380030003e200866280c680301100d00d903c41250240002c1c030300014403043c150030495a00c19500e030b4001c00c61038104440d404 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 547627014 1250 547625764 547625797
    0x209100e13080304030f0c0507062303090309211b04060501020d17070201090f08070605070203040602151302090906010608010909050604061508060702061006110a030c080f0d02040305010e03 84
    0x10046031044140401100d03160070047d001480585806203007003141c2d0300a0000401f841c0d601000310748029003203090680d604001a00b181403842105450f03010340015903010301002c100e0400c00203002550990085002400d5500c280040840b14400880500d2024041d40c20968002075651001801e003045003500e80c0e8000f9914604208400d0380c7d000035014804642d2545c2d5403001040f420030803481d850f03109891031941d804d0360746440c0341035600007881d60041d50010700081001d42e4001c245154500203c269021450380c9604040302c1c0c0b070680e0308019403c20810b101300024440c0003d0100d0584401b07031030b482064aea130341c8502030a5405003940200103800020104001400c19000b079018180e10018000c4030030b8849230818607116085407104010317403208050100610840e40b40c10003400c42c61512485a0a03c2480e07a507407030080702c000900300240d044500088c002d40b24150703161500d540c180b05a5941d02140510040d4001c2e0005451315480c0001105065200004803183d044c04910703d203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 547628264 1250 547627014 547627021
    0x30b03161d1504060803070c0501030504030903080a0210180501110a090e0901020409020c0a060c1e080a0e07080102070302190209180a120c1a010803040504090606030209100e130803 80
    0x10624800090704010480d10b41d5102c1d0456542c80b805094064032260000b941c03903d00a06098240701312550200303051600e002c0034040401d074000015416650000c4140f81e0fa484000c0d001c07440c00c00e8010900510700d24151118180440304c00c041c84045010300000d200c000d2124000894a2107084501c10219411110401c0301d01c41c00103000f903100310060001803c1585da50503140990b40505c2c0d9455044e080004a1070401607544641c0c03004400c1c9240c0b00307860300741d001c41805d503d0600409603418400100001034080c0001d80140020210301801c0d1520309030f45290340c60103034000460031800b5000f1660100320340c80d0102d0f004a6030640080405006483d607050044411fa0107203a141c0b03c0d0b0091031a44400300e42034188010b030f42d41031959003030b64001460406151000900c3c0c0b604c4d204e01d04000c010462000c0c000300343c6003580e000b11030003d0800c59500d002e400609080e44001d4001640004214100f500d4440030004c80c0ca40946204c203590b600212208010708021000300b0008050020 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 547629514 1250 547628264 547628309
    0x3110106210c08060c0304050d0e2b050f030a090806060d08070c0f03210c032a170a0f2d03140f01030201020f301207030b0316 56
    0x464003071501500032880b40d107403100c6495040010031100710708203102c00002d1004010301080000741d89841460111101303000c01d40010403201242c21100123800004d4084074601d01e52002c6496156448403c440e562810031801c1c544981000142a01103406907400040c05000030030013500c901b030000e00350606a00d0070340c0d62080300e40001e0030643e81610211030114016200c041c4040c00717580102801400580344d14140f009642038150348004000f0105000f8001a800c43d40580442c0f01009660f001c68200210310310001950b241d01500011703103001c40c20301018000700100030158480e510031409140002003a81c51000ea82c150161908940c004a103015050400221404c0c0c1340e4500400c1c0c9038803500b00300c4404082a10004e0211410000400440d0780400c00b406492804201401a001c89900d000c03419925820014403103405d14042c1042c504c40e490216210703905042e5802c1004d0610b6031300100200501030005000e8400d007120315101c4440142d4180c1107401002400c440040c00080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 547630764 1250 547629514 547629569
    0x150f0117010504330e01060516020d05010e0a0b0f09061308090a05042d05010f09021b0f07060908121614060a0915050103050c0d052803110106 63
    0x5a196070311400c5160020f01c1c2408182400301102e91050813003030504100c600140341e4410b81c04007040c42400c00021951121175508401d07004d030100c4010441e5859030504d2405809134509a08850103605003280402011034240303802003804011604850799103800302ca0391035074280d904000c000d5050b6480c20009050f00b0081450b5400540103d035125900c03000701c0d043e10f8030b0100c107441c4585c0b4101c4004107110809686060700c8145c007130a1100b0b52501b240207204c09214050b0300c500c1a0001510400140f0300300072880707035107490b60485030306510035a41543c58401c0f6028190000d02a11000101580d00290070055544210b4146240003849081c1200e000d2001d0000c03036000c60f45d1103003208a24404e0001c98071402c03000c030020401c00c00c5441d0034900119807001c0610503600d088010b20200340d0005040880140079503203050a4034140c103040307182408080c0b07041ca20304500302800c0c0c3c8504600060000184c0300c6c0c4c4071107900390354503450542602c07081c1c080c6150110009401d00c0300b9084145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 547632014 1250 547630764 547630781
    0x10f09113405030f0417070f05010e011413050108090a03082d071d0a08030304021c14070303030b10020d05090d050f010903022103010303050f12150f0117010504 71
    0x1000d64440a10740c2e40b03440c15130700718005030303000158042004c1200140d000302c00f40c0355046003c042d0807003030304020b004800304005001705410003200c454a450281d0050301728030a019041d42a00380c50744100459500c1030106401541c2c00100040301048900400141003011564981c45002c0540d4914a25031942030ba1140207110031794200d00140b5a808100144500500030b030f030351701c0504202144084860114000341c0c43e004100c20041040a80804800d80750055412160503001440540c0c149100c440c000134040c00860500c020441c001100080c94002c4034820744050108040c0b400400c108810702100c40405600304410540c56140700e04014208958010038681c10201541c444038901841103040311040ea644507110f0043c99010003141d0b00008101c80c00b1140c0e802c0b41c01e41c07902507010600c00107042c0080442c2041da00e036003440a8a0046051182c0c41c6d10f5032500c1c0854440a900340e00030140a115a2070640d0340c607500c92451002420030001c2c0c0c0300c629900e0501440002d15a90 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 547633264 1250 547632014 547632097
    0x3080d02071a090f060c120f13080a090302030d05070b0a05040303020c0d0c110910120302030910080613112203060c0804060f06060c0602091305010f0911 68
    0x49000c614040390290b80c0c64003034400200100b000100d4410007070b203410006000a40c00e0007042c420801e01c8906020096800350701d80765140d0030b81d01e99510124040352442c4001b40380c80c80100d070340001240e02c0b0780350b6030032039008908603410261003078000e0303a052054860240803856070000241c110031440e04460f40040c4a0b2800500c7d0604480c01d250074254a0111180043c0c03400142c6818801d551502ca10400c00440321201281003203c00e07145004094482c201c400000724601c0020700d4028409d441d81c03800e0240150b01c00b0b6440d400000c03c807842c01c0381e03030380c3c8100d584d0740000c0d00355055031062201c062102e1591a14212684440c50a0208030f1a41a041c0091a520200000700c00c2e0052140103150b51320740c86030509140c540300090b120f929501245542c6008800c2201c00da00c00d80c406406600030000507580c00002c401300385161001807c01d01c80c0e034141800085d194210040c048111007410004004800c90104125181c0c46020180585203840401c0080e6150f00c034200f840c941c424a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 547634514 1250 547633264 547633283
    0x30b0f0f160c11091f090209030a03140c07090c1b0c12021c05010b09070203031b0702063708010503031e1318060909031e020c130f060f03080d0207 65
    0x4400024074042412150051004030303101817801442a20000007002d004501070560074001300d10080f80d0350f4117070328602034100a500600e1741442340c504811101c2c00380960060390741ca29103c40c41100a07010040000c2c000481c04401c50514400524403022806c0d0702c5142d08284929040d600c2105040420040ea480388528851080120140301a0b00b00d451050002184045002d000c12800c1d000c014054000e5400802c204050000b0056030940380245c0065001c1d02c4001c0d41c004107619000c4e290108254004400e650700714007048241c90001c2d12100e40340c401c5407028170b031800c4519280a00c21030390540e0ac20701240b225038030900c0c61080080c000040132420300c5540c07e034407020202c817a070080e0464110039105641030b400d64091000648100030741402412281d075001403021010400d500c01c0c0c0a0302d0315103216080d01c2444a041c1e2628010b228a241ca1040d28101000340021112200c101d480e020700000c04100354041c0c0c46c100c039040450103061090301e080000180d486030400311000b812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 547635764 1250 547634514 547634543
    0x31104020d0608010e15160518040504030314061525020303070b01050f120a021e100801090f0c02031602060409051905101a160c030b0f0f160c 63
    0x8651182c900107100e100e0011681c585462038607418103071990040140f4452031410051160b0030900c41f440184050329000d40d481c2e401070180340d142807150100d15401400c0038280000d0540c5070b04402001036004007050543e41700c180070442041d0050958068040c403d00004440d1000d084907118190b40100c40d1000010041c2c0c0000d046502c50902218100d22100c010b01003814040d003c0b800500041e00c4581844c921203d100c0c0d550b440c0e07910028840d01300c0307854403c0048802c512030341c90201c0c064003503c41840262800f4280407024050b1001c001c1c03400302106910840e9004d04000407005802451134014401d00621644c0d01a0304242d030000303c00c0200207440c0c440752241d180300b0f032680b50035440c1844503861400151400604070505680030540c050150510703c1200b9180d8034044842c103980c5001d2400d6560300e06800010141c541e00004d07074000305004400000300c0c82070b0b400303c010590a17030b5561681d0000c04415911200103540202c0420182402850091811801402c00240118 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 547637014 1250 547635764 547635787
    0xa1b050f030c0d0e1503040f020d0c090f230103120207080d0c030201140f07031e0f020703080a1b0f0203090a140f010c0b150d0503130e010b1303110402 67
    0x900c0420b03600b00a501040c2441649035010514045185046a1200000c650801d844c0b920740009403018000c0b40c070b245c0308402150340e0141ca03004220383c0031000b4900b059030750007201e00400c0166044141d16080c02c0e51410450f0703410341c0d0074080c8040304020500a90171501c0f000034441d958180c03d81580300f04000401c44490030414105c00031010342e0b815086007000e18009003540d6100f036400c00440031076014040b0030417484050591200c003078075000503039044d0780032000c28200c401c07404000b0312413501d0199466040a80c00502025000e030701c0341c0203103032036041055045490408111149218040940c0d207020b2003581d00c0e00340340b13805204580c10440d29400041c9c101800380d00c03441da4031003452802c1d095824005013501c0381031000d007082c402c2440282c540b901104401060504056a60701c4c00d9100307a55060410401300c1d400000701d03030700d5140c1e05500c110155800d0203141940301c180700002a400c020b0f8403c480016005034960f4203100d1655030741030f90b044158110a41e1154082c41140c8180 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 547638264 1250 547637014 547637017
    0x100b0303030c0a1110270b060415090513060b0607030504030303090c05030d270614221206050c43031d03120417070504110a0e060a1b050f03 62
    0x706044500040d0030348008a40c005d1001c400c0006c03402e08280403030341d40128440700002c9034031490946d40814050280c2c4162a041c581035002881e030246004240170a0b450320507851b8000c144070390301c00c20060140d541040034070f001d21400100015020402440080d100703401403d403641c0314540c0006444e0304c07000041e040c6002c0d91607250000301d103203401070080050030506203420300e003140d500c80d51503007058402000302440714005c00140100051644404030000f810402030402540e031a03a081d500c0700e1080c840030507540300035603205050101003224045400308480c0c00c060030144c50b402c5004d100e468044040b0002400c3d044041707400b4009102541c0c0c0b124400d00c000c0c0729554a60490a001000824140c0100503043c021792004a4254443d0241d90840b800c0e904905851f07030f10010039003461441d0000139001581c003e1308004042c1080c0c0326481c0a000c40d8036064031003000401101c002c2c400c3c103000751005c0d0710001d522440e092284914103000d10703490314003c60079158640b8861b046503245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 547639514 1250 547638264 547638283
    0x6050d0807060c090501021203060a080724180302120a050607020d171006140c16030510090c05060a050904140f09030310090f0b130b03100b0303030c0a11 68
    0x625000607100700700301c2d441c850040b910415080c410034007400c100000b9614402d609000480c0d1000001007030403075484080c0c403002003d15404581e01d90307484140d51050012103010700d0702c4070b640c0c2d4006540f24600401501e240304040180e40a1404d255800300000e01c964440982c00c42d00070000000c01040c82401401d110f601c0e91b800424400440100c0108062420702c01a2044051142840511801c440300d602c103e558601d80f210f91016120805c0209105100020405124003810100c00309000d036440400c036400381d810380381d030301d030b00204902d0540e2441c000c01007110421510600003464500082d000d68841851301d14208409500800e00f2a04038100ac01e2135104104c0801200d448038241c031682c0a41e14101460450526211012405c1140c0c015216616200c1d100c1e514150b04a5000e9100c201c8000e140c00041e89480002030001c0070000c200303c0c001e0207001d1855000308454007803010300d084041c0041d440c5664420001040b40c10140b0518208040c904119503944000c0022654 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 547640764 1250 547639514 547639523
    0xf0b0d081c020304080d1112010e010302040509060609160c080d0603110a060c0f06111912020c07030213021b010605043b0316060b0f010507050d03020a0306050d 71
    0x7a500c403014541c50224800349000c1c07034218010803c000000d001c1d00d0a4a02c0c01e080c5010104124900c3c0c040d84d0003502501d05607800d4000d811000103403c00c05026114103c0b40281e60400403030311011199900c4500c11207040e038010526134013140300000031516001c510b05482c40c03c2c0705140200d545a40c00c3c1d502100c074000c1244e40794001482844446884091030b02c0003104c80d29905031518001502144620101500100781c0761400f9080c4816034002c4c3d00440c440a0041d950b85030a089a017040a4460381400000740042946801261242c030031a0700071040c4100401d103403031840c2d0030810315159400845921580901502e10385554100f07040d007000a52800200d1168205014801160800070302c012451203207008039140c40b0310f0040400180345a042044c42205032901c0c03403d1a512501d8140080313031391528440d07806d0152035405180f07480030460f558010000c1ca40011990b501030004083d0442e041030010844071806540105400203040c140801d0b40d0303590b40b00103160728800c2e05d42901c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 547642014 1250 547640764 547640767
    0x6050d02012d1e21150e07021509010c0219060b040905031206150306040e01291503041212090f1a06010c08030c180d03020f1c020606040f0b0d08 64
    0x98001c100c0002c0d00c108800c6030700d804041c0040040c15540e1070030310450248504c541e070340c0c2d0407960002c1c2d00084101521a415001601e03042c9244000e540e200000359080a1444080114030914018060410689425402442120108224941c016001c0c8000301d40c1315688122444203a1542d000d0000704a01410241d61140b44407419900c00c6000100b44921407643c05131484103c94203002a6500800c054600042546c10360444500600200185070840303c00d503940c40001c9000f01c00000d0340c05209554400d2103034403048001d2120b010540d0000c188541c40c8907180c00079842098500103541c0007040c0802c007000c06031a05070f200f0107410403d41d1000411075031120508240f840322a0410828a0301d401403c03a00d407504600c600028103161010743e400240000c428651045048840d54000c108040d030856900d0041e650300407030086074020340079585060304120701004031540c500b00a9000b8041e1540d0310010000101104030044010a0707527220200116201c0413901c68000380f04078440d0f03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 547643264 1250 547642014 547642037
    0x1e210213060e0a091104030602090f03010f0f060b25031e0c1a0403021b061b0f0c0303120a05071103070b071202130902030c19020604060f06050d02012d 67
    0xf10801c1d50740e820140c0043c0c244441c1c00745d0303450031000b11012a50030090060700c1c0c4408100003040d40e18001e5001d0742c150f0030252103000f000b140c0e50000a036160074070810070030b4a0755044155000c4c000c0c800925803404a13080c540305001041d5030a600c03083d2107850901888124442110800c280e925030620000d42d01081e242c08001d1920200341105180e038541103114070b8160340003580c800c1049802c2d1030220380b14141c00295190b110039204415814100d03031066008086d2040e41d10403840c4030040151040c91411021414088102d41c0250180498040d295442c02c000c0c00191a0241003201040462550401c04802c00d00c0500881813251300202020b00380300310000d11000c0b1a00848180038410000e00c9690040703480c1040442c0c0700f043c00540c0b29501c41d10003241c14044c10500c0c030001d90720007503680d503007e50100d00e0900c00c0703108480410410100c88880003c6842601401790802071303501c2a50050340c0030300d06001900340080a0312209280d071011040480340410000e1000c2115003001c0c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 547644514 1250 547643264 547643269
    0x12030e04060504060302031c1806021501091e0b1c050a060e1911040609140a0c08040807020108091c020a11091012060f050c0a1e210213060e 62
    0x2a40002c000c1200c05000d41c5080d500065100c464003940c1c007018450013106688414010008440340100702e800740082c4543c0c1e69000394503040440018101041218004a40c4010740d202e4952a01c4071403003498040901c503e0703c0303002020680c0b9003d6108a10080318005005001c5082c10554421000f6242803609480c20406860900d01004801d41000e00a100070107684542d884505070000c400c0048180b0084c00304009110581000f82c0c61801e20340d1500d030042104485900a9001150802c0300c049480412034034440140c40082864004005000145d0700c01c024968002e5998410746102a200d928420b00442501c0645809600880c440700180620400c00189550095440000c81c2c03900c0300c41c0c400f0242c030a018810741c0c05625841e0740140949a400f5403080050100c0410180c1418110580141c01004122000802d450b00401e0054038484c203218280e10070b0340f0742404003c2c0711859000641c0917201c50350040d5509002076000e2140340c60001006000d80e1701d840b415414035006 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 547645764 1250 547644514 547644521
    0x50d0816032006090606041802060705010501060801080a020a1818051b0316060f1206080105010e15030a0303020d0902060f040503160e01050d1415071b03020a0b04080412030e04 78
    0x40080303401c86002c01c004c0030804110503610090898001449405440c200783d170180e03a011020350407a10214401c41007000c15409241601c40603203466015a81e1152050780d034800c2014002d41100301001d040000884100e041680d81c091040d0110b80281500300c1c280414007210300584566120340c46039440c0c100446015030f0b8409007a006003902c140c001e4110620f2000512404c410440100341441d1642e1141c006500f581440400c00d01805984543e424041e100a001d03000441000360081580315541e82000c3c1200503019014007400703a40d0740c4044c1c000b5001008541c0d51503032038079140c03001070b5241c000420071044085281d540303590402c81072604c1d0000920080038004400f0400388605040e000300f82d811223504541c04051585503242c202ea103172401414088240c0704584004144088207519135118041302e5840c03040c9585100f42c01d010000c040c41020b000360700440c400a02280400b800c00340d1082c0500041423800e941c40400080d01c00308c00106800061103032512707041e2440c0070701 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 547647014 1250 547645764 547645817
    0x1e1b2a08070c120318050a0506030117010e0a0c08010614091506210108010f060f09050403051207030902030d050a12020c0c180714030403050307120b0307060215090610050d081603 79
    0x640c4411201e02300f10101c3d0301c0e03100c180200380f0071488800055914071001d4000401c00d15011080e10b100c0d0f203040c50003108421050240603081e5090103c04901d0301c0400c40d041014801c000d25035580b98513203031100701903034240301d001503048602040b02409031907141342120740c0591004d03000d421075071510b6600c41c01c4075200d510300d48502e400e000d0100305840704c0c0760301181511840c95000035192030360306d020741e00ca10444003440c0c0d50494032820015030f650154030043c1280d0003a0309488440304078030011a01c51250074001404904102291910044190b01400700d00600c50201c0d290095844000380001000c015820344803c401003c001e141a48144820a40210f84100c1400c50030035a8015040d03000080c19007003001000d07050740e5109000d640000c866401c024068079020b41e10303407000075283c4c09a618407101003000000803c4c80c0d14070016220b8441d0460440c6960740301d04047c01c009030000382e00c1c1f05607800c407410712061041c5081e409010301100d01c41e84888018018106940113460001c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 547648264 1250 547647014 547647019
    0x100f09050301060605190314041514161404050405010816090c021002090d06152d0b130e0709090b0f0904061e1b2a08070c12031805 58
    0x118040290f180c02109442d060b42e0154860601b0000c4040c084005040360388400116041c168140001d1010b1042c4c0546040c40502d000e101001c1c0b07007201e100395441c00395451015000c40384240e425040c8590540c1000c031000e594228500381d03481001a003036601c05e0b0408800ca03085560840f002ca2404980c840052005102c00c0c0408052101c019495404000d0441c14460300050648404d54552401140c0c10307600110402c0141540fa0701a130400700c49010340303150b0321500480740c03181503800c0d10780c0306041c44242d04030074485040c05208405d607003250145281150441c02c0101760b42c07040c0c1300716503c14020b60fa02c0e9000c0500d402c01030403d13a000c0c40046400307003001d1003481c3d00c941c0340c58014076445a086840441c011207a0121349040d80080a800d814542c54034980e600200f1750490310602254040c1d40f02c00050304003008180c03c03e0004024080081c150b0707001c0d5000510310801400b8001c1c020340e02e0351a07072079442c07100c0000c0200c404404c800140080f03205403040d1507120b0b0f0b60405030005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 547649514 1250 547648264 547648271
    0x412020106120b01080705032103330319150207050102070828030c080a0519020f040509061801031502070c0612060e06060403260f1e09060a080a0b100f09050301 71
    0x2180c1e001d403c08100c88044c0822800000661104408c8502040760302e481c003070012002f00241c0382d5010386040f401400c0d20030f0140c41d01d030030500c0304031401d0207024a0308044103418040040c860000207500000c0304540300e540a100c0100803503040c4028000c4113210044522506008111202664100301341601c140352818190000040d441440341e54042c220340000200d6803228521710b0844900782034100d510310f0001174480012030744003000c0e008581d41601c0e00e4485480f00d8007081421200300c01d014221108950042001c1044800c44c2c49180d11001c1c001032514003c1d40b07444000c820700350490700c08240900043c040012052003440c0047c03244e440500324906107031f000a00d0301d00c21888058441511200d1a080c2150602c070103010480800d40c82603510711004820741e24a4012081d40802548030000740f0441c4a4007804507070580c1801031090b4901f140c00c8905980e202d43c09020b040505580c2c0088100030f07202c070b000d460302403081d035240c055400c2d400c9403004041081c07a8012134040e904 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 547650764 1250 547649514 547649533
    0x30902042007060b0d0809190f0b04060212121b0412030801080d2a03051c05041e020102031e09090405060603010b0f030a1712010b0d0e150412020106120b0108070503 73
    0xc102003a03501212040700d00142c0c40316850040a4230408507000780154102e800400074800401c0001042102d84e140c0a40e081d42e0900700e032050040c0120b4000a6500000c00c5c0065446010701410200481c3d0f03488403242040d495651f0660702000c83e60040f408203c28100512101c10b00b04400412510b881c0b030008482400c4082241345440004051098251204000300030140601c0586a2003171104c2110b0040124050401d00980001c0c7e400b40d41c42c09036402d000e8080c0d14481e01145019806800071490300c03801d01ca0002041803000da07000e403028424054820255290441280181d000303130014061810b0503810903084070240e0312040c0c03140402c1014400580c40100e540a8500d030048002c1c04401c407a6031002c591031041c0145081a80f0000001054a4200b0000340c985414101c4003008048240a0b005a03101800701d01c000480c5d40d81070004c1c0002c0c03050101804078100c28400400c201d95120001c20024060f044215189142107005104a103001c000c2d07040146022001000c1008 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 547652014 1250 547650764 547650773
    0xc02070f171b012c1c200409020306150114040602060a050702420c0306040b01020124090f4d1201061e030902042007060b0d 55
    0x6481e482c10b40b60b150380300707030070742c82c06a0180c9107420995040d039118403034a4003003440180c2d02412540c1a10b1040010700c44c1c00c9015003c80c1c4001519607030000c069403804070070400030b086e40c0c1d400c140110750040d1152608401a00e09100e02c50060351010303501c038003200100300050019460030015410075202072104000c0e01e43e000480703a07003201d01000b00060503218100201e09042201c49402c64500c16014a400e508030304040405071280c12030101d40d41a000701c500344000d400e007581c180d00d40c8902400483c800b8a440c1d0712440a000050000041000d1100c141a48a007440d00105901c0044010208030540b400d0003500f24042c5000310400902030030001c880a080c070003000320701c100248010f42c1900b0071021022100c0d0007240700710a00021003031007010f101c0399000c540704c031041250b038400011740c081c0a10300c00c540e80306041c001e003038428403402130450040c55503100c180da1054075500341d400da003001c4451044224031030307a003550782d18461420410141d490302880940140039044501c03001c03c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 547653264 1250 547652014 547652023
    0xe092406040f021c0f020903070b04181406010e030a060617010e06091f090803010b0306011b020306011502030f0406020a0c060206010b090d02030c090f0604060e06090406020c0304090c02070f17 85
    0x507210070000003100811090717008000d001e65125907802d8400d00e40041440b115a502500c2152010504030660290182d0380c0015075041c010081280901000413403907a60080303108800301100542100c003540d0446e1140000d41d1203651241032921a000c8003100044d00030b00814000e48000401802c0c14100700010315a01c4030703c03aa80c60ba04503c0b8404018141c119504000e100b10341010402341c4a5844181240440c0e00c1940c1081c080b840f01840c494510084010706042660020f0203400b080c2c0c60000d07000b218003070803c00981140810005c1101d041e00c0140600050f00c0d4a0b03009056044491400c0420a03849070001000d552101c40100030043c03400c821142c1030441030302c0c0011460031034400b280c0780c035a4403591282c1c0905240c0806c42c0102c7c0d17041c545445818102c80a1100d10303030710202c00050351000c2d62407503001644500018003103103568005140320641c2d00100c0c3c0c942955107040c1002c8030b5024450740010303048400104640503012803648050300003008100ca05180012406588 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 547654514 1250 547653264 547653307
    0x110f010608100c17161119081b0703350313020a080607030b030d050906090f0f0a03080703020601061b030e0301060b040305030405031e070e092406040f02 68
    0x442c1e1114041032246226071002e0141c00845901d02d144d40c03e2030015640c0c00856000354000044140d044844501b000080351680c20a109001d1205840036403500c0700e113a800344d07916120b90080b503165644181030400a244c01180204a40a03c0810a14520a869110094840d42401500480c940c4100060110b03034119003500d50340c0c9075807511440840e0002c20a98415841c900405040101442d01600001a4108205c1c01e5034080750304030805480d01d010360001e8982148060181c1802c41c00d00c0d081400800c20000c040000070701450000840c403481d1030300b084855080206505082540411007180905800c1c1082246141814042d2202c6082d00102070100a03004004102d50345082d40800003500314030005913600c80d1207041041c0c0e030360f0051040c00e010b441950042d6a58992070405a1906140f0001800c2ca10789041d2191011600280101016004514441010618540c084e40007642c06400e008841c0c80c0034001c00040b1a401242005010b00400c503c0300404104550341e0300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 547655764 1250 547654514 547654543
    0xe0f090d051606020301090e1c0e0603060d0f030c0501230a02030a0b0a080102070311030307090b07110612010302031507480210090e01091e0c110f010608 68
    0x1120b400540c25900004011070000e407001c0d100000101d03003c2525000400c1c5810032900721425a180d00700c08554011454041000150034070a200f044c0740340100046402860003403031820100d007581c0715001e400e00c919101700d001c1000c4c140800c00f0040700b80070300960183d50f10520081054484140d4000c0704d40204040711590340000029080310b620362081101760b44c060050140e00707031100c0a032070003076020420980114205566103030003054000704491003081180e5411400910b007200c03010041d000003204581c80c100c18501c00d4086e81321540070300700003414121440e0b05540b450050504240844410880803110341041040d041d4205078882c161803010a440700341414040c003880c000802c85150800b290500e03c0b80300746600100116012114000c840030409488000400d841c003400f640b140c068080c0b8550700402034221140e010b0700d00a85c541491040c000c0040c0c039200225103a000d00400071900d400b001101d103010402000508400b140001c000c11420800e02c642c0d12025114170300c1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 547657014 1250 547655764 547655767
    0x11060915151003050a02070c0b131a0403030e01050c011e0f14071b050703060203070e0d0c0b030a2c0c0d0b0f06010207030b0106020706021603030e09070509190e0f090d05 75
    0x850070032040e411607c2c030756081130720700307103129120f80000d40d460707021a03558141a46015404101c050740c2480d00802d6100c1c00032068500303859942d0542d01182d200c1c0241e07040c00000e000e0307484c03200c0081c001c079403000c0306010090703074003060240000044034015894005070303a150003200414406585201a0050200d050ed21602c8030202d90504050721032450060650044002c00410030503650060b5018081e16203c0712485010103051141c1c05604600207050481e1201c0200a103140c01d02c002e54000c50107210201d1042001e031220100c50f00700840e030310078041415041c60003200040c40781c0424602d085420181c01035058a40a4100b1405040e06580b40146004204181e00805c03260f0015940541500080e6940351b101945481380d5105c0d107c054002e90344150050400811300c2410303a94151500125a1f20000c1440340c5a5002410401030060804c825050755030766150490402c034618550000c1d0300d040116100409402502000760140007409000c0d410394042440007008680c0e00d4010b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 547658264 1250 547657014 547657021
    0x902030316050c04060816080f060a110409024b0d0e06040c030b010803030105151b0316050c0d050607050711130b030d090f090207031106091515100305 67
    0x2a420b001e007442c039082d4003600d00b45d80080c030320001203045294050009030981c0c0e2140e94003020ba0703c800d107070000c40e4035541208000a800d20340650140160600050300207051030b0b103901c100f000702e0f03009201c160000321101c1c2c1008101101d015040e08a2440c0c640c10b04229119000a05250950910111440040031880b81d02c112030940c05654003003001411120607040034102020598040e00050781c260441030004105103400004490403110003819049d02c81040c03001d01d600c180c01a0482c006080c041c1140906807610420190641003602d5a210b11540202e260a610f010210000d00d8001d074520000030003c00c0c0c0c00710790341e0792009803802d041b030750343c4098500f14841d4948001010740c80400c1484401000c07070344e503001d030780305100903004c980f012000035100303503444a80c1380308011000740311000512103921940c02a01e007040c0b182c2032410916454281440c00c1034001c941002079640190f81030140703451401c83d05504a182c0f140c1440440394050f021403004d40804488200381a00d80b40032 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 547659514 1250 547658264 547658273
    0x201060e06101404060c0c0e040809040506010e030d02070906061b080a020a0b090109020a1202031c1407120306050d03021c091e05010e040212040210052205130902030316 75
    0x4041c2e261100b08440f6a581d03440d450040c000c07081e819400d45019800003400f184006440c1d010310b000b6500b250100d0b06201514040002401e0014503040c10450840340980090b1010440c0c0340740311482e81c020700368581c20f001c1c50382b040f2600783d80325070300304101d07204800103030780b200030b00f500b0401d80100340c1ca0b6503040d4190781070f40b800e02034000007429402c81000300411450190b01c00c5034024402c541e4011075039621804d070010802c0e81d07400231754550090f14440100d040e200f00c624058030304a04020b4424921401c411000f41c10003c025141c000c1d0b251800d960b565818032131030b005071a0444803040341500c961002940c400340807440082c042e1004001101c85401200c440004264140c5070301800e03183c41144045800480c0304032030102c1c01919172076900345854001d6039150030100300e03141c2840ea2703150200034070f00c030360f0011a90500004110008020301d00c0c94107680c0c2d000c4004040c8070010300d04020710582c14543c80310803c00e18031f400504801a41d01000722026601002189180106a03051 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 547660764 1250 547659514 547659527
    0xf09050c0c060405070e070e010e0d03020c030a060e1917090a2c061f030506060909090a030e04062d0f06020106030209090102280923030d0201060e0610 67
    0x50352034007442403000f0041004800518041960342940000206e40c4802109407200c1c0e0554a46901142401e0f890546a0400d4105004e00034024411a0914410000480c0c01d01095503000d44081c2e460704070000d801d00007000b01c058910140e00c0c407051110100c3d00c8890390030602e06415090464000341c000d00310380d503c0030084080c1c28090145041c02c00c00101c000d00e9000c1110118258035074000010304145000e40c800c00142e02030b0804c840139060748510840007000020181980248148105a016220145c2051103194990014140c244050502a1250002da00c00c50b21803402d019082c8842180e1117400c206030003031200ca140301156a10f403004980b5240d03402005420401c294005611070381500b040c000c8900070340300990241c8907a0076090903072244030300b2220302c3c070400200401c0c1d400302e465200400610303d1604002140d103d0f142e1807400c04900b048180000c0010340700300c1480c42c4c1170100050030035181c0001c0060500d0040617400f6050b0003018180708041306504804c170180681e0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 547661870 1106 547660764 547660777
    0x10b030c04021c02030a0501080f030306100309020102030d090809010e030703020622090908090906100f05090a031a01030302150405150c2b0b0a0f09050c 68
    0x3010721001e94402c0d0040a256406896080c010032064800303180280851540854030703500d070002040c81d1044014240040317070410400d200403540c0c2d5107414268907449080c041491200d600060f410360080c5403803041c149040500f06c41c108100800144441c4900340c07114051f2445107020b040d030b106d9841c00300940121041004050381206807400c1110034035003076030b00d600d0761b0b032555040c6003601c40c680012031b42c424010803c0c0701c15180400382c0d541d1121041d20211550354940030001d1401440075603030b42c140080021000103503214031403030a010311f800c075892441c4850b80540500915000340b0043e4010301030b40f05840309074104941e1081c0166004001000003060600000504c0400038010b10050700c001c1041086000444061a607000c01300000031141480d62a80c0d5000d640440508071300c5041e01800c00d01c50703812040c0300b00302130341c4085200044694030681510294402c05 = true := by decide +kernel

theorem cover : BRFrame.Cov 547482014 547661870 := by
  have h0 := BRFrame.cov_init 547482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 547482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 547482014 ≤ n) (h2 : n < 547661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
