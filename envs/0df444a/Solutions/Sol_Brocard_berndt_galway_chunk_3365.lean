-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3365
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:27:00.911353+00:00
-- url     : https://prove2.me/submissions/6e1f7aed-bdc6-4066-ba45-cf30c1e67a13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 605035971 ≤ n < 605215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 605037221 1250 605035971 605036017
    0xb031e0703030818061003021017061302070b0f0609060d0c03080a09030f0c030b01090608060a02031519050f100806100201021b1006090e070b09030c0d030e04050903 73
    0x1040e4600400c2403844c00c03c103039106101c441d428005584a40c07a14980c12841ea401e520401102080400f00441009032511024501051a4160542040003200d2030442d4095030300c941406407080040041c5051101004c2c00030450310000e01d10302400c0201e440681c0c035628071007842105e80e1241130280c410200030b04204086403c80c0020502e0000d10328200c3c0d1026120345602004a180d440c044801c080c000800700300f8040811b0300c0c540982102e0105204040c5050100340d40d9010242c00c502c2d8290740040803c0c15109000c69540082402030440c1c40c4070b55610451009440c3d4a100b40d90143c4881c9010040c1443c0116141d00b440070540c45545080e10b4001c00e01450080c141c42d0a401d56508210750f0207a214104007000347e0f050740030000d0a50ba1920104c1405a913207503031090390440e080c01180f412021000c14000150740c040d81d60103465002400c00030b1714110081f90b500c0c2d00b01c2031010b410014540d002440b004104c034103440c00e000d01d4441e498015a00e21900100034a030140d5822032350 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 605038471 1250 605037221 605037227
    0x10e06010c170a0e0a0b1201150906140412050f0106060c0213051302040204270e0a0b1b19020c010207061409010203190305091011040b0702220b031e070303 69
    0x50250124a09203404015503001701d2010500c54001d101c4000c0c000c181002d0131000c1d8001d041c09090660900b2031020701003000a4040e45081c01004280000d50000031074202d01c1c14295001400c20040102802a007030411503211034604203201083e508100b008500203004202098902e0350160954405a00b00c448a0740185406000a1f041a130b03802e82c41805603803580043c001500c4e1650600c0d807503989290584040e08034920101c002c441c01c044040030102c60204888400c00d4000d003100c5016541c483d0103e400015141010081d80c01c045442d0341028160004142c090f4629000c03618bc4107001740059a40362081c3c403401c2c0010b1564000a481c140b2610060f20400d881801160304141043e044100c42d05040751700382c40040d41c0c8400b000305c802001c100309003d09100150070800c6d142044290700c0d09100e9801540170305500010074000b15100c1d030402d0140624181d40e000803044485880d20051714046000c28400c2c480c482e143d508400341c107403903042c103a0ba10700010035000e4034507a416 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 605039721 1250 605038471 605038477
    0x40f0e030d0c080a02090913020f031f06060806090a05130501060305030d060b0910110c1c0b060603070e060a050f072301060e1b0415051c020307020c21030a0503010e06010c17 77
    0x8a8014441c00c6280d1032584041055120300084220340c519331030304900d0800100ca1042e44824200003040091010b180c80d1603524a400071814600403c3d6540d03061143d503040044617000400c4e0f90300e00f1000001b80100440940b400c20544c240c1404840d075140584011030240b6802668003030050941c0c015480c1c05004100da485101c4c41c161034000d499080042e9040e0b5108480710700b803901d12a030580403c91081c1a490384484100c3d400c1341141060400100700705031648041d03001e4407000424200d0680504240c40c820005d01048940d40e1515191000c0316103824848183c55000d910518944040706024a0064036140015550075a80380740407600314805a40282d0300880c42040049001200641444800d101644445585545400d4007012006000c440741c10500d205000384890030380e002c00d007000e101e10203d5003049171203003082c203180c25a4103604030724180e1311000401c800000c0d00b210255048520350881100603681d184010340b075401c00c00707000030004600e40500445120507a03006e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 605040971 1250 605039721 605039723
    0x30b040605130b0324040605090328021515240702010c061d060106110106060c02010e030106150c42020d230709080705040f0e030d0c080a02090913 65
    0x72130f120070008400781a000d80801c2003031745c540f00c0380200b00f000b800003601580b034026071100000c520300712041401e140c420011244130030030920f6032803140042038801c001e040140d0540c00250812402d1000030b00c401c0c2002c0c07005060290000081100b0026003041c0c0012084001d03031030781c5180903000da004468240b410002103510950302c828000c581c60010720750400021080b402068154100b0901a10141c40c2e00421900c980c186407080c0207440d8003403c2c1c09100c550a00f403d0184107951400030f0702524458110b0b05003071520343d91030500c041d4018007210145000c0c18201041138070549040540e03008902205407095055a01e000154003900c071001150307408000c006062840c49100074083e80c2c000e016031703c40400c01c29041c6000c00782c060800da070004081e051007200f2900d05002c80c0e071611510703c9114415070b41c4501140c406c1c1c0c0d264220780c0e044170906083d660ba900858100c0401800e2441000c0001002400021480074185c070031100c203164000c010088030780c0c036040e200c1c2a050340910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 605042221 1250 605040971 605040973
    0xb011407060c09091b120b100e1201051b1605070905060f10120209010203070204091506082109010905030109060e0d0c110d110310020703030b040605130b03 69
    0x204164128444501514500d841100049511401c2160040c440c07401074010415440c5040c4040100d44a02c1c102200ca0010604062a28600c400302d01ea00401140e004140c100003224201d03c221640491420303c0ca601c102c0d610180da03100400214203e5004444c1c030003440203660f200f0741802444001420f0710f00304003291100500360503030b58281007208503405550040c4d2248140140c5240090250602e408251440c11400070f00d1540204815002409801d0f0150b00040451203a4400d104950703006402030002d00116102d80b0b0201440c001c407005680545240240c00b02d440c1e0320200d507005000b14080340e07101640c101162030801b154881c0141380e040c00310039031000406031028015554101e01640300042d02ca03514030849810301c0007a0114108000c02003140c0b400040c402c075010740c1c1143c0151443e038159200c07032030301043d001103c074520f0303500d4800da024115100d20250028611103200355800d00030f195064081c07106844a502450f03a000d0095101e0007080314a940c002d001d000d000038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 605043471 1250 605042221 605042237
    0x3040f1205071e0507180f0f0e0607080414030f1818280c020307150203011d22150b03010b100f230405040b03150117030c060705041d0c030a0b01 64
    0x100800c8440140342e9900840c87c0d111210b0104c1032400e072160707014280805000b48642c85403100724507180c4030010442c0081c800510301040911072020b0f03900500204101c1140e80d0b03401015114092500000031080340d0700005615a66035041582c2244020f00d0002608061034440000200480005001a143c14010b801c0429140140390181380c1c6028419005541d840c503190030311044209103102c1c055103031401000100050000300c8100c040f800104104216661161404071403072064018240310408040d4501340203200d0342188041030481182010002c1641c0c1600741400e0751050045c16600140010380c541c8500d02810075500601c00c00c0c5040011009030310503404082b6801c0e00050003100300402d06028034106441054a80c0604030000e001c003461051000035207400500074003800e0450740300b561404e1002003060b500540743d6201542c40902c0c10002c0100f1a820611440748501c0c3d040007001825a42668264000c0012990007481d41d9a2402520040c0c400c00301621304200e006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 605044721 1250 605043471 605043479
    0x30d14010f270e06010303030509060a150b0703050d0e01140f04050c1e0a030c05040e0609060103020607050718020304060b01030b030a02060a020a05060a0c0f08090c041a040203040f1205071e0507 86
    0x24000d0f13a000e07500c42c2d00d00155038102030030600e00d845402803840f2032036480c012030205c0410546e00d00d503084441e6040c1c519551011851f040303800d03020307a110001006040110301c4a040310103401403030f410b60698000d0405a42d9070b84e07007074200c22030603a0054055040700380f43c010541481007a03001c0c0c06a444d42c210901107500d00c041019050a03910595130307000d4118050019240501803d03011a800030300504850038485061074a42d10107200080c4030361000140e40301004000d21100000381210380c405e1119810a61981c006548200c40072200117203010f107210401d40c0284520200e005000d070090090880326400d22055500c040c50b050254460500c600000500c1081020700c101c000b140c0114031041c9445d00076020000e5040070b03000f444070a800b0070007a46d00004450350350003000c880100d07001907501c4401007541e81d940c0d070b0f054100c1e0000081100340584103114450191180f0010810a0000e44e41198140a00701c1d00030b25142062408245914901074244103a50080d015641e6071507503 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 605045971 1250 605044721 605044723
    0x31c0209011709010e010e030c0c0f01110609030c0706051801270b070b010914070305040309120317060301020a09141203070f03020d0504030230030d14010f270e 71
    0xc4403c4840e6030b4440114414009082c0100444161504011810000145805601c8800c0d10715218001e00c40803541d02c069a116080c08000214542c00740c500d941003000e003031902c0742c1c81030141e200c20340f01c1e00c40c000407194404c00403031316031142060ba00d03071401c2e454000449180c140e1007445113070078448814070320714022034000701302c028040020459074803c042c2c50310000b0130b81c0592000e200f242c038040600c40760303144955982e03510034854a4005815600d07881c05a40130381c143c2e005038004140451155003015000904080301c0c98a5600051043d44d800701058240e2203000503480014924080800500515022003c13120030010501034001030034183c590f14580083d0b50503260b500c40c0c4d50300f22060580600c44251241c4031454102d103001d06640100c0d01701300d40c40c242510b045010002c105000992031381c0303403c074040000041d00d680d084c0300b1030f03000701426601d001c0d03004c8084680000642038403050b400340c0443c0e910400d8400e41003000e031307a0000b03c0c80041356038201c9561207041c8240c0c0d604d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 605047221 1250 605045971 605046017
    0xc06020a05090a0504060b1204030201140c04050301050901060b04171009111002030a140d0e070b0d0606020f0d0311250b06090906180709021305010f02031c020901 72
    0x40c0e40d946911101800b0410035220a02d070b010034000d034581074051221081900484428524038914101c0716199460107d00500040d4800e550302d58240b01400042c0c0b110500402c01c40e50701b02e0088c080e40d1105400030303007220440e101c0c050491504201c01c0040e0101010001040301a4105494010b090300210009654880c1001c0710100b040c1031001c821031900c00703000704400c1010f03c011400c1004d8107101514610081c0c0030b201a00102050511415038250440f12034009110141e40849540d02d000b004181c000305c00017007446060aa001c1403280c80021400020400c0b00001c0109103880c0c007096001f0b001002d00790048045c208004402d850303180c004440340400c42d030f1121842e001142442c11a105005d42420301c502c108005019420790002000c54024030840750303403026900401c010702d00d02031280d0b000c040342c50f0020075118006400c030110401110700030b0302c030002511b45100e0100d03147c0c0320388140030450510708181d500032030141d0760141c0f40080060500e040f004c4440d042503a1408 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 605048471 1250 605047221 605047237
    0x1051908091015090c02061902030a021c0903080a090305190912080d05220b0c041d06031203010602060414010b040f050907230108090307080a0801060e03121602010c0602 75
    0x4001d00104100744100c038030411888141600c0900150f0520481f230240e0025101c884400840d0048007044080855a0495160884d00310584100000c80070202d000340015a6041c3c0206520794009840d0100e00d002d14481254580d0394640b0b482c0c41540c9182e10720400490070020040d16080202740c40069004000d5524040d0040d00e4a0301030000c5150203680005040034070f40903070070001c401c1020038400702460340d80d48807003925050350f5515200c18850040b60321400380b0819041e1800d1040b00262000c0b405180141d080d1607100b560503101c80c2e1544401e100785001a07000c2030024010868000c1c1c80d01000c0001000480c5c0c010041d000941034860800c41c0d983d4242c2c0e42c0c1d007408810300b0304000c2d00d001070071144c209410347c0c901c01000c452940010031085050003042d2001560851090041ba880f07507500040f42174464840d00402018a0000d02a040c00300d0602e03a2000072510380010700d94240407404a1303651800c20b0815040c4040920840221f050014507401003000548500243c11f0038 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 605049721 1250 605048471 605048501
    0x3040f060908032a0405040209040e010c0c0606050609092403030d231902090613120309060516061a090103030e01030b150d051f030b15010519080910 66
    0x82c10035580c01804135250340e01c880c0c070746a081100e0b034130030b078501030b0a60b030444208440058447d051000800d001e84011515000a9481d0034000015182c22407990040640210400c0200d151179005000e0345115078880305034403582185c0010480301d080c605540551010741c40d008103140404022920755004003820034103058880040e2840d5030005c11202c0f0b00000248071311a00f0f410f00000e840320700d40b2200e001052151300021180e4042d1150701c2180c00c4001c0030724262900c595a410443e00301100403800701e001031803651001420034865003c0da2110b0a003100502c203001516929000140001c86c02607100c041e100c03240f1b06059540040d40e0740258000d44035140302c0171040300010200d0300e00201840c800c28030704c505409400c80d56819a01c00d000002000a40368565a0394180c00241060340703814124900032003c402c200e051356082e4000c03080c80e003000c1c6a505082c00190380501601b9081000d81c2001c2c0c03540414540b113139408642005503030050310300001c0c0c07080e071443c161141802702c9032107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 605050971 1250 605049721 605049727
    0x1812030a0e0906040506090109150f09061a12150109260d11120306120708030c1905101d07080f070b07050303010603150506040806040308010807081203040f060908 72
    0x214205002010352010f004c890400062401c00300258540e00c040c090950b015030745881c03000700203458040401c00382801e21018140d45903030b80c044001a105500821490701e1b401c080000104070302c50155034070310005000381505035403081c40314100090402c0b46681000184030780041e5000e0a003c00c0c103041c0504281e28504402803918807850408115183d03001c22500d0f00e0300100307203500400c8240350724810a00030b43c0d40c2e0300d45000040415404e801d901201b4020003000081a010000081c8101121481940e4203d91070603101403008441c94000703442ca4100910b11966402d070380c0d0002d0346900c80ca0b4a02c000c001440c1074180d2405101e90040581540080c6078248040e80c100201d800174a0300c01e904500c0e00c0b919540d150b031a40810322800041c03540301c0280800500c044d040340005004082d021a03119950ba4500c155180b40540b0207401181003280040750804e40404d206050711017010007442c0300e0b91101481001648000c00595103d00f05600c1840014000c1c0140b06029009013a0151 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 605052221 1250 605050971 605050997
    0xd050d1404080c0c032a04060b03090303010e01060203070309090f111801351801020a09090b010c051c180b030103210e1215070201050108010c0908031812030a 70
    0x201e86503a00b030708640300e030340580001c04c1404d01300c10801031510403103446da031000402c0b50042409003007035400030440640040304000303c580000000d5030480d9005904501d240c1d982e0041643c030b0740f08070000a400100000b01c140700b0000940c0004840d2590020000780e0045100c1c032032a903507000354240c000b003070002420300042980e000e6603200650780c0c0c0716021404014020100721031401c0c0f8880c4407550381203200c000341c4280d440e8107004500c032002600955032224040b5006140c1d54190160b80000c40ca080b48001d03a1f544500c808480031640140201600083e24048603041c00454400c00100401c5442200d4000b074403c441c18000c003680c00a4684a50443c94051080c6106400c103c0c42d0b1307015284450300301948688104911402a150b4110071101000558203040d001d240300700c42d0f542c20340244811907a0560040d4101c8060200130000644580400c481104451240070107a038010b2001c40c10020600300b0600a1210003090588240154002a42582c01003050071003c00c01c0c04044003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 605053471 1250 605052221 605052223
    0x1e060602070e06150c0a0f020a080c01091403030c070b04030b1b0418020f0304030e0f04061d280606030510050913020a05121c020d020d050d1404080c 66
    0x505400e0020700041d0b07061040b2401c1520004000c180700e503003c900c002c004a5a42c504a685038040d41c3c0603100360305090f041140e1a82c140d240c04a0140c1c40c82c10000030410400b142034038034000c0517591003034050301d45180c1424070000c400c40c3c15810b0008000c80060340c602003103060b00404695100a48039403650501310b0708114000c3c590015100140071010031219210211015103555800d690110811980948002c1c00384805044507114004248818160807006610601c0750441d000403020114106101c1520300c0b0348504c4521000300c542800c410514000c4c02d40c0d0041c0c0d1401c1c1465140c4c50302240540d041c0700016944a5165a000700780181c0d585030181c186d11078900d81207007401341d03e803102207420320703030f00a0000e240091500749180855807001015001803000400c4000000204044903485e40311442e00301013041011845425103a00114a4009008854010b400c0301c118094095500364400368001303503090b58410a68a0300d9003000409805580103040807902c07803901c00c4580b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 605054721 1250 605053471 605053481
    0x60a0f0314100615050a020a152f04060c0f020901030b090714011d190b0c150f0105091306020409021c05042d0c03121b08120711011e 59
    0x1502d15541822000e100d110682c4a02021211503480c0290b44c4000b001400c82c207103803040000820080302140e50b4071315a2501c2e04100c0042000c4c18a09442ea121510b401d01281200300c10504004014402040300e40d0083d8123886481e405003104084610b910350004071100026001150038812040078058000380801c02c25014143c0c0864814903a5180e0300040e020020101141c8504000310421038140c0d159a9503005450040c800001011501c0708410680c82c0c22842c90500d543c420110000025012040c126000b640000005c1400d6400c4c02c080c00351041008005034601c1541d40c1c440800280c8a200600c010309182c0b500503100c0c1200a43c290748a01d4529003c100282424140400324240620344285003014040b010b8050fa0030200540c3c5074010882e000d00204280308000003441099031034020301c0307240ca90300c1004510b98200c2021503101e039010080c001070740c2440b0305907078840588070180e0410071504100940441c4106801c0c25200c0420810103200043d000808002801e4015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 605055971 1250 605054721 605054743
    0xd08100608060105040b0f09040f05220f0f050f0601090501030b07052704141003020f0612040803071b11010818280b13021f020312060a0f0314 63
    0x4401c0301c0e820000002850b0b40254021070070030400020b8a0441c402e82c4600300c030f0074900050424405102100480c1c0024201284c424010320803140d008195046c00d0201060b4040d40100c0503541401d140c2c44461400c2c0e1b0401d0700700da41b485056244015210b0401070f1034000e10300d42d600803802e581140342c4030707003040b1001e4203104c14060180801c4070494442080e01c15070240c0700041d80386c008003480000e005040e000d5901075550b080c001c00d10281003400c00c14507058038002c1c3d54540c0c15200400c10b1124901c103c0807190038000b0058041000120b000000b1070f0015543d180c41c02c65050040c0128001104c900402c40da8140d0440f0b2202d01560408800f9a01c20012903002e03201c6256640629220700e50032440c40e030150401d2841c03005140d55140e400f10003179000301d1241c1d21407410b400748031601a0f664030107900c40c04103000664100d054080e960560210543d0156080454030200845c403c1c001600856001d02c1140740030400301d40350700b6160000c501804180344140550700410781024021a8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 605057221 1250 605055971 605055977
    0x60e01081e04080d06230105210403051b0607080a20160803010e010f0806040f020f031c02010902040b0d0f080a0216060c02030606030d08160309050d081006 69
    0x10405580782800089410400c80c1201010903075840c5041826841403010310b00340c4030f1030b040c404240303502c03203050240940340481481010300d0214801910203001d6214015034031204000c1e01211040d00900b40b98102d84603040c030b030f4181403481c0b0100480100c0b210101041d540710004002c1342d240d00c0181d6582009120508010082a5004944051f522221507008500b00024040046501c4c8081c224840c0d402601854407543c40d0002c0080c103c07000c0c8600c070464803180f80042441900440d400d401280c0c8010001d4940880f50b0910601c1c203c11440c9035407602818500101049084901e85140071160380000f429900920410040314041204580101a40f2240000095440c40e2641c41300d80c02c040955200c0780001412441d00d0316140480300d40e141686070014001d034101004d00d082910072402e40b0510fa440c4000e2641e40d0641c11070340c10000300e07050042029008907022145125880d03103401714800d4184d0f114185009110200c68000070241d46c10010b076502c40e12010b102400d4503207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 605058471 1250 605057221 605057237
    0x80a210e060409022a0a0203060c0f1b0123190b03030f0f13030503090a0e09060403050f0f120901050726131a070f050703051e1c0501060e01 62
    0x403010a405020314000e403a186039001521480440184501442d48415000d03000e914140c0e82966640320241403030124020301c2444041000c3e80074140c10f40f900c00c00781d90740c82828400380042c456990000f031031a5011a55943c0d1001402401d101b001189800c04030102e01c3c5141409100501c0340035810400707540d03152505d02e6101c61981c001c41221846030392814910f0b00c541609000080600c00c2c840c207010101c4d40a10300000b0044080f0140008601c21074252180c82d940716924180d9407012940c1c4150f5822400018001a010305c02501209000540c07103030134420b48444042c11640440c0c409141624508200b00c1002c0090080c44e9222040d445d0000d030010300804110481c0080c0030a102400c8103c030002405040e11f4180312400c2c58004103060102000304055500641d826a620000100d90481a0800c03d004e201100c4020760b040d9951460031883c210036001a2106492950140c40e04000e142862002a0b43c01d4407108801e03030300007806525081000e04003030400c56446051110103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 605059721 1250 605058471 605058497
    0x7050306010e071403010305010906051311090405120a03290d11030127060501051207030206071721090a08070b040f080a030606080f1b0a09080a21 65
    0x450141d044520407500010b05886030b01054070b402c0c80c0c505000300d180001000020902c80150814003e050203100308200649500001c0c58400b0703514070300a0510f2003520414403003801c1465129900a0240c0141d5a803449104080e01169111f0081040041e03125046101040f652000d00d048001100c6009101085404042840800c001c440036062000c04500030000785c9080d04451240314501024510301031420091341c4494044d5201540e0803454440041070300d0410000f190304400c04500200b9165286070300700301c400e501c4040210f6010900391007d19000d0220b4029042c0b0201991058011701d0f07100b0f107945800400103004640c1c0354002c605440104425000f01c5004035000780f224480c65540d400c4c0b14000019503000200f6140001915900b642d038558004c0c400d130b60703965840c507a041e22642e415840850042d1840f00c4449011030301100c3d078014030401007a06242a060840000d951207428a0401110017019915030078852204040d002603031103101c841c2e403064103041d4050001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 605060971 1250 605059721 605059723
    0x1508010509010e0f040305092d031b12030405090f0601021204120807030201090b01091d1c0c02030703080301080321040c061b0212030d060806090a020415050904050c12070503 77
    0x1020b01003804c44080030020070281441203044820088026014110316903054a102c40e140038422880c42ca074201c010404c403540c3c40d002c90301183c0031142c0060750011b0f40c2408100a488075400c170b08010340d40b00030400060a1707100c1c490010b11440c8820714940007860020006410690b41c410480040e2030104018800c200301680588001034111400f907841d076902d482c040e8010003081070058802d20744440001418196a00035050841071010900043c03c41d0b1b460305a51003407040d01000460ba102136a003120188039881c22141d00e4002030864903070715600c1d111550158020b801898080e00001808801c0718034502c1182003000809a00d00c42e0752900c0c2e11815403201c0140034030420850700c02c4241d080341131640758440466070020280c18554000401907556640190713038443c002410804e00289092010504510914442707002e8085811540d0030030000f040e00603030410320b98000503004502a20b5144205108030300c940d0080c8001101c107810090038681d44072002d00a036110b10001d11868074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 605062221 1250 605060971 605060999
    0x201050c03044b0203010b1009090203060d14010209091b0702010f020102040906120c060e06030a05040807060c0203220b070303020d02092e0e0603010509041506150801050901 77
    0x1c0790040000401c0e02c41c0b8410b507041d4054a8901c4401000c072503c425060310200c900500580c402c5000b0004003071240c0c244407142c1e07004280b43c004254030300760810924205030021644030f000240320703809400441d5903000c0080301403000400c4a0307501054151060400718a1190000e030061480010071000f80320186441c400c02600030b040110b005a0401018001d4054501030301c60314800748000364031070710160074001615005903003a60300f101e000100d26000710110800c0400140500707285596210744c58001c0c00000c0c1084800860400c0790401007204d922506111583c10703406541d4032800300085091482c2c081143c1c000d000710a80040104814600480e183c059042c02c016881d410407201c41c2d4002d0040c0b028880e0400c44c007a5030215144116042c19981c8588501161545d4008040403200c4000d2140c81a8118100300010301441c90540107640e030103840742c1d080c0600100032540c010269910b03948840215640c003042e106c55a50040c5503035015103c03c1d60300765020361400c07100c280340c4a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 605063471 1250 605062221 605062253
    0x60e0a030f060f1b210501061e02070305031201090b0f0303030a0c0c0503030c030708010803090d080f1c020c0706020f15060112050f010906050f1e270103030201050c0304 75
    0x1c1c0d5180c0f00c882da8118507401070444000300d28109003854a0303010000d803003e0b14031220803e80d40c0002d40040c01900c0c051180e141079407000e6407110014021030800780140f4a400d00c1d442c007903124188000001550420090032412041c451640e05545402e0a120550340f240c0251440380041104025040d10000f0a6960108031a00042511140200166051482c00c0340107085408000108940d05603250010743c0120078550390511036030307680e81c2c0740c40d00d81c080d01c5840e681c003550b04000c6a0102da203240c00380101c80750380f5054501e0312006444ca103070050301d0300c03105000203600440c3c8541c81e5403052010400600e0f042c00a40814400107940c941c4070061400754040445a00003c00d825074070a26083d09031425401c01040342c2e003464010a0b449220901ca0801020300b07140c0049010b040802ca0001070704000f402c0c1219005003002d50341c5400d2403042e115904240103540b80641c109450300305850800c856103e00c02c0d2541581802803d43d00001c0581a007141c0c00c2050100040149210100e40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 605064721 1250 605063471 605063483
    0x80405060f10170a020108010f080a150e06090109050118111026010801110c0a170c0a0f110418060f020f120f0609011d041416060e0a030f 61
    0x550303118030042c41e22040039040001d1212505078010010000091180111030007601d60020f0f5a81c0da00b0300000143c031902820486030040c1c030020b800180c240210148202004034042454042107120300d140100c115100c80703250f1346400050381802401e10038410a12000c041e5070743c1c1742031b45407070f1842903003003240259000c3c6020880c0500402e00c130349581c510300c8800c0003158404512500003a40410001e0040380d00552130001036601c4146801c0072902c1501002d00905885221921642d082c0200d81e031144d075031030f03004010303c4007500400d1040b5a02d031441107a115219080b40e080c80c4200c1d9420400842c015440d102080740b01040e5114007400300d9030f002501082c500c0802c88070101a0080301c24800c1e2459001ca201c40ca04001d080c00b4502c2002d10100000381a55518100314100d0401e2188205c144c2d1028103500c0c0441e80c40c07030700035402030003000420b0465043c0c0840c40d1800141024080415900107400c1c05600e502140c0c246032404202c2e0703407101d014116118100511034090000b040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 605065971 1250 605064721 605064751
    0x121104050f04060914090709140601050a020c0319031b020a05061303060504061a03151f08030a0801081b090604090212010609020d0b0d1a041b060509040c08040506 72
    0xd55030b40c5400900141268500500c0510b0740d40c428a10039490a603180c141e00d0242c08408104002944102c64000112500d54109512200019101c07584000c01140860042004254143c0c40410138035051f1507110054851000b41c505004100d614034064090a41c01084040740141e90380036100400c1c0c1e001147d1081d5508801b0320f40c030602c0c000660009001e1070030300013000140123440d403200c00c14103040070055203108400010503450395070300c0c10307458032203d481400306001d8003482c59102d4651201d45242c02c4065103c00d0b81c245541c01c442c0400000844036001408440418070030194219260010a11070030300d2030000601c0c144009040314026a0384000071001c0d560b40b002000e09560426008108045c1c6070080c54019500860b811250642419020480382c20704190311a440340d0010804405c006100007815002c40010704280c0740301c1010258034040759801e6619000418182e11400d40d1040c20340d041c00165800403020b442401200001c2001060f80071801d607601a0a0401c5929 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 605067221 1250 605065971 605065999
    0x61b0219090905030a0801091517070b07141507140d0603020d05010501080705010c0b010315110a090608070507052121100803030103170a02010b0405090c0112110405 73
    0x8400e0a6210910050070000c1c0c800910901100601ca4003982e6510400b40da80c0312640b00c1c0c181d4040380300310300c8030b004070380400c0202d00c00b6000340301c1080003a8002e440559541e0995500c40344c202d104241e840c1030301f10f60709500600d01041a0b000540481304844020f01c1c044d94040c0c0007480b44042203407122000203d04203800c28030b0784a80c0241d54024807001030807140d42843d41c020b0400f4020640981301c1d1610114596000b16080c5600683c4419800d00c0d603800c6554090045c00c980d000c06c1c01c6640c8403c1182460003140001c0c0504d080030742e6444a4507131030540e00510a0001500940901c00c04001c100d01041010449025102118070701030150b9054202030012031003172804900d000300500b50f114bd40480c00e4003105006000648114803107540310925241c070381c8028031004001c044002c00c010304040c03c52024005044d1070780000642c0c4540c4c02c01080548000311620615500300c42406105580c0229104a02c425404d008102119469102202134410740c00b035030f4410219404041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 605068471 1250 605067221 605067259
    0x901050907080a1e0c0f1b03051c020301080f010b0d0305070b100e190605040606021c03060f060807020d0c11010e03030f040f1706150f030a021f0207061b02 69
    0x66249044c107240c2a4007002e0116440004010ba4120980011544400020782d03d20804400600b04001044260502c00d659019140c0340c0c4038a03040a80550f000c840b10101d50032600c003540c0240030714000b0300300304098680c00c1d074212110509800d10440041a44c0f1000c0396100080da0009136210000010740e48490072580f140a100758031a086c100d45000030801044c42031010282002452241841601d464508010696500d401440c0c0182e02020050b00000f07420764205804e103002d818006085a00d030034074204001e505030030402c00714803030406109005604000d5110700100515000d41002261307524800c045c011410349504215080b2003d243c240d0f030a008803209a900c10640302d5480307685094100003030109200e9074100c901e4a0184c041a441c0116a103845501e0130561040300900e007070b00b0420200301020030075800d48903a0458000689401c40e4454115144680d8036040c103c5280d4005e00c0d0442d150009010403880f542e2464464550f2801c00d0303c125811520841c0714444003101e0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 605069721 1250 605068471 605068481
    0x20706021203010614160b040c09060803040e070e01050c070605091302071502030c090307090b01020610080709090609082b020901080a0f0212010b071b080309131104030b010905060901050907080a 86
    0x9044287c40d00c081c00100302c00b030103220b4220780b43c40509001103a528600c0c1a1a402140b1030001d07030104a0740010003481c0300d24a940c4001505040090030105e0041c0304600e042c001340c1002010800c006904006442e0408a400e45001c100c0419850000f040d550b6604102c0700560b0049803135008000305d10103c2c0f05c1400d5400d134010246c215034040d503441002a0141116000c442d01600650020404100c006004402940d55210007403a0161800f2107900c0103042e1441c081d10f0180e074441111001038644c44c01040761890b50181d0354403100c000704248020003e440e12345c10070144100300443e52039030041e1181d5806169400005400d410041d60b410181c45011030200c0e48540000c008608904200e0140c0122030103840c01d49101e042502407580d40301c040c1d00542035164800c0c848800e1519003d40c0520300e1180d00314012900842d0414001003a400a0300202c3d4802d94110040c040d41249228140e40300c0c0d005c8801d1412035142202040b905500640141d041003520710018403002825009 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 605070971 1250 605069721 605069723
    0x2030318011413090c080f0115140f0a03050c04051806130501030f0b060103020307140a020703051902030c090606092b0b06090609070f21090302070602120301061416 73
    0xc1d981e40070581c0040c000d0f8440381c0a02560381d40b030030340c40000e800c2c031070034200d8820103501c1c2882c1c07002d07400d10f0203001168100340300310030410040742c1030350074402c900c60003034100587d400b201079032140c140013406020f540004002c0d10a072a024481003001d941c8a403059906000e40c540005202e441d41004980098481d074401109a030030440000100210821440d58050260310f08800d80d8031404011401d0b0720064403e9800606000c0c407042d81c554900f0010520000300c2e00440d0000d55a9580b02410006042c1701039007800c408590b00c00542c102444440c01e81803049030007494a00c4c0c01c1c000941c55004805070f42c2e008000112100f62680d20a09110078074a401c5d00021000c40000d14004001d200110364150040001170b003c00c015042080510740511030a84581890282c110000c403001c80316080d04005c03607400200e0701c07002d000261154a04241c00307580a804040d0501d41c011303103064000c5c03a101c007070070780b04000400c03010f980710b60b0f40c4407001e00145249035516a40b0020b0300c0d0401c550702c8 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 605072221 1250 605070971 605071007
    0x90c0c0309060c24040c03110402090d0320031329030f04031103090a0b03070c0b01030c03060c0906020c1005070b070804140304211403071203180203031801 69
    0x510314405500c0018440308124900300f200d40c119502ca46101050103060b90004e01d03a40c46c00301c0031b00024440ea81030f04a22074000c0d0006046c00300b420300140b550340f120082a004591300c072010880400300011006030b0440c0c40b40003507181215450761148108124880d0406400b44943c1c3c54550100303e500810800210000294407400d00582c10b00740716800b982e04038003062031550322541702e0f4808030664440c000c0c0104114512840c10100c0d8450381e00040c00d0404020389500301c0400108a240c80d00d000c0c0d07018076213224070306065280c10b05c200d030341c039410010500950802c2080195070000b24098402c1c41500e521b902110f00010988032801030200051500030382c00100700d6000d030b216003200d1086020390814201c0b244008010750b00da101d24059401443c24030702d04030f800404c034803030b280d41507c2c41481000c640304192802c0700d0440d0485e0004441883c5d180d2801c944690307040c0145860791031058014034103480340c2e82c0080c2e580d205c0d100700318038aa2030079214106a82c1c02034003001c8600c03003404 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 605073471 1250 605072221 605072227
    0xf061210050904030225061205041e060902030606061905090d08040803090102010b0114070f260d3c060b0a03060602100908030c0c010f0c0806011b02090c0c030906 72
    0x840c0280d2500300e07003030b1079074204114914401c46c0411484007220450f0b500b51a41d007448503150148030b000e014000d0095075000c40c01d00ea078041500b07401d000303014000c0c0115070020360b8000510415042c64000341c41c65200358004d110307401c0000c11030815015811001e08000d03540f100c003813001c143e6541e10003001400c20800414000341c0302c0703c00300c010004a802640204031082200c001900c000c0001d5050f640d01d007100b0300125000950203c0641203140c090400517400b4602d01454211491500a0310819441c0c081001404144030b40203002e0b207d8800d540d0a0358050740d4011280f10030404c03080694924513003c040094045881d40050042c04001c2021a5900700303941016000c0c002c588180001803060741019500307500304d44280c642066200503440d1a64407144500502a080407402061075565241e038882c0c00c138528131440600740c905449640142c980400003409041006030441c40302e0145040e804c00581d900489164000d40720403046484050a000081c40c50150140c0e981d0491000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 605074721 1250 605073471 605073473
    0x40e0f0103020f210a0b150a030c0909050c040c09060801080c0306072006040311240a0b0102120307090e0105030609060c0a0e120703051c02120304031413050306060f061210050904 79
    0x40120903c1400940e0719090074843d80e47c00d0000074802c610014021200c81c0f1401d0003001c010317400c81239803680102c0c11070308122180d10004046850242c411004074015440400185800c8000d00d801060fa58000d00b03503030406103001c00d84419009084000b001002801078500d0080920348001c0c080c0b80504903001840d00349405481040c068030744280780d21418440600b0107011440111841c080321840c0c1507203448484014019141032803a050560054000766128001d801c0c02075441380c0070302c1d82c521200c0e514050300e140844c1e80680005020b07401040403c11112030009142d90007440410007580c1d56521000100d0b000300308030b03030754070f900c1113041001b100941400225031060b01d00410a490030f041c01c4141c2c00340400b506441120140e0012170b10a800111444042c582c010f01038100b4002400114107054030303c0d400200302c0c41c000b40d03401c4400e121500b4108103070343e4414019a40d5074000300c2342d4000070300703680182103100082030940000520250f8801e2040001048094502100e600706 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 605075971 1250 605074721 605074733
    0x13080604050604200d0b060a0305030a080a18030206060f03030904023f0c180a06050a020709050606091c080304030c120512191d03040e0f0103020f210a 67
    0x209072020307581c604d03103101441d01507090420741c40204a00280012107195107650707810310424000307080d02da00c0f2080c1100000440c106100a040101c3e240e40d514281d460300e50340c42d01c111603c0560781d030110b048142ca6480040d40025409410560840f110b551003081d8000003443e5104007000b81c2d811a001148541d4014810820384501020340c039485c600c20020014000b0b400041080c2240603881040003060040c0c1c003100080c03404100d4000e0300c101506402010410300f244070762000c40083c800040c030800b03150703050242d00080c1c000d03501f041c04981494000900035019000300355109005000d181d010911113030b1640a40c40e944119001d0701c0385094140540681000b031429607441030300d04680a103480c0300d00c00b101c0c42c100c454907e042d0180c44450000d40c1c20f644d0000040481c03640c9080c4503294480c1e070002e03010006103c20055940343c0c1030540e08001060302402c414081e500c00b100606c0140c0e100074620120700c01c02e03039018107140c21911480301d2084440da450342d01070244c01040010b01030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 605077221 1250 605075971 605075983
    0x3020a090902210a0212030c0106031110090807060f0302093304121e0f0507170a08040905091510060305070f080601110703020402040e060a170a0201051308060405 72
    0x100842d048100f0414043d1410440d211020054010390003840f0002d00501d8035003e000001c3c6011030072207041c150078103c19400c59290350001e4482042055800c170042c5099481c41e11840c1c2c8030301e00403001d02e02d4007004540e620302d6402520203000440c1c50704050a440380e415100010740c01088144503607101c02020b022017a42d0451301c0c1503014003440d146202160b02d0111811120104404002c0b104662a40500300005c0400000204003010030000460603803084070120700c0c084c401400c180d5244c140f03000180c003050700c02000c0582203114600c0c0440d2082d0b0a0340d04071052070300040303801c0da04e14410a040041071f0300e8681d50915134005009244403003170341e464181d81c0da07500c0801c541d8a80001c1900c402c200341540780000f0340c1e00c02c0060181d520a440c0c2c51283c1090100f1035000302e840391b000500b03030703040b68104090311840d075000c205e080d01d8210b80c000e00511380c078280785007400d000800c683d8480e000700d40060305000340020140074240802c42840d00070415001a101542840c6c9005a2110 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 605078471 1250 605077221 605077223
    0x10b04050111031603080408042408090d021002070812090307110409021c03030e010e060a2007030e061606090308070306050a0905090312070215011a0406050d0603020a0909 76
    0x16512840c5050b00030000088074080d0000c60524892450039903000c03101a04003c004444011040c03100003181505207818a000300c006030301c5009580101d4400900120703001300b0746070003544490706c00d030f003060b0300030980d0000d440c1a02005680d5510714204202c3c2e034450b130f801140d4141034220030402c45000c040040c1a0440c881c400440f00c2d00c2070352080005465205ca0701942c0142c80c0b9161800101e000c1d04030800e024403a040c0411014111408035084a4007101d02004540245d82040042c6007944a8400c404400703614011038100c03043c1d6080b89900580380000e0612003000004c21103950791078241c90748042c1c58a00400800d005190110240046100450100b008407003c550b40901134002e5405948014000c41c44162500380058017410001d8108501c0f03000410035141403000003003001307100302440d80091811032050840c001450005a01c40f0000350340e86000c40d01c28060160031142212410700d4025155218400c0d50340003000039500003035006142090004015619800c503c00031 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 605079721 1250 605078471 605078477
    0x906020d050a080114131508071211130e0607030218101b2402090a0e0c18131b090501050405031510080f010501090b0d020109061412010b040501 64
    0x291140c820a50301c0e8010400c034a4080b84a0303000500c040003103046140440701c0024003180e01a114070001b9000c58040740c0c00d000c0a442c40c101e081c000c2c41c10400c00d00c401448100962aa109101e071504e41c0c0c800080c04107030f44202d400d883d05440455503a003005065082210a8441a0400f400c025000b0f41c0a030500071503c41d0b0300000c1c0c090070316054196580090040c7c945040c80c0c861609141c004000d41081101c085100d41e11012059285403084442c1010500300142d581d07641c1820040c2c491141d5101100c0b4400786000c02482c8007150b002d45242e071060702000d8914070039003400940312040109108100724500428400c801e080c00c00000341c14103443d154892540c0c0c94030011565031003a1300515805605c190cc00b00d50313158420054540c0403559001d040301140e107a2027024105038106d5850b0324145c0d100e03001448050454420610006000c44c0c400800121700c0c0d00113001c001251050a00b03200c0d0340140c69800d0010310040710410024100701640c19a140c803401c1e004c40d00030380656400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 605080971 1250 605079721 605079733
    0x30421060501060f1707030e0307060c090e15061e0c06010906050d020d122007030c0e1909020301020d021605070602070815131e1a070c020913020a06090602 69
    0x103050300540030800c10382e0b159901d600d03040d281c030041750003404000761001c010180d0b90322410040b00c1c070500103804018400e003004201485a84001030200c4401d42000c454240d01105010340c0591842503616680d01c160ba41544414044e5685960200d903503110001c0b020000030f5110f03c441c2e000c900c4d00d05880c29a4010800d190f03d9600703011303030b4000310b40c0001e4000211503e0400450080c5030480745a010500d440c4001d501c42240354041c1c44107049980c1c49590040c00e0a008200c00001613002602146040440c1c51421207203080b0b1b004280c00d081c1c65840d95915460081d0748081d0100c40d443c0c110700d98295a40d4802c2c088404d01e07518041401e8849025100c00480d807648080703440800c8440e024010026019801c070748012069016090601041c020f1f071800d400504282d42044480008040141e004201410701c004542e001010b0f4000080d402000c1019154008960482c2a50199031080c060390302c10049005503803030700d140030b0b501c41d1f092040021020743c0441b5400c182c520b5a400c3d109 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 605082221 1250 605080971 605080979
    0x2030703051f14060d1d0f0606062106010c0206030903040608010905060307051507020a090507030b03070302060d11162402090a0302010e040f0c020c0f0117010303030203040203030421060501 84
    0x2c1c801690040740c00500500000791160b141c254040c00304080030070300000b90600c4030443e01d40071401e00c0004004a402010848071140d00034820030394005030a440e00e52038107048800c00c01d00b0305819405010401e924a000c140b003640300341090003034a98040c125540d00d00341465826525005486607030300207108000007103103c051034001d40740104000b03402400494203010401001c48020840100040c80c01c1c0a1040581d80d456038000080c245058005030a05104d0001002c0d50100400a4001e03030100000f0801602d50904988184072424400120034160164500a610815400e40c13180301016070701d08248a10303004420003c000c25047d80b000c101c0c03138081781c100780d01503000390551210307440d00c040003d540a2401800e0f00c450041000400703c05110a1100711400c10f140f15006074024600d041d03050910b03c0b440d40d00e80c0c03000d00b065042c4080c00502401d6414050200400701600440450210b46003041134401a00c20400311001208858544582107001150305445103820240002 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 605083471 1250 605082221 605082271
    0x40519081b030f040506030402060706090309030212030930030d050610090f03020409021c05160f081011040503150613060806132909060108060708041b090203070305 73
    0x1d01d100c3c15401e8501d0400e880c181c201301160300010020380c1c01450405c800c40c0001c2e0507115161506100742c4a200b829421801400a04100c2801d00b044540c0200300800316a500e0303044c4104855809000e0840c014603482071165a03020b20a2050600e00c00422588101d001c1c0360099482b40304180c504040c20481c540d0103e8040000e8810317108410800c49091016007407a030070605225001030140310b0311100040c1c4141344640060030a45042d000a40da40d00018404140b070f4004004150904e1202d074206501c00e070f107905041c05401001d43c1d0328000d420140b0094416500203000003425141c515103c45148005c441c42100e4586c801d44000510b8100e40042e8811030741039a1041d0001e04803542d803100f8142061961105c01e0710302001040d20011132680424080390301541d10401045c96041c07040c0b205e403070700030180c02c00c9049802400801c110598445070b115402508407404801d03010300140e01006e00e016980140d141c0c1d40c000020003445540540005d0700a0340c00420594104207180501 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 605084721 1250 605083471 605083477
    0x1119211d03160308070302130806040510110909040f08130f0f0b180f12010b09090304060e01050d14071d0a03030504050103110c1005060909010c0207030605040519081b03 75
    0x38102c1600b03808407900801d205000c4640c0c01070190600506e00305841c03440c0c2d050924103500c100c04952101d010841045400d020080c4000142903050040c04002c8a4ac015a8010740072503078065410080064244440000c14240311600020303d10b540e40364001d01c4680345110360003014200b481180c80041ca60784280d1000303045421540a5900713250b40d02d074800c0300307400700140300b282c3c4048805046c06c01035941d90501c00254203141e000042c110490340c03d000c90740000412424803900700348230170007440d0b400ca4080010948c4c240b80403940d8100c40b4005c17a00034a03402055811142c03001742002070140d004540501c80b014518801d00e03c5020203810410003c4032400002c00050041c4010015940a03800410055401851590504000d45151407401241c050780139085a214803e01460382452400b154001c14410f0082c0583e4424210107560f0f001c0c10320005103050b60703402c000b50074000d080c400e00405240b11a009040300c50380d07040c9412140c10100d0b00c0c4a003904d0124061749000b03000412 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 605085971 1250 605084721 605084737
    0x140d110c010e19050a08090f032b0302070b060d1b0e06010801080a1101080a0b09091005160503010b0a0c060c08180304080714030a0506070504030501060501031119211d03 75
    0x1801490143c6d5511100364000e9080207800c29841d104840d100c2e6024440c80400321076010003190941000d494600304506114020402c1c188100081000725400c01c3e912503201b001600c0ba01c9450f040b074a8442e1020b840001c91022101a203140407030a180795018184c094002641c90100e1030340c840120710b03107807444c0c040000c1100c5201448640603500030521258032400220000400a44580101e00001c504840410164200e9080d15040420501c030b159004441d600c1f80041c41765140a015000348410b000300390700481c0c00b184070345815100d14039800801c7c0d4850002e00a241d590781c00a00084030035035254611020301d840101005c0000000c3d03404581c203520041016510303180425400071030303406055826003d205080b90201c0e00400405008104c16074903a0f541d2865828110b08640c682e0704142d0406042000380c48000c412101034401c03107030009001e4240540e0458003540c00110014010044060052620038004180c1e0702807004106071442440b01d083e48068500d881c1d21031604 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 605087221 1250 605085971 605085973
    0x50120120f0613090506090d090807030f0213060303080a0e0f1e07153605040e01090b1905060d0b011502030904020730140d110c010e1905 61
    0x1d8240c88507025910340000e00a01100483c0382490000001e5443e400f60641d481d600c1802480541c0404002d81c4100d040a8a00f280300359040880e01526501c40744400780610351001c24041c155a5003605024041e6942c900400c14076950303140191421504a8040c884c3c589840318618441e10042100d18280d8600409008150362103180030300001d240e030090741007034030481d040481c06444075102185101d07407544481382c0d03104042c01541c000c080301040c52580010904d4034001440c0f0359450781c03000c0c2c410440b000704118540a02c2d850040c0040e21000e04280d0a90091201c24842d250f4050314401c1500c00906c0940d8500c4240146105002c40040001d01c000004220121002c04842e511400324410340b803174280d1060000b42640c000c1203058803890000d64104010700c256200c1020000c001e05503120320340100e040301402c9555018100480000c000078a1500b0220591103d00100e42e2100283c0c1c4802c7c544007814000c2c94404058045032161f502c3ca17107019803105a101066692100c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 605088471 1250 605087221 605087257
    0x1b22030605180c0112020903010f090c0f08150406090b010e0106170907050f01050c0106240f0207150302040e240307030b06010f0c0206030f0a11070c030f050703020a03050120 77
    0x1001110511198100d0143c0b655080c02411003032383d030a0192a2002d031450f0303c003050700c554504100c4100401e5600a00b100d05004408201041c40410780041003c1229040c02c507980e910b0800301c0141070300030002040e0302801400891030449140219058a26641c4c030036402c032801c80c038010801c3c481550b403500140e00454042181d443c21421081480106140287c00c242446a61609440b060382000e0910400034101c4040701d0404c111401c0625114503040282505562001e5200c0125000c1d442c000f0100c00c00444615000c1c1e011140148006070f184812071810031a410700e03e2425030718108441003e20a00348040c5000110102030380d4020810300e403140c59210054550500315242001480000364100d0003591350807015600c610019140c0008030714014030020111490064103001c00c04c2c0c1484150007040000040000ba40d92003410807820000d82d0400342e142a01562009500000c072090200822006402c82d80380c20043d1a0390003030003810b4101d1980030340a862030302e900a000c0a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 605089721 1250 605088471 605088493
    0x403030212160c031a0703060e1302012c100c122123061c061d070b0417060601082a0a0201200f031b2203060518 50
    0x40034000010036041010303000641e2481610703081c0f64410348460326034032450700405c40d40f84451603018206240400c82c1d2420030340010359642d406843c0220400d141c0c01c0050842e4010b1a5954000328902141842c90300c00e82000d401d14280028840d020303045502070040c10600840d9082c0c2d02c20781c000c4524100c01c8101c48104c440300c9019282581a40300c60030f201490b500c2d144a0098082640381c0c425030309911035080b101c0515000f610050155024042e40a0131048007230248a64a034846004284081c1000c110744610303021909130001802040c9000a9500c0c828000304100c0b0111503080107901800069191624012510180030070081c41c0010300240600c111008a104011204440a4594808211103030403011a450250b999981c030b800b521900341507044288110980713110700e00580744071010b0560001400d8503c122405422601c80080c1d804c0c1510018400c1c0d4000c10003200c802c0c0c9012110311581d01c000d0360328902e4140403c1e21690003001c0b44c0d030440d529070f0040402c5510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 605090971 1250 605089721 605089753
    0xa1b03030e130f1407030518060105190f06020d080903040f03020103020d092f04020c032d0d051008300409020304050304090501052b020d020303070b0a06060504030302 74
    0x104240d280390030f60390b100418050000c1d21680302d140e403038a0090582803130700480c050211500078058008402d01c0c45040c0744a4480003610b07c0c10340d0402d81d000d51800b0101d13084400036040c86e82101c1000c8982e20b4011408642c00581090304c00341c681d4030441113842c0d50241540300e00c0b5600543c0740105003520b0034000b550003900201000c9400c01000290100c0c113440341d0f070060764150841104050700501800680d2290704c03003401c1c82c080484003185080d007102c480350f549114a10102140e031089a000600350322001b0700ba801c10000c80c040c45661515040035510040030122080700165100c2800891018800200c0510260080000b58040600c0040000c0000a00c4820140d0864208070220300041035001a40c015485030004540303650030a0402400c0d900140c002d28002c81001c1c0300f00381d1006100003401c040040314040e149044c2202e00101e080303d00540400ba41600c00010f10000308000c8600c52031144010304404c02c520307078858604031482c3c4a10b200150050344030312080070103c02d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 605092221 1250 605090971 605090989
    0xf020d0e01050d0e010603111503010509090c09090c04140601050714010e0f070503012016020402070b13050c3f010606092c0406090f05010203090a1b03030e 69
    0x506101d4142494543c40c80c041d14910007026050307035140c0400300100205981742c1c0c0c0d80508201d900e0040c000706500000081e000503c034880c82010036502103801e0202c140401000c0c0d000c082c2292031246054590540d861000a2080d8040d6160000143c0480000741c191400713810140e44041ca0a0415283c0c03100e9044140180c40455599009c0007010320b504001400b4000c0000024103006441c10082608403000403c14170300c81004820707013009904102c8101c41c46100520303080c02c20b08084c0d001080003402050760003403462001c0360922210340407881c0e20080051081d41120140f100079014810b01c01c2220890304d6603a0000700da40c0903890a2151404d0b0702e4000701d8544555a0341c4144d1007800d68030281e0045001c0ba90b552001d0204103824200c011540382c3c00711100c8415180c000d03544511340c1004001911b1a944c0e420010304002a604520540315007020003951a8104510340d60b480c0c44071500c01701d414031402d25910082507a4486446c08680d050380310003003000486c40522007110 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 605093471 1250 605092221 605092247
    0x5040b0109091d0f03041202060a0207080a081b211e030c0c07150f030c022b0e0102010b06090909070e0a0b040b12060c0f040e180105070f020d 63
    0x9410080420200d03410302c10034126040c1c503e01c0c0500420b12a814600704020b410129040343c0007040b05000ca080c205404840280d8140c50840d9107200d40382c4200d013040a207801c8290b1380d0281124407010302c07500001038401e5212207581e401102c2c0c01901060b54801010740100400c80752170020140c4001c8000180031800c4144400030a0442e09102e59801c540c01100d203014004400300e0140b5030030204000700d401070a0b0b207440006000c4815038000c0e01c004111000d0f0010152034083c0104101d100344012039155420460051009441ca8410300141c1401105032000034411030f4108260340c4140602a841500134005030303c5c00d00c2d000e00344014180010000c44292040350070024642c00342c404c00a100f00403d20300050a00440742c2040143d60102000500c594812801d06880e95404682d20390400d483c000d549546205095111409018035070250104036101c00402c980c00b20140480e0395501019002000950345509040e102c1903a030f09030120060340200d00320003049000d81d00da02291 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 605094721 1250 605093471 605093477
    0x30a0510020306060f0d271e03030605030a0606030302010c090608180c090c070203060f0c1b1002040605250b150d0b0405241506030c130e01030b011e05040b01 70
    0x1101c103190300e40c6035544c81402c1c54000e250341c2c7c11401c0202c000606003a0041c40301d009a81c8400c2200303454142003488200d042c8610300030140d030800109406030780100020f040103400c0d21140e82003420050020801c0c0d22050f409035003440c404444180c8104c0030041503a5003a1100041511741008500c9028481210064588217292a602d55642c40781600c1d48907120300c03400a5603400d100d105160070f094000d0040c0300700c00d0000d414019500b03102415103d0700882e80d0884002000c1e031000325481e0181c1c160040361083d02c00180030407950340c0003000f0141c4001c64401c05507054a072401e8001d95080515001e8403030320700c01000c03a800c501c240219a07620b28000306206400a056201c1c09106131066800b12041d42c4a05024941c9100200700110038001e0102e40601034a440c20660b60004840c0c0b1000384900c1000000404810180090b60301c0b824021194044842e19400300e11081c44c42030100351850f031340c0c0a0000803c403d034005040c08c401d5802d1550714009180209000141120b910701da418 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 605095971 1250 605094721 605094727
    0xf07020708030f1617040f120201051921091703010503030406140913060608070e130b010207080d110f0118030503060d02090c190306050f010e12011514030a051002030606 75
    0x805c1481510940301400102c1e065a22450041001c2070038010350301c46000740805650440c05070703800c1400c0e904045000c0342680c0c600004004110b40e00f5020140300c030042118285d007109002001c5e4414565284240300000940000d4070004a05000c24407546034181d00810051055910480c0314032268081d0b41c0c1c015041a400f04000b9a440c000c1d007200d104020348e186400c11895510041e110341140c56401c0406a21a000f004078003807545141d000001c050702c51003222500c0c0d10030030811000b4000e02d000d071140d140c1d07080070050a088a50507400c000b88a401011182c2d1013040c400e4904540c0314080c80f03ca0384225035402e5030b81e40c10051100747d02545000210016868440344144141030703000041d80d45104554000c002a0024040701303080515102080c09036881d1855886007850003402d040a030304507500300144000d55030488860b00e40d4289410742104441d100306220907108070039104038101604e14141036603555075240140855005411a8003d0041d6a00454001d04060b0074689 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 605097221 1250 605095971 605095973
    0xf040917030702010219050304150e10020d0c030e030301080a0b0a1b02010b19180207080c0f0109020109091e090309090c08100f060c060b0103090c0e0f07020708030f16 74
    0x12074200711148000742c0d40002c1d84000c0c42d03100b01c2d82c01806038000d060a90840c01c1c60b440f1080424182c00070a401c296403141407881c608810000c0b0341030302c03d0804040d0741c0c41032803240302d80140c80e0408105c00460306106040900007000b00a50341070310381030801440200200d850713654800c44003800c0740c45103030b40e40c240d0300416680280b40301452960503000820172800c034a06118840d0540f04941d80d400516920510007000c1780040000702e00032205015850704d0309800c05802601c510f018048462064210140d48404190864160315000b41c0f03c07114280e0f910020702c0d05a41c0c49000c0140c024101e00702c50307108400564001464907020380b81a404441d11100c42c0d40c12075000042c40004659800204080700b40549a10b402074828180e61680443c5020350180410a000c0c000400c150b844039007ca107e83d04c6980329100168203e0540b4030599564108040c10745c20588003050002902d60026124030700001c1c2c040210707003c810041d843d080d0007603800f00e507079042000c1c203e0508541016900c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 605098471 1250 605097221 605097263
    0x7030f08100e0429090a03050304150203190605030d050304020d051f0209040612050c1011010609060e0a0501230a1802091207030302150c190806030d030504020f0409 73
    0xe803083c0c0c41640c03510a909540c01c0c06441c0c84030b2244d1144040160a4200115410045281200c0c103031301d801c0a41d1607456034603002e08031142001007240d15600c0803003040500c5020154402c20400007120030441c0ca5207440c02c0c0350319000300b144508080f1f00c0800109005040890720050130754000c40c03c0c4e4005401e00403c11210030740c0c851826801d65008240c0c0e000e246003a2190b032000740f40855001149001c01e07a48c0c65202e00480b1070191040b0003221105041c81c1c002c14055007000d140100800c0001c5d16138042b14010700341405100c10400c001c80024900c04501e1003014140c0301000701018112030f0141c00090601d40e098011908060420340001d1001584a080720a40000759030143e194001107050081d410040181c2c1c030b0040c4e02c20201000426000710f0b00350f80070300d9103160b4042da03035490a826503182d2190450760b05c040c2c00607010240241b0342c03017039805004080c210141c819950301c084084041e00e2080e10040d500070424642c40c2480c2c03412791700910311240304004151401921613145 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 605099721 1250 605098471 605098499
    0x8090a080106260f0a061d16060f0c060c0206010e130c030209060409081617040e06040f0b120c010e1503130f0f0b01030c061b0f140a0c14030307030f0810 68
    0x4a074001e4860404108451021f024514200041e04c01810901c0c001c00c0580006215441108140701885400700b144a00c180315400c002a0000028440c913225540000d544074002d00c2a031a42104810220b0109540c0c205440360b1542c0140520750310b6415a000c0101d034400280c1f0709039105586817807a0000a85c180c015201038000545016540c520074200104640d58802209030f800c40100303c00d0004910b511042d940004068400244950003c10000e0041c40020f4900d40d101e00d0070303520010907000002d03c0059506c0281d95903081800c4240034004c4103c1012501d104491080c40015504507041b070340c203940d10340107814040c003410150b01c0d005040c1c2908c900a8900e10074940051003404a00c0820400a11140c81c0000440f8002441c840f80e48000e180002c1ca8299803901d10405c2c4604001c034040e00606410595100003c113103007001c40072a45200c2d00d80c40c4038200d10b01550714907000c000d8402c040c0c1c140d11819164070b1104002c9a0041008044480da64070103180840d8008804000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 605100971 1250 605099721 605099723
    0x111c03080916080c09090609030307030b01020307150203163020120702030306100c0c0e01060c0302150c0304020d15050f04060b0301060b0415020c090408090a080106260f0a 76
    0x180c13420003101001d011011a00904e000b425a01c0202481484240041106e52061080c58001819211500104d00b5807150902c080c25001d4146201c90761584294000c0d030144c40c04c44c00340141d2088802c420f076004600d0b0061480303a81c1e1901000000b00110703685081c07032080e80041c0001c85e0209401104072007040502d81021016010610244e109030301100d890f00100d6134001036045103480400608180c40515070407003001202e001c008104403803105a807014054104a41d9503641e12031074002d283c441000750940c014451903070101c202141030100740e40074450403580c0524581d241d409000c2101c02c0d5000450340c080351076590b0558000c0c0d5102e814081c901c00c001e420440d050034108007069454180095100340d00d8200100900c0080c40c003102c08440001c240c10f416031082c16030680c20240071050b025088182e0320100300c20804480002c1062102c00c0b50850f05498070b4000304c50807141c0502407130640c1d01038035022405141400080015030711850045401e0101c40c00b010606000304a44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 605102221 1250 605100971 605100973
    0x1509050d110108130503191e0e0a06050309120a0c0f1a011d010905060103061a030603010e070b18060403060c0309110d081602041512111c0308091608 66
    0x1c0d10011540e803100c1d5240e0401400c2a4081501d20280c950544a101e0111000f00d48407000059544050145a0f00c1343c0481401c13200c4111100500c8000d041198402001c1c0d10886124001140b6540a80300762400740c0580700041c101011020114a603643c00158403030f050000782035440300022581125078200758422656030100c6041000841c843c120180c01000d02000303107034a040c01940b0714003d600c3c1126401038000c9401e840f000300580041980e070300f00915041c0c00605000d20f038202080158080c41040e0000c0140000b0240c1d02c545400300e40c0158189100104503141c10105260341040035124020503080c50650342e41ea4200c11147ca03010820003184d1100144014040204106281c21030305903000140300403030341d8071f0145610540400c041e0301d480108140b000d5483d103030300101d081ca0150028449443c0c0b036a083d08040032081d10100c8080c0580d40005060303040030f241d501900345400c05404001000360b901503840317a00062a612491154181e051389480340b042001f0020800d0304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 605103471 1250 605102221 605102243
    0x90a08070812070903020102100b04020c150105100207050312090109090e0a0c090b180408070609030c0c050a0302210c0402040605090f030d0c0b070207080d120507020c030303011509050d 82
    0x74400034805401010f0340c0c1402000001000540d07000b0070400500d058221001804065a5000800902440703014107154400c107028242c1c0c1c4d4a620115078140d4004440c0c031414090100d404903540c5200b070082940603009400406843c5201c00003030006220141001904961504829422903084001140f403da101900610900143c07c0c01038010b0041207000307000000c28038012030f5880b035100300440303152501803001409100341c100035a20300681c0310105001102c0c260400030100e103d8940251460800c420300081c0c10b14206a02404a0b54083c11200d004550016035402900c08602035001e18000c48102c1c102c50341c1c0707900c000c1002c1c140300d4450a841e0040c01c001e0144e00018000d107540207038401c4800f40c140d01c2d00409075503003407a8407110031002c41d80c1c0d03110128141409540a11540c0c4520f0036000d240d550030408019041070f1820041040b030f500e40c1400c90352400c4003079100745c0540040005002c0c3d0304030710071404d181d0305450406040080e500c41c041564019000c0003615081488 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 605104721 1250 605103471 605103487
    0x402030c0904151b0e03070e06100507050a050a0b091c03020901020c180109060603060b180d0605040c15020624040e0f030d0b0901032001091d0103060b1512090a080708 74
    0x125174403880c1d98240e00410310241050924000400c010f0080b52190b503400038030710b280c248940200c0310000d81c0001582c40400c0140b810740d54138011f0b50012101c0902880009011041c00a01d000c40680c089145000368188141e05500035030101e8407482c11402800f11801c481c0d12101003091000340d0949829005600d02803205040ba042074101400f01820301c84104440c81184040e941d6240744919407115407140e1000103440c200ea40310006058038104001c00080c882e03e14241400c50701d03904852101e60b464860200d8498508440744002c0381811081055411403044000411a8000d0000101d000000b07080c140303481d82c4d420811341c036648000323018041910f603401100741c0454141d40400040d41541c0d514101800c40307140000fa0300c5100f4403965516071080200398001c08031039401d070040c0541c854042e0b82d01c4000b40000e555a80c102101c010441c1016a00d208191400c094001d00380040c1100d480c1d1510405060320119100398a10760380811071071401485090311030016603907600c141c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 605105971 1250 605104721 605104727
    0xa05070503010e2a040204030b0109200306030a0b040c1208031f06081303230903010608030307090504020c030d18050607090b0a030b281d0402030c0904151b 69
    0x506940c03100c10350000700307104c0d88080d206554141d007040040c03400d05030515400e01090007401154030203020441810000242000c0070b900c0740c0f18106401c200b013608159101c8401c145032000791005600343c0d202e880c851003c1040d802140390402d02c0744d40b00c2e1071001d40d41c6003440c0d090f00408000799881c40d000000d10000044400055040c0d880030b019201e40c0902c2c6c0030016040c0ea00042a0f8984103d140d00d502041511a0390803e00e400912540034031442c10b003114003001a0040300c0031034041d40c0b07458004982c1d2480042980d1180f403d9540d410300c024104404c1c0406900145010074031840180114101c0300340d00e000b4510109203a07006050703c0c1060f03040c014500307000a07003a0400e10400b104140a149580d204a880e004124103010640ca0041c0700425950751aa03107017400ca1110200020041b101070548031001c031820340d501c0d4404600c000b8540d292851050324025490750000402070100d0400c010300c0359015000e00460720300c0310b0030040710278140c83e0410b03070000d8024002034003444040d070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 605107221 1250 605105971 605105981
    0xc080c0c010e04060b0a110a061a1e130b06130e0402152a0a051606030b0108011d0702070e1f0905090a110f031002120c0a050403060f020c0a0507050301 67
    0x120031601408650700d03102c58100f01b03100310846542040003e20307900700d1809040140381c40e4180d2100c400c2221403240d07400680c1005121444920030400c10f02484004004c01c070280d1140d084c010003811480008180798001092041041900b0104c103002c80d5050701c40d480a15001840c49410205051a2620401c2422149150460b0365400b0a0000340141c5540300e0348008001c2034032407182a490a200c03401440e040703001d070f0700030160710425041c18001c400001d0000308071345080e20180079651504005603003a0a0074010b031207058000301c211044540241d22141d801c503003580182e440c416140d0780c1c41c000602c0225150700d00100009200d0350610183c81c042d2000b0000184104005c0c1000c900c440c0c2ca0340b1280130042c128005252100b80141e03501c81e00014440c40042c00c8600c280d0054244001039040740c2c03a042c1c000c40740030700011265200001250448506660303110320b041d0550351407400030320514803500c45141e82071000c200365803420030468100b9030045c8000c2107000c0c5400100b5007512 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 605108471 1250 605107221 605107247
    0x60901020921060a05040c2402010605010e0f04020f120403091514090d0501020c030c06090c0906030a0303020f0d0606080a0507050f3004140f0a1e030c080c0c01 71
    0x4a0890301c800b000e50700114182c1e41284280e00e0100b440e0b2103900300070140d14a550803890084988121101d49040d104075490307007a003101d400134010165150019a82402c00041264202c1c8010030414101d00c0d060340200b5003c0c10103a1010f09140b500342e9201110b0b83e08550480114a2400d030902c840f1280c00041074981d20319107401000c0f002e44141207a03a5020303c401340d501508041554904200d4290191041400c207101207a0b06d440c2082072090350b95400307031420090b42c0070300242182503044c0341d1041307031180c04083c00816200f00366541c202d00a42c00520740603c041802d01000c420700426009140007840180e5500c032050030288800d5003280e6020780302d00c0500100f00700404000b1806800d54a6038603a03092960b40c00c01003400d0616103035603100b184401841041042108100c0300d100302d52103520303194044401c0e08560516144d0b40c2d039490000a0180d00c0405507403402c00c020b072100810b605200385842c030360710740b000da58800303094100f10744100c9207400014410160756800f440ca61451 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 605109721 1250 605108471 605108509
    0x1b03170703090b270d0b15040509030a020c060a09081e011515050c0102040506070506040b07020a11150d050c1b031309050c070c080102030103060c080f060616050609010209 76
    0x2035800400741e403613100e03600301401c82c04040d0042150103a44540e04c10000c031790080c25510043c60030b0440e00e42d00716201624184070f5403030f04000c1120000008103461102c03040380c000b0864042d41c0801c210803034200d01415000c00c190750740d010a410609101e036525500c3c40c45078000380fa074140c883c0305003540c0121650000104d01010100b01c641c0100626003003c620a00300a0380e10025890118003a101d950000c682005001403460100000010740c00e105a01880240c00f554441c804200c2e01ca030b42c800805807249460303c20030805440d0100c0681e06004020010318035102941c2c4041c1c0603100206c80010100001081880329080b00003010441d0a140f607014500c0c2003034640400d07942d810b160003030300c82066403040090583c5502100301c42c03945402c40c40b400300b102e507903904082c0070b03601c240400ca0354142085210304510340034a00c50380c01035044034003078261545c41e00240101600201c455451003030341004040049001440520301030510b4400159490030b40700180050342c1d4404030105c41c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 605110971 1250 605109721 605109727
    0x50c0f010c1706010f021f0e12040306060e010308030c0a05041502060604060f06080a0b04090c0e040312020f1b0c04020d090b062d0f120618010b0d1b03170703090b 72
    0x203a2a80424280b07002110f00a460001816105c1c0c0c01e0024445c004010100b4414000300524000342701c3c0103041224400c4000b40410358070303000801000002880000c0c40d204081c00800d41101071500034155248007480e26170304142c0e4401d03191840c0302d542030304480036811078420301000d0f00b8240240c5000d441d401c1041d510183c03030301000505030f04006210325038240e621509403450b59115081004120341103900c800c40c8588681c034008118005a400724007148a49012001040550080c3c41020070070081d11414480c8600400c2004980c05084480c81d0044081d100402d076210310252001040c03207400055071051303e00d0140ba0001000d01001d2141c100c07042905801c280c00d01100c40b84407200491001c20030300c80c0c07000c28101c040710358203154800c1030825901c09d44200012168030079600b20000e884a554116910745c01ca5003045c40f65500f1250700401100481c0300710346640403020740c0755880c00c51030340d40e626901d61100e103661450340036220004501c1d0600d41d0190094002e014113040c418030b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 605112221 1250 605110971 605110997
    0x2205100512091510151e05090a030204020d06030606080c0d261206010f03110307030207020a03020d0803042a14210708120309030307050c0f010c170601 67
    0x1009000304009a0381c00720075040062040c41040c4818005034070820249102400c0c551080d2a03000303c03d00038100600000d5482004280c49070407500143c0d01482128150007040980480d05603100c0301105800900c030650010040e1618401441c00101c81d442c0051214154604a400d88581c0d50141c6001d511580c21104c1941d111175120040f40e41c405451401540200420580c44450035206001e4550200c0d041c500c02c8003110001e07215102c01d036030300380700c030038101c14140c04851090100b80e018100c02d10006800078080e50051171400e0000700001c0c0d040c3d98130342c00500b0010050404546110000c0b00380000c002101c000b164840e04054540a410740b0040881004105a0b1140c50000c1d81e224145025135240d640928a0000c40031130b4402d11008520308a031395030ba60358072420b100e6101e060250040000460141c900807410b45e4091460f6840d0622f04541d1070300100c06d464075a015580c0030f024581403d11500070514082d032a986070101c591094015654002030545040c4170801c01c0040e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 605113471 1250 605112221 605112227
    0x5370807080120071e0503090a050102060f0a021303080414010e0904080a1202190306080c062805210a140106080703091110020304080106090209060406050c010908220510 75
    0x3164410300d0352010f0340c032400c1c181442508844022007461140d20342c01d01060030310138044001c01c91928180c40003003040b5640c03401280e036040208c07158000251440041611144950001d00c040091404105545500c0703407562195540180e011820001014070011002d503000094a00d0f42901240d020801e803420383c0352aa007910507003000d00c080285c60030030300c5c003049103d90558a1143c16061865035400c0b0300c00c2e020780141928080c02078a84135544c1403125a140c07000c22100a950076924440040c400031002c3c1e84400f07480d40108003400014051050401d50300c1000e90b8450b4000007280c01d01d802c06103c0c2d00100c2e004d070340c1115201038400d4010703c000c64114201c607070050818500000c20050b07500b020709000f03499403c400d50044490780b1030240c440d400800760054542800c02000040d07903034850581244900b58443d50881000d000c04c0200c07071700810203440e65442100012032112041c0e0b491031516404415103000980d11750507001110105060b203070b0007404080c1d83c41041440c03809005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 605114721 1250 605113471 605113511
    0x290405030a0b06030106090908090a05061804051e070f0e0103023f01120203060c0a0c080a051e0315030606090118020409020a03050412020703020109053708070801 72
    0xb5000450304030105080d40c03000d5204500400305094108034050b05454080e42c0c0d81c0c00118850f2040240175404522850544100c945510520103860740e4038403004188800f40c240201405000c801c00f130000004822035511040c0700c0d100350380d10118100f510314006440340c00221001410103205015021680441420314407000000c0b010f111040b00300600c0c6403005125844007044180c25482c00001c0180c060210030a11b0ba1080307059402c40d503a40c40140c000e901a5540c40c0300003d03152007240010550072402484444e24500c0c2040c68480c5084024000304150030009811320800000c000c468150555601028403080380a4002400c102002800d0201c040c06801c03d1443c844465800005d06070307040710004c10005100355240d218408014004007001c58054800f400402c0c150b05040e480440c8400c160b039416103541100c5820174042c04022a908000d17045c09051019403d160480b49000711000401c8814032030030b0a500700307500300b8200180f50b40315840a1381070140c8600d10155080305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 605115971 1250 605114721 605114723
    0x2c0f091f0b071a06040b130e010b0d0f23150f0703020315010806040f051024050415030603051b010221040b090102011e06080607080108150901060f290405030a 70
    0xc128899101c0c44001401001d04c1b680c0340d0b5010400e5064480c0100f903a82000340c1e40c50241d0000c0000c100c5032024000200d1113190000d00d0100e100000e48006a2002100f003007141080b40b86950300101840713494a1b00400f58040c0045a0808040102500000c0300d81c035807000341ca10f03042d030544c00d07d082d01340122075521079580d050004140015030346441c1c0d580800b207452403070395041c0284e0528980802160102d80680720000c030001c4081515410b410351a4000314245560b46403034a071912100284140d0100554410980ca07081c0000110b0001c0003401e03400000c500000140e255854000f900e0106003040601a00f541101380c800c142410105840895902040325a540c04c2c5510040b401000117200304c00c1b200001400c801070900c1c080d07020005a400d40e108903601501c0f032210995a014091050401329849080d1190080138502442c0b50031102060000c123446403031306054a44800759412007198186484900800d0802001d68116098100841580340a08220110b034070b0713a0301c50300 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 605117221 1250 605115971 605116013
    0x609041d01090b0f0105010c05030f070c030b071e0908070e0402061308060115210f1b050a1704170a0215252c0f091f0b07 54
    0x1111261045584040c0003090314020002c001035203079403600d040b6140c41618010441d1204c40004500da5024028a40905800c4030045081115140c0c0702d154684c440c072000c45070044c498034000000b5003010769242c000c4c1c0d115140da0002c5412138243c0030302c8802c100700d100200040280d081060880c01309203001a00c00f202c640502c10307034960000c5049403040d4070403514a4142c0c0100002c88090109105040c0c4500001204900180810032a074800b1000e1500016804212907003803001d104e90b024081b40280541702207051502121030b1114a083d4203100c40100d080012403104c0c403640a210702102100100c410782107400e0a44a1136450780390302e000485458800146100014000c22225141081c02019400103280c01c503075086202d03402d290040e41d00035100740d074190400c2c000c40385524181c00c3c4505100e4000079801d050580381411000094022860b6003003801203881d0001011b20403410002582440c00a200389002014007030381c021101e07040c050041a00058101c411105090380001d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 605118471 1250 605117221 605117231
    0x20a0b09030c1008070906020106030c060e01261009052202060d060308071205030609072a0b0412020303010b03070c0321060f060e0f040c09050a080f06060103020702060904 76
    0x150120349000d0700c01d0030032030380540c0e008200c0500f55849104503202d110719070395610440e40d4a03078041e42650f40c140030050181100340c3d4141300c0184a403910301c441301c40502d0700c03074501300c55045035002e031a03e01c140e01d1a00584980030002c00c080c0e084c514000400c0c1c0307114100450300e0300340e0103280c117070104990149480d00c800d40004150340c0c03003038242ca0204003441c00c10820250b0740e1030084210362200c02c00316201c9045049010000d030040c0180d03031040001428030b401c6a51101000c40d8040304c00c2071200005043c035155060448900081c080c03100f4801c5100c19a10308241c02c01000c814100200001198402c100600c079440061082d250040054282821b1291403494280c1d410f01d12807a20354445c2548000241b00003c0380e03005503045400d1140760b00b4a4a8032081d0480700b8207080a0003a0b04900038001100b200e09056000314554030b030a103042c14940d07898000107a01140154030000c0c40b5800810424501c990501c0308607040b10003428214035104459010801da03020380070a080c4519910b13 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 605119721 1250 605118471 605118487
    0xa05040506010e1002012412020909070b040e0406060b040b07030e0f12030a0314060105040b0304170a02030a08130b0a1503060e0307530a1106060a03020a0b 69
    0x3c83e4003074a50100244607024401880e04000d0080c106000540c00254034412420b1040d2050380d5810b045c0d43d000d110454403001d40d0f40900c0910f801c00f62056001c0e102d079000c0081c682c4c420a003e4005030048100e0485c40b400d142c00c00906882c800c0e0040741c21840200010004e180294040796101030389810004d211418460001d00d100381020011504012052458404002c01000400351807030702c0d03101009540b2061194081d070742d00494290780031501c200000e000309011000550760082c40307041c4000f00c0c08950030140485800403942c45001d40c0c00030442c81e5440d5006549a81d01c10740c1003c6180d400607144d1034450900801070010200380d542d940e01380300c2c03215502669038080d40d04044188102c244408800d5540e6100040a413181490005000303002c00d101801076403880d41044440e07003101e02407040841c0341880314003111000b00c1121050200d004062000c0c0c0700a01c0540c0342c1580303003000a19880d0034080001e20b52441030f06240c1c0c080c4016901e807141750b0b050751880500d050f220414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 605120971 1250 605119721 605119727
    0x9020114030f012309010f0e0f0105060a030b0301020702030124080313030303020a020c09010f0503010b06030108120a1e2d1719060b030403030e0303072309220510050a0504050601 79
    0x40d13410702c1d40c1041500c00041119010350303807940216103564054200d43c4d50f5500050654000030300506a00510421000754510320079005812042402800141340151030b5001908491303d0900300341400158401042403008a04001c200a0106c50040c41c9840c152410780d01003840c00c0c0c00014140355001c9100507510740b080010b003d2982c0c000d40f09032100d5031522518110000144203080c425030814a400703c080c240082564122420440100705004980b120500790360042c0340391500700540b10785d100d500d070009881907905040c2551900440364003503000a40440441002000c8002050f480c6c4600c2107500002150102d02031403c1c2400a84131010789141e100c1c2480c290040c4141094000f01e091400b060040d40124426202044698134488002e9104e000440d602d1000c20024039098400c40c0d0f191031816103503070120108520b80040b00d000654048294004941e002c1c98400119442e05024821160002445009a48524900800512104490b005a900a903112000b0031302e9a40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 605122221 1250 605120971 605121029
    0x307090915030203011b020c06070809100512150102060f040c05220c0c0c181404080304020a170d1b020301090f05010510150f120e0109020114030f01 66
    0x1041440a00c01501e020801d89081081c90000ba80700e5464403c1c104d6901080d407113074400c001100d03005000103540315410094079030880340b002d0314805d104004892055a880c5240706844155072981ea03142c400d00814401d4200d001080d00d10002c10251900344036a0300002c031180c0c04100030360500c03142d540301c0c506202000c50582c03080fa04075009c801114044540c9075183c01c200004030380e040102c00c00c10300040b50350403c0d0742d4025008561303048040c030114010300c00440c0ba101000602250103030060b00c00b07040e10003080381c0a070780410002c801e0004520b000c890b00d000074600cac0c00c00144032070240600c1940300c07800b80014109008a00119594610032002500d0140d07800070b00030001c1184074100f8825040030320204407401d5182200185a0140c0d10540d031050359804008102240d624050a42e05460605920b03030900280400d80e030302020b024000c036904010700c1ca0002c42d00c2c040520024050880c81032410b10701c00c0d0305008000015401d00041411101c2d200686c18411b105d072816a55100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 605123471 1250 605122221 605122229
    0x1706281506020a0308150a03030c06110f210126011b030501031b0605040302010509180c0d0c1403131b060329010e010806120319021917030709 63
    0x42600000301e81d0380104604036501c0c040d40300d00402d07130ba82d10b5916010242154400c1da101011842c10b10100c1d1041d68a6070540c1d01c20000000c86006000200c079131134000d182010f201307980002e0340c44c03d1014890420818103128048401c510b505048100320700006051240c01407040c80c5521100f4000300350080e00620b8009055591074082083e401009000d0900054442c03111030f8045681741600222118102d41581c1e82d101e0400c2c0c11580111010750001502c030ba4048d200207801c000c034403490940180168840f2000c2a42c8858202c20708d425100440e50103c01c3c401d40c65040781030406e041003140d9100d00d8010108170b2501e240d1030504450410308110708000c01c01e03082e002c0707180e41e019031120010594540d46007500f4041c084083c10f0b2080300c1c071a47c0d07000841031803c01c101940a410075940184c0c000708001e41c849000c16482e407458200c04402810745030fa44222586064040c0a0803003102d00008040160300320f07035250511400c1003122521504030340013000560240c8950306060182c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 605124721 1250 605123471 605123501
    0x150b040b0904110a050910050411040b0d0f050c07080304110102011e05061c050a03080703020919050405012408040503070803041b051e011101020c0610170628 70
    0x10b0410341000c05051100644450080c081024003152030303d4421280e9210b14402062240828249000c1c00080e02821414140c0c0c1107061002107220b918650242c00e01d0007254034000f550000f024010002d95070080c107400e4501d40c0410149000ca40000b040b20b07441600140e07420301d54003891004034018400540c1102040c10881c1840e51040002d40245001309021640d000e100c0b01c1d5450a42c16411148100804692048040500081c002d5031013690100c180d044c014100303440c20012079400121402c1014030340400340c00511044c42c207441481c1c09010102002d601180231204148501d40403554220248145003000030200310b42082250035203544a414aa124102840c215241c050b8144905000400048000c03400e0300b00840151400c1021000c804030920032400155440c502d1440c00b4112950200522000030500b009000c2c080e00b02c81c480186100d10380006825002542c3c0401520364201e0014003280c10010a049032040d07440303c0700e1081d0481140d1a00004200c980d0390780c055 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 605125971 1250 605124721 605124739
    0x204050114061b0f070b071101030513060b0d080a02030c10150e0903070c0f0e090a081b1e061006050708030a051f080309030d0327081b0a02040c0804150b040b 70
    0x4c01b42c128006412900c0c072401407600f40c0c0840c0d50054040e10030488120003016002840140400c132550040400c2040140101d41111102e0300c815049502c200c4448000d0b134800a85c1404c40b0208114081f0261009001000541ca0012102d203006441c0d1140c4502108500089540208207104881c5031541c45902248c00b40d40d28148160424820312072100310080710000666000f40204039030762860740c05a130701b40c5000200051880c81429a1a88650b90b03c110380620b0300580e2105414150100d8075001400f0926001043c03c0d00d9502c10740221082020a002c84030000b42c10030180ca40050800034041703065070320955603041c00781100d0046d03a074200300f42e2000515084048002d202c00c22040d802c1ea80708004000301602075a80da040003100c02c6909107110030110880031441c00d1150f00c580a4140340c591507822400b14810b400301a46a00c0e00320380c00c24000c500d0288142c0d8440f603403034140140d007881e181d00d504850703a49100e1a58112510743c8000c62140c1c0d44c5501c45660746000402c0000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 605127221 1250 605125971 605125979
    0x1506120709020a0c0201030c0509130f0e010e060109270602030a2a090b0909010b070f02060d051009050115080c0412060204090f110d0b0d060603050a0204050114061b0f07 75
    0x100d5411142c0003179000c2071524030444000c80c403e0f001c40c1c080e00b1000d451a02d00d4001a200c0700d004140b01c0b070303c1108450741d0700060b00e0701035070a019441c22aa02c8000602040d41003541000c02c450380702c000d42c00c804010702d16024803d00c401401c208065044400140c495840600d800302600309500a04040e4101c03040341d40b03040342c0041aa00710301101e40d50f0441e41035220160204644541d00c422a03011301864010080307080c07140b0050111a00c07c001c1001c1c080f10307070360120303416400c405400400503031201c0401c102d01080d003450400505c561b440600c0194540380c50802c03c01340d120244010008004000341402110301c1c21074005100605150000380441d0030484001c3d041800f810038164280f0b07000904240c064080d8040d40004642c1062410035104442402003903084480d5400210686441c00403520502c60000114015805807110040303030303c10801242c405070440c00441440c0c0d5011030303190f143c040030f0b20214648411403d0301003450b050580e08e00280c5018524081c491140041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 605128471 1250 605127221 605127227
    0xd0b0d03050c0d080118051005121b041e09020a03080c030a0e0a032a031209081020090301060b0d0605130203160e0d050d0f0e01021506120709020a 65
    0x100a0501a40c241c4003850714400046801300401c3c4101c504004007055008819407140e070016411102089421410966490101e1040700301044020065000f5020b003000079081205420380050041b40d040046001d20742864245080c101c2c0035814072a0b80d080d0000864a41184d45006541c112a02c151100311a49820380d0320390104000800143c2000141e442a0814080d41d4081d66400b803203011400b220600c86400d000e52110600366400311440f070000110301c84921501d81740115965000f0501d0800755100d1a0521040c0c01e207000030700d00254031441001c6641090f10020051850780c0d0b4501c0c2c2c1e0303070000b070140c00b5980124400660008581d100c2651540c08907088400558142540300b500c003000740100d0008485100700300b420036074219000740c80b606009400e4030300101050056109626550301d400942d10700240401c0064144100d440c0d00246012041d510901c018200344a40c02c0102d044c2407409405140103070000d903a08400c5401c2800080c0c00b82c0301c100b0b01103480c1d02e4903000003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 605129721 1250 605128471 605128477
    0xd09050607020d1b03030e0313080304050a1403120c0102070510090203122b140f0126120d0608060403020c180f15010e0a09023c0d0b0d0305 62
    0x1c100503200c1c40400400480c003c4070000c0c0300e1091003107a242c40d0f40d02a1805d03005000701081000082c001000380468450200c00024007528103d4015910385040c4414482e00c401d15400a4103c00f4426000041590700010544113900200c1407032030300c41e2040074125001e40180c44000b000703401400c0040c0b046045c0b42d07204400c000d0089080f03640919200c00300080038070441c66072001083d540310050486001d52420b0301d034101044c07100007400c143d042c20321040c40782c800d8034420703000e0390a180100080c0b119044040300c0390001c0455000b801e1450b404c1d16a55507c0b003045034005190106880c1900c00131944030380001c00034041614003925252030700948503807941501520a8001e040055902c1c11900303000e43c0b14600b00c56050701c1a440b0503050105901800a8282c100001c002c005034494a400b0480030060400c070b000580c59601031100c81d0420342245105549000044226888400d800c0308010424908121450381c2c0e54502800f41c8042d00e10564200e030050740420300d20701010383c41802 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 605130971 1250 605129721 605129731
    0x2102d111b06060613060e0130060501141e0904020c03040e0c0304030c0803090f0304060306140d03050a11100c0503090c030114011a0c0a0c05090901090201080a110d090506 76
    0x1e845040da03d40040110300c0c005c0a662071044521840300b800304600410769052449814100b00b00c80030302903200c100541e07140185011603451440c0c21070303001450743e0051074098139003428110302c1d1018407100506140503035402c00c074088400041040035600040101c50300d030000900250343d42d03c01e094030903030740340c1c0944618000314012000284005d000c80042d40e01071a41660790703400400040d1680005508061300850140c001d14440007060791041005000601882d140820031602e0007118902d15443c40d880c442c0294800303401e0100080c0d0010848848050b24101342120a0304603a031a03140500402c2400403107803030140c0d110071454126015610a280b20030823107011014110a00d42170354018040b0081c0007a4890041c802e0120052814820140c01c07404182084000e200d180d14101010304145e4040925803014003a6003403148040c0c0c1d000c03200400034010a405540000d003122801448040c0066132104041146030940f01180c9007000308010511550f0983e0a0007500c540040c4c0b8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 605132221 1250 605130971 605130973
    0x130e06010f031a06071505100611071a21010e010330271d07020f060a0f09020303030414190b0c0306030f070801090302102d111b 57
    0x20740c2040c0340c2c03090041c00b9100740e000c40e08074510303c018000c1c080903800140044412030030108450072007001900c50703548550b01c80749030304060b18a4510003400c00d0300c900342240c0054120107414001c1c002c24201c0101092035501a29540d4012041001c000c0001010166807124a21000203440d01c40e1082a0f81660700078604100c041c9400301e044903080f00c0100302c1c03000702c0c1d04803c0c8900da028020b44014a640c40781040ca000e2801c250500410b001c0819000501d458003800d42c000c40d80c1d500614584d612141d07e0005004540303030180c00d01d944283c020040340e03040c0d40300c0502002114154002e868807550140403a82c607070415282180752a501c0e0344903058948074100e928581c0341c1e0316051a07000c0580009081c1c03080d8560480e00c070745692004021680521400248009003242001418020703e01c1000010b8544800d00c0d00900380b8017840344481d050f90038000a140c40340c10607002c0354103416503084d280d42c448000f030301d5110142c02c608940c02104a00403d101c010008021103252207001c81e04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 605133471 1250 605132221 605132237
    0x150108010c0905011d0f180f060d0c031704030b09010207050c01031104210503040305030705010b010c0305120439091103010302060a0c0210030207060b0a0509160302130e0601 77
    0x4402c540d408001e104540c002040300300e441c62480380400114401840c0a4101c450710020710010a0307209070365102d519403040c209030801821a50828400c0e0304050700b140d42c20608a0030fa1074194610110b8003016081040200040310300316041000c031001183e01c081d1107101450f046007814003e41002206850038015922001e18a40c8207108070101c85000f0f48106007000d0030651041070030a849580804214041800b034004100c00700b01500085110324000e43e40c6000b54949282034130500b03e010340c1400000700007480000e4112054800040728694256059507131410845510340203040e800c4028030146488a490000c00254a11110450380000900a9680710306070111303090440000d100c4c80052005000614000340101350203101c1c0d14221103c0031581e00016100f151605045020a900069090400c0240d00071140214002c42d00380c031502e803510000c20300c1540c0040030b070000f10810040e40d0103914001c0c0d0550311061988144248400d0721010000101c0c20b0607140140072034180 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 605134721 1250 605133471 605133491
    0x20c06010f0617070813080c07032402030601090e0402041b120c1e2001051e0603030309121b030409061a16110d02060706051816030f030207030515010801 68
    0x2045160150348182d03a0101701c0d035902c603504212007103d8001100c520034104115410a0810060003003d140144240841d01c400c0b000540c441c00a06d031001c0040b607006008121031030307030030a135081e0840300d00c000c0344861680c6620010307005105040d04189100391181103511241d51000480c1000d0060001c1003100304a6081c003075900010030040e1400b00c04c400000402e503a40310340703144041600350800c4e220b50400c5501c51075080d030740c1c2241d003200480d51f0b91100520207100e851406420500540c051440c5040c10702807a92103899500c5040b0030020001104003440c10182c0c042041c000d24076007504d03200c540b42d400c48130282086101c0c458800800070383d90800040c982d41203038450f400b00d801c03030310346003a0550b56041d0b1505070a211030380c050a038046000168a40d0f070018080948204030008043c6040002c000c1c1120002120441c258406058103800800555290080c4c9400426102c40401186012460f202d141e800080c920700401005003854071007a00070302d0503104100000c0c0858194 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 605135971 1250 605134721 605134757
    0x90102040311060901050c0f03090a090b060909190204081e0f060403030e0c06040306140c0a0e0d05010b03010c2610090e010b3708030702100201020c06010f06 70
    0xd40c000501000320b00004500c99280c0305000307181d04541070405904250105a0300c038248400035400c0080c0350800108008107150003450314003e800030700c0e0304010800410f004103500c0e021b0915075a000d000264041811014608624980c4225588040d95116120300b0082d0b00e410800f0442a2040d141407a13000c0100004103450110084410003812103998640f812006040300c9101c82c2d0a40c015950bc028032921907070b0081c0090343c00764501003040300810710810110507004250003040031083c0b00301b22525520080001e08000d04894480c80303000507080107401071201d594256407640c0b07400010614550030580f54070b1020032101c5140d0003010881103100c0c0200040303a503001c221000e0301d024088210283d0200ba41c44c00c1d4500000f070041d1152001c9040c2c1119980341c80c24042840a00828040e44040008482401504800a501d29200300c2030b680b40a8640002e21680d00181c2c000f01c00c80c030035416620381240d44030072101c0e156503c94140f40c580130140a03100c0002c5021180c80d02c5804 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 605137221 1250 605135971 605135977
    0x200109050301050c2203020409030c0201170f0a02070503040e100503060a0902060712020a14060114030109171e03040c050a06030b1311070503040e01080706020a03020a11010e0603070f08090102 85
    0x2007043d441070714120005c0c1e107a510701400e982d01380624000020012000d41c590f07200d201d2034180b198035414000fa079035000140ca000c01038140901600361010411680d5006000515080b86040c0400360307c034000791611a01710b00a50300110964890407007040581c0c911402c00b5001c55a080c2d0035900c454071041c115809841c0615400b94005500f0061400011040c0d00d4811070841d85105960307030201c42e580d99003024002483c89941ea90302600043c0501e0124225000419004a00800c10f1119954500785c034040303080021504510040b80256034000344002c0300043c006141905036680c5014a000c0100e42040d00401e070080c1a080c0010900c1402889034041001009003070008000510005070050120309803440c42851081c01000002081000a0320280800542e0307a086917040c07984640c5044810307400181113512801c0408003290b004111100041c2c0c02c140541d10a658a00c0141c510b50b070700d50807c1da004440002085880c991000c4d403004042d0b182e6450501c1500c45401007401c1c1c0c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 605138471 1250 605137221 605137231
    0x5060a0e090705060d060e1302010e010314010e1810200921011e1b0807051c1104030602070204050f01080c010c02120601030c03110a1a03040c0320010905030105 71
    0xc0e004003018000d5140c18400385c4548440840080707a455103a1220481e6180140d50040e41c3e60b40041c000ca0440d030b040340c14490709103000e1a007003281c02456190380e007410340c040c4140300e20582c1050103c0c2c4420310b051980f182e02400403040b1540c00350b203204240001c24640d0102c0c481048a004982c101000c540c08660700501700034031440d0203400f00b064903810b550400300d2082166696a20788040070000c4e0b255500e51000100000030094070910350000c9240c44400000e00700039500003001109a04007066a80700e0b0038140c0c001e0819002410044000d0003040d210b20003003080854008200b28268000b44442c1d40309440610191701d415a40c00e0b2482c00c20301428000c1d402000b050802544a2081022000d00041044c1d500004080f03940b400c0c8902a0800d079103050340080180203020a00e0101c804801c01a070701d1003006460310245030440c184480714411104030002c085010700408817048405180c0020360a80d4520030350742204260205010202d000c10120b601c0010640380601c01c2d103120b1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 605139721 1250 605138471 605138473
    0x306191a010e010e0f033901270308030c04091404080f0a0c0b04050304060906020f0604030305070e040e01021e090904030f05040e070503040303050f071d010210020d05060a0e09 78
    0x2d00b240e400107550010300030b03d030680c10240040c40c82e04203650400514481800b140108065802d0400710b5102e0058801c803040d034100030180d685481664469002094460581d1004565111603698062105401c0d403010703107120b0000c0248081c48840fa00180100c425120040000e41090b102c640c101900440e800f504264061003940c034003075004d000070460002180703415001511241c2d6400c00e07242c1d0983c1c0075202e562002c5005d102a94124800d44050f05141c001842002c20030944e103a40c1d144001c01c02410951204c0110302503e005240e826084040100180b10498000c1c030a24000e401c016080814080c400700350448449140b000c0f56403804000d030000180d5600c0da02c068900e04000445001003240c10080000c2c28800d11b000d46005016954a150f580c0c1450704004050396000b4016484100c0c41d0400d200c58103400030308041a100e50b4a07003c2c0c00240812005078181401040b06000307046c00002d00305a10b52241d84050b114103401c48200c102230341c8865011140c194111051045 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 605140971 1250 605139721 605139737
    0xe0403080601080a0213090c080702030f0d0902120a150b0f01090911130603020304060c050f070b280501170d02030d05061c0305030f0c030907030209150306191a01 72
    0xc20351082c5030950784241c0d1008054908040744040340c80300002540051021f507901e241850101d94404807080d00f10801344025401d00c05031200b074019078031a4250035240e00741c3d540740c0c001c115100c001d860540c0c0c42605042d03544481c0d181c00c10980c04c07003c0714902604280b074080701341c00e140342490034049941c4040c0d40c0c42e01c1e1541440c0c0940c0043c00540514036002c1005c0c060503043d452984654400b91820355005a1203003468a042020340b00104080c4043c00014001025031001e1031003039801c040c2c1c20280910054032074815003a41c01d606280074540025901c0300c00c002840003a04068100d51040e807180e03a00a4013881120b44a600301c0400c10b006070020044411010790079042642c00540040c880c08c25204500300c3d100341401c01880440101d00c011080015032800e400c41180e0100c50050030754514a0804603460715260a404002d100707941d004c000c12032000003900d010002e01d0010342103403420b09029035100c1c001c0355403243d0b00f400c03a4200010158207400b2010340c0084c0040684503150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 605142221 1250 605140971 605140981
    0x2040e04151e0911060307090e06220b0f0603100303021005160c0804080a0c050319080405100c021e030f010902011b050f010f0f0e150f0903070f050c0a0e040308 71
    0x2c00307401d00680c19518010f00410301c8210342d0b2980011400790080d03071688810a8038000d40000b041400a00c4c03184941c410303061041441102d0b110800e00e0380c803460800506901c09074005081a0201727069140c0005021041111032940300340f01100f90380c086d4007100c07070b40501400b07480140c43d8101c2d003403150542c2003000154503601500315440030904c10078005043c03035160a8090300c0c0030071140c002d13076120600060401441c14144600e0b107048540741e040031592000c54070b40007507501c22442600d0261b925100c122490074460100c800340545d0041080e003614820006650382100e00540141c070074010761550020300d040c140700d510142541a101c0544054071055400044542c00307a0a4481d030040d0500c40c80c034404288a582609480c0c04000078404d4002c5060104807200d00061800961001044120564201014680c4555040300700034880d43c4103000d090850150701c40080c9040500340580302080b2020928081c1d060301a100c10a04694403150a04820790584020f030110752418003040d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 605143471 1250 605142221 605142281
    0x40909030c05010504060203010e01080606210a20040606110703020904060b0d0308040302160b09040905160b030a0b06040506093309100e010206220602040e0415 71
    0x8186400390400c208104115210182998000c5501325181580000140250103422910501400500300100a02e00e030040225020498041e00110019842a40e07040c407100c5c2041151541039110320100d42c40e091500c01d1811980072540058466418400e001c11070500c0f4680f44200d038425a0001c180035841c580038003c80400123081030354065150760194505445a4820043e928803d5890400e035240c07505000b82040901c0d54110b041e903043d0f541c100000d00c061720588880b0702c1e0448000400d4002c0345000361412000c06035015420f01141b00c001a640d00c1e840c05103200d0b140c001c40612189001e04c0c100b06643c440c40c090213600a9061081000c282810302020350b500072165141c081c00d95180c11000100c201800c580c1c4070030030000503880c01074204101d01d030301c0c90174440c00c0a07184401224000b0f519424010000c84000380e44602075440c110303590030707501080c80e0000c1046580d41c4e1182c10310800c07210104c4090702d62040040d25001394208511540a903482003460002c501c040786003c01c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 605144721 1250 605143471 605143481
    0x1230702100c14190801080d27120302030a09050103060e0f060f03072c09120304050307150902030d140301061b0803070324030c05220e0f0c040b060409 67
    0x104210b111403284040c80f140d0080004607148035958141c0c82d03000340024000341d81604045269006000c43d032002a811007000b46a0000f000001d1280d00b404501c0c81c503a240b000d62007d4207500304410034505040d00071004103650300403a900d0b4000640c840b030041d026100b03079100f10001004d0800014152804541e42643c0000c07000f400030040c42c40700d0000134a03100e1107410800c0b00256484000c0c400410341c6002e400540800000395056180501e08942c84000000c805081c0ca00f0010001d001c108080c401c40d246c040d400b8088416046500c4501401440303c42400c030b0080c450522410b8070903004116041000c03072403406c000e00e5a82420411a0300e00c51076403290350b000300c5802c0c042c00000c0c40301003e1446544290740014261482c1081c064054400f44000c2100000b404000c0c03000c01d110742103072401e44405868210301580340d00055440d205075103180c41d454900e07260b000042e4900106100c4981c201d40030481d0244858803007084100c5901c0d11945601450401080011042c19045 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 605145971 1250 605144721 605144741
    0x105060703120219030507030b010c080d1d010507030903080915010513090c12020a0f0e0714090306071e02030a0915020a0c0b030f0a09020f040504020f0d050123070210 74
    0x5814a50540001c0c070340c00c8040040344c0e012070344910070403030b807698903125555034540c2c01d00e04500c2c000f54980b620760301c51050f1004503007150f403115480d1a0308000c3d81080116a1805002000107207880c03d402001455400b600701c2c0082d5150011940d0901c0029110002c0c03007080c484000164641030402800d0503003031038a280e1540c3c0766007102c8040f0708d081d440c050041034101c40b80302101c90903104000045809030041e03134059402c00014040d031172034002001d9200c20369013080c0c44100c2e02c0c00040d030769a02824450715407620400c4204040c0e42d51000802000380c0050002103039125101d00d06030703142d0080b120b41c03c4c000307000e6104c10401c0008041501801c0303840350059656003e060703294a00126100d41240c001e00c80f0010a1041d4404a002d80c0c80c0c1c41080b18504200c40c00700340e03000904150400e41d00c0c03446243c490340403505541d1603c0c02c14080f42c2c001442d4400c045107501d8254044e04150030114140c82917010318580c0c440e805045c051284899a01070090804160b000704028020012 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 605147221 1250 605145971 605146007
    0x20606150d051504020d0614040e03030a020a090e160311190503040f2f09011206020d0f0606110c030606090f0c04080303070c150603021c1505100f0b030105060703 72
    0x30f00d161640d1004015141ca00b22021071807501302a8800420060070070114000e0786080b2180c0d810010120035250004840d000169039024415811100c080322a002190600d082400780701440301d0a095807820812151000d01100060b29901c0c82d940c01008078000354203002e6418107a0341c510035002580c1c0584038100c00d07920b80383c1603100e86800302c4038003015a90441c04101131350403585034048030031040e140440d2004402e605182650a0390040c44000600680c0c0100e8400c091034090707001684107004410b401c1000517a02e400080180542c1e03031101806004200e58003001e030402080d194030a00019001112a46440d001c001030315400419030f07559000240b0010524880034401103004007810341d03412450000c0c85c00d00130300b06410404c01070701c1c0f00d1401008200585500e2450081c100003d10081c10161990401051003003a00e0002c03280e50703180004005035072952403405800c0e01c0001c60100b034165103e100c608500d00c8280030702a480103042c00340000080c07003280f072484d00c0042c800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 605148471 1250 605147221 605147251
    0x120902220e0304031b0803071e0201050702040c0f120902060a080c040906080c10050a08011a0418021801050a050f0d0612050a140106050a051306030f0c06020606150d05 74
    0x548850700b580c1054000300c5000600c0c61609001d02440400d04c8040c01d25103010f186000c1175680c689140080a503c0410682412481c110070f41e07020b0340588000d6a00030703009110808609100400440d11041f1030700203e90910201140d50700c0c0c40c4980591558060003803813170303d80c800c001622008001072028410b040700308004540000b0074082c1000600d4110700803c1203850080400400340000300100d0200401401390184250780445914119a19290b160020b100c00382e400d4481807145400c0105400e0804070342c4649192568000c0207000c0503a03410309a808141c0b401192f1900c204c40c02c0c0d400007203042c040c0940000c140f00c01420074110b0340c00c0000c0d840f0742c2c2e84a000384102c915001520236070820002241405201c50107481d409401000810101e410a000142c00402902915000c0c0c2c0c8201c070504041c181940c480c4d009540c00c04c0f0420300030740e03c1d4904035100f405607000d00001405000042146801d00740c00c80c90820064a0890b400c00180c0c400c0817000b440e0080091040d00720701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 605149721 1250 605148471 605148491
    0x2030c072004050703330b040e180a030f110312090d030608010510030609150e030a020c04020a12050a0912111e15130c140112090222 59
    0x12101c030030261194542041c010500d000c0410007151001401e0500781410081c40403a04034010000c0c0d01e112800c0d00c50300c1c40400c080000200c0000080d00940c445000c0041c02044500417603039564800c0456580b411130f8440d08440c8140c84010001c00140417a01103a00044a00d00454007a03007240f000f44212810101e1201994056110039164807046810000c0310048850f41741c05204007901c81c1500a2080b4105000d10342d421210902c8050101e595851a00342040100107810446060b40d080c10f102c06000350b0342171a101e070b1120707601c03030058401c000c0c2d0391405080500a45103120201d0325803500304401e14103103101600000f490f0681407a81d503400d0b44000346540f803004461044a0f40c0b10004108865000e52401503004018008001c0c0d40c4c04250b541d03400060007038180803109018220f6030700e440385680c0c00b141c2c0c0e24000800b585c6043c1d83c0440c40142500c094417050300241d07909000c9840030110982140c12010001e074020022010300030440300800c0001d54114030018001403512a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 605150971 1250 605149721 605149733
    0x315050a1a2b05061306151812080415030c12020702061309020d0c081b0702120304061d09040c140d06060b09030f0d020304120314030403021501060e011202030c07 72
    0x441024001282d581c0e20500c003403810003102c142c1d6005c0b00e01d07604000c8a4280340d681c41440300c885d0428820448036480000e80101000c0e6004000e00950380076402c01e80c85441d040760650810302902010310456440004400d01c280196084a0081d403a00600c500d45c990180005c0e5000e540c051b600300c2c03010070030018920a01000c4200034500d80c0c600507115200601d00a080d2007450248004100140007804128461010b00b40241041c20407001e0780c848582c4023107224642c02001c42e44d0280408103001400d590402160700e19062074480c500c401650703c1041107641c03007044d40c010b4403540706043e084c0142000084140c00e0507500400184030f90625136220829900140c0100112403801300d00d00495003410020400c2448404024107042141a10001d42e80e000f540b00e000c00040764500c060342030500980c21040030a900b108142e58901c1c090034081c3d0b450500503005184103648030b00000f4410710880300d0220680c016940c0813001101002100060b420152502203400001c10410000980c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 605152221 1250 605150971 605151037
    0x6091912050f030a0b030c0109060210091e0501051510020a0b09030d0c020106051e061c0603020d050a1403130b03101d04030215010f03060e0c09070315050a1a 70
    0x200c070090220b25000c8610526040c20760300381c7e00301d0611010110601030386030045001003c81913a00e40000340f100e5241421448182c00d0594001d0000e0120000004d000c4190807181c4941c018010640c0a0600d0f5828445d540840c5d8a40c0310040e00700508140020300721071806500070b1940030840c0c0c14610201010307070484003055050000360399038000420413070070030080c407808550b5031440c50340c0c08205400120340144511440000c03502c00f420381088045c4c2d0304d640400f01458000c3c03c0000494441e00d0034940d0b03000e052005546858001010328204c040010454650f401d8041c090000f05140140c28241b5400241c00d080c60550344d0a80811111403040c4044803000240d011045a0300703181c180a42000d40710f2070802d21050b8414010302ca00200202010102e030707800440002d42002c0700d0145410950203e1446900200c55014070000c50350580082c201d21070000e412040c1550717100d0400001d8800d038410481c0382241c400c87c00c2808003804c0c024110075040401c99200142c00604c0885902d6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 605153471 1250 605152221 605152231
    0x19050327030c0f031216020f0105010b030a1404030e040e1e01090b010e01050105040303111e0d0906020f070501030c021c2c0102071503060b0d05010806091912050f03 73
    0x5030011602d4080caa1041102842d00c40e4403902444c90310759180203080b054400203180b030002498101003402c42d0b03482001004007110701c00008100c1945c54240e600441c4c0d01c10354011854605101c18028164200030710750f0300999150f141c1d2010441c0900500000d8455820a61500d003c0c825002c05403804412000c60007580c43c000000d50101c00c3d107400940301e407041e0000708050380b1034030041c0700c1641c0001c01c42d0150f82c0c26080400c00000c51140c001e140842000500c0310041c007014a1101c003142c0001c03150075480c003540303030800c2042c0c45000883e0f6a04407548843c50702e50102d5400c0005502135030000c508401144150740b00d007085c2609000c084a03542c05000001030320a92016820a01e1650b1484103440d400d031080303444020500002d6a0324034cc1d0251403070301260221100c4aa40c003d0348110001d045840011703807200c0000d00440d0040509100ba02c817580a941d00284c0880404500765440709442043e51039280c1003a103c6440075080301d82210300707002c400c00460310322810040245102e4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 605154721 1250 605153471 605153473
    0x1506090204080d020f1207060f1b090e0a0b240717070c121a0601021e01060e0a06030b041101020c09040b090d18050904060f020705160b19050327 64
    0x24910108020305e1300100c0788042034150445013007000111002e104441245421030790110344038602c111071030003c00c40a02d1443c000008154140f500a400024110880e40d14000303021042c7c1d07800030317240162141065000c0c4e00104550080b030100051207507011880c0c0420550034189907540e56509044084142401c02064003ca1544204056001405c01600360710600b031f40c103108107030755486039101744900310042c014019000581591003004001e0103d20107000700d1040040102c0901d000f0714880c007400e29000f1506c800a003000c0402c2c0914801c40e68000080301c542d603903544540030003040c0001072504600480340001c0720355580e4402a80940e000c3c0c00c400442c0d040010040e85403c00105c0c0c40d10078070200351040c0c440603052440b41d200b1074005583d603034843e6859142c0300004141c00080b0614040c400705e0400b0600c580020302d03164039500050b40920b225156104900305001d1015009440d00c0301c4000044601e214101943d04a030461005000703221280741044691111083c1c58511 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 605155971 1250 605154721 605154733
    0x706150b03011d010b190e030109020901091d030301080c1302160b070e0d03021b010c05120c0f1504120507050703031d18070503060a090513060c0e090103150609020408 74
    0x810070310f450064018031a40036514a00340d42c0b00ea010a21032090011202400400507000900c5c1e01c00f0b4100d203030700d6540200f403d180380da1551001c1c0d00501e56000c84000d0030700030b00d0050300c0c6a40008112070590f04c81034000e01404200c1020004083e034010164080f00d502401902d034144990300e0394241030341c45002039010a151a510042040d024126010300c1154040103100100790041081d24650304103601103511113038283d0041c0ca00b100c404200411510401740809144140d00014140454a003c00d0f23a00e500e400c05103440d40d4040441400e00000d00410100e00040c1d110500b0007405002c0742881420103000381c80e8941000d5a940c4254080380005079103008a280c07803514998000d00446059401c141301c0071081c0b081c0e0030028078203010700000202041441d0b64030800380e401000d50120920403072a2941c0d080074010907103001107074080c1c101040a410345008010701d8001643c080c1004d62903a18540350324941c03090034010703529101e5a030031010401c0c0801d40010005424100020b04d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 605157221 1250 605155971 605156009
    0x70804080703080d0c0f080a230903030609010b0703050f03060a030203031909050d051902031c020a0b010b0c211e1210080304030303020304032c040c030c02030706150b0301 76
    0x50b1110105a04d0400130801a46e00b1803076082614550060b002d0300c000552403514201d5011395445180c0ca040d03090f85000d0030080040400030040d80710300800c1d0361907692640e071035101c2541c0d40140c02d4004d001c10024405946031315814406103512400040c0780e0302101c0d90b69004641507501642c500c4110618124030399400c00c0d00300d580d01c00140000e454007004008541c42e103940728140080c00c50750030034406507024155030342002540c0c2d0b000c10401c0204000e00c1c00c0040a940c50401351021500202c410740002180c1050105540808880c5070207000303540030341800e0780d2103034900d20420305542070f060146075440b600c145105511194403159036551820302c568a0302c0e9086000348903204080320040240200600401924100c0381e040c1000340c1ca98480d4501510316510b2b648246200c80303840c090355019a50105209280c095041c2c400304892541c101c0218190f80c030100c907400150b40200103460000c3c00300e611144042c01008410128aa2030300308075803c0c2d500070b070f100d00c000c0303507041b01580703 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 605158471 1250 605157221 605157247
    0x30f05060a0e06090d08040c09230a0b18100801020f09120a0305070807150903080f0a090b0c07020a0e090706110a020d031b0f0803090d09050303090607080408070308 73
    0x341d002c204100140700500d4a000e426a4403005000010100042100030070b04101403100d8000180001c0c440910074404c41201002d03a54546508807000210303110f0209400e08414400e04034a0200540441c0c140d80340200c4100a0450241880c2f483c00b040d20800030b900103080c409020418007a103d5990749403900e00400202c0c5402044040544e041540304600281d006022074200b50b03405095543c07a41c180f406c1c0202e004095240e0b41002138144103001080603800388d01e00d840340040780440300d0070f41c84000d030b01c00803036440c4003000f4000c40e00030300454811419070014150645c13004100842160325000c64030003042043ea0300322000e520800c0244800c642048807031a44040c2600103041c034200940014107010b10101010341802401100062a0700301c840000780d8081d000382d44000440410310b00406103a104070340e80c0c0b000303000300480300546910580f040022120020010350520411408100d040d5120272070031103621b0700c10000040d885030144810401140506c54075a03e810b1040c0c8030b1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 605159721 1250 605158471 605158481
    0x50a05010806060d0506120d0f0f110604020105030a091509050d050304033c0e0a210b0601111204030302070b040b19091d0103060c09081c09030f05060a 67
    0xa41448240020003001d40ca9003070556620602843d00441c0c0d0f038450002003aa900b28608000e4094003804030181041900001c248004039542d58130b044148803031003012221010048088801078009030045005903120748003840c2c1103e007000c00081c0d070780c0340740d0ba580311341481d0300549404c89611050400c09102081c4609650f41034281003480c41c5141c644d070000c00c0c408140b08408035105041c04a0120f80509140200c4080e00444808000d1100c500c0042c15501d0354654851041d0a070201c042202014000500b1400c64800304144644415598800803018000e140a0400c244200d45a112010400c40440003034038007031140350b5a90550034001c1c1000318580100d520070b4170420003040841c2581c022540034040c1441c3c00e580b150900441150094555441070b211051580c0547c010f4529501c0400e048911400c0200000d40c414034081d00c5003142c1c1d200b0520a5008849000310f10942140d202030300c06114504901126103a90380c000000b134482c0c40640306944a2410010b00c24000e00c40d07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 605160971 1250 605159721 605159729
    0x60c21070917010e07050f0d1709040207050f0c1e0112110703050301180507080403081803030c27090606070f0b0a02030a050a0e06060d03170c2104080306090402010e0415050a 77
    0x7554803600640e101040031142e150800401c2c801800c9d800080c401c1c0300100361001e101c4000d0081d541d5221508100380c8d69426800700e140f043c010007203101c50625000310f007145000c80007201c2442c1a42c0342001540d40f0000d0303485600380251901c0e45914402144801030940d14402e0710303442d03180e50400d00c51001800f07d114101200c2c92030642404842070b009200203501542c1417030101c48541d201090380c0242e1010280400c001c0c03002106000c020010907003d0b150001e500054001c400d1640510320550005000840360403444030804a446410407000070705a95014140341030780303078102c0c3d80c840d840c501048403007058455000c000d0140c884420301a1640007104454140111455001947e80f2100301400d101d1190748046903010806000d8141e0741c8580d0040e855034401d80c900050075040e15030200382c11000b00d95000c0405000c10f40740721a01c0d0b01807a0040715090031030341c6440a1003203400e40680207034140302240c0d04c980d4142daa28010030030b0562042c02c10900b00c5181c0300912a42d0440d50308 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 605162221 1250 605160971 605160979
    0x3081603050108030d0207051c090617190228030b0a090e0c221401060915020a03051c1e11180f0409020d14060c21070917010e0705 58
    0x80100f01c460780020a48103161120034005a440401d4940103180513850001012004001c1440840064022003d0000c80d80c0701e41350b40c0c0a0014414400709151804c80345444107001c400d80d10904008164003502d52680360117144189103120000040c811203124045000080c0c4811f0607024a00303001c000c85000f020520014007900340c81e039a40756180c00144183c01c2c01507440d0344030480201400241003203510120101006158148218898070a02c04d02607c80403a04601e00056844050b580d9075104103099805000644c24a40d01150550f1040000b50341c0c541012110b00c440303050902c5425041a62640368041c000e22030041030742900d2621040c1d003003011050020380d001c1640081240342d07455040310907007110302860380014020101e80074065008142499500e041000a202410301603240d40300b2a83c2980d204030303c0c2001ca2040c44502c200710100c0102c21450145008141e039007001c414106040b01540751550000d0a010017240d00c2520f079140c4110f4142040c09104000107400161 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 605163471 1250 605162221 605162231
    0x18100902060304021005040b04080322061b03030912020d020106080d09060315080a0305180d0f0b1015090509010806061f05070f0c0e0f01030c09200703081603 70
    0x240004110b80801480640030b821560060103203d80f24004030ba002d0500449031a850f203844030241607882e00160030303881841c0e40c00c10001219400c2d604d6007800304d420642c0c507500c0c01c0b0000d0209407200c1850303440c01c4043c10340351181c03c4001f03400041c1540b0482030940c0241215240300c00001d003035035035035800f54910b50001c030400108540c0c408540404e481c050704001c109001700703820710604e14203c0c3e4081c111fa400303007032007203000c01d42e1160040000e03003803540000001d42180ca08002c0c0b1030300d65417001415034214000540015409007451584145031215080c241035903505500b00b0540f01c440060300040c1c039100c045c00f907032030311140607400f40c05170364004d080030703c3d0403008502180e45046204000510390b000415080e4420011107100c26481110950484064a407241442819000d80107000c088100042d00291030f50406e00d04a07600400d20045051500c403030341d0000c04140308140110a0076008466000200e0001042228480c0d07a58500c90f15002c903d00301c1d045014030390381c01054100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 605164721 1250 605163471 605163473
    0xc021c0206071502281205221106040b09090109050702150403030209100e0102070f0b3c070c060e0102300c070e0601080c0711060409140f010909050307061112181009 73
    0x2300c09140c443e250b1202040040452401c040000d00100c03038845074400703000074003c20a103401d2000703423242050075510144641d8132a05a8030607900100c800b980141d01c84031100c01000704500c04650404c0c024180145132405140111f0f564200240208010540d43c2042412659040000c40010b201030150034640c0303414800d02c070030244600314102c01c8402c091001800c01002074200c0190502e0400010a2401040c1d2036181a941103c601601c81d0311084c400041c42c40d000d420f1403410454141c0c013a04906120032132002c6203445019222003080d00344e43c4450010780c2800c00400091880c0e00040403da0700c0d210004c1d04c1d112004100c00d0402044d00709102d0000319040c1551046c9500c00d140a94560040002c00c40724012a80b10f05e5201d4202200780c2070a4803400580c45c000e14250b410701c0c10a0780c8454070b04068400b12980100b19910400c04140480d2544d0f20211001007007071920307450325911600780c3d015440e0580c0e802c1c3d0b090580440048141c1c00c200039400c031201042609010001c12 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 605165971 1250 605164721 605164741
    0x114030c0906100201021c05070e04020703120914120c061f030b0916090f06050102010614040209030f12030f090705010503010b0a021c0c021c0206071502281205 71
    0x10240100d80120f80448862032224000c0d0140e40f40c00e00e454001c10700680e10300200c4801703444e0547d1468042040e100c01040181003078000c5030219a050f48955003680801da0384040240303016002603c0c5179401c5200c51300f030b913030b42805945500600b001000e92180c1d60007003101d0030584090840ea0072424003a50306005810b014100d40c0440b5088081c034004c5907105c100e03c5007019001e68407101010f4100801003800b1090b541f00100e042060030080000c2504d49005a0880300207000e40146010f0100d48804249000d0300100004030026064500b1081c00b412042d14051024a056020f08400f00c204004148071076005503001d550040117282c0d10b0b26000001e442031006009031005075400180c5130020341d0082010003030410303010b804039800f13040e5100028805806288101e11503024480d4010044514100c2030f6a580d400500d00ea14001c1e03145d440364060800703902d0044165400380211440e0318513078080080070064203006020064200c40b1300801070612814003a8140c1d141c0340c240b1400c00c0c2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 605167221 1250 605165971 605165989
    0xb120c030708011502032101031203061802090114070c03021f050a1b0b07080a0c020c0315060a0902131815092304060c0f0203120a0528050114030c 65
    0x101d844041390002549100c22400c511032070f82d410743d4042c0a24201c0c01c8030203082014504170790045071036204032017000388118180c81c802e1249550700c000004800d82000250f0f070017000300385014103140451211001041030307176401001040d0341a000140b020810f5080007582414440030f00210120601c02401014080707010b83e40a12007000310518801441740941816000c40b10b0304800031003482d02d04100d00a1000c541220320b1441142080300035400c4a00000f060160320381c3c001c001c0d025015011000d4120090300900a80d440702c0603520015441c2c610b0f2004052500032200d0043e24503081c808008aa00766840c4214110352802c1e070310300d8403207550003408400c0d10b4100c8000316402146c0e1400c40307220200d80401c0c1d00b9030885403090000b003104d194030055050409441c1d02401901410f01a078481c0210002c0d5103c40c815400050103800441c1c1c0056403040280d155000c581c05c0398082c400031031030084c0e0220112070b641c0c030041c04501000e81d5000c1c0c010800310000c00c040d0b0800e001141c2804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 605168471 1250 605167221 605167229
    0x903030813020303031603060f030b040f060b090a0209011b11041a121b120304061404030c062309030a02060c0a020d0c1401051305010c0c0b03010b120c03070801 71
    0x421a2400318040030241d400000d1a2600101240e440341400364141c2952030490b800c81010034644040051018080407051003181e0700028100980e90b0b4989501d00c00c1c0c540460200e802c641e0725400400c0650f50000c2d80c1d800390040301801a200c0c1c072010005856548400c00c1c0c4800300048424520024140ca0303c60040f9403002d9402241c24070242d06034460350a014094260300c00d101c41216001c0100000302c09081c03034800d920081c052401281440544e07420104507114079001040240b14050140c1040081c85041804003031410741e50381c450050140c0c03141c02039400074070980c1e00c2201b84900d001115440e000100078043c503040f16031002a03030324203440c0340007405481e000c00c0c50b251340d01e802d0082650640c0c01820882c101c1c006d5150900380d08035507004950190f408410403840b294803c0007a076188510000ca070100ca42d090030300540c1d000b4441c0301c04842048210102103500040c803005103009020411b107258603030602c584420700481000300144203000050041103040ca41c060f921504607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 605169721 1250 605168471 605168477
    0x90c090a09060e010c0320070218040c0503120a0210060609051512040501091502120f0c1e0910050f18120d091508060a03110105120c03010311010c03090303 69
    0x161042d01e032900c041e0541480041c029460300200c0035a0a8143c3c01c407030742c1c000103108290011408030b45041424050018040d400c550040c844c056403002d0303640d1207904a4041c5500d114110794460000c0c1c80d0400809907400c0801010070461105a0100f04c802c156046102d03080c01040d080110040c016001403003000e00c600c0040080c0c103551440303141181c4010211100d003400c07601d06410b05d02d011b020000c05c2100d82264140d03644505e440980b007a03c03c991088058892142c58845c3c400d0034045014003c400c03981010071a81c3c5100c07144007003005031082c00326a00e548940746001044141c1140f000c02c001488004c001c2a12f80003000009c0b550490b0440141d400c9601c81c22010940715504012203c6461140070921082c081d04a140349003280c8520708401000510803004543c0c1280c2a0386454002040e46401d0000500454207440c481c4018501241812105c44062101c01c5081d541d51148a20000052040c00103581c90300c65000001c0c00c0031040090281d41c000c3c0703d120320344005020 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 605170971 1250 605169721 605169731
    0x90c0111010c121a13140105090709030b0a0608010203090a020a0512030706020a21060503060106030e1c02030906070f0507091103070509030a0c1e050406060e01181517090c090a 78
    0x90072449540c90700046000307805ca8040a0404040388000c1ca15000c00ca12200525070000800d450070040380c51048071642d40345841b140c03860790b40c00c140403400303800310305141d49444010808010900c05144102d0050340103102000030340c01032012030040b80d00168000c034030b40c1915200041001040b2542e041c4d01c40310041e03540e16240001c80b4bc96103e001100711682300c01000703d0218546800a03030a5032022003ea880e00d9a8800c4190700f22980f41310b8000a0f41c1001030b50244040c0740e0355001c11040d25500540707142c20440c00015900781c0c0b080390100e68100c03007035401c4014818208948005050103100820149000381c40c96102400018452010000006442c0c045074505001d200600c40c0d209401203005500c60403003010389014961404011031240c2e00000d41c51a06000d11811560903490302c1c40d649406500440f00d02520440d080f181c5000101c0000346541580b02a140060980e6201c0040b030f014448080248900034010080c1c0340c0c000c1204d507040b55543c03070820b600f00100c1038000031 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 605172221 1250 605170971 605170991
    0x8091e15090a0503030c0f0c01080105010c0b04020a05060d0f181a04030e030a080903010506030d050d0f02070804092301060219061506081605030906041415090c0111010c12 76
    0x7035a602d0a40005800d4000456a089100700001e103201c1004810703000d40f4420b0300e0806c01141c44d0340c024401c00c4d00044140e1180004507104003805a04140050000c0207020b4440d0041841a4802150006c081d995001113009003021449002c00c1418004030000c3d045040713854440000e65401181585140510041000c050003001c400e01200000341c10f0b034204006605180c1c0340354019541582c0a5420000041e9aa150100c0e036149072080d280c03501401c11048034003180c0102440707640c440100e5402c200960100302d05001800040518072008141a00c004400b284c034001804c1c801132401f050342e0300500c2556001b04082e14000c40003120441c0d18446414a00c01605000b140a44528441103001c29101d0f44841428410014036250030f1066100702011119480100c8040c0080c0c0c015101040c00641200745601110b00c25074112007000c94002d0440030200d10940d42d40e181a408000b6040c007950700241515a202808c00007003001c840704c0000908025100070b0180007640da101c503804 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 605173471 1250 605172221 605172229
    0x303111915021b0a0b01150e13020a05090a080a030201200315010c02040f0501030b010b040806400201030b0d0305071127010e10150f03110708091e1509 67
    0x1091141c00004c0b10a900f00c103003048101d1481c203005210041914041c0050011f0040b04c691650301c0015101c0581240728520303c00081d04103101e054100002004040c4d80c90750b500010401411038607014060100c072a240282c01c45510310003803803054240400c4d601071100c4001c240ea03842007251301c3d40f04d204e605c0e60004844001c80484001c1d8810b20300800000454a60303480349069911032100c0b4101d03641c031041c80d1501405a40f082d10490b41c843c10000f001c030200d03000c11001c00c03040c60700344c1c40b00c183d58a80d220500c07420154040d065030000c48545820366a060052080c0700e2015a03900c190302c0e005882c003d1451140d03210242560040c1d001c1c8551b1a1644801c44500c1c0c00d00002c04000d000c41c0000c0c800b1021020b01c284031824010202065409140302d4406040303e0300b001c61003d600d040e088040c0c42e10743c503e400360003c1c103607075100209d64166580c00801c1c2451180030880c7da02e4850380100400000007200c407000d16907111281440035200c0d00d440c8a08c0240a400345504c1d40e140700e00003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 605174721 1250 605173471 605173507
    0xa05060310111b0c04050f1005190f170c0a14010818032a03040f061b08040b09120c030d1101060b040801051e15130213030311191502 59
    0x9100c003c00c01c0c12034068080c0000c20422100fa8040f542070007980c64615441103030103800e540f982c01003892150b081105203010041701000c413806140b01c1148581d1254824403a00e51035103c08180010400e4200d61401c0522010540c004200c40918206040022110301c02d50070044041c107014208010450841403480790080c00510b0004580c0e8410201c03204010fa9104812034401417840c0341404100540044207032025903940c222040308103440d20604417000010f00404002107a1402c0440c0c0114462500030005400c0d0341004a680e6030880b414000304c66101c0c0c2c1c56116a0700030030b81c40d10007507401083c40c000072842403508003100300740350181e00c2c01040c01d41c1c403041d11208009030009114406411040c0720700154000c014075a0028601661480822955024444000300c031b201906d1815803089450380244210042c14840241c1e0f03009d175001a190801d0300440c81c0914011072030a41080441803650640400002c0704285640b80403140c00c41010418241e90045071485a1003004120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 605175971 1250 605174721 605174737
    0x160c0308070302221e03080f16060203040b011d070f03050717041a1b070210030e1509071505070807080f0307111501060e0909190b0f0a0506031011 65
    0x4019111603034480691800c1030184030303010716924244030805d0b02c040b441d10307284120303a00103403030030310f07105400340c400c0160b510540c14000c20344070300801c01d4040b400d14400f0303504c540d01c541c00d1400107504180c654116041924090b40403890354104008020b0340c00100c0503184800c90801007215140c80b0300139141c4800c0003403030242e180075141c100020300c40340b600b109a02082c0201252203d884039901c0309102030190046c513019110420111f8010308064103141e070400540d250004003010044100c3d8200500403c041c540884880103100912000f070218400412481382e12134545803e00c0b001500390b0041c0e20019011036004200c00f01800700e1481240c0c501e13507501c0c403410754914103420003402c1d444c500040c0751850302c58084941141002c00603041e051b120305072503290309005203508004d64500000c10041c001e000700070341840401620780c8800360700e922030450070070645824241070585000c014503a10040c0d0500c801d0005a03140440e42401c400b841d6040483c0782c440d1309100c1c00c6544034201c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 605177221 1250 605175971 605175997
    0x4090515191e06060504060c2d03030e1209030d0537030608150103140a29100e010b131a070213090213090203010b09090d0206160c0308070302 63
    0x80e04000c010103214980c0201094404200f4551502e0341104d65000e036000d000b000c900d60410000100e0034800655001182411540b090010044180e800b1041052800c502191f101d4406039442441446440c2400c16050741490030719451900207941c45410b18200c40030704c04001220a0159101c10402c0040e421030b43d5221140d00c0383d0440384045c00900e50144000034a041d401041000001c079914200a040078400307004c13642961106031010110070051445480789802d040001041e140381c04103613100041402c1e03542001409000125000200044544c0c180414180300d51154055014159104420400d442d851488001d450541c6181c11000c0300003540f130500c07502ca1503054011300c0d003544299004014a40600341c200250307004048029800030410000c076040f450103a1207609043d0004001007400000800440c902070000d95203c051a000801c04144844e010414a908081c4a00e40d07040c1303903000c013107004010030440500141006144404584101e2080d016201009402c00e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 605178471 1250 605177221 605177231
    0x92416030e070e010e0702030715050711070f0f05031f021303170418051302040c12050a0203010e012403020d0e0607090e09070810020309070e150108060409051519 72
    0x141820f62100c600744100101c0850810000d55041c0c0f0100a80303134080c0d8403012480111303244003401009004000c0c81c0100300000050302075203148040181c0700050086644001c2601c1c1000409000d85901c0e03002a8040d81c44135400440a01c040b1520b0624240d41d00d10058489450031001d2140340d1042c0c0c400780440c068408151480742c482401402101c11400380301598031070140d049002c0c2c48085641c4108024290643d00c0941231a0f002904858810b14200460a542c1400041210003d0307422440490340840180f00011052041c00e0241c04901070312485a0581c094110000030200e012108041d0081180d04121110350004080d0300950000d503072032803070302da440282210018400d0f40821408040800ea030321001148050035104400091700e606070701c801220004e0b42c40a02459000c0c41425000100d01174a001c819024440c2200c0c0042c3c802015400140bc0c403002811040c8a0703440c081e4440c002800014000c40131024980d8004055552445005050700503040c03441c40441c144 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 605179721 1250 605178471 605178479
    0x1e06040602100506010f170901060801020406110c0d05071206020405040203010603090b060111030703030203100503120c0d03050708190603060c0201021e04050303031f1a03092416030e07 82
    0x401c0b031a484080b400000c10a640da814011034101d11541c60b04008a100f0071f01e0304c4207101100c03440a81c00f041690010a40b155200f0141b401ca80c0030341d10180c001100520b0103c81c80201380f1070a02450301c102ca0b2078401c99031540b140e6446175007910440d01d031a10350003e2501000b003a03805450080000410442d26903941e844088c01604a02c41c04507240c00150000071261341c01800840b189a0411009604044d00c540c2c0550095001034101044546c1004000925540800c410346036210001d00058a40d01e56100c00c62401403000c0020040c14100070801545643c4041d2482d40b248100744100154071089800700010300395504060074a0341003403100500d85805400500d455440c0812101240e0526a403000150045001e10b130ba150b0410004141c064100281d102c0034a141a1050040315079110100448402c11049602d204038001c404c2103441e20003030000c10900e100307101040c0c3d0b110245449400044400810074001c4052800c502d00406202c2d40c8050350341d407000742c00c4a1681c2d4503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 605180971 1250 605179721 605179723
    0x61803090501170712021c110915030606070f080904110405120601050f0402210405010f0f051306021e04140f01020a0b070305040f0210080106030c050f030103021e06040602 76
    0x958040d0a003ca40c1e200e20045908041d0500148140c42d50758510045030300103c00040a5031040c015081c42c1c280f08080d980700d5100b14406d0000010351440f9840d0b0350400c0e03c2c140940e000b008072110f180782c0420700411a41d600d81c07000301d5022651248650b4044007041c9008035240c050071b86640c2d0810320f002216500c0e09208002801a98411682ca641b0043d4180986603515000d008040e0003050300202c1d04014100703034000e0601000d41c0d91040329a2283c91210300040d081c01c90301910b09a4440a40b41810301451082e140003585028050103145000da0a0340d5003641c21401c02800b85030b00240da40352250001010031a5030380c0d00c0c005181c0e039650312013020042070020304200380319402c0005c000711036600000708912503542c0003d0400c1943d0b42c0074000d400400004100343c80d0703000340c1c140f4040141e4602c10b00110b10066a184d0300100d505050008017111248038201090040411188040f0038119003a02e04582c0d040b6040312220303043d06005040d4015169006400c0f21000c0340100300d480e0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 605182221 1250 605180971 605180987
    0x1120c090302030f0f03040b070c031a041a0c16030201060515070c050627010c06050a090c0f1206050c0c0a0506010603110f030112050c0319031106070813061803 71
    0x10007103049031244e00384008860b03102d038010031140d91181d10420040152030318000144c074065002d4100394855541d280c0307800c2d416030400304259007581148820002000129000d0b120390215401c00e400c420710b001c42c110f40c000e201d1a001c1440000141c800c1000701403007508424080d040290502c0040301101c13014881c55004100225042110480d0216180c10000d05036030311000e283c1000c0c02c11032000b510000b55142c9034402941001100e001030340104031103026250084405900c00162022242043c3e00ba00e10f0b0794014001c00c01031a04100f03c001558079105040c40d800640002d82c0d602c071a507442d01036200d01c1401c00d01d54040c2d170051303800348200031407114121400d0707440500c06480050a40d8840307216207000380c66482c0e0300f400140005c18031a41d40e0480c1074450400c84410304a41d00019190601040318040d18107010f82d145401c041c2e204487c45040c03090b20000f4200d5052020f0064042c2000900b0006546641074460090000a0700003c071040d03d14104039001881d1400d00a10081e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 605183471 1250 605182221 605182223
    0xe0a02040e0303070203040308070501140c0c01150614091915090603060501020a11130e01050118020913050403053c070b0408030709030215030a0b0d030207030206070201120c0903 79
    0x510306074a5094421000c000c0320310580180e8059880c00341569180b0003140c100b82405d071032541d41c81c046000403601903409640a1101c0b00c40540d210450300d94500d00391b603603c880d02c40d08201403d03c01c01070290010301c200c0404c14655102c030b850b01c00c14808a07550700ca416540100100c0d6850700000d4007601c5000c001e41c0c0120707660740d50222944811055080e41e2640c401c3c240141c1c460503801010616452074006c1c00200103086910846140b070040d800d86252507480503560355a200104031a9590514015402110318815802e16511000140022003001154540c2d90744030340016040500c903030229100d0300b40b000c406403c10a285901e00c1c01d940c03856125401c1c80354411091104c211141825600e0f80b6510400105c1a540d665481c0d5030a03030400340c8030000740000b9107008801a03588205400045060b00289074503807400c400c50f070040d0b6031f944807503601408000c0b42c0c07a27011030340c049001c00075681c060f02d4260b541e42c403034401240c0c4694550b1011118904d40b1080181142d403003c5402c0490b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 605184721 1250 605183471 605183479
    0x90a03080910022415030307150e0109030c02060714030d050a0507050c0d030b0f180618040b0a0203090a0b04140f0d0f08090106030609030c0b010b16020f030a060e0a02 74
    0x26402c9603400f6a500c440300d10707058003e10f001242007851101e02d9189654050404142290400010320100346590040c01040300c04212901e1204504e04462103640e04e1a80350300e00900c00c9040a40b0090b004192002c4064082c07280001c0d41024000c2d1020705c2c1450134684000c60383d48000315100c1c440108015645559600c0c1040b020401c900d110300306035020610f042001d0041030520390002c0d4000c0000603540d07500000f1032011119644c1d01c010155900034074840103024245002c3c010003c3c2a010203c1ca40c81c01e518010038400411007041200d41d01001c20280140e8031340764011100d107030135035495005001c400d54504100402100610041c071120307851080f10035422000001c1519100c5801500c800500b0301d1681c030310403520507480340d07410002900c00040c4683c3c880c1c842c0f0382594a9503a040c1c022a000592050070441083d00c40c86c010300302c00000500702000303400d41125080d181880030340300f584249988842681c060020711387d42540010100030b02e8210f80c1d0b1a50b140c048005050f0f1113 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 605185971 1250 605184721 605184739
    0xa03150b0402180607021801090204141e0d080909190f05061f0c05030f0a08010f080c010e060d0f0e0111070b28020d051005040912080903090a030809 66
    0xa6060900940302e0b10f4089104108190319448144065a000002e051b43c0c0306401e2642d54004894509005020703200b030020240c1d54509180c03856400720441c0b48064000c0078001c0f1050b441d4032520703244032450502240c1c0b5601050a9041c007005c00d0084810542d0301c084a4400d00426000c80e0038440744541e12500e042c4030b50f500085071101111409c0380c050f5001400c00c5a140760424900c1010f00e00c440e01ca04203460b0b54055502c0301c0e071441e000a8000d40c6544000a04588250b82040400b801001d206448007903e500f81303400c55844418440400c0d052003e415440c2c01e241e91a03400b529248940c90b10700700241215075210f00068003207018000d0055190005241d440750b140801c40d403c0513017005c0200410f45a00499000c0c5c00801809c07050900f9002d013880c5074031703840c40c001001d034082a41408105418905500c900c48440341c0d00c002c0c4690310700303404100042c1c0e10314103d00706280d442c1001031995070b403040010b09620400a4450b03110310f91040101c00c1100d60170140560040c1907521800c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 605187221 1250 605185971 605185991
    0x504050709230702030325111507031b09031527020f0616080f0c07060e09060108011d04030536040b011403060310050c0306010f14270a0315 62
    0x5c0c6034803040c0d0313034401c03003500088401141c1074541c442e080104007e89404501d030b030a95200c181c14918a41ca440007007501070f200344840e0552602800998400d1070844261004c81e04202030300004162000805000c0c01201e03140202041760301001114419403420407000e12280901c1c030781c0030350001c01248140060095581c090034250141c401804000028038032403074080e01c0d002200d0f00320b07060401c1c0300c7c881040342418512050210307000406042d151200f15040300010031102d940c0050100307040140320030042100c00b0261065811403c1044451111070f225410100c400784a148840744150140d4000c2c16800c0f803000726198500303260418102c0d0f0045031041000705560010402e140050102580080406001c03c01140c010034024201d03007110b15005040b1055407030454816001c03410201c01c03c900c95800c51030300e4044100602d861150120301c41034058150086181444001180c02c40000c2c070603894600c88035045100600c000310740c917600c0c1791400001c0d420010090070750b801c0000c514 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 605188471 1250 605187221 605187223
    0x222103020309150c131710110a08090c120c1c050a03140405130b130504051b130e010b101d0405150a14010e0a1202040504050709230702 60
    0x82d01403504030340a080c0d400d5a600800e12240c0d03001c0e000501031401000740c070707600c0640c52480c20001c0185c0c00c2e40b2083e881200c010745007048820b140a0344441d082c8010821512014000c84000303000710705080c3c00c1c41e180c07020007a20702100200a140c002c0036820003a0114500021000c60f480303c2140e80ba8040c81c08045c1503400581074035002091607024025031070020740202c00d600080c1c1d0440030100c0c281340e0f40c0c0000030f0807000307495040381d41e00390707200c0f07056089041044150410096a84080c04681000c0da141e5507580c888030070452484040110342440c4c2ea803000b100702040341d04c2d07003018400c490b80c4941c00c2e402090b007000380341c2c881d0508854071171a150050040382a108140c1d15260b00d103400810a02c005070800912039030801c040140c0d0300c0156603600d8400c101800090240241d203c01c03a2001403c000002d01c102c522541001004101d418003260209404030340c11382d808a032641f41c2d450103602c0d0007403540128400c00d0404845240410307050a03c200640c1c0b45904500482e01d64590603 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 605189721 1250 605188471 605188477
    0xf010f0812041412030a03090b0106050918180106091505010f0806060325020a021509060d020a05161a100510140f1c06050a080d0822210302 62
    0x20150507001072000300510408258141d0a03000c1c090400c03040400d40490050440c1d100d0484900403d95950b842d00601444040150140c009401d2442c44d0840d0100002c8002c00c0746c014040706102d82000040c6909079004c120400801303228006d01a00f038039181a40054051a20301104000c81060000f500350720895101c4818a1603803160f1503a622600c0c01e00c82d44d45d000030103140741d022026003001e11445980e0429540d411840e40a0306850545d88100301044444209540d2003040a00c404406030340c41000311340c200d1002450050f80c41c062000203644602441c0300b0121400051911324051281002148414502004101016690300001c500c1441c243d030289035004290308204600342c0b40100d05120441c40e015109a003402e0706000d800b0416400009040303440d4048803100011a01c00d070040a0103003401310b0b142e15641e070804428580c0c40c80034007480b01c10004400003042c22601541c020101204202da0071110300011401c00001c9181d001034840040085030744e038907800600c40c1c03080d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 605190971 1250 605189721 605189743
    0x1a0604081b041413030c0807060b01081b04060503041e0b01062c12010609060f05190e0606130b07200405040302071e0503030a092c06040e030c060f010f08 68
    0x5000960b0b120302001300030000d00721070300320140a9464404004910504003401506109500c081205034568000500040b409460301b991030a400c0084a0743c00000130644040c3e403800d141c05600d030f65460404055902072644c6d04080801100b804e1400e0080ca010028160f81c250340780c0059020261180c10b4510a003190025036940c801c0085000314607100014280720010f880002c5541c80d00ca03c1c00a00b29038407a44204280c0c3d02030a8200154140020811b4100c1c0a0111015038146041d11741c011401004241e0b03445003200141e070341c1003e2500c000c0740b4041d0200e044090344680c01441c000b84411400c03280031065100ea00b880b150a4606402032030f2142d030b4542e02030a40d42d85030030500915a5064913120600c80c00742440840c0c151001c002404640d00a65940410300740362040440c01c1c0380400740741445502906074640000b104480505810540a503000149001c00d440118250300039414554164014602407003040d1203840541410303150510340c445061540c0d00700560342e032140044 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 605192221 1250 605190971 605191001
    0x2060f010e0601031a040e010e0d0c050d05130909110906040e1c0201330e1311010c050a240603150b01140f0d0b0d050a061a0604081b04 60
    0x1c0024a0b41d48a40c200c2c0c204a013403800c0c50b5200ca040d40c00000e05072001c2d5204210300340e40d2003240680305482009007000211143c14258000c2e01d403502e40a885601d9290f005040c0900007c4601d40590940a110010306e40000d042014a203203145c031031180154250580d200301d82a101281352482c09200b550035210400000b010034403000d0f521104030b4441c814155056568400c203030500540740c00c07000c098901e520300c25007903d42d0141510b20700b002220703081010600c0c480d50070042100002200511500d400000c20b51728a4840c4004880b04901640300410b0307801005180807c02120003400d0702e00313140001c441003549103602d20483c1101e04600c0f01804d40b01400d5030400621456602c4104005c0f0107151219211103003210350b1180d9885410746418440e00041c40100c01d42d941d201b41280440c04030740e41c1e2011510b545a480c1d407080254070103090070346d0b51450001d0480310404c1260040da0040d1166444664600ba52500d580c0181050b40c04861071402c1c05116107454420480a030640c3c003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 605193471 1250 605192221 605192249
    0x50306010b040803070303090c080111041a070512130315090c0605130b070212061311030c0f06310303021b240c06040804090b030708031c1b05040602060f01 69
    0x5241240a0488c2c0390381a151180f1070316010401c500d0038002e4070030b80c118006400d039445242002130281c0381e030813185119550764244032000000714041101c1803d00900146540c96a04890008c00030214503440280310240350340c24454119020b4005201d800d020310341255541d5030381c210a4580c2c4c81440000c0032031203164481407058202240c0a401c41a0014201c0c2c04030f40c8050344480d15003101a1060901d8807400050441006400d00307107000c1d101410360144c808000e951010401e18a454044030f031050101259030f03004252506414010b01c9111101501712407100c1d0001c03154000c49010680050140c101040c00c0c019120000c09114400a0604160f8240240540000140c00c294480c1c41013000c00442c002914100080d0740124040d0f50030380e44c1c4a15020034a0101d418800c103003402a00a854100004200401030740c00d80004101101741d109008180c0100030300d02049521a41a550b481d03180c0c03103d900401030300c290b40e407030b03001c0310116103480307a0000c02107000344100c152410410f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 605194721 1250 605193471 605193473
    0xe0118090903020a1407031403070206030c0306030f16150206131205130e060f0409020d081e0403060504030216030507050112060b1b060a0903020604170f03040606050306010b04080307 81
    0x2580500040781c0a44150b070821025540c40748032502000c402001a6031180c10203009009048001c038032440d000500851410800d43d02250060000800070310300210040000360080d1418082480c2110b900c0c019501d8818005c103109035a41058040c002c006c8080c2c02c029071400c2c0c0001901c90003032084400b4541c0041e001d0703980b051521040c1c0c0310303042008018001c0014081c4282c4264000e00700b920034506903468003400703008000491041d018031a40c1426000c00268591030329490005401080103590f41108030108104d081c410f40713080303d4100c1c000900205000c941d900241c0103e10175400d071000343c6003245490340b100607540405045604841e80c10449903000e0240e6052107802034a0128140350740341c1c241106c0c0e400145241030900310341e480140301142d0a00c2050b9008030010030030044000c1c1030324002e559200003030000b00400004000d000c10b48202c031042c0e03600310507a0035030240e80e0301d014549040640340c58859140a48100b1001040f2207240100340c505842c0000f0081d03080101d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 605195971 1250 605194721 605194739
    0x60114180613021b0102030a1401060e0d06200c10110a21020403060c03050604020f0403060e011d070305010c08060607110d0c0611070515120403030b03011b0e0118 72
    0x10ba4115104115800c000c43c1c4011001842165401c1503503000042e124a0124081800c0d14481c03001042c5510460005001098109400302240da0b81940c4000d12084545440c000900203550f8510702c0ea03207912034008814000c50b00810350710141405441c42c5072507211404040da8200100c01244903030902081524601c50880022003607255001d0b1012044084d09031003c83c0c0c415002035032003907160b05614842d40d4050061325004401501c00314901011141d80000500650000500c401d450300c0443d000c2c41000d40140341e0103503c0c100640350032500a14255540c0f10b5030711081f52903500304445000d25500599a4602c10030002d07003242d1400e681552110041d042c1011096804841c090030507011030603501d130300005411f094680031010410b440e04c0a1038481d680d0311652180d90315094003d030106081064401150042004043c2034890345016406403043c02d0140303130550b11b054540310420308500c1c03c40b0440b41142c4c1710f170401c0044010044038113682c1a00721100c0d80c0425003040142e440 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 605197221 1250 605195971 605195989
    0x605090607080702040606050904201c0b10110d0201060b070f0515042901050604030f23010501031406040201082a0c030c240703021b030c0601141806 66
    0x1c86142c900b4500101580010300315003140d080a40003074400b040750601420a8403420030641200c9000c0c100d040c0d000d0348a68076910546007217500c98407048003200c4208006402c07030201114018054801805003078002080e1440c0c100c0303041154440c1072035414002e4018815003099981444803903251140c3c030345500480c1814070364121060b10a4517610708242141e43e00300740c0983c2c8598208189840c1c80c00d440080c400c0258041a071044030140104041e50710300080b1001c90364401e521032104080c505252440c00001c501160700280002c2a50054030f5042d031244e03041c0e0781b04002c650384800ca01550240c2c0c400702120001e001c038040c00c1c08100e0004200303100c80d400f000000d00d83c888444e03c80c2d0346600e407508130049081d80f0790300c041004203007068140051170794110143c036140c0d4030000f6400c94403840c800c0601002c0c1415400680c81d1030482d54901400c090502c14000c5036a40d100c500f2400e541c411091280c001d510310400c8a0300c0346490910540d000c88603505031600220780b0740100708504d440f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 605198471 1250 605197221 605197223
    0x50603060f03030c0c09060307050310241203021b09040609151406031203040b0106030c120e0604050c011d061606060e04030f051c0b0d0b0a0b0f0a0605090607 70
    0xc0301d5006102180e60410040c10104040e5002c1c0010030025800c0c0240c1a101409041c42a08101014401034500060344082c1c400c1d1014085086000c00a5007040003400c0e0341280e00912034000c003c0349260000000e00106032195085a440d41480c0c46a100014101c074007541c2d001140d4008540403a0b1035070011034002c1d014061000b03480030201c02101c1282c1284480c41c0e01e040660040200a00d0180011180300b000d00c2072951440c54169113100125005001c0c0d1300030303d9610840400310b84c1c0300d060902800150304001b0040c0500e00c071b0004d90b550341d044500b1602c9200325201003020354408e541424000030040040f407481e0611401300b04580d003012000c3d03492840d8521507000402d01900900380200185000302c1114203286c00e0050060110f07100c51030500204100c103c0401d220428140c40400016000088c4403126400141d10250b03000c0e4064540b001600c10f0084101d256481594242d404964500d1210000403c0c0a4031100d144586400f1880501c00003e0500b00781006100d51 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 605199721 1250 605198471 605198479
    0x306060e2106010f030209060301053c100306150f090c0309170a020d020f0607030b0d0f0507090b0102160603020a1116140f090403050a090807151403070905060306 72
    0x2500e21194030b00d400000d90203440100b18400301002581410946241c0201007a0028409031070b0060707002e16036000700b2403401c1c25028010505030401c1801682c020700c0c220080c1800140b400c000b0080c0d0340c003801d18002522220f162031800c801c41c0e2480031185080310400722403149518902801c0ca001402d0f215804010305880d8412000050b45410240042040035495940c4030380700504020300e00000c02c01544255480601c0090a4010020301158031070443e1801041d084441c04c041812050780c254000c08a030351024851040010114003201070f500880410080c02c603404c001280e072204500990000001c04000c107114a03440303038000b0130200140c0d0811440c00303101c3c403004925181c2c0040d03008074054803020003031140c2190079011040c08082103500c440581d40860001d08210000380000703061200009101c19054001d0307031240002c10414080d01c151583d105101e0104c1c1950010140c0080c6500c0400b2400440040a0b179004902607562014200c0c100014400f10754001741580d640 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 605200971 1250 605199721 605199769
    0x30a06080a0c2c0405071707031709040603020303030a0f0b060403080304120203070f061e0e03191b2301110f030c07022805040501060f05182e0306060e 67
    0x302d107150f20205000701d100d0001410b0313051502c4064501e06140d00071001c0c6641102c0302c2040410140e824080500c105034180907500c65801c80050000e01c003d600080d0140400310401a41c1c501c41c0d400f070031405280d1101800640503003070070001c1510070350100410200060020801040003030300741e02d002c0c21190044a02d00380703ca4a8003404c00350310400c01c5501070740b103d91a4003100d0b0090f02e000f071034240ca500d040c860070b0a0138000ca500d078050801c480302056004160f0051140c800d8a00d10f6045107401180aa90145400d00c051120b0200c07040b051000c044c1c010856a0384014481c0d5090307411400840d0f802d00c4003800b1300845651010b03048124203501130082c034002d40da0342c070386d02d200084d0400b044101624941c04203244c02809980404d11861605004100181c1c00c1601061b10554500d480359580c0058400c1109100c4000105a000309444a018110b098085c14021140320030032100629511525812001e0310b00c60301811000500040a60409082050400c803180b02c0070b02c20b11794 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 605202221 1250 605200971 605201039
    0x20706091b080d0804080a050306180903090f0925110d03141302061e0c0a0309030201080c03040f0b07170a060915051e0d0b010605030a06080a0c 64
    0x1030700d550051042048030604042046121020802040d4605043c286501c291030039841380000c40c02504441c82c00d0200010000c1c00720b0341d8401f0504550703592842421480c1c18488001a0b981d040499036a01441c0045003122861520a07286446140d1a4038241c0541005801420f1078422280e101824004080c00100810405222603905c0403103503a000100c000300c501480c00c80c100302420205201d0020201d450168450a0803500141c030400c004546000c0c0900b041c0c201e9119488034010940a9200f5000416501c102d2101c00c0368000d0380c41c1612a01c580c0d440c01414031080c1e0b4024144a100d2f80038030009081010010b5001c2103d0a0034182c2c501e603d0090071000f00c04884a02409035a50010b01c01501584100c4000e0414098102403080c00c4c00c0109a0040705419080900e102032880030060f5501d151042500030351002c403078402540c0d6000d01420a07041900c0004c980c0703040000100750f503d40002c400070f000360080c9640480300d10f000004800b00ca40b008401d214104a520f4804d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 605203471 1250 605202221 605202233
    0x1e0e10091e0e06070f0c0213020a090b0c010603030f0801150e060f0307021c050a0801090506040b03030f0306011403040503030a0b040e0703140d0905031b0102071d090d0e01020d0302070609 83
    0x100b19812014090116403611200007018803101082801c14030854200c98800750b100c2a40303a10743c00c1c00800340140d461140e40c009036110f4a440e80140c04d20440051034551402040d08080116032207516050303c2c1c41d42c0d17400103a610900c02d020f001140400c00c01c803040740d40d02c00d00290081140c041d100614044051141344003075401281c8880150f442040501480200c00c29842c407004010725095061101d048001420520b061044405094070348003c201540e55560007051406002012030355030700701403107002416030030807203143d8046010000070316100181c0c80b044030711441d403001c0a54990f60381d428861004000a581003500b090307030b944192030006800c102d000c0c051405900002080250060301c1031919200d540c1c840d08002c098102001540c8001035079030780555800007140c0c4d0ba4013501e00101e02c1e2490b59030045c2c90243e6240455542d0000348003040e07004292032005c1d03a1800d03005032000d545a40d425400540141c3c00618400c941501c2a806071200c1c030301c10f80d4045210100742e03c81c5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 605204721 1250 605203471 605203481
    0x807080d021321060506060d0504030206100906050901090507090f08030423030c1003020c01020a030c030e010501030b060d0510060b0a2606150903071e0e10091e 71
    0x1610a00360700291211412801c85841070091143c0029651100e82c2203400f1540380b581c00c08014070890300c0b03201049069403036606582c01c190500340104514641030070000c1d607580041d503940980501e01a4003285d800524020442924030180100d00030364030b0100032000400c0010207036010421040b1011841c000070400000c020080500155100c40c00d0000505209a44062802d01d8607585204c0c20b1060b1404070f4405201b0380100c6000308185122501030740070340f2401c078886003d13510006094181517095484038810300190340e01000180c0e00c3c4043c2c1822a5400e000180140440500250280c9020094030048900c00c7e03041d25400c42042c1801016a041500030403c000d074041044500a5413210829441401d80e50303101c0d142c0c6a111312508000b9502400c1e150185400440d0400c0c01541c10080b01d0704998007030120740040d6603a0154101c1c080d2410800311085151610008a0110016000c1e002d80d00b19204485150303d4140782e903005000711f034246c0001034021022483d55008038411 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 605205971 1250 605204721 605204737
    0x1e0f020d050c0a140d14180d080d020a030c0e0405040c0e1b07080703140427180b060103050903040b03011403070f060e1f0c06090201020f070b122503020304080708 72
    0x14100100d548601401c40684110743c2000c4010a01004000320461542840321800036a40300b20894114104427086110b201100134100307000007154501194154407084410344540d507014500c0c031080c420841a2141503802903e4000451000c1c0200240c0794400780c1c01003c1130b0281c2c6002d42980000303107001e402c03c030001d440038034001c2148004d042d00580711100140c92107544601d01414007140800d003035100b140040b6a141d50026400c0c40c00e140d640301c0c01e030750351071900d032100304003160b2800308442803049803994002800c00300800c03103807500001a44e0948100b504030301d007180e08249004c1d01c200030051403181d0503c20000c1c002040014000000042d09095444490798500d400c180b103011099845140d1450301e90f4003c0c0e0180d65805260f1590640d03100742d000c1502d007140e000407480c0030680c0050202c43d0003020000210054103a000303280c450510510a691981c95140c0164510392040c000d080316802650042d190b18801c7d402142e100d0300c16001d803400c004403500d800e0740307603000350708 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 605207221 1250 605205971 605205973
    0xc0615120a06060f080c031f0207140d0e0103020301061b0204230106180e04140708010c0f110c0306040f03210606023f07050d1e0f020d050c0a14 64
    0x9020301413980c542c503042d0050b2048100802c40d61800402280d503950415504003005c00101c011a1400da021b5012101803a81004030040d0440081c100c09032039564607a20480407600c8590444555402802901d040b50175540701c17035140b580c0110020f0114a90400d00b281d22640d00c0c64400074200007200c00b041210b160078084500c0b03606010000e00b140d50304240504140035140b004100f0411540340e01544151310580440a0350002e40606140844a400c203034069420248903592441c1d01c0350f1190005109035580c62404000700c1c89090b101d001e144d12043c1c25400041c0000c0101c0c2d8040c014044440c42450701402c0d090790081d02202c40705100d8408840d80b51200c004105082c1d0400c0240f00c00c0a600d1120100c0c0845000320b6040e240c8007120704100b0718000d012013404034003020103031030900360444191515681100300040c0b442c00741280340e001c2c040408821144143c45280803010200c8207400a141c080c0c4802001d944a40042000c0850b82c0304014a900000d10a1600d444130000702c54 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 605208471 1250 605207221 605207231
    0x11130e131e05240105150c060705250605060a12020d0210180605121602060403142b05010f03031403060d14070e07020f0a0803060117010e0604110c0615120a06 70
    0x17404001c20810710a000340707800007043c031488141110204070320303800c180141031050381c0e0820101c6d441d41019681d001849040d40d100c08403014130880d43c001600c10b14040300c10740320b0700d0380b0340d0013071410b001c81d09e100650000907055542005017041000800b0105640c1000c1202041c008807d0b540f05550760450000514081000710a251078400303c1034024480003200c00b0b240e555000300a40ea503c000300040d04100050000d0b1090f0003080e4111030901c2c40310703000c010b49960107421a403140e0115a8aa40170070385008000100350701408844c0c416a0f03815522003480301c2c01502c0e10324260304040e002035840303855910101c0001c0c61030f1411109910818019204081c5001403010380150003c0c8500150b400846100c9081ca00100d400190395500c010510349a0701d07103200403a0150885030b54500c060b144a40045103880c3c100d03000381e03c140c000300c90600c4580e034038140c01c0000b03004074100825a94840d202044c440501d48050000285010340303580b44507207068617281d10349401000281c9402f6a55 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 605209721 1250 605208471 605208479
    0xe030604150b01030e0a030f1e0206101203050a050903030904090f030305091c0c1a01121b14060304050f030316140702061c11130e131e052401 63
    0x1e4000c40d41c20110908042241945000f0500c1d1104041603005040055803400012058028604000c0188030426148891125500065603400c81036500b107910b88181c41c1c3c0001c454031720700381e408080c40d0316a0b20386003080342038038090f100c0750007031400d065042c001446407141c55104d610941c8107150040e201030040807060f01740074040b140b0240c4142d03200e0b0044003a41450440d80092400c1d4415a80341c0700c0627180060406074603051118001d07041c43e481c01c1000084942070000c0300034a444c0520701e220020300d21900302410041d520303c00d1241030250000c44901ca443c01801130365106014030151110461a0402c882c08e682c03044905011a900d107140b0701088a81c05078440c0100700b2445c0070b80740740040e69000180103006814442d80401603c0c510001010402c3d040020f1007184034070f061780c036a105141c11383c1c00c0e48081c2c0107078031016400d480010480074000b000709110303070340048899001800e580f404582c50a411301080c2d410740301d00002008040524804024950b1070020032913025410 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 605210971 1250 605209721 605209763
    0x141f0e0a092f1008060d030c0515040c060e2202071209080c09040512131706070e010302031005040b0114030c0414091e0709030b040b01050f0a0f050f010e030604 71
    0x2c81642c03180210700303699080104030f801c000e07010f400c00801c881002d2600d08529085a03102e11110000f040ca02070041600f450814103030b00709000f60f105002a0a40c1070311a00c003150107035044e02c3c0341039010030b588022004001114962140500c1c0c19100549040210b444e070342400845600310800082c445801080b42000510003805544021600001c0ca42415203400d075650384401e1080455881c009a60080840c107500c40304000c0488034003403110005491842d5460f0300080f141c1c01c6c0400c2d06c2c441b094500b58401d108583c40381d9000b80c4982c48403410700050200804a401d5003505105001c1008115405000c0c061361181c0150118190745900b40240580190039131130302640546808024008101c030300e48410b80b11880084100755060762400000c85d4403004681c005001090301c0070a00040c0aa00c00f400e5043e10340684004460105e500d041c064516068814840100b40d811410b1001d49030507030110400d80414074029409621020000c0d040201c240ca00300c800c40310b042c0450a040c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 605212221 1250 605210971 605211053
    0x3050d02031c0e070305061312090308030a0e030f0403211403040803190c031a01080105060f0906190c1104050118051b0409141f0e0a09 60
    0x5980d1014505240080c600d99280d01c200040c0c0300c0d2140e44500603d02c0e904020007064008581060403604203062015240a580c082d654083d00c101c02c00c0e00e071800c08280124507078412640d000c80010324540e0303a0422030f0020301460402020a0204200151044100b000a0409903025a0503030b2403400b014854801c000c10003c050340103004494070ba00e4040526502900d511640102e292030341c95072012980b2400d10258800a400186800305010030315526030700c080510054020841c10998070394006484c110801d204440d401201000410050300d0240003415445001910f81410f118403000301104000ca003041d00d900003003030180d01038248900082c225150708030903601000f2035410304400c05000c0301c16021282039680c90300049900c02044d884610100603401d062140c60700c0c1c47e1840540608001d6150500401402c0007182e803a09048015800361455800c10030181890040f00c0c40203040b0041010b1001548d4503106000f1900003140030705144507003107001030b00308503101402c40d00328 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 605213471 1250 605212221 605212243
    0xc0e03101103070f210209040e0c0915040b0a030501050f010902090112020a020c090a0203090d0516020111120301030c06030c0203160201230f030103140a0b060904030c08130305 78
    0x2505150304110380c0188a011a0340201c243d140a01038189040000e40b801540c0d2060350fa5400c0c40500c43d2068981740341d0140032000310481c0c060041c801c942d502556107007034a8601d80d5201c50f1761008034446840b01200c044040070050808143d122900b400035940400580c81907450b0394407030b030400ac00d0342d400324071355405021440d01c03c60601a80360002841c031854080d498011541c00a1000f2800b070003040b0714841801c0003003600380070386080802040603401c1507404e0003a80c81034500601160303008805454000383e071034207085140e00c0a0b400469401d40c11816101441c09440d410707000e0321007210f000f9400fa500400c0321002035841c0840080c200c0c0d000032811811900240680880440c61032483e558403a0246844845005488926244141c0c22068154444000540d010400102c0ba0243d03040f00d009060b0390140320001070146480b40d607030a00050048408030001032042c60b02001c0709070454028605000754004950742d8039041d6011084140e80021440e90400812204110782e13440d030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 605214721 1250 605213471 605213503
    0x50303090607170105012f0d09050a1d04060603021306080d0e221107030e15030108120c0a02040e0115090c12020906090402130303030513020913030c060c0e03 70
    0x249001002c00c8103460f6060090070704204255802c501c034040c5040003c2c00e9420803a05415845003107411042c0e403190380340300403008500c02c0c0800242500c0c003091580211f0350720031041e010084060021501900000300100d94003a60780c0c1d00840580c54801d880c140c402c0c143c48000448501b0b0120b503031714211001c039040042208407100300c1825101c4008911034819088004c81c0c00d031150041c0325000c0c20f41e10009103148080400c034482407590044041c01d4040003511480d8040c6400304215001d48824024001c49034020407a07502902a0350006080e160341c00710654241405a0780028140da40c1e240005100e13a44548001090350001d48403100100683d03c0200310a40000d000582002a0b40080b61031070740d400710703200442c0c0e2901d82c04c440d41188002c10071542c441000f124100140c8080c0410b43c002850302c40007440c20552100000805500280051159500e0ba2281e80401c240c0309000c40400c4003000b12003001a685004524480303105844100421000c01c090500c1c10103205103010007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 605215827 1106 605214721 605214737
    0xf150b060a0f110a0807030819060e010302040f090327030b01080708330718060207080d17040b0c0403051501032f04020c010612050303090607 63
    0x1d4104603201c103807040f100c0301400355407480d46480041c07051504100500c0031038018640942d100320811190307103480c0f050100d90019100c2c40d5000420090340b08005000b186040d0180038a107503004401080420016280201204022000844c0c04408000c41c80c00801c000c5804602840d002405818956519050f9a950700c55a100c1c0c03525502074052030600786010328020b130f0412030301c0c1c0ca0303140320412101c41043c10f114006440703002408040740c2100b0320f100342008110020501c94002e002c00b030345880101d03030403c45480d0700e020801c42c02a50100e0b0500403681c1d41604641c01c0310a0001550720b03440410080d210700e4001424501c03d0080048a4019400e400c0d8160780c800d0003000f40039542100e43c074062451000042225042d105824203007400d240d03000c0c042c1070184600209281350307034010780d04c040d055081042c3d0b82c0d0b030400010030202c510104070785034001c41d1619029203 = true := by decide +kernel

theorem cover : BRFrame.Cov 605035971 605215827 := by
  have h0 := BRFrame.cov_init 605035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 605035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 605035971 ≤ n) (h2 : n < 605215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
