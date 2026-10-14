-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0167
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:13:44.247555+00:00
-- url     : https://prove2.me/submissions/9904af2b-a502-4deb-94d0-1eb57d2c56f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 29856120 ≤ n < 30035976 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 29857370 1250 29856120 29856161
    0x928020616050d0507031407050111030108030c1506090f0c07060f0f0e011e0c03060305120c120301140d050a050d020c1216050d02031002070602030601091508010504020c150a 77
    0x401c4d000b03805450009800d5103844540808904c2940c141d680402821200d556a400204c03115000c0b42000c1c1d4041d0405c0802540c40d20081203e452a281003c0b01a400d03c42c8240d00700b05071135403900b51140c0e10186005100315991150f40106c07006026409000b0039180c140f041d5000806419072021001042000d41808007465400005080702d10510180544101d4410401c802c0704840e0800700d0303850072030b1800140e850fa4039140ca5003400e001011841c10418000b51842d0072104c02c126061250449043c098699450500215a00500c9441c081c0c0a0110301c148001840301c00d1000184d4290030000780d5030010742070744c402900d62403000034541c4100701c10301c1e0309030203581c0015800d40390b0100a0500f45c1414208810007210341d5401c04100d9241c40742880714a00400c150002c0e26240d80710381409a00c80c14290005082c0c444c050b040003007042c2c03030490640340322680700c1c40d81411213070705a034010707a60f81c05900200d00708105805c40041782c890041c10f01080c040c0301e034401e0140b00480e4014520 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 29858620 1250 29857370 29857393
    0xc0406060e010c0b0613020d020301061710060c060209030d020f06131505040606080d0804061a090403030b030106090c090302100504080d120b0a0e040b01090203092802061605 77
    0x800880074140d00e8009102c1907164400a140c2e0300950340c1002c401800844221900e07096402680d01c15a40710030f410f42c000c4010040103400400d0b423411441c691035407424919100f004910150704074030505040010b02e000c800140001f40d411030340c44410103801e64400071240c24020399903407140d00c10740142c1e00c00c2400050060321703441c6540d041a5440b19100300d0108050743c050010b01800744c8250b03481c95690000041d200e6080208202405440c0c85240c0340307203030034100401207840503c0c0c0d440b10300d2003070801c1c40415036800d441d1a9105602d0f080000f08140f1032800b0134010641a0040706585152440402d05141c200100c04101c0340300300c030020303250640e0403402c4607940240c1c81446403591040110400060040300c0c0c0c5001042c20440000c2c010031f5900000312004415413204100101030f03814803051201c17010740c0a01410f022401035140d42441d5641c1c0e56200300c5406c440041040200003004480c0d503d1000c540400d40081c00241c64496070040408416241c0c0b40032951885400d18241 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 29859870 1250 29858620 29858627
    0x40207110f03031303030e030709090b010608060103090b040204050a0b0312040305010f020703090b07030201020c060a0203090d0207060905060d06030204060305010506090108010c0903080a1106010b0406020f070f170a050a03020c040606 103
    0x1280c0c0150000c4c0300300400e2031a6001d0300c42c010003030030741c95040c064100003081d07103c0940b0400310210301070040c5102a501d07202010700304140280c1506d04040c104074010000c244400300c1250055030644c2c00007410759036600158000c00604400b5a4140501c04422960001c100d01400c183c80c021030007000f094072040651022485406801004a2442c4000304008104040036060081c0a800007500e403440907610142061b4045410300300f265404401e0244c2c6013400c10071218a50b880d400149240d50a16601402e14604c5100c2c0da4801c0d5400a5541170525041e0803000003564041c0060042d00d4076842c02c94041c02040b69454000c0d01000000102440140140f24a024041d141c0151490445d22801035551000e80440d003400f803c01b828031031403041008218000c1c0b50480c00540c03250309000d4002d08142c45000c82c0030140e441100705002c0003207000c01000c2221a110ba1401403284a08441c5007404903003100070740b150042001040a05802003148501c01000311010071049844078410f4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 29861120 1250 29859870 29859877
    0x7060201110c0a02061605030720060a12051005090c07020f090106090311010c1e0b010b0a0516020d0804030803090606010503010311012d1e0809030d05100302040207110f0303 77
    0x800396400f0007080c40243c180705004228512015080142070b071219228185542e11440003191560341d807c5c0c0c01c4802141c21f80814078003000444001d0718011469030000d040444031282902c485a0b90030102d5500404070070f40350018500504900d800b840d092002c40300581001c40300b40d000d00181010390b40145095082c59042e10020340301c10ba8001e0454903504528016030b02000e045c0a009820314000c10289080c09000c11000d00142c000f04880780391040400c2410f901a00ca40c03001442240140790b0054207940558031400407094421101e400001c40c10601c0d2030020f4001c050000d408002e01c0025030080d441a4403c208442e0242c4075000111281d00c02403002030000c0d040802d20311410340c4a00090903020001e0100d14414260b001030b240708031030303e034109030300422002c00380d911503072210400341e0b00c40740c4d00e03810610442e1400c606803136228860100000080d5950b140024022008900c940e000f458016204548603034480c50b021008004490003603115100c1001803c14524000084 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 29862370 1250 29861120 29861137
    0x10c02010807050f040e1513050105030d0c17040e01060306060801060806061c020a0f031b020a2603040602070515010b0d0c020304090e0106051503130b270706020111 73
    0xc200141e51911001c64850308a2101342c01203460410000500d4120000c03800c0c0a00755a00e00444030940c000304100510610b80985c041017401d02c0d004200c213580204032303541c0d01000c2d4103051410240500d080c400c10030174a455104440b50100b00841c0602d81c100140f03061b6400354500b04007458468a064490b61030902c900000541c81d0740016540e0704240340070f4001c0c0040104800c0e13101158a0b00507040e60440000100080d104a0500d00c1080d414050701404240e80b031001c0d0000625428000d4455424681c0600b055180e00511900d030300724180718024a80311903542c203489040a00d04007020794414481505d5500c41c1540310603c959403903a049048500140000749006250340c403030f81c0600070b04040041580800c0c4000984041940a890301c44043c0c0c0703000058080c100f400f04941c03400c0801030000d00f0601441000300c0004204981e0400c1038100002c0c001950328401d5401c0382450740030340d4111503d01790a405811500c0000e0307007800e58410381c009000d031800e802450030300340c006d00c0807 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 29863620 1250 29862370 29862377
    0x6030c020f0615010302070f060c020309040f0b0a090c0203040905040b060a06030b030d0e130906050906010e0708040803060a03021f08090a02060f0306040b0a0b0903060f04050606210d0201021305010c0201 90
    0x305000f00350b00a90040400a01c5259409a03014a546600013100c4101801c100503170000540070843d446d02d445004154940041c04103d00110000400d40f901c01d580104502580e9a20003c001640200151001445041400d10443c40d0074031300130b004e10806075401801080113500103d0600d0080c0a50440090007400600281003104c00c01c654244141d5802ca4200c02407402d020b8940c0a02d0140051180c02004042004e0900c1c000080c68010140d1000003403948500a1150706588450714907001034200003526103a07261640091011b180d1544029841320741558142903040300e1404400d021141074489020f207035158012903898000000c0300a520407020409031244000d03080c00396030400005080010112106004a00d0910280e00601d0b031085001c1600189442c1c1003018a07441200945a010503042c650b440c243d440a010b0300c2c0e188104074414882d0500310f2054489142c480c0c2503c21541008045140a03000703502c040c8250b22000c090660205180d4080d403944800140e041e034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 29864870 1250 29863620 29863651
    0xf091b0305061f110f061501030506031e030d05010e0405060603060c1b10090302070801050601020d080103020f030c061909080d0507031103090411090103150f090c020c0a06030c020f06 81
    0x115400742c1c00d80ca0242c00b005001c4010891810004200000c1445c01c1d4040001c140c1418945400c04034000540801c504060078181080400d45000c180c3c5041950030b10107048244050368a00350840c0503800103103440034540000010302070510300c00c0500076401502524485d03150542231588a034421100c200d40b0600800c00030200704000d0540c080d550f00e41c1800d4880412141030001d040d200c0640040c0c006a22030a0184411a000c0c400c40b41c0116090005140e01c0c410590082c0094a051001a200d409025104403184d1000d006a290132140101103d03915402001c141d6040e0000c035a0a0000a02111010501c03200002d13140300d00261075110385003418646d5a041b52910250300244085005c00d01603003959440343d025107684200005801511150008001422030f020011a0704140c0c103807035000c102e08000010b0480c00e880c1d02c0400407a200954034002e81c03074000c0f07601c007803504903500341800212950b1642c4000030003800c40d401d0300c0340d03044c40d81044c1e5a20602a5100482c2d6170000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 29866120 1250 29864870 29864899
    0x30e010623040207020a082401051507080d0c080114040203011d0714030109050a0b010309020f0609010504050a080a05010c1805012604120306050616020402030c040f091b030506 78
    0x60031094502000401c058038001361503010801d00042540700c1c03600741e030142c0c1d104011a060032042c40020122040380c0303ca150b14000004216a0324007500e2540c0d81400200e440038031a950003151441c2c440000203001c0400e02a80c001c3c0340a00134415645040240d41ca4100720385403500031a81240c40180c42d04903400c08103600c400c02103001030106418400d00a1801d040b02000c10081d600074002c1040010341c0d454085402c0050300c00d0b29500038101450000900c0042e030718091802c1c8001c40a59507940c56012540040e80c030b80c826500001d5001c02c2194001540120000d11315100600c80e200903c40e19003c09001e0b03a030003021800d6051003007064003041c0415407040328811821040e446c41b0101e584008c28011080d42c0050314165080d00354400490029a0035018181c010801170310814503003224010100323007107044418000d119a8000000c2503500150703e082c5c9024003101d0003050140c1e566406034800410b00304458415216100d005035103000e0107407090f54482c217030107081d51042d240c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 29867370 1250 29866120 29866169
    0x1060b09040b0d051203040201020d0c0302030d0504061e020c010c0207050117060303070b0702010902030601060207060906030b12070807030c120b22060608010605011202040609050d03020a050d08040201030e0106 93
    0x42c0c141d040d402c0310442d2258004903030208a400401000c00321429075905050000a043c541300764502000d0050403a076072000282d00100f2981032001d41440000c07591907030702e40305003d4041c11801c0d40030305000c0c80c1000100051075000f80343c02c121980081101c0202a03400340c0c4c03502064807134540071407625a44140150100031816610480003030540b442c00400350b49000c3c200205440d0000140e540c0c02600e411410108206405480fa5000504103203243c0840105909400e004400406444418442650321025019010b00980c40150f0308155145d04040382c5d80c020700c1c407007a00c00d40905800018030460456007001903c0e040728034050240d6032034070f07101d10700b50741400f00c6440c44103144c58880101d586841041d01400c561800482da05140100040c244011204810b0701c00380f0400c410403401d500108480100c9106403050000324049080603410707d0480c2030302a06030300030031907580303455680040c249100c5c504c00d8138100080210a10441d00301c4013140110001030b00141c6444408804 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 29868620 1250 29867370 29867381
    0x90c1e030a1b09051503060703060b1b010902030f010e1903090302010509131b09080610060818070303020c0901140307030303021b030f07020111030a0c080304020a0801180c060201060b0904 83
    0x70300c1d1004212103980b840e50b501100c808032404218041780500e51200c510702809040d800c0407851806004171410042c0c20032440c8a20000340428504001504012000039041005029001002e5440a0141c050700038007a124000c1083c400c1d0058042c0280c4003a000341000c81ca107901540d8900c8403a0440d0b0041d03443d0b40c8460400c40e8440c060000006820010340501c0076219002c4254040d040c40c99000a401c116981d00001d0700c54100c0810042c965013614500d004a070060729200300c86d9200d084030b002140044101c0d13250140641000403040c181c000903801c00105d0300350780c4040d5607031341d40308a421003501c40c000695141d00820010801720f40300c1c1e00540000340c01400840c03049100000d92510715031000c4540d02560002107508000c0d581c11002016004804201961810204c041c006001c07001101d001491560007001281c00d40d2a945505400391049030020480941e4000024a9003400f0440c1110b20724818031002ca4010b02c1805941d0032589500f8181e0300748100c080c20007001e4103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 29869870 1250 29868620 29868653
    0xc080702250b03040302010b1003020708031506070506040506011401081911040504060e0f06040603080304060216060e01200f04060e0d02040203010609090e010203060d02041802030105090c1e030a 86
    0x20001c034408a07403030110768011400b96111307400010342070841c6024400d1100461040409140c81401154046041d060071280c1c01440d408007240e1808002002a82900500030098440c1c8104070800040003000511a41600d0700340150941c09511f0f2001182d030901d085510240e02d90a43c0380b1070702c051586401c103058161020901c682495161808602203070390b2a80021080c40040c401d0146c0074a6031060a0780010090340e0a000081c00c2d0b81394594a448080c0c40103004640c00243c0b045940c0080e5140d0044076403002c4103100c40002100c04074041c01000346400914000502c0000c1d0382c81c450000c0794181040a1841c41c18140381c00c3d0252403c6a03c4410700d50800418980742c00141d41e9840198040c00154481c600e4842c10401031300101d9500d8144610300742c3c030401c140314850b50794000c1d16030340075411a004500003054405402460400c1c0000039055820a0144401245c0200d5000b00c045000c0c0d54100c2c85059040c03459080d0740400e00d40c9078040d04100310a00215941041584455 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 29871120 1250 29869870 29869933
    0x312030b010c05100f051303090b03090a0b0a02090f010807080a0b0d02090702031e0c0309130e1218030106030b070c050304150801050406090b09010608100506030108010f0c080702 79
    0x10806501e406007800e10007100034071000d545500317800c40d800c19486440d4110b404100c0c602d848400c0d0340d030f02415034005801003010100340400010411141000741d01030745c031341c40010754040c0d081c0348000c0c0b40a900207050503031194403080c400c200d16500c1006951711a2174569a948595191203080c00010719440c91020340058943e80100d001d80c4810f207040307004000c26402181e46070180b6080e000b001c4a407107140c5045050803c03500428110020030303960410f40c2120581c1080c103002c0100340c01048200c15000c80e41c0a05054400c9a0407a0340c05840181c049a003040c856851601c109422540b01e8000189900440000305140324032840b0b403080341c1446003007203901d0304d0340340c00c4040394041e000c0c401440040c03020401401142018092a402001e141200303015510b60040003510b400014000c9100b00444880000d20030701d90034000c2c0d001407801402d462f91f81c0d43c460324420701a20141500100490501000b42c001d54400c0c445203114140030f074003510620600002903500c2000705140c02c1201c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 29872370 1250 29871120 29871137
    0x4110301061e090b01020a0f171c0605040501140607080304021903120e0904051e12040609050418020303040306020a0306050a0b070302070803040f060e0d060510080c03070312030b01 80
    0x206007078100b550103203409002c1c2c02401514007068082640e0480300da150441d0807841c0030300c00140c80e401c9400c030303daa4041c41c40a08440591141a010b018207445000140200d415107012442a648400308ad41c1090b01d09000c00d82e00e642c0c1031020000080d03801c1d9005a81042444085010303035000d950818401015042880038241c803900000100d40c0013074076032141030b0300c0850f8201c0e0080100ca4070b6000503500c2c81e01d189041e4440c551914076080b29013161300e10b1000301c4100700c081480340d41800d00070001d141d5200c0c1d440f0600104618940d004460043e8a801d4580100250368032150841560003002180f4207421540e81c01c01030340180700b0380e8090588031000031450707076111107045003e00040c42405031110441d0400074502800c560000f016500100418400320001803840307000c2c2c03401800c05054803041240804c0484075080c0d0003901ca240b5003002c0c05228404003074031008840e01c01080303541408980c01050303200d01586c480244130f0446400441d1000b070190b0010720785440141401e890 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 29873620 1250 29872370 29872379
    0x622030c0c0e09030408060106020a0807120e030318040e07050f1309020405010303121508060c0a120e030a0909050105010c200d06050a060e0108030f0c10110a080f0403080411030106 80
    0x82c0030307000d5881c0c10381900042814044054100041401001c183c402010b41d4051078071001030500c80c070700014260050240a40c03180c28003130b0710203450b007150140c1220364607000c0840460710300e1000350106124500b04048082c0c1d04100103680b1054030402401121200a028100b2200400394019151041c0c1c50710042070260380c4a22885e07000b503009031a40000040b45441e144e04442103202c140101d00d00e80d05e418080d0030400140c2c0e65003c403018001c0d9039a01c0c5840c10654000c6000a0f07014041070500115000404d0080041c00d00764a040d1030f4040ca0945900240c3d080d2076007400352a0019030381001c035101090031140300c426100c0e05008841c08004552000c50803070540510141c40700f170b482d2401e01c0082d40b0107120310001800345650a12455060203140e40d10380c030580d00c0c0030160060200d1000410b82d0700380300300c2d00036510b041c0d801c01c0403c41000304010103400184526010940b400c00240c015071511401905c0b82e035041c0e99032429a03a0307660315000303032041c2000d0445d00b640d6102c10124 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 29874870 1250 29873620 29873639
    0x6030a0c0b071505270a0804080703050c0307060e040b0112090f23061f050a030b0103030206011a0702040e01021c090506060a15050711061204050622030c0c 69
    0xe050701d540a2541d40c08503040c44840d81c209510948440c901c0d00e02003120f803600f26a01035044c00c1c070359030000c0040da04400c030761858104510009010b0042c0041e000800490000303003801201c1c0309405844524110600b01601c441440c400c100200380c10004001d4140b4182e8040841d58005061030b805039403201560300104c84418500300c800304070204425061201c9103080b0540143d18501403150800780c000c1b040c3e1120806007042d1014034801041e45000c0d00c0400265020300405130401c07002c20b66034144010600800c1c4000d50140c0036400001c1880b44960b220195035040d8994090b00e05190350b82440011b00e07803c45443e105541c05e211400c41c00c200c038500b41100042c0d14002040307500c22030a0039410b00784060031041c0b150b4495a0304000b0f4a8518000c0c640811690404540703a05e0b030750602c0150411025051070b03010f10000340c4004501c0c04c070108140280d0191088030a0f9a41d0200010240300c25600d015682d0010340c20340c0d4000901c92500d541a051245c607691410658400466 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 29876120 1250 29874870 29874893
    0x1b031c08070201050604060803040608060f0d0b041103030304020904020d0203010f0e1e01200d06030203030a0804120f080109020a03020408030723010209130203090118080306010f02030301030b0a0506030a 90
    0x18000038003444180070480c0d6090050382d40168040f070f020040c607031400e0042d1303030b580c80342344521828071108800246090303540107815502c000e07016003100c0340c01202c0c3c50040420403003114112032032031981051079030508000040d248201d5000e040800c0603101c070340821a210a040400701d07819925070808011041c014002c458002001c0801400300114241041c210040394102d0880b883c2e15082a0801224015a0302c0700900c005035a23042d62400000c034030801500035908007a405100c005510f1401c6035021560900c103902500504400184602c8100c620002a0b88508005852100140850000d550083c1507900080c1001480c05544264050440d0040349054a003445d291031541c2c0b402084458807203404201c0030003140b400802d400061034019411380d44018542e404800180400c80c2580000e40220301eaa83c0041c40100616210702c40742e20490f4000d000034400001181000e00000940f4142c9034084220051036403a9120040141002051103a1500c9000e1404001c1440003025 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 29877370 1250 29876120 29876173
    0xb0a091a010810090b01140a030501110a080f090606060a0903060e03030a0c0212030109020702011214061c031205040c1205030c0d09030218040302031e1902060601021b03 75
    0x22030304950700d481c05203420403414240c46041503040c0000d000c001800da29005055800603001083c18980040101e844032620b034000910b203619200460048070034610180c034407000705075a42d0900f5590000400204841504d02c2c16050f448030012801d0303490103030007a00c60b290040c40d12944807a0740307440c1c18055884040c204006900f00000f8864401251300807104001c1c440d0000345031840c0341a07807011407480144951a94968042445800c5a1241e1881e27070001601090030f20082800c80c0031100407100988910f072041d40940200900d014056520003010750305922122501102802480c0107803800030000c4507a00e60100c40880d070501e49541d1201114010030042d522000c00c007103101c1c074001c200c0c140c20082c0b103184402040143d81c3d0110800312542024054400350311140f509a20310f0003042c40310f00b420030080085104410803000507225001e105c060342180411075050036038643c60207844250068129020503200085981803103d10341c02e001d802c644005601406e400182c2200041 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 29878620 1250 29877370 29877413
    0xa080a0e0703060b040b01080103030801060e0102031207080703240603020706090807120801060306030803042a080f10061a070c05060a080403031d0d1b080a05091009120b0a09 77
    0x8904081c209442105445882230174000942e5045450103007400105100d40e00030012296498141e0364824010b4a901208415046030241068600540100801c44503d400a4a4000711030140303102030804083d0551f9500b60170b00358500b0404110082e42c003003201520003c1e12803032441e000600c60713002080e0660041811490b6404035103c010120103060344003c1c101400d200017803022807564800c4a4119500c15640117000c0411100d091007482d00c50b003000b071484c81c4004c0001d4001400705800b254080d80a06607400c60451211080c1110f03114002c500f62003e8580940300003209010040c11130750300a048640b01c4a0b50b4400085843c1e00003034480c8005130408013880304051300750244051450244116181281c070314440e040c1e541d004078130000d080118946c0d841d945581d0342001d080c1d0007500141718030f0359031602c600c001e032180d07108680345800b44c3d4100340c801040e248101d01400a0ba101441c1b401511103140d1121a064900501001c0c141543c4550360400203907100120703a2002c00c5401c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 29879870 1250 29878620 29878631
    0xf1d012102040302120c03060604020a032004080d020f030d0908040801020a030b120f0604061808070c03030906050a0212031005130902010f0203090a120305070807030314010b07080a080a0e070306 86
    0x4117000300c2075101981851203a012140c581d40c80d41d400302d0520307407100f800e4800503210124084100c000c0c103403100c0e00302d03079654002260030740d40c81b0440010700694554100303e0b041500a8401203030356039008001d503c4260400d00c07596030710031015003060001701c1c003400c0074504040d1218143ca00b2a03001c40500400300e65908034424160a140b030303410241c14107031409890303400c160707691007030f110880240010071596032100403a032503107080c1070500b440c03d4009044944508240c5071229a080300d60000b6004100340a10005040d4403400403240d6411095020344000030040f60b1004060300050080c451640b200440031415407074120042e45040c2a80c86d011818100303a0001511001700300b01c403c002c64208001d1b070005922500f110204541010340485c107061240d080840f8240940940100080300020f00101455803540080c940c0ea080614011000d980e11200300036103109109000304400003d100f01c42501e03000704a0241e01454556000c1580030600c0380b09414400b032a0800c49010383d031034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 29881120 1250 29879870 29879873
    0xf030a080f0421020102061302030f0109110a05100f08040611031f21111305040f050706020303010f14040609060b040807050603010302030601120302030904091101020d0f1d0121020403 81
    0x58001c1d118802c1c0d0703c492000000103900000d40b06c0030010202030760211010902c000b11f480400002e842d60742006c00030011070400d0314001e04982030b18202c25124803044040400d19103040c010400f000c46103515039807141141d82c482681c00c003000800546203255601002003441405500461084d1320390103140c5200010018072140d400c1654001d84840c40300010504a450791160103100440e402090800700c102201c030004104204800ca260545400c1c0818801001024480c241910b4416810ba51807a074407082c049070359001c01d1003181da0410846c1810009448102407898010101030008103205450340703079000640b15658000100340c5400035082010030340a2110030090401198030034035552460b00080c1e546c1070103019001e9000b02c0f061b034036000c1500800460311115401b50090001000b00d08014420a40302803005016004181d11046070a01c00d00e0010800c5140b51980c040003410900f11410b240e050080c5641132200541c842c2000c40680384004030341c004041005aa00c6066 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 29882370 1250 29881120 29881139
    0x601060e010815010905060c07050a030305040302100c0506070f17180c0d0809040b01052b0606050a0215070203040f0b030603160f090203060402040b0a080403080709030209060f030a080f04 83
    0x420b6001260291100f03154680e90142c80107044030740c11030350b085d00c4407000010305080800c5ca920040d8840d005000002c101034100000c0d00850b802241c5c20071f03440c1c03170703128040d0340740000c03290000c109030084000900d150340542c40342c5089005a20342400c56240c041c2d0b6218030400142e0300c43c1958903000070050b40712042080703140103120702541c18049507500d0b0364805043c0e004042c465403160744c80d9210f40b64070b03901c00c0c0d0035989049a04c4240140d21828480249641d028030801001007c0c2003c46c00315416015100b1a80c000565600034100e40d101c00650300319002000e4000301c110301040000141120f24084520040d1200d0031031203a50342405001c05150440303070803002041a806201c100050030b180a01441194031010f400760f0350350f94140001f002841241c11038800c9110100b9945840da070301820325072140e88617445405a036250542d064403042100e200007035200e011a00000d01fa4102024400108040901151039100d001d0b543c80d41250044030990944e14400714081108403074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 29883620 1250 29882370 29882387
    0xd05040f120c0b04060c14160201030501090605060d0b030c03120315010906170903041d060109060e0607030c11040c02240712020306030c03060a06060801090b0102030301180209030601060e01 84
    0x2054140b94a1503111607403200514400107101030440c0340e0710404201c0c081d004551004101000210440d520034003180c42042c0e100244c2070603400a45864000300c6c00b000984035000641d0030003411a81800c2c0c820100324003610107614040d80501a81110180c19142000215074006000c0d090a80741c0c981000021900e000440c4020f04101c24a20108410342c1c00006002c00342d8800c07400680c8a90311a400c00d46076102e03581c0003c1035140502120042c2c25110510b10b4001c40b003da0340c21034a55520f40007200c008075903550041d40803008128190002c0d00481400d1030b00351007400701401c40200400000c0407100641561000b603041041c0b01d0072491010300c0d0468054150b1104032400e070400e840d008240d8040500704110706903001000c03d0490313404125255070000020111005407410310340240142a55126200200e80994000714406d2a07030b0081a10310b1034184d000714203580c0b800b41d0256803244035100c800700791a070806c03084845407030602c0018042c0c6055100d010807940c030790700018258403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 29884870 1250 29883620 29883653
    0x30c12060e030901140a020a0506040305220f050f01020703080f19031103010e0402120d02070602240609040c03080d0203041208040203060c1309180203120304080904020706020d05040f 81
    0x10030401c1404401d80e0854012801005c4181e42ca0b511250000c406034509810320201800c248a00c004102c10154450024040b80c94401c8503054000b0112442c41d4081e0b40034001c0303015070002c001c001c0c003150030701200046078050144100e5100b0780c0e07a9104c4420940c00100103483c0c09074001104120912048407800841c21240350400c003400e01010025501d0006000b2a00c00842e404042000d5603124019100141c240030b080ea0081c0a1260303010359900580c0c0306031405406205880c1000c5440d44c0c00204002c51b2258040c181c694400c030410900c5070b8010000c0f40c0494040c60003202062501d00074094240c151640141e0741d04190500c441a81c0c001340703106080000c068108401610040b81080d040010108220b4490b03c03c0d900c040c045035442d80140e10311900c0d048a02d03884280442c1000300c920b00a4040e01c1480c01c0c80541410644004c032405400300d641000004003504042d80248041d5008010050030520040b42400507124191000c0c0c1d0720007034448104051001c1d02c0320441c400c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 29886120 1250 29884870 29884873
    0x109120212070206030a060312090303030510061d01021903030f14160c03051909050f03010606090b0306030109020a0602100f0507020a030c0c0306090803070201050705030f01030206070c030c12060e 87
    0x94400348140c4254482c0e25070007401100c000c0301160000c2041c1e04200059a409900410096650400101a01c400340b200764002411302000c29031407441c4540c004191a601e41e164407502d680c2e06407000b400710030992410f046201e00d02c90b242d0703a01c51a48420410344d22079036002c6901c0540642501c02e58410000101c1200d14103400d000f540e504c3c00d80d141903400a41d0030048282c071250b0a0030743e8180207050300c115800c241c0340c0c803c2500c154404c68100645000b01c0c0d48201d4070f0020070500d801c0304c03050300030b40000c1484600d0074000217034560f02940d800503006002207050286607010814042a980c0440b0150b4028501d60181a001e0300810800c00c01d42c1e1300030040c034a01030000030340c0c1d4000d000010782400909010030060096240580c009941c004005100441e250300d05030106502c01c5403000010352a04001c5040b0301c1c4180704880c000d40303140c07488071000e909680801a103a07014040444441054660010000b03000341c440f035000740001c3d9050795040d07240d0f04180c0c00303445844034001c049 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 29887370 1250 29886120 29886133
    0xf17040801060e070e01030e070b03090703020a09090503030f0408040801111b0d0504060c060e030316180302010918020705010509010c1202070807030c021201020309030d06050103050f07030c0905060c01091202 92
    0x4650301100d241704641e02442c02195194200b20118180700240d00181e4410100008102c541d0500050000c100ca00c241c44043d501591142a44111541441c00605079001000450b450030001e420180e0420b00811081d031406945a1030142125040310409d40320540c0840c46074009042d40702140d42200b01c400140141c1c0c10030140051581c03145020b441c0c1400803000013003092181c1a0321a0392a83d4120b0201c95590038041898240c5c070030030201c0c480000b80d240ba080b4074100d861101020440754107840b20302c41d407428100d15454016285440d80c419690034040e0a000c60001d0003842c2c0a1648100006803510780c3caa0024911000c0a00c4005044d00401403440080d02c014110b54a81da0540742559107007a8510001d00491810b43c1120015800403007406010760010000b01481801d07004c0401c00c4603912401502600d00440f110341c900c408100000320258069004050b03c4860b500c0c0c00a0444d440d40d00082c6290005064850903030b40d52021002040396002070845811b116000a02e038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 29888620 1250 29887370 29887381
    0x1080f190203130c08030d05070c05070b0f0715050609060a0e010510020102040b0a050315120a061e06060503010504050f0f0103120e0603010308030603010c0e01020c0405040f17040801060e 83
    0x29040a50448a00c41a034000001911443c0948600104561040e0300040c481d83e500c1117581e0b42d8220400101401e0301c2c050100d01440d001d80003420045501c640900783ca13514200c52821113411140072408004010400000000e07080c400c03005080c0c0d03030302d01c000885042041c2400300070b000041603580140711080d02800002100c0007144d0443c1e03400c1760103540441c0641030881c013a0046a200400b0300c0c030041402400550040040c5110702c44d910148071803814000100b0400c0740c0c00162481c0f080c2c00c03000b03e0202003a0540c000c04c01c58444005104000c807010000c0e0006c40326560300540000e00003000500c06440e150003116041074110380e13100800d04003902007021140381844000c00001301602241d2041c0e009800c12602c1c00f000901107620782d03a50b4104501d144c1d01c2102c269201c1c0d440c0c80c410500c81401405140940c10f01a4003c00c1280e62200a000c000d0102502c1034468000803111400096038801d070700c0c41968080c03110641c0316840c2c40245070a5504640044030818900c0e000c114 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 29889870 1250 29888620 29888641
    0xc020606030a060b0312120a0c0c08030112141209030c040608070509191a12060118180519050721020409062004050312160204020a090e100501080f 65
    0x41c0c2e070503002000002d29445040010f8a0b054240100355200130300030a0078a4803424080d00180b10390302c02d0405010003444140111200b903564034008020301c0c0c0604c01071144400349200c81983c1445900d01740c900d003441c4c507000e52800292038400c60f80c080300014074414604043c004c40041d2901940d0610195041c000c4031500d4055a0003414001c1403084001294041c400341c090714404040201001480540482403603d07000c0070f01520300409041e0003006c0007a0380003a0441c1204c4441c0045807c40300f841000402501106030a505d4550010346a540414000e2200740b051410110b9481009400c51030a10b051400ca9444115940360315084a03603c500e0195207810b407168102c600044200092070000c000380f01da8540e0300d1115641e1952500d0009402004005031002181210080e50100f40403060341e2007202c0c400684841e07580c016000500f0030350081c000c0b96000d4204007500f1f81c0c40301514101014204c80c81c9641500c6804200407030350f04124619004848440960b4140c074003803034800d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 29891120 1250 29889870 29889883
    0x6030213120201051c090309050603040b07050f041d1b0c03030a0b04061e030303060f08100b010509090a090b070c05030702010c0c0b0d050901050f01081c020705090a0903030c02060603 81
    0x10440440341c240c900e01103a1107501101e1541d070341d4145080c628101004400d004004220301140403c41244003c6810328140060341c0c840c591140781c480b01b5555980044629420a034040d402451084c00301150b0080510300c2180c02c0d00b03940040c82c2c442c0ca00054050110400c2508203100c41004001c45144103902108076139000641c0710000c9507980213000850010462940410403d2400014001e10003240b5000303c0104d9020307540511003d80c56a901c40c030300c451075200e603000300e90140d4250398409034140c01960584e50141000c504011031400400c542c0315049603418203441d40ea00781042000b0175044401e40105007842c1c03000500781e00ea0703103960356441039a0000e03060003850309a800401c06581c014070301400c05202c00c1603c038030103240b03a1809003c09403002501035007030000194962015111190403603001d88002c1c81e15800003411852610020220b0108500842c03102242c1c60b214188510701170b95440000040100a50600070200c0d116540e0b22011034009801340880c40c1d40000c0d49 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 29892370 1250 29891120 29891129
    0x80c090a1401030b13020a030303140705030106020712020301110a0519050a080406180818240301050d0302030409021b0615060d1d0604050102130b07030f05090102010e07030506090706030213 84
    0x207180307503403107001245c03030f41602c00d0f81c0003940002c10410200c201540340e00849221280c090007080c081d290702030242e5081c0424004e0b1401607219030403c000300c0c15620440c00d41a40013800010314110300740744d108880d42c00307042440c0c00300e42c0002c0c80142c3e4002d4500840c0301340d0742603c0c0442c100101c400000340740e100302a101600032502c52a0326640c4094a4048452596010064544d6600d1700300400c405041a118114032801500007541c80610940c138105401e0031641b60175a00d560b0a04040000d0001d90740d0003601107100030b1001180c044d41c82d1000f0b0a00c1d9204580e0f039107240c250402c200c1e2400a00410440490307a0a22038440c16448450a40c4d450100000d00441d200f02c4034110240341c1080e004a10400d40b0400d801e00042c800c06500411140f01e44160307000000d80c0301c581d80200d0b80701f4814000c00091729140c4070743d00c50340300b00702900180c00144000b28503252481580c2d4500340d40394006a80c9504104244075000d041041410300070030361804d0035820b04540c50305000e10244035104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 29893620 1250 29892370 29892383
    0x1212180519170304050d090e040503030105010e0105120106031505040e07090507090f0806060907050a0f0f0e03030d060312020304030305070b04021206090d020c0109050a03110411030a0507020105010e06060313140106080c090a140103 102
    0x100107004da80140141c0b00080503c640c104f401b03694803a4024094200c4000607142c44028400c0407031a81081d000790a08414288010a002840c10300b8800c020300303005081404008200c0307008510f4400e00c1d114007000f000c040300104024144402008030084024142c04103100080003280c100d1a04080d60030400c90941c1400a15840c1b0030348161503200c2c11140e2243c2c140000906400f200c0101d52003141501d001d1111a00665a203001c181c0e500d106e94003000c2c0c0891018040a8001040e4000762940544090840004040d6007010145441010345102d215900801100c0c90003640c100040c000300d481c00d1800382641460300c00410ad50001302d010181c001e4030041907840e0907072242e4210003025241c280c4001d69a1a003c80107a004140c107941d080015401d0500004034400f4841d0307000c1c0140001808140b07507444905d07001010b00d02c400c0c0d00700c641a194403081d6440c14000c1c842d180c01032900201616010340030b40200041200c000301604c049a14000410384444061619641504c1d400729 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 29894870 1250 29893620 29893637
    0x6070912030c0c172b02030304060209060412080a0e0103061d09010209030304060f0f03060b0f030711060c0a09050607080a050f04031212180519170304050d090e04050303010501 78
    0x52540f448030444c3c0201d4403070080c031031100440d00000244805000c101e03d201d4520329905010355000c51714860781240050b8414400709020800940c01403004e20b030003d104615150741c1d1000100c0700302c0c8080d000e03900c024012600300d038420b030000012804c1c0c1000b4681000440d041c10401d10a24080040040340c107c4140b0006107110425030468000c1c0000504503911603968000041110701103005160000d0101c1c109000524003900903501a1100402298106000060021480d400c01030240040051107130002d10310400030b0200724050f0700e2f518040740c0d491040c0103000e0a04209980100e00541c402c1002802140e821025100c2e84400c0d49401e82e80c80c0c054682c01c207842c0c003850700086d0405440111603922036412880c04419401e1820003803045a0b44120b11540c07400d01030300c016146401040c2c00c0250800034258900d211441100450194040b5400d1070002d0b0300100c408441a83c04104002880b40d04034101170020300000c84545054902691070355128081841118184500314 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 29896120 1250 29894870 29894873
    0x60302070503090d2103050702060106050903101409011118010509190b040312020c01020a030e060f070b040201020609060709090b010909020d06180b1e04060302030607020c010206070912030c 84
    0x18400c0382d1415000500e4005100c2442c1421079021311024000982500c858030845d032018001d01441d0300c91b0507550080c240a80c43c1c09001d83c1c0301e51000d820b403a810f020b802c100580700e030540d1107040782000088441210314a030142e5142d08607a0071403075040c5103140510400291980764104080b03568000c2c03a225403117000200109500c0003c44e4215140d40458507000301c0d410254902030000c4a0043c80c0903200300c0c0410310266121540c400c1c0c40741c01600400507070804203000d841c50500fa0785025090b6072900014030754150054000003400c40f02090900244401e540e0304001041d0003001d1031014080c2414039541c01b030080d480d5880791001032511600326503a04d07801944913034020812018203654604070218144010103a0b800b4040c26014440708500380040d80784180205c1400240c04903614100f050416252155055010b40c0d121f911444c01100688007881403a016003a01e40041c22004c80c000d001a0034140020489410090810010800d0b14240700c458081190542040000c0c032180c3d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 29897370 1250 29896120 29896123
    0x21020f1203090d0311010c030b10140903121206060f04030b04050309120105180c010207091802040c21020310030201080711060709050102070506040602060c0a03020d060e0703050901060e010603020705 88
    0x450802d19401152058a9000e145e00b10181c5500c3d0304241000b0070020702038500a408a4217182003054004036011005056540035407209402e80f042d20100505141c4940c00081c03420681048607180203201007400b4040107800480359801000440300b00c0d0030a6a0307480c031035400d03000d00e1201800f07810b03032480480e09005041c0b0441d0344c07000e0040c0101c98040807211980b806480e0070f0f50ba5106101ea5100044002c034070210b070162010605901400704180b0300b015240251020301082c00c00c2c5c10360941ca180c0180d80311b100f03403a110991078a0380a0b86264030200d2062510080380c1040059004000b0000216503411f0410305899090038400c07a2605d5008007101c44c0d42d401500301c5940c1c803a2509100702c158001c841142100c000340c2c200c440080e00c0e00c0070f001a0340210302c078030b074003580c0440c01190f24665803034042e00310424186001410010701690400030707500e075540401d50307010707078107091001305030345401521341c0200550003c0c002e0510303018401c101da56051284030304040c0e0104088040140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 29898620 1250 29897370 29897377
    0x7120f090606050907030b062a0a0303150608010302030c0603040609020a090605030d0507020f091305030307080105090105040905060a0f0605060409050117070e04080f121021020f1203 81
    0x10241008009241c0c60280700804042c09860b105000c15000502020321034002d60341300c0003015002d00c0c11302c00b15841c1f06825410039110700e60310001c041500040748104200e18401640650b4002c81c1c001d122040003103c00da030701d400103400c000401c1c0047c00540c500066800440d44103580960360ba03599410a0001001d510800a51144c95902d000444440c0c80d002841616000c030140c80d02d02170b040f1070689103485001402908008205650a0f407441c0441210341c2c000c3d0111841600404907540302d60550384100d802034082522a00140a5801c1100700d59015080c252001c000004071078032040c1d83c0d40e1005003550201030300c5040542010303801d0b41040009000241045460b5515489000081d000074004c044488180a2204804000024268040b0740480060302100d8655440f800342c55403016001000750b04c1c0402040408810b400801407080340c008403000360141c10200340c06401e081c10010201d8025000c59040b005d030b5240301c184d230a0b0780021640c0031002d01e02000400c0c00c502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 29899870 1250 29898620 29898641
    0x80d1e0e0405130203060604150504090507120807051c0c061a040603030206010305011103010b030406020d0b091302010f1d040b13180c09200304020307030615030219050105030712 79
    0x1030400b0140070010244002e0310014038422410356409503030703a10a11086400500c402c14440038603403007c000314100391707000e02c0c0c42500030b2081d10405a120b41076041031860840b021605107500140d007400b07200c000d009464034030030f5400240d00010709000340240412402c05000c0c1c0f1081d0381e00c00e00304940d220000c0070606900c01900501180c0d03a2418040e44480c2c2c00d1005903129400d0081c0641808088400c0328140d520121141c0c3c11600c40f03480c0c540088d0002d141480900399140620344c2da41c2d8618004a00c99484c0703178051809051540300042182c03001c05900c0301406240410280e21500700c0c030614298440c140c60000b40705480700c0000301200152040e40c4e200303030718042c003a45980c00d1661280c036002c0e0140010544242d62400c0740f0085450340d09143c1c05440d4000000c014903030a1034021604240014112011180c40381c56980c1210a170a131007444104001c0010401c50504030381c8007007510440481d02d100d42d860b00c00041c0491000800180c1000403c20202c00031400c103603c203c0002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 29901120 1250 29899870 29899879
    0x20a030605100201060602060f1303080406060b07060f0c030506030c011b1712070f02030d0b040905070f090b0105070506010510020a05030406080106110120090a0801050a0f06080d1e0e 81
    0x509020302c060b0080c0b80c903024400050007080006009200d101c14980c0c0100d11003840d20f50603044546007140c0150b07028104440d00b603120700000070585120809014210b000329030010785401e0207042d0b14100c8040c0203030300301803509000030003030726a03008203481c92024006c4c01c0103c1ca03d00078003880441e52040c04002441d0004518041c5010740f01c0c4400340034118041d04034090140c03102c203000d0b540170300d0800e51980141c0c010841c800200c54a50455071400b50094404941201195038190038008560819040c901c90070b00708000003c40d07405024282c1400703081407031414146403159526010140601d50041030555680c2d1103042c030810205516a80200c1900d40359600c400d00244500000e02c42d90000a0904111070702c603d00600c551040710b00c02e610b88011031810a000720946401a00d010340d03001d26140800200100c0038028648070b224483c0c40081c1c81d10491f010541250f2940d000401240d008400120308c0a80250805075154030700b06200b03240c0e110850040b2244800f01080c075811 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 29902370 1250 29901120 29901139
    0x14010311041e020304060c11030a1b0203030d050708011d01031e14010504050616120506040204090e0c0a15050a08090a0606032301051b0d0608160911041404020a030605 74
    0x402c8440e03014501075482080309103d4808940001c50341401c101440000750b4000700036584000e40190300c1c090250040229881454400d0b400090a50300090a03103071080d41c440d003c00540d1980030010f540500390701008080c00d940c030054500500a01404000c00e04030101c00c4c240c001181040b00c102c40355900c8481c0b040040c0382e00ca01103019000071b41d800c03179440c46108041108090790390203813042e81d50300782d41d406000311405070217a000d848050940ca80050742048081200601ca029060000300554018000f212000c4c0601505442d035034050310300020b45140c01c0c00040d90010403611111505e1603c184e0729264031800508140c4254001003200f49009400000c0001d01d50303000e2090101000d00241d2403080c000020700740c83e021a01e144c070021101013207102c81e03c1220003524000418070000070b0180d4981220724940307240c00c0c2f000c80100041d40010410004140114070240440040041c1081d2404030024080300007040d503548556008150b201d000c610a81c03094005040c02800c5154 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 29903620 1250 29902370 29902421
    0x7030311101d010608030702010c200a060e0901080106030209060904030912060e06100e01060f02030705060106200a0803010b1c050a020a0e03120a20070303090f091401031104 77
    0x4800d4402d0244000c0d94285180052840f402000783d8000d590182c50303242141b402030b9070f001000c01e02042c0c1d40c1885210042c440ea869124100f0450281010f500d89410803078003501008640f8105038040d19003a0b050a01c280300680300c9291060300710000f503451081741e440300e00c2c05841902c0b480c0c122032084021940d650040c0583e070380202400f0314848003560b02a0700c03104c00031110300b11140105006070740d581004103c1148036000d504001942c0c2d205490400703502d59502d50810a00383d221b24002484042100800301d007074411000c81c00e500c040148882c060326500c0f43ca99000510400365500340200714004c0c009000105118441c031b54000070041840d101180000a400c0345001c000080c0c505881465103080025099600d00403407a441411311811400445602402840d005601a0050815000080d007081032002035403080d283c810380c3d9801d140c00b081e409131456000240085c100140903443c440f00e4803065042d030f0b4021144444920300302e000700f000f40080108c500090031000042c1c42 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 29904870 1250 29903620 29903651
    0x2060a030c020307082217060117011d0604030905090702070501030504030309080c060403030f0b0307030818031204150e011d060f04030f02040b030303090607030218060d1a120703031110 82
    0x54421b0140f50300c0c030125211115a100d40085100c284070b194000c1d001440524283c4485085c42a90b00b0008240d08502d4400ad222000200e0300c3d26005500140a1108040d00080300e0400b610303040d80c84011a1030305800095850400707201d00d0341403641d10800705050603c01c1e08148941c58010925580d42e0321203c030342c80d940f01401c403400e500103494100103042c0a00f041c051405190002002048941d0968641208652107031040c00700d101002c00b294201504d0501c80e800c01e147c04295900e44491030110b1100c90b2400401d000400c2051403219600c1e942c0c2c025a45860201c035503900d00d2414407851021603503902c1264480a0710300c0000c00c0c00000c0007100c0711501e03905d51081d10148400a100030515030740c0c1c0001e80f101d03070194000781c00203003082d0301c01d80c0544000c0403403211203066196088013080040c0d102c000c00704600d94a4100c4900303c00308400c6545007840d000e9401200c244080a90b142c0c45000b90b00004040104201001c60001c01c100300c0b130016120060010000e2040003045d45 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 29906120 1250 29904870 29904907
    0xe060414030417031b070f0506180301050c0705010507030b010c0b0703090c090e070f03110913021c12020d051e0d0c0c050d0203030402010909050406180503180d02060a030c02030708 80
    0xb02c5e54403680302c0c1812141e20700428000b00303d0f00701c03201800c009800c1200308150794000080044001011a00c0084142c1c4c0034028507010700906804070360b641d142030405c40c1c2515801820790040c0360400c403035403c0d580d0380310324401d410b40c1d0001c5062010381c079608822400b4000002d40a0900500c030f5002040c0e0640760380c803030000d40010304121014940e8031000c400150b13101d8030018040ca40c00d0308514101c0c5c2400081d403a070000445151040440c0d050380041c000c0c00000c035a807071008001c061280200a40813610503100c216a00061640c150003078001419803049001094001b281401d9090540d0b80d074000760342e0301c8400100b00384030301c84022100406441d01c01c041a01e8910030b25a10030149030002c000c580c002c0360107a6840a401c1e0510000310041c0001a00456006036500003c058044030104862070f914071550280da41c41d20301c0017406082e0b42050000c00c0c820507990085400607652581241e400c4280c41c2400300303180350503d03420790a600502001070074150001031180c010b04181c0618 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 29907370 1250 29906120 29906137
    0x71106120708191506080907090207120e1e06090102030c010e0c010206010e1302010e060403080a08150105040b070b100305070b0c120306131a0a0f1403010e06041403041703 76
    0x102c1a0a03940c0c01d80e80c4064550400d010000514015801d01c2007900c55990b0a40c804580c0b002c071030300c1c1c8d0303521481c4d00200c3e40015000c0d00c20f8441c84000c21160366114594005100d01100c40583e80000b81c2803038044118507503403a901c00c0c000010851a1030340240240c40851099100030040452199002c503103d502d4542003070700600580001242911104006038060000068060348a11181d40103645a001c915016584140e050200000003518100103101131000f43e65107859a0900300000c0341e1100c4941d107400c1c14080b040c0010f0060000140954520130742199005201d62a02022a14030f0070311500050300704e0003050300214201203101c00509600c1d8840003216400c50a02102e00c0003800251416584500f647c00308100b9080380c2d1300102d9100440002c500103415219000440c4150a81d00c0011412030800007006203a848600c0c59100540c140d0084c0301c02c140c81c0c00865280d100050004051303141422403503580a008100f40c80c054405414014511140030749250364a0300304544 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 29908620 1250 29907370 29907391
    0x30a1512240c1b020310110901030b060408030f3f01060305010302010801030201180e070e03060121080705070801150503010e0f0d030209120a03080403090b0708071106120708 77
    0x126000c0301d10480c401d807004500c0581e10012040700301d104000020390180c1c826a131510858000c1030240c12a4030411044200f442d0380d041e503c030b0f0103a0002d020788468040091059400b8801080610000310894003420300c40d10300d503580e90b40e403400340c551941c00d01d40600550034115020005210b00c1c0b6400b400380300760042a00c1c48c550380d840a048054035824000240010005801040154000c0c0480c10301d01f03140031802c1d6456a101c41ba800020303030341107400c4030003d01c01810080f01403c00340a8030380941401241e10440c010412450841141051801004070f14001002424404c06001c200701812102c0000c0c41020350b2046e90540c489040d00800b03110303500e40408080c44402c00100c3d000c090b60a00060214910051001d50003900f04102c1070b81c0210541008800d84203060003c00101403082d111440e081c2060305000388480c0b4103410035014050b0400061010803015005d41d0100c0d5030048080510001c8900450f8003030050703001002b1135608070024005a0b80c0c0000815105030300002 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 29909870 1250 29908620 29908673
    0xe0906040c080c030d0f020102070b04030f090603110307050903071a07060c030b010c1506030503030a050a20040b03040c09020c010e011a09011a0f0307120b0604060203030a1512 78
    0x2000340c3d10b808841e014203504da440050002252030103003621092011030b03070000504002142d00c440e00c4030182110120700044001c009001002c1d08615280040c150920b81044a140060480013140c840940324000b840004514424590b80400140c0051f101c5895180d10041070340340d05142d84e800410781240d0300c40c00c6c0391140352440c1c82031050304e11443d0140d4941c80c410600d80c84d09010609500707110340329075484440200100d94208001d40c050190380300d0000e06032400e40d001030b04882d210500c126900e40c0700340300b0105d50051340e0300b66000d81d8119407440d03071b0f00d80f00d501d0102c028024507071201c4903060011031400701144040d800542403d00c0c0100074810601c03940c940c09440e224100300c155000758013a0051102c002d5010082600c0804806114900000b80142103001d0304202c4024000440314035488481c21954000c580301d402c01500c4090401d070500101949a000c001e1008526a03a500110300c082031400f8098402042c0012204141003200d0500040c00b082d590301408010740c180 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 29911120 1250 29909870 29909879
    0x21003020f0306040504020a08190209100510080a1503110a150c08031506070804080f030304020603010e19151d09070302090c0919030515010f050105070204060e0906040c 75
    0xa008a4400c15907104800e0701d19035a07001004000c20000d0000da8101400d804080b0755008200100108550f403803044000c49509441003007a501c4c0b00414101410007904800c000a403030300b5040f011522428104039400e55076030320000e0010000c1d5892655001056030700001400070440e9014104801902d242c19a02c1e02d40d00c0c002c012120001100000810035030300d0101050080020b55081110344c4200e00c1c03285503420018082d90044141035138a80d10000d001c118950003004413203d8060750002440c19864a0740004615020503c0780d400d0259240700040c0c02000307400030580d050305011800f00300343e203e00d008003041039089002c0e6030001c442d44100016500c12031500a4400c400b010010b05110782180c1c00e01c8095200540010380d40c18007072041080c582e6500e15405101d49689400200742e51960400c507140c00182e07100040782c180d0060050040381c6003c0c00b0746003580e10070708146075a10003d10100f4024100b80d44142e401c0c000140c184a07034006c000c075940b4080e9028070f03070144009854 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 29912370 1250 29911120 29911127
    0x90501021b01050301090c0c020a0e0907060e0d02090a090506010f0f0e040503070f0305040f08101b020601060f05040503010905030c061b0306010309080705100605030d0306050d150213080a0210 85
    0x1c0c5030150100d1414001004101600d4000b10501d001d60315090769107402e1680820040e6419811240e048903040003001081202000020000e18403450410b414154200202c0c81800b1000c50290044180000107508001c5541010801503484000c03560b903580e55880780c918096190048000b101c456107070010b07109000c0d0b01c12a00941e0070402562400c50b47d65240039070421405000c0703060100502c40010600c856060f010300400702c10026000c0a001c410004086a004440000c0700b4003481d02d10014071a40055124152755a03802c141003803100c65103090340d19001d2075000c10350642c201b824900c1080008405848240010000c8034070a0721040042c001650007101882050f030810700000c0e445600c02c0d080f004120740100c0341c00307282611549a0a080a1880e0100d0031032035113032802001582410424510b00c5241d0307141c2084210b00700000100104041c14010b0074800c1c005c80302084040321581112004031004016000703440c6d440741d00b152651022a8207910030220b483c0c240c0c907140e01 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 29913620 1250 29912370 29912413
    0x1104051003050705060717070302010b090601031e050601020106090f0614090112170d0608060906010f0f03080904020c0601081608071511100f0b04050109060303090b0a0302070506010609050102 85
    0x2e0000c00f0345400c40c00c060501003e038204c01e10a8442c501030194100901d42540c0080900078041e03400450300c80204001d0080504000e00303000c3c105840c002441c0001044442c02200c801d100f10b00102c1c0c6a111200100d01502e21754001110051170540c0d10311640c1400d41c400b0044808058408110100c0b8808100030751000340300d1003400e65289403070360b0005540302c0c0815019110300001c85040040d560031400072185690001c24103035110b00207211030071000700f00960043c80d050028030010350078840856040040ca00c4001c1c000b0340c004c0f03030410480e95107806803800450002d00f222503c0da9074055196490750408940417410304425008540b580c1c0105418060340c849004100a9540c114401c40700f480051401c1161801610607071f030550506800340b034580300240900850f8045001c0200320894406034403140d8010b150001c02c20000750482c601c0c4080b203082461898494031100301c190040d100d03504000b051809160004601e003904040d1075400e85800380d00b15000c0c0d40ca00c01e02c4800d2000d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 29914870 1250 29913620 29913623
    0x30b042003040308040501090b070c030e04050403020c130609021305010f03020309030702010c031106070305010611071809140708031b150606030a0906020f031f0e1506070f1104051003 81
    0x410400010b80441c2c000c6000c0d0340c0052050000150303445503a2aa8080030006540500019403405162003e260340700701d1018801c00e0465040055003440d540182d940c1103954041809513809000104da51009a80040d00410b98510155515260314440c6000020b6900800e408200b4000c102c40311140b00b4400d40740300d4850400152329100290f0019503001d604420308408108100c03401c80c64041e41800044e000d4652034502040715410050045d0155081010545880d07214071400c1005a441105201407410b84540c002840001c47c24003039048045001002480e110b0304a0004009000200800341d0040c4803940940e00004400030300d8032641d4621440301000c00700744c0451407c0c5071880003140c10066050002401032080c0c0d56103000c2e6041081182854600441048240c40030141d24900000540c5504030405080c44048020020040c0240703804500c4049201c400340c403050200c4000ca50003142c0058288000d180101141d074001004900a03801c0c04082030100f842d512450003900e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 29916120 1250 29914870 29914931
    0xd1103010e0402060f0903150105030111071716120906030506042a02100f140901050405030f0a090902040824010602190c030b09150c1c020703020109060c030b04 71
    0x940b01c640810203203030041c005a540c1e0350300130404007400355005c04c104000b0744410384501403507614210030182154045018905031100800c5160001006c50000c1e441c08484050b5140d15081001c20b128444140558010200c03c000b04e01a43d50a0704074100c0c03000c440c09540e0034000c5545110a02041c5c0302d0800e030254104111803921444200601c502908020703039417049642c000c01040e51801611422003900d2002660781d903125040c0f0105162040d03000c200b50000b404142007a41d2001da0ba88208040c90f502d40a01080920300d03284030704000402020a00b8040d5201c030b8440c40c1441c3c0303e2444a0440700681d1400042d401d49810161a4a040718a0b580250080320214242c00702c200401c16070440e20003805420100c00120412121409640f0f008000d102e881c1e48169140390400001e411304422030700a01100300c2400c502e01f512184800401d0340036032641c1c50391506074007401c4462001842c40c1c1c101404a06240c0d0302d58003007140110100c90502800c0c010b0b1700c0040d02c1a1140b403003000e05 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 29917370 1250 29916120 29916149
    0x290103051218040c1205010f080c100804020904110603100806071106011401090b0f03041202010e0717010e011a03150f0606090d050a081201080613021201060503120d110301 76
    0x7a103404c2d07201007030031041801d00840d1716450000705412210b00b6049403c00700c0400c81c0502c0084c00404c88004d005209451044103442031410203080a00300400c02403041807103d0018041140ba1200014207680141c901500c1c1d0034081440303584480a401142c2c40f5100b40000a00080d2060900280c83d007005405808180d0038944a8a90000452503050500c0f001110000f401e401d05001003031000e030402c000503100c0c20203240201000e21050f44e030310b046a042c01c10002d0715000108006040f02e80071003980d19070302040c42030780e4050700d0f00c1d6030103610551906804031040604070880c500840c500b2805e13200c0c0c8110b02440e5803803002060f55045c0782c1a4282c00082d1040c14600d0050800d03850003820300281502030340c2c400f481d046001c001118001c030042030030108011f0049480c0e000d0505040540726600d442e041c084103054010704040d20685004080c0c42c9414029401000940409015940d01c0c0103018010341169008400c2c140c1c0061408451342c40181565003078a060b06c0f8080c010300303903 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 29918620 1250 29917370 29917417
    0x61103070b0f060307030203030409020909010b0c032a03070f030e010323070302040b0703050703030b0a050607030e040e15090d08010501020607050a02010209040207110f04060605070206072901030512 88
    0x40342d0000421194062181c0340300400503940c01c0003d00010300316041c015940320b00c4801440240d1006912135034003000140800a2816408010744088403811442c810500c840080009066850000040100e0100084032410b0001102112000703e000b9140c21200d1060b19004402307c446d449002c40b2400c82201005c0e0040d682418102d810180c0f500d005414141c5403c000342155000d0901200480d50014501003055018003a41908410440d50041e410740745c140410f03aa4403e01900908121002c0c18000b40341c0c1d510340c0208540106071044441090710084501911841562069414401d1259480b0b0071440b4040043c1611f006038040e010545500401342c603070703400030764920042d55028084400d00e5121480a44040c07805100b01c1080c0401302001d01000300803901c0c6050049050990038081c00b50040112882c141d415102107a43e49840d080c41d54900790810900d0a905444030404820301e0520003040e4142c90140d01030380d20492181104a10910517a80403001c0500c8070340003001c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 29919870 1250 29918620 29918641
    0x20d0e0c0a120212030a080703050603011103131b090902040f020a0207150c05060c072102030a0e12010603050607080702010e070b07080c07061206050901030206030105091009020a0306061103070b 86
    0x40002c0d10181810040c0b00062444c6403c40c0c004130420f400049203081004049503140c00b40c95004142503000b08002d29001c3c500402170302c030090000903040d032194410800c00008054005003940503001d107000464954007080b01820724883e042c1e100701c0c185891005002a280300b1180ca03115190000c003e200d05e001a01580c041c075280261043c40320b90441c000100d2000d10030244180f01c21044180c0e81d4905241442c0003482d000d01e09280f00745490b44609815070000102c40305c0c03141e2418011060f1602d00e00050201002d24107041d02035003080b400001b00040090103e01441094580b802c90ba0340c3e0440c22401c88410500c04116540840c0d420040c10818a008004032801070074564034044100740801d2130021a6404000000c90a981c0320341040e80c644281c6003d4001110400c2c400d51654001030243d00040c0a803521503080d03031000c80d4503403407402c1c1900004e0115030003d41d11080d0784400500148028860b44000c9400a03a000251100c08070441e1300c803a510070300d4801251640e8550a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 29921120 1250 29919870 29919899
    0x1218050d030806011b030206010f060203070c21060906091703070f0c060b040c08010315060b09060c01060312050304050709050105011d0102010617030c0705010302090d03030506040f0609020d0e0c0a 87
    0x81c14040080d030000f540207146172004540d0380c0260010042c0c0d51404203103240c800b280358800c4085420074844400005d41089a200488440f501000007803414002001081800100010031051410192038108402d941194503558014400e49041182c003080522182c03000f204c10b0340000d0301442e04c070f00489010380b8107855554020000000c100030394101140c110790141168101141c0901c0041080103050601041d0040c8002d6040c04100e18100c442c1005c3d0260280b507522452000c11403a07402c8a09502ca04001e6130065281d804550071424041c155078407c2e03d042c0c0390b5000366079000c0f4044001e8007c247c1200c006075240014070310040083c0c202414440c0d078a50441d500c3c5d007c0020340007401b03070b80c04210382d0351039015594441d41c01c810305213001041e0340318505141c010b214070760b03035030755400c4e984007055406080114071507a502c00014001c146180030703905010315000d00407503040b803142e010300312040c0d040750200103040c1e842500030b0b43c0d0011480c80c3e40c0d2090b0801742c1444080e180800e80b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 29922370 1250 29921120 29921131
    0x15080705010504061b15020703020c090601090f0302010804050a120f030b040605090406020c01090b1611060403050702010c06020405090a1d1b0d08040504020a02030903070e01030f080c191218050d0308 88
    0x190154444406c0c0c038016a40402c0d0160016440350380340782024601170040c0d503000380090906001281c0b5000c050000d240e420f11001c2d050058a8002a091100034454800001d03808070207480340c0c0700310135400781c24480071040c030030006440c0819051050034184580d60944e0001860a4480c0d51035640c3c14002c2d46c0710103040112035403510500c0000a15254215004010030101305501c0c0e65141401018007115000c1000c0e02d0b400b0300c05000219030440100e6070240d07020b207025034144c51181401400b903c602e42c0415040310f001c10070040c0009844d417000c007801555050b009200d400342004d061b42c510320141403903101c4a244190302d0652518011022905204650540c02c0a40d1070700064226000b40b00900d000d80c00004034140c503480c043c04468090310030500103001e9541161241c3d00e011541d01402044031a0001d18000021020001004100401400c00407007082c135140c9036011035204120940811b4400812410300c156140034001a510f016000c042004990340b4115a010b40140c071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 29923620 1250 29922370 29922383
    0xa02031b1504030f12020708042c010816080102120606091203030c04030c06020a0503270d0f0314160204050a0b121609020a05090f0a0915080705010504061b 69
    0x15455104200001c014415400f80c2c9400503508040c03400074210083c101d41d0320030514810044180000c6c40381060b1000d894030302d00e1400c84181c40b502418224080720781d410304002089000003e100e4030020702c0420419400049510160352060300d10b00740c1c0a0242c0c0c42d11101409000180503003080c00c064078101100070128a802004051170300c0c2136034010340b100105070000003401c1c4144030524030408000c1c091480280380402c041c1d01c0b055120300841d591421062404905003020407941d928052103948000d10941808050b45461b00d412a1400011400f06104000304006051840160751100707002044000000d0b1701a42044010100144144619940c42442100340d032203641c0700b410b840c6a81c400504031000d282c8030004820070b15602510b95a40100482c3c0c2140b54405c1c15101c08050030b560601402400f400094504116a0002c0d6200b5260550307400050b11010201c008540342c100a580006844d0401100c1c2d6110300d0040c1000300c0c0c140c0c40c0d01038280050710601c1c2c050750f00800 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 29924870 1250 29923620 29923633
    0x11030304080a410f0a0207050a05060a2a021003020306040b19050103110c070605040e060405011208070501061e0609050a05031c03060b0703030501080c09010513110d0501030b010810020a02031b 85
    0x100704001c55084055210010392003550280160f080c270006074000b600040360b0580c00c018606c0c0005106d060b00b45506400210b00d0000c0707440c1c0f1860400b28403006503009240400100f02644028020b401c119801440380b030610485140300d082000109071032030109040b82e0542c40c240001900900f075000c42d607044d10f810420421607030300c005100740070103059540e075541e0740c8a1400e441c00c40030560241500b8070039807070517004100054024011024455101c03104036264081410300900500065016610304120300303001100d0071241050550507a41c4a8481c0340d138640d210710600291102c2401220740640c0148450b05605540e07445884600701b03a80340c0440c029840f41c00988140d00002c40c100c000c81e4660b0014045103174240101420010705a6404550703614080c0090203d080300c50310000388c140c0c0c603802c0803080000d00c0115600d01c0d021071000e00c15540d49241444942009202d03044c03484c0103a00c1005000841402101c1c1d480400381d0003181085000c1d601c8400ea201c0c020101d01e15445001c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 29926120 1250 29924870 29924887
    0xc130305060108030c0d05030f0a0903111e160b090d0215070501020a03050604051608090111030103140f0a121d030d03050108010f090201050f070311030304080a41 72
    0x4120041c0030f4aa030001550b00e0310803510b0740d5450400c41c0d00400c070500c0400d00402c1011a80c504445511440d60040411450300908096500803440c1001d0307201409100c0c564010000c0e041c076101408507030344d01200c00740d0b1141c080da010120b101d8050b43c100010104000e440a16004010741803043c002042408186004628030a007a031202900b101e13565008030300d6201c00c07505482079551020341600d0901083c42c01c50076400341c2025001114050141e000003207040045d0940c0034640d620304489034242d89507180d0500c03001d58416040c80402620412164a400170340100b4040c000c0303903020680d040008501c1105560440e04030050600b021707940c02c0e070803034269010081c00c0100007543c0c03070018407541429206800c0d80c14400c0040640c904107030407000180d82c04011120200304004440f5101c56040c03404842d551000310302e5401c0340c80080188800d0007030034002007120211710b0300c0e045482c5d4180d101d030b008801d241c203054019010b99610325402d206406400c0ea004c60800d018130a1624901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 29927370 1250 29926120 29926123
    0x503030711090a0e06040f03030b130204090c1403011715040f03080705090123040f0b0406020c0d08040603050910060807050f06030f1305010e01020403060209091305060c130305 78
    0x145406455041544480035490706040c02c078141c002c10050030a001402000c80c0c0307580c2c0d070080544000c18680102e0f00320001e143c4aa03004001078000105041c10589400151002035002400fa8030400d83c5014140c40b161030150705240b00582000c80c425085a2921440c142c0328813409841c0d803400e00614410310007200c0e0880308584182d110303401e10b0030f9203c05803d00402c1004000c00c1001481001c001c1c4001980c0c01211107429031202c0e000135917005140541480c203d01855021b411040960711002c11f0000c031a801030000c0d078040b54200d03030758001403000f0401c1100d0f81a001401a400030041401414465005543d010020b60100d441056640c03143c20200c1e030f1642d108228680000380c0c140000e14020496001000c4211803c504504000c404203040802c0642980070b182c2000e55460304000c0300303401040746550084002c54441d90fa83c24100040c2d44410b08140c803c03181d0000050000324411202800c00f41c1000081c0803075641e01a15040c00e50241c400750300d420801d1480000010720 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 29928620 1250 29927370 29927377
    0x3020708060f160903022209050d05070510020403080708030702011d03040f06030212070309030c05060123060a090e130605090109140d081f0803130302010e03010c0203040b090a050303 81
    0x18aa20704901480d02c19100903d85810f1008039040055054082000d0b9884440d403d2100e1030341902c54000c0d055400340100200300e401c00080060095001000140345c01c01d0151400501a00035a0b000b508183c1141040384228003000300390340b000784044070108584001650344004c2c640000504840104101500b401e940c40a00c5201c1c1d10000d024416038900d40c144000801c00380c1000e6042851803040c007072441100409031800c165031081c007182814450384801e403600790400306941d076958440010325a01110340d0314540880765407000f045114240395048a2083d409982c600114500740044120780000c050030748149161031b601d41ca00442c030b80744034090003081c00100000d003901a5140c841102038026881c00c000b50800c1c44e80c0742120741c00c010410303800052415464442540b043c60005203c0581e00301c2d12442c4804a40d01140a07905030403003094038003d0300c92144050f03500c4101402e07180c0d1664400c005030070500040104900b6240600340c0c0e030301c00400c0032121549800102c0c2c41c541 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 29929870 1250 29928620 29928631
    0x503010e0109030e010c110d02010e060d060e060105070b1602030c1e070501031e0b04020f0309010e1005012303010204051002060708130804030308060a0504060f030c080304050a050d0302070806 85
    0x255103503048000c0680140d40300c13500240030b080106200c0b0003504d0380240000020b905038043d091144456046a118014110030441e00400c22901c03440a0100c2c000140000e014800300024400c0100710b8a42c0200250b802c207035480700c0f907840b01c0d0f40c82040c100c1600d20b0144085080d8071040c8003a05032500700388401c9401448445da200c3d40e903410341e94201e00e0201594030050504d0702d4062442c100107048210300b1302da507091480118039407540c2c0000c10000d1060140e202c107540f2000c020303c0150740064109900811282003191691042e411003d0100d94080c0b14050103410f85010100e41c2e4504840d0303852010400400060803e41d44d040800e0300c8070700325021600141c00c400104041a0707005400369805c020342c0b0340c840c2201d00c1c2c9551042947d10685c04081d052000d000000b0300c15a0340c13008840040c21000e0000d1120503610f415180b120140360100b1a1543c880100c0031402c200000241c5086400003000e1519040c948403c1c424529003c01083d01140181360000c031342e241d42008074500a8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 29931120 1250 29929870 29929873
    0x80a0e040e030409141005030d081f03060b03150609070c03020a0804090204080f030f0403020f21011a1c0b060114030106020616030e06060909010605030712330c03060503010e 77
    0x70080b0000034021400013400981b079204680001c1c44079132400160b00000290034103040c2d10688903542e0b2a03031041602da085000c0051a410003108000310742c3c20100810304160121020003242d190075805981d1708640581d048110607001805040c070880710441414000d00649003074a9541d02d8140040d80b03d600800d42e0703590000303020000c88600b0072200480c4402200910304000e000c50707495020f44903620010348500c141028948280d80e500241508100b5a0070b298256040c03c2401c8a0180091001c85818005120980c910703a00704000c00041d4030181d0811042d89140da9915031004100140540b17041110222010442208030b5008501070b01d00e6030010000791505519665602403c403010404250401e20302d440e400c3c0d000907103260045822200d1250303e82d40d50340c085004141d00c1d40001da15100300e0100184101304d01074046a414054000e00b0400e800c2c1e4500c890258802c02c070b280d0381d1840c02201c3c5100a504a40c0f011b81e29402c9403401080c1c0381e96070320000e800c0d10345001e0452540e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 29932370 1250 29931120 29931131
    0x60d05010911010e0a030302070e07030204050415050108011403070509040305070c06080402031c230c0a0606030204050109050705030109020901021515040507020f0703020112090c0e0f13080a0e040e030409 90
    0x3540c4c120340703c9000e01c08102c0e44207004606581d0000d40b91001c030700c11320302141d44c403402090300b060203601950050702d000303003040140fa0000d008000010049204403404110481d00108000300c0039041c11502e100081d005151740c1e03244c20306000c0301c0380c0010001d40810205000076400610240c44e000c0040031241d40b12601401c03e40101401c00c2800031200008000f81083c28070a90f401250f80c0003d0b07109a4413081e107100421090040703d00c1000c000424902610798031108014450f03000781c041d40d009483c1000203a0300c908881e82103800c1030780c4410100d0300c18401080391100c150020b0003402018815240d031034002d0302d207040110400f9150071452644440311305442d0b080a00c5100d40c0000c6030700c002c100c0078228980c5180c4850040c0006070400400560841e580c2e50345403c1040d141c0e41c002c05100750390b81c0c0c4280004000400307803030181e4404a40c1021580e10b0078461010207a081c1c11000740340c6002c0c1d610f2070035221602040c0109401c1925241b44203000b06c810300c0a003000b4660024040f41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 29933620 1250 29932370 29932403
    0x308030106090819030e030705060c01020d06120c0b0d060308030a0504031209031d010201090516061403040804170c0409050d020106090608030a08041e0507140405130209060d050109 80
    0x1c984aa00a070f6183e0703000000c603c01ca0b2283c510188902609400c0c44404c2540c0c6002081c1000700c0780d00700a811500c0080c2040c86144150300070820b0214070181001500d03198086000c07003484000014150041c1884140201c0581400501114401d010005180313981c035598910141c1040b111100050356131020007051682202c0614203942002c5010088009980d801814140054521400507502c555400286034002d51156007001c0d044011103d0030840c0481c0325000e954903020b000c002948400b02d0300000e07503404003964083c5501000103810a03041c144400000218056201c00e503110b405c59405081d00e442c4102903a260080001e01042005854081e094031180e07484402054500b4600b0003a410020060300c1d610001441c040c100c0352128240440340407071488281c81201021a0080308003e40064410200c035200e200174410640480100012143c0488000160102825a217001032410b80c5056501541c020262001c41446454071402c507600c03000101c0d02c0f18409140c1c0760 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 29934870 1250 29933620 29933627
    0xa111308031305060702130b01020a050105090d090e090312040c030219030b01050a03110409061d0303010515030c1605190f0203010509010b1e010309020909030d0c02011a0114040902040308030106 86
    0x80901002e40300e2911740000c950200d8440310012903002a0b0f50f075180075403444c0360300c02e001410b0a9a0000020b0060b401c260281030340347da410004000110392010f00000e101d03a40f6410301441020300300702450628803e0103081c07070000c1c0010421100d0300c40c115400300051740c68100740c00828008003c000040c03030030f515002039000c4060300800d00c02c24000200f0400a500d421003c0b45a40060700e000c118041341e45020710160a4807a009556100351a1703a05201041c0040614101c44c011030f00310340100518840c2c2c8400e480182c070003250000c000c10003401e540300005000c3c54440c0c4504102c40c0141c240c908107060340c10310400f0841d0340c02d00800d08402517140901502d078104c03100c02c008100d00c441210000d0440314602000301405a420804066640c1c000d5000005031500501124030340d151165482d5181d034440c01c40003804d1498501d041c84814414402e40862403541d0b079011061080392401566403085002ea00741c0c40e40750402000c81e00c0c0c041c038005030005520550b20103440354103004018 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 29936120 1250 29934870 29934907
    0x50a0b0f032508010603150506010503010302150c070b0c010b030111031005010c05010b03010507030203040b0a0504080d11040506040b190c03080103021005090409050303090d02070b030a11130803 86
    0x168400c0c1480c0840c040540d401186100321410380980d00008400d500d078070120b480c69141d2055495519211002040c844e00c0c2c0c01c0760300d2100100100300030b20b584003c01510140020302020f5041003007002007500349000c0500a19140400030111070b0a184e807a0001d40740c1750300c052203030f00c050394488042c1c9040d8102400b924018089851106055103406030b155401a0800d21415040202d40c0d60341c1c070240107080d4400400c0c11009002408189002007014010354426101100e03c429140c000500b42d9000d84141802280c3c408580381c034001266208034060441e50001c0c81d00c6800820001481d540c610b402800104200d602158070703400c0d40404550707850a110414018441021602800a80d01c42d0b60581034942c122007400000c5140f2900304c925009907040743e60404e282103664414840000f001c5d5219202e44421a4180000c014080361503085a21075154840001e01c01f04c0c185d1669604611510a58880018241089503200c07080444031a440034025400c000381c3c13a4889000034842 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 29937370 1250 29936120 29936141
    0x3010e010618200313050304081f0203040213020d0b0a0e04060c02070602060606160203031b010605010e090a0c0e060a030509060a0203090c01080601140c1507140412050c060706050a 80
    0x1084007410030200031043c0c80e81e44850300c03002c4000000142c034041802194460302c1350404200c90300d1740d8840d44415070300d0b81000c24111040c41041d4070700444070742c2802140d104940c007074460400140c1420700100690812100712030f605407a40126082c544904107a2070061101c1c0c0c141c2e40341410241440000c542450032003200315089884203203c40740c3c00040340c1d070b0004002da40050381c1b03007180504403031501300300f2500940c14000080e86000c110360359510388181c0f0b00d58500803c41c00b55074070019101d14040001040d0002e0a030380c00150010403070f0b441072000c078003d41000c4c4500c401c41c40000700140e000340b0a180220b90758805000112408103d810b03441101a40110300d581005900c8540d00c207075401c0e410b41046464800540c559105e04403115030140c0c5c60b480b903521a141c8102c0726444030a1100c0f807603880c0c81e40030001844244196400011a040350f90783c0b600d450305183c0d0304900c41a480c1d40954180c402c0710914122a1103d00c01440a54003403000060709080c00718409040d07030f6400c2d41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 29938620 1250 29937370 29937419
    0x727051203070512030603030706020f070302010e03040609050103110705010e060403080114090a0203040309080d030f0b0402031302191d0703140106080c090307050a080a020913080403021302070203010e0106 91
    0x49000040c000103000c100210300314512981769940d00d000646144140c1740c00400305030000c1030050f000123107074004d0070440d48280c00900601c10410005e640c1ca002c0e43c411000020101c100c10403646d4000d9001c24181d034407585d00b840c581041a1543c0b4213440c05158174140719032090b0200000c0c113030710550303650241c003001060300c2011400d28001520040d000c4c0c00164050f50000200b01018003540c01c02004101910079a840c6802d4040050002d04128860148044c101b0482c1801882c080c400c903849101400c5040c1c803482c0040e007e10030707103e61052800e0f0b081842d150f0042019010420035115003011048032142514096400501341c4031510301100616200d0030047c40300581100e00d0582c040a0749a50b44d450b0900c1d20002480c2c014994400b5802003085c52300450b8100d40480c420b242103000ba0303014151511903c8043e4004000c2d4040079007c8441030105100610384203e032911000c00581e00075081c5082a00028211860340303254a20507036491004000c01050000040d494000780803 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 29939870 1250 29938620 29938627
    0xf0c010509030c030d05070c09110301150c05060711101509020906040b03040c0f050303030405100c030618020a021501080703060203070302071b0503010e0d0e0904032607022a0103050727051203 85
    0x4041e00040c4c00180105020203740c0031030345100610030040720850680003403c8030300c0c5082035100541010385980c0c0c052024094079a17000300c1d9581c54040c184071900b4072150024458a8064000000e4010004070f03035101004100001c0d0055880000c3c500590043d007205011138903041f0424565071540c1d0140d070180d0820700400010440c0403498a05c00160310300301203030612445004500401003a00701c042907911036440098030044a50280c035801d00184c08a0303130707201d012036019058240d0910900c01d460b403202609000107409500070710b8010007142405800d184481c0e566a40c00600700c00b454034000440101003000b46424040c4103030341e4842201604403084032040051070b4503084030316280144c080c44045001c15103e81035640c01903d1112070484421110a4120701c0c0000c01d07100440103100300f0b1441001080f043e8488140784072221020604076034288010b4028040c01030059061081d0581024107884075a100300300d010841c840ca45200c80d0030300e010011108184020300c4225070040c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 29941120 1250 29939870 29939891
    0x7030b0102010c0806011205060f030a030201020304110d0b071d090106050703090605040b070b090f030c03130506040608042303160506100e1314030706060806090f0c010509030c030d05070c09 84
    0x3d1400040402c811005c0350b01d40c0c500001c140b0ad01c40c08080d00340c06100b000d1802043c1613040d03025501036441480900c10800750f000070805208e000c40000b60010f40c0e5400411603a9000c0d6540c03001000d42c01902c080c43e18626000201c0c03602c03090b0b1150021410014013802016031140310700700680f18070301341107003028100102d180440c040c1e100300400c02841280481d0503506e0400c0182d0b0006089422242d0381c01c3e444490a0f120b0304005034a0380c048000010101d040c0c644a8260340a90381260f49403501682c858594000340f12060000340c450080142c0490390316502400101002000034030001140b80d018030f0b015180c42402010b0740005c4074000e1082c050080d4500515400070307464000815650f01c00d08042c01c607602c00101c1d4440074480021030608001c103580221007182c6802055074615990b864665454031580078a80c0c510f5081680d80705010340c0a0006030100c1207002d0115840d014848000c2454002c0304264000402d8020854400f00507a0300c90500161000ca1014004844403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 29942370 1250 29941120 29941127
    0x7060509010f0f0807030b010c050105012403020903060a0f09020a080106080c031c08060303120109140106030902090601110316110906011701030b040f050102070606090c02010e12090a080607030b0102010c080601 93
    0x281c000e40030140c0b02c190188460313204100700e49406070040006c10331035039100f03800c801c000c1440c010081e1008102c04000310240c020710980d4011b00c40036010704041c1d562010034030300508012183e01140750f600c1c3c20220140e00c82d100000301400780700000003a803030300705a011842c221080311440d110f0b6020b404015a04011400001060880d81c200200c041d00d0b50000a829030007002c900300b40b100c131a000005401052900055140303c5840d02c8140b090b6202c420840550321044030294205000310301007140b652040c11080c4002d80340c4816642800d922040141d9059111001954100d4420a142d4400d14000c981503401103001d081241c1e61000240340800102e005100151100000800040070310100003421354929030301600843d0303640141c0c80c05d000180313440d0050152062401c0e403d42540c9005104401c056000c4a004000e400340076a01c90003164070200900360060391841c00081c1080b0304004080c006d030016140816120041b9000900b1070300780c10307c0b0030200f04901040c405103036003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 29943620 1250 29942370 29942387
    0x110412051e0c061b010216060f053102010509060a02010504020907050901020a0602030606070206040e0403020705010306051305060402090306070815011806050a020c09011d0907030c060809010e07060509010f0f 92
    0x81102050b81003a21130001d8500a00845100c202e07500515400c42c810042245d002c4940c480b007a03c002c2100d51034600c400c902180c04040c00219070100341420070711004580300c903000050310514105281949002c00300b045504052301860250391030304148030440c50030b02699a8400030070300d4034a042140380d00000307543e103c40d40c1c0003900315a8004042a107a44071602142c0000360003401c032543e80d603910020b004d6200c03812142030300103000d4040080340c0756200380282811079070700902c0d000c0b4441d01d88030704c90000d0901802c401c3d44654204a8034a864070b00b40f00c440d10840c40b54541c42614680320300c0160b4050850b00e03185042102e8088134045030f400c0d052380d0380300782c80321072910302d4948480600036490203000110359503202c000140000740300340000904a1092100b509c4100c683c2e160041c00e565a05524040146820140c050602040d485030000da540004c046c0000b184007030741142d00504200c13894102c1c1000400001b040021543c04c422520782d5159186841c0c02c10034807150f001172400030b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 29944870 1250 29943620 29943637
    0x603021b0f0c06220303050a02010e0607022503060905010c0f0c020303030a0c020f0f07060306080703020607080306060409090803061e0d080a020f0102040f08010b06030108030706110412051e0c06 86
    0x44010840030f07076104c10810101c03891141d4083d140c032150b8a904000d0056003010f100b0000640c200400d02c1202d43c1c004c20700324004c1c1c2040d0010070090130347c00d40c0d038605d056030241c40400d641500e05001000c16014010140c50710701920000546842d003400c010b24100c040100c02040c002c0a400e50750050301d0010482e9444051a400082c9454000c08101e003001c10000e504036a920801303001e15000e03070010598070300b26000341d00c0410203103640300355513034440e0703110311001e0352148080c804800420181c50065a10030002040300340ba00c1d440340005421140c8500d002d40b0b1600c004410001141080030f00400141000da1401c1398194030314000035004040c404004015503c04100704c58218000c01c0b201013800380d010025912680c0351048418143c2c00d500c940e500319802c100d40300200781070020480b03050b101a50b0185140c1400c030749038a4040c088802c00c188002104001c0000c3ea403440200c1c220885104802030040305000401c03610241682c144514000c0d04018070401e029656542210100c5 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 29946120 1250 29944870 29944879
    0x30c050910050d03090807170303040816020a0801020304020f090c031b0f07140601090c05030c0f04030803070216051e01030506120105040b011802090607080d090602040603021b0f0c 80
    0x155a2107201e441416025401280c00107000c282c031104040d042081e94090b207503860200c030015556001c414240c4005000f64480700d030810004038020a00d1540140a00045459208192401c41c0d0209036824050b50000a142c1d601105001c114a010303102c40d00f0800c0c044030480c20070b080c40d840c1c1c90f00d64403014100c14800c240643c0c104080400840c182d40c002038418203e55240e451900b0590102e4902c0c070000105401840f001190345410781c41100c103400c01c10360b101c500315581c95640402c0d580c065001a0001c0724184000000104018000c5201d8001c40e4040c140c2c1e40d240c60b10846c00e200039504080e1052490210079541e10030300d0207028a400301c007403030b010800c0e40300c3c0e5000c2282c965500b00d14400310750034a0200b10501c520041c1441c100c1c0d40b014688a07400001c01480c10403401450101648800c0400c06140802e04600140c40a52680d0700700282c0e81e011a91903401701d82c050350008000c41c3e000701d50340c4040102000c1130b0b08140301000240101c1d144407040940c07100d10bd09200c0d80306 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 29947370 1250 29946120 29946139
    0x11203170712110a0912050601030f0c050604030804170d050307030c1e0305070f08060108010b0304020102100507030617070f1a0c0106081c1b03140d09060204030201030b0604030c05 80
    0x2980c0b00d42481a1000c6401c001003029102110700002c080c0e02c4041d511010170300310200040d02d18114001200700b190000090881c0ea421641c80c1080c20340c027544191035849914001040645c0e0f6000208015071044610320342d924074151100c0e60b10991803614102c0d9030400002c8003100b6030020200e903444402881c001601d6107103000291011003580c00f0303900420b913241d01c141c4c0b1000e4055211900490703094445e03502003011410111007031001102c0b820300055001d00108603030440c12010f0b64010b44140195080c2d0001c01c03100b0000c0f50b0046500341c2c00030751140802c001400e500304010000366a21009004401c2c200b1070002000c1c0424810040c62440501d02c0c50700e0000342c1000d0b00d83e4400d4200080c030006070764111265540811000300400c00c003850f0100c10065001f5004080a000c0d45510382041111a03102a140c52550341d044601d5400f0402c00d074007081c14144a10581984100c400503102c5080d800010b0482d006081c00c5409030004000c240040703601d0400c44411602d00300d8802e100d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 29948620 1250 29947370 29947381
    0xb010f080c0a020a06020f0a02070b0c0a08071509031d04022706070c0e06040615020c0111070801060e041709010206130305040506030406140603010204050d030c050111030108070303020601120317 86
    0x79001361007502614091021030000d001c8003c90000b0007100503641c3c2203c0c0d40c281c4030342c0c0b0042c0c14031425003100c01c0c40d405081d00c4000601050080d000c254012100a01800c038072404910941f41c4a4034110000b83c00342c131003800d142081c00700802e0072070810f54046007404580107086217640c2d002c03039640c1c00300c82c5c503210380151a5840100712307802c2c5540409102070182d56100c3c19840030605171042032042e41003500c0030034070b030341c500348441800b40d031590041c92001c00e80001034541e518002080c0310700780504000400c0c40c00c024022440101504a510b01c0181341508100340384648110448030100c02c20002d0400d1030b0b0b07000410a401c4200308c140c0b10680a4249000d407901e20517072388459003010b004410030050140710b900c1140616101d940c12440d40d92200105800c0784241d0280951005c1160440000321f4030620407244400d100d1800040d18914010071004980c009a00a81d05940062414400c00d0f6043c003049005015a88450b49042d43c25a0041c084158040b0300c80824401c8800142 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 29949870 1250 29948620 29948623
    0xc0d0503070501020a080f150609060306040f0c090302030c030604050601060f02070e131101020f10020c0102040306020723070e0a111e04080d020c0901152a060b010f080c0a02 77
    0x20480350b8810001c5549280740c99028114920484101c0d418001000029844030b941c00111050b0080c024992842c0c0021032080009642003e0016a009a1b42e084002c5030712405200d2451710165a032124140e0a1842c810940b421100d50141402608003c0500c000078000081403410741c0d4060618040c1300000c031b101280f8040c0c0c00c1e4018141c803407440b0184024030b8004d03041405c406005042029540d1004001682d650110b10802002503009032000c410302420380d8058104541000c0015107810b41c0c9031143da0a9810141060350740c04200c580e0002c0600d01c0c12401e40c002210080640030035498050403141448000b03064070f00681e161010304070b40b22801c000700c0e203d80c42000741427940c5200b40103200c40d990300f15005140240c881c00d108110312500001e400600000020001d4503e6820a4048010300a40c140c80d0814071841c00d0b50260704211180c0041c4440444d9400d00c2c2c00000d80c3d0914400b0381e0388100c80541030141115110888a5119910342d610070342030ba00c1d05540c0c11070404c08a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 29951120 1250 29949870 29949877
    0x603020a1202010c0803010f030309050301090c06030e03071a060103060e040b0604050a180f03110102040509041502040806070e1302030405030d090302120403061a010306051c05071703030702060f090c0d0503 91
    0x1081e0440006c000700f100c2c603c90f101300003581e0090390f6041e901130b11001070500301c810420303002c1c0c01d111424070300b0052070b0302c02c1c1c0010041014910903a810300780c0541d20315040107004075911140070241070030090b055a00d846164001c042c0f00c4044901c60525854604002030060000380c09140c403000000d10314015500050b00d02c4ca810480e006401600d41080c1038104504203040300083c87c00d01d00c2d0a00682c050081c1c0f029100002c250011390303216503a0306020030071841c101d61070650b0203100000b9080d206000c694802e10554881226000d201800c11140c00004840a00154030500900002c14400400e403415110078800001d80105107042c141e10b082000f40004400a10008000c410881d0b25085808a243c024002e0a400d146250065040d510f090140c140c001c4440380e061048898083d0920406034011000e864600b0746078840e000b0041001c01392110550320000034001e00f01c1c0d041011661000308400040e19500b403501c165612260088041885620411600020310109000301c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 29952370 1250 29951120 29951123
    0x40b0403030213060c02030c0909070506030a060914090106080304030b01031e05030301120309050a030209041205160602180901030c1203050904090507210206030703240e0a0f0603020a1202010c 85
    0x3011107065131844010700348415108100d00070b008000c1d01103150b0078068003190003a09110090900241007106000e01504020b1035251216203602d80094803c2c0148a01742012008000350b0328945000038410707003900c2c42036000007140d510030001000460000205541560b51251251618481326030300c4a8101c124443c1c0a440c83c003000000191107855031a19000b114441d44424000d40c0c0d4a9082050b5421380e032001035003045d03180d4001400034440c0100003034803031100d041c141c0c180910722003a25a041c1c00040e0031110b1f81da001900010181503800b980d0205902190300e0300c0c240d8115610755540303050034407402a441454a260004150042003610640070028104000080050403c10342d50341d605e20503401c030742e440c0344050f801c46584c642400e41b000f078001d0091803950301d83c01803c50041500c80c058400002050940041903500d202150004198050701003600e8148044400304403007489954020307903407400d0130400058881800507422910a08800c5500b44500e000507112102203810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 29953620 1250 29952370 29952397
    0x20102011d010203071403010812070302030c01140406270201030e0304050316030215030f0c031e09101104030215130308070501050406061a070209191505100e09040b04030302 77
    0x22000701601c15805503101c3d12955440300f002c4c0740b1140da4402144428003a0380c415401c691008513030411140c0c01032030028880c0c41264500f901002000d821521184014000300c0c4080d014401072003803c2c043d0704180f80d1000107410000311103011041c80a400c2090003410300d40c8900006031102000c0c810745004081c0a403e841c481c08104000200c034403903d0100324400c0055003034601d000745031881500d20440544c038041100791518582051a42c00042c000354500610000700488414801046030181c88200c0060008115566000065984c6441504441d020600040000d40d48095800f005c0e002d10702196691b41102e0907415403004a550005003000000142141c10800e05500107445039000b2181084540c1e01c801c048800311a500c0764000c80d040c01032261901600c0d044082035006821300b40c0d03860032050700020480035200000c40b10265a403800314200540e040ca40c5c9607080c05812894544240c50a250015400c54800390001c0c200181071000241014040e50484148091420 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 29954870 1250 29953620 29953661
    0x20070906080616050306150f0f040803070b01060e010905190e040309090e03070b040b0a0e06070504061707020d39060b0405060901061d040204090617060c09040902010201 75
    0x403070781950b8900c15100520b08003500507480c526107100e071055a0207040e0080a2034965080d030004050607801c04030031482e500d441013018844881280000304000c00814029607124481c504000402141c160711039824000034000c0402982e0307000b080b08090380c0040710300d400c00e01c107280e250700e03c0c080c400e801001042a0a070203000078960000601c004840d0b40c1c0f042132001c400214512030308e87c0140400240300d5881500420001035551480940c0400c40e460300080301904660500d152602c155080c0010410005041c8032450b0700140035080d11050781e041c0c0409040050000359207140050816007001000c10704a4601c80400203040584010042c2d030361841c0000864000280c020000c0444140d860562845454202402800c6c418900103000102a0703107000c9007070f40d1511201c86001089802074040c500103a40c2c0e8800380c409459115800502282082c0542e2100021500d072240958404802c0200160301e00f011204001303801d90b0041008045440143d01605c0c599507804803c0308000b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 29956120 1250 29954870 29954879
    0x140f0d080426012310050a06050702030c030a0303061a030118020c070305030304121710140102010b0d0501140606270a0803030411030106090905100908120f010504050a02090120070906 81
    0x8481054094081c452a611319280c1c00c12440541c4590f204040d0441d90440b0308111142c040c2c001307040e080d8005400d0383d4003080c001c0d001a040014042c4100e0110755107440a1002c1c000300a0307440c1c1c4c3c0070135054030b40d80381d035041c1031a16680c3d004125200100c1500007403501e00c044420b002c404015640501103d0300d0703040c985004480030846255a0001500111a480b140d601c3c55552500400d00c0041018003581403412894030040000e02c40c505664032030544040079200e280350802558060400007030f0040f411140440042c60142001c0d02c1600140044440d800500e40b1580c2e02111250056521040b400d010450320125644514a1404040104024054a40c540c5480030313004030001c0040507100c04034001150540040540142c1c400007030300780d29000036844040d02c40d00401106080c10325018007a00c0a4404841d607000d8481d040004006a0802d40502904610606002c0d0709045500300020720044d50b044c03803c458141d9808050305500b01c24030650380581822103080c400203488 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 29957370 1250 29956120 29956151
    0x6020f03040b0a0506040b0609090703060510020c10090509010b0a03090206030c030901060f0b0a030f0b0a030f05070f0b0a08130b07090305100203040308072601140f0d08042601 78
    0x3203c00c2c202c01400c043c0040c00030314182c85140d103003240081c015810403000605010807001c00410110615989840200342a0f40e5409a880c0a80d40c2e0fa00901000329040c091040c15565559070b1028449480c1e070510060380d6241d00c032410b6900c58128580ca44100c0c43c3e0480252103014400780d00020000288046885030070000c500c1001c4800c0240030a69581c07010b140721059a118289690340f080c0b14a10001d44240c0003196051000f050115850302d0020020700c4180c2c46c0d034012281c11862040c0074040040a02550700140700c804400500a450100c144030355108202d01e441c00c00c03100da0002002c0010309910200c40a41100b140c024520b402d003006041101c01d030100303689604ca100c1610030703600c0c441e0088070301c500d605560300c0c1c80ea82c5850700141c604407201494a412006450401008019645181d40c001e241300503c0f450745520080a01001712040c0c00030a016650809009000c40c1104084408031001c424010008442c50f13014440c10018030040d05090307508080001281c1d002 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 29958620 1250 29957370 29957393
    0x50709030203150103050d0e04090803011e060206010b040909050102130b030117010b030706260a05240a0608060402040801050108030405090f1b130308030a0c110f030702060706020f0304 82
    0x7080e422140e900303241081d000030300103007407000800300c1d0320a07208031146c1b6101d842c00e0001d03050041c1c00070442820316540c803421274200342c0003600405542901c50700b2030890601302500910050000e883c0c40c0d414903501d12258442c500511000075100c02c103403c02c2080035411520004a84448a003d0300d40303551800705140c0c001e08c1209000c401101c0e00d036400308010320a0850985000f070007001554075060301a500040021120002204219203030310200301186040f62003120490000940392900581290701d400e0340d40441e05451000c024075688a4a40441c400161a0036041c415070966036480050080c0c800d80e004900a54200800080c00000010107001030b101e00f00e448104a90b01c01c0b500d004043e008072150003030300081c81c0140c070114a04100a004a101c40050294030f0398480d110410164015074107403134001d07135800649101c6680300704410704400d506000b41ca100b4203084070f03481c5d40f401451006803241d140042d1102c1003028650444000c4140148400d84a00c3c0500f4081d85586 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 29959870 1250 29958620 29958623
    0xa030905060108030901081b040b1603081621020d0c0201020c060c090303180409020a03030f020d02060106050a1101090506040f0b01140612181f0f14060d0302030d05070903 76
    0x400c03075001065501001c016501c0300c0c18180e40782c441990720784006020062040d404103180c49000c00c40800d40c1d4001d880140314100007501402034044030303440d0007460b010005040d102210550350307000d0700095100c80014000444141c1c3d640c450800f80a081000703105100149801e9841e114004581d6038041d0081c1035400641e07005d9803869907610b400b0b070000384180c0c0c0c80b02e54140c10800510641c540b002100c0d0300310203005030000801440d142e001c01d4040d6955001500403406098803508880c0d0304000c6407800d2510742c80034000d00d5141c4080230705580246000d041c244208520070101680003548000d0f00340790004102c420504060806900f44101c0b980c0c25181e1114040022510307088284d061420340202403d050314020341c102c0107944003c40a031822a00f0844c5001c90751608100704441c0309548072030411484040d0381c0b107500004941d000846941c00c1790070b080990281101c0b50529686c032010a403402e001094052800301d0070342c814409060540c62801090040041d44192804241e9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 29961120 1250 29959870 29959873
    0x18070207090b030c1c030201020405061b010c021b010c080f0a050a140406080411120a06020301210c0506091513060908031206040e0f100c080f0412031e020a030905 72
    0x1000e590041c59103440d0042d0303146400c5400f81c10100c8040c0004c546074040c85006e13100050a0076107503000079586030311501d1203218149440400c0d20400d00207100d207400d9214a400204041040c00610000c40c0305102001c5060010300c03c0341d034003401482c40440d080b40030700321015556029140d601801c5a008003c940300050440d1050500b8101c604088034103480032911000c0850382d45a441d03080700990500d0441e000080d110038108500c004000c180e4402d44100005600c079130510020b18140240201000520501c5420440c0450840c482030815504203a60203940c801e694070124512018000702401f0040c00040e0380c1316111014100b11041c0d4200380d40d99000d1546e690600e6a90340550002108032108003c04a2210f24141d8003060440724101c06032154160090f4006041606000c03801c00d10725201c000500000b0f60045c002c59004200705082042401d050702d8480241c0c018461a0003072540e902c5107001c0861010300c0c0308400080d0000b0a6644074014034004000d0300304101c0c1100d0300d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 29962370 1250 29961120 29961131
    0xf061608030c0703020706020a350703120b0a051305040303150801050f06040e100b0f040204230301050112060b010309200405010e160c1502041707080c130b1807020709 74
    0x11f5a00c0883c00c20161500f022403803104100030b01070401210f1a840d500100442c0d08400e03540d13403e0020713026100c0d144c000d444001041d400303408014250381d2481141d0b885030120070401e1010380c4e00da001280503a0344110b00001c59585528080d4010000d281b4070411094840310b00144031001500028858031009840005581340c8a09100035101c0b4103c0c00940c54018125950607060542d11507411710300000d00e078020010a9501050880c0d1060704141450f07185120000501410b030b40c850b0600204c290020400b03585000c0300c0090465010310000e04480e00c602d0b030740409070700c246c00c20b828064221080307640040ea140300104582c000d18100e51301683c14640001403c84d00010366a2041c1e100c400c2805070005004412541280a540c0c00c882400c02082c40f4240e5400510151014000c4080d0301c3e02c0c03e82110000910b41042d0307501001c2d15500030300300300059480341a40da800200b03400c1e00c0400c3c80280341c40095030303841080000941d29074005c010400c1550b80080c01c2c0301122102c0808012 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 29963620 1250 29962370 29962379
    0x9090f060e0105070c0f050705040e01060501081609051315120516030506011208070803090106081b10050702030309040c05030a20070f050708010908070b070309020f061608030c07030207 82
    0x341d40041300d540f008074103a0b854a001084080e00c00082c0684180c00351051107880e0780014003100e0710001204007680d591003042c862560402407440c1c208181c1c9001504d904000c800041c840b01990180b94000d400030502c4540c01000c0340c11014280c041d41e008c044010761140700903c918201040261000c0c4a80d021901003107081d00342200c10741c0d8100c4085d0106a007170070b0040d51001c42000c8101d41c903030410000c100c041414140950b028a401030300114500b8584418189007040e5441300e0701a44640c215001c0c480c1d0740319503005699403030508002d5140d0080d80002400d50041c8221581c05c642071104518486601100941c881c4508400c20001c80303020061141210f02c1d2040b0f0081038410401204d03010490600c000c4407028461412240d445442d150705600752000e12808403404a00400da1004114001c013149030b1100007807030b040100c050f4a80008951421501c0a90300615002030002106580031010000468120840740c0e51390900307280c150040d0b40241025001801a81030106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 29964870 1250 29963620 29963623
    0xc0b07080f01031101020f0303011502070602060c09010f110a0318090e0705060309011d06010317031312030209040c170a0506090a02130f03060c03060506130b07080409090f060e 78
    0x103008080764070340309440380c0c00c50b40ea000302c29511840c0507040d4030500c00340c44c80c1c4c600e003000210b028040c0c0e140c00301421405401c01a00d414207a400c800e041d90050003c2081c414000410f40b5641d90091a02c0307400110421001d0f2101c00e42103403540c116020380c10b04007040c160083da4011403640b005065500d80d69550314404d084617902011a1495004232004204d1031a15001843d00710002c0b40001840340d20140c00d81203503814003031003018644c1240380100309101d511282c1d0000d24680e02601403443c500920b900030800700c110402040c914681d1016034245120742d041c2c3d614050003034010060781081d000e001c0d12480203000000c070200401c000241494410f8041d42d0301503000038001180d90344510f06042c002e03420844420400b4007401100095091901c50404011801a400041c0c0c00300602c03001400e452190700701d40d003d120200041c1804540d400490b4080350a4030320390039210004d5240203903061140c0c0d03010700243d50420482c0000d0050340070209040520510080000800324603009 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 29966120 1250 29964870 29964887
    0x603070b070609110306070804110105070b01060807030e030318010f06120201050705030d050a0f0b0904030503010b070302010b030106080102130609060509090a1e0e011d03040306020a090909030c0b07 88
    0x20410300c10309002041c000b072002d8005940f107a214071010b86000300d84901003440d0510444401303000600d4442070005002c040030b0042c01f60a804e02e0405c0c600101c0d601c4426107214184038080811042c0800640c1480c840e51064003401c40b41410389549041101c0d100111603c28444040c2035480d1591803801c3c07184903c10002215420102100e03001d0003500191a1500080001c0c0c810b03010410450000c48000c0c8117a62013041869000070319240700c10080c0c0b003222200108980a20518002d21011941100580b41101c000c03544442d035800e500d1800724094642c08032803d0b050742c04d014011604c1c05040d0080d0040600c8403c0761801c807955800101d070912050f0cc0781102241c0300700483c0641e420000041d40d40500d80700404204881480b1b00c07001981c40800c00d1003d269610300300940000c9080c0142406200102042d101c513000210040d5220703c01c1d80b200829096002030785400380350060504100070310101c40c0400130b081e410306025000992400048803034100400014101e5406440c42c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 29967370 1250 29966120 29966129
    0x111010218010503071101050f071713020f060405040908090102121315090e040311060604061d060a050306070206010e0f04050d0e04020d020c0313090207050316020f040c0f08060307 80
    0x103030345102070060040d02d903584060aa0000c004028441d40049042400380343e000380c09106186c0080e2a0210340103001c10301305000801241c50040034080448814002c5000054040741e01101051600d0300240842c440e95002542040c10f1003003000510203d00041c0a00382030030b8007030328078005990703e00000d0380c8034a452340004410460001d004050014021140303400c0c1c2d030b007001c2c0c400d50f0322094000d5440000b01d0b821070010300500170500d00f8110500c940da40101c029a414000c0c5801c0078001c6007610344204ca42c2455080210009101750b4500010900510300502a40e05034100325200a44030303d800d0090311000707031412010a030100e01c04030301c02d485107402c24041d10094907850801c5484105001d4040e0303100c1c2e001c1c0040d40010409100502d150f0807806c0c0219a1001d500c106a05035107580c0d030221010b0361041c041314001c900084107c41c02e035803103416a000d020390741c1d01c005003841c0c0799840c40d550410300d06070351480081e82115400301c946040d07403a07103025035884108050f51080315024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 29968620 1250 29967370 29967397
    0xe1501140a080d0509010215160e01050405150313080316020714010504030609050f030f040501080a0b2101020d050f010305010b030a0c060e03030c15100e01030209010b0711040e010b01110102 84
    0x580e00030300f0740300310054070340c50005205461040002d1020304103651003d42c2c81071541080c4a003040780007a04084800b60604081c00c2c0541003d00c1c2c800010080c1c592449110300c000300000000d01754100c3d050046032201d9004504076100c1c1030403000d01c0891309040d08400f000d8072039401c2c042048086450403001d0740c0e505a5a192409007186e466901500d80d2810484c9e031449803411881c040c440900c080d200350170708001266192031600000500745903000c7c1c00b0384c440300d18140c09515140c4901444084641076240c06810308001d1040e50360082c0310300c1d07407212102c40c40d0006101005200030030b02ea049902400003404202c000c2400c042d164a1181802010102445402c01801e405001070500a25009056031300303002d0355026650800d69254403c5001c43da51104000f04030b40004c0c2031802612290702159070b1981594041400580e042c019000e84d0800801c814003000400b14480020041c00741050061441c1d01d01c14501901700c0d800a280800c14240510000c41c80c14420744000300c0a40a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 29969870 1250 29968620 29968633
    0x10806060f12101406030d080f040f08040f06030501031a070e190f0e0117030403080d180f0501050103060c020a03050301120302030702090702060f01050105040506120a0e1501140a08 80
    0xc005000b00c00c0c820611241c0a510180d0b09489114481c004542081000011003460b2030b0b0105820901c00504075014030aa031014810b13a201d142e13940c0d540c41075129190f42a10100d81c18080c100c2e0003a0350150102c0100740c04045205035146e040281244e214003500e90981c490800074102004040740c0190010700459805c0301545410b02d020700040001070845403016465821002c0311400c16002909041080c1004020340301300c0341d0009600f120f0340809981824119074034140b4500c02c106015107082e44442e20310104a180b0700340400b500d90700081c03c60401d4001c1c50000e000e04800d21055814518113105010b40a00200e554140d82d1f034141d0319a85141c0c205800c9081d80b4030101ea040d0304600c01444280300513221241d065000328016002010603181103440303820043d005801c80382c10400140001c20080d250101542e20b00e6491405044060f9030b0f1901c01e100030059135008940701e21801051144009041609505030385641d50302410384407000d003d12031410514440c105486d0b1004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 29971120 1250 29969870 29969899
    0x1060801140112060f020c010608030702031e0601090203071e02010903080705030c0d0207050102070206071a0c07020a030303021b01060f061209020a0e04080f04030303050618010602071503060506040902040e01080606 95
    0x551010211617403804005007060360040c0010700b11001c5030400070080c2e10004a01007945010001c5101000d48945a0b4603d00b103d001c003140c0303030f03031042c41a0b85c07443c0c0d00403012138102d6020760820400c1000f405060f02840840030390007030290101d1607040d40030480e55404185900e100f403040740d01c5690b00740071103071501840c0003841c2c00070340c040001a2803c0d5420311030000145d0725040100302090240412985003000441002704411016000d010741c0d41c4100458001070719003241080859405080060f01c40d0f4500440400d0246840d1006c26994a00700000c42c0b288455142c520a644e0541c0e10a07900d44000c80810088881c100e102950101d034002c0100280070403013503c940e201e07114500c5541044400d29003440c042d0044c1d0021408243c58400301700c1030382040e1882483d41c0e600c2035860748030795140040183d2581c105003d0800305401c1c080d20320703229900a4021500424015040550b01c40c1d94805500003504180100110301e05c2280c00000c442d000040e0140c09514010075514840121 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 29972370 1250 29971120 29971133
    0x902150304032c0f0411030f0f0c03060306060f01020a020a03030915020118080a05040b0319050c1603031104080312250f030902040f09050a12020f07030224040801060801140112 78
    0x102207204d40d0081e11081e00c3c130401890600914044c0c1c46051840f021404c1440140d418184000e01ca514181c4040c0200511b03a500011241e40245058505008062540c40100d00300140c094000c0d4002003204000820181c1c0502008129405822600410f0122440c12030036070340c140d21105e03440c0b45442d031a1004a0b1000d0000d0440c0f10302c500b040d03458590b40c0e10b2455100d8004591040d003446042c11401c0c0d81e44e0311806826031212203103604900e02040204260030030b070322181004d401c0564416030100b01044000c1240c014007202001c42c0e4031070051549000034101e00715099074007c510b042c02c60140c0c03c0ca2002c030a960b0fa40c207031101f1a2480001508500911020100340e0340684c0368200c0e201d08034154858800301c41c0c01000030303040c41046401c04822030752008170400110742c40a480b440c031100d00441c00c03000352a811140f0140034071007114030002d00307403140c541780150305000200045c000381c1c15030282046603c500002c1c003070019004080c43e01642c09101c0c0144d20941c0c4400080080c64 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 29973620 1250 29972370 29972389
    0x6090c0e04020c01061806050103050a02030c12091e0a020a08030c0a110a0b04080a1a010f0504110d0518060105010507080904050901060801020301151404080d050d0902150304032c 79
    0x1414400041d40d11b507204152040303200c000050703403400782c0e9a50f02400b003941e043c001d059010309280c01c250314504006158a4281c8110f18082080c05104408940c0c0f43d102480a03a0390010504000c3d61408441100f1a4035442580800c078400e0104441c000354480010040e2420341d8000009006198107039100c3d29407220210346241d510125020001c103000343c510001e030001c0d024034402000340c4141d500e0451410f0190f664100e00c0244030b840104200d42582d6202c6c03081e00c4e82540c001c01c0c000645102c0214900800084140141c14041008940d41200001c2d419042541e411900359990750401541e00c0d00c501d0350040e028403c2001900c2c4141010341100703070415105800003904a82d19544d1a00b2a00b003a000400e5050540c0520018680d200040c2c50f114030700c0d0300c01c10345131a20b000301c500da5808408404605000010a030039010440f640d005001c82c81d0042c00650303c4003081c201200c0135600445007280821031940300074400f26054034051f02c1c2e10f000b00a41d082c516942d0003c1000c1c0d0711 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 29974870 1250 29973620 29973637
    0x607030c0b0103030c0303050603070b0f160614041a04030215040f0501050c0d0c0201060e06010309020d060501061e02010911060d1e05060a0501080c090409080408030c06040606090c0e0402 83
    0x32400c5248001548140e00c060085001c0c0d5075035080c15150303140c0201980d4003d40210300c40d0340007103400e0000c1d1420390200c9410b041d40c4e41c15203991b2060b080f8201c09102c0c1003000a0300b0785182084a0030302c45203030203a481c401c0b80b1610b800000a480700c580b02401d108242c4014005134000da15030200c1d03902e800d00c0580c0050154001c4080d6040c21f98849003958801c458560000798082500008100b244c001c00d0146c1210780000c0c4142c41c04c0c4091012a1100140140d0406403540c1030201951911140c0e0000643c01440502c459030715007030017501d80049021000c0850304400b40c0007440d1407040c810902d102e0780c0400e808000c0c8213402e04120317094202004044507a9940c001c40990165443c04101000c02001004941480e21104200d85210b840d48840e0601607460100584041024129000324070122000624070f001401c1c80f00d854010307070304104041c0c030000070914004040098104d01c0703144100d00500a482e2a0b104c103200756180e0303200d00c0e00815007041038043c0901d0715402078600413 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 29976120 1250 29974870 29974877
    0x60b0406080f070609080a05060f0604060803070807050d0e0904030e0312070302070e0907240302160303050a05060301020f0d02070812010308030103120504050109060c02042012060d11060703 84
    0x761152011030070322240c542035a103150301000c0108200c0c0d40004c1c00200500d02c10740030740b814900e1070715010340b2070380014a81e00003001804000340090781d899004030007900b120002c481c0c65a9a0340790180e8a5800003905640c01e00c01e034074280441c0d51291031a41c10303945016001c0700054a4075501580d031440d000010a40c1405101c4100c501742e41c011014001c490300030390041480c0c4e4a00603882d0040b80c8080c0074400c40d0f400c00b00c0188402581d26000c8600e1881d0021620460348410200310300a024805001307401d02e16032014002816415080a4010203407141c0802c45600c40c071082500700d118180e207094803e2814081d5140c000c1191740540920350060074200d04c3e01d1056041c00c52140e100340c00031214410048018824000c0c1c0d0718030030307601415070b080c00707440c03d0308150001c0d0407054240f082c0010044001c200104540f01e94000e544c0c800d409000c0015108000e000c2d013007290704040840c0c1103240d07a100004c0c1071482d000d843c0400b035580141c3c100c2100380100c410301c8810b50207802c0a07004e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 29977370 1250 29976120 29976131
    0x90f0308070c140102040306180503090907050706020406030b190305070501050d11030a09030815010207140103020c010c020106080f0309060d02070f140c010801050906182205030901080f13060b04 86
    0xc6410f00711108503c1d1601400140d6490031480d00c00c007114010750171180b51120380380034000065800001c036244244102c0d200e05050381e620358211903d22030b602000f06040e0003c18009006a01038118135255102164925580842c12020181c240d1441c071000d04160b202c2c001c10407107035006000614103405141c001107500c0001e0b0700000c405a0007a030b08a9a055500c160742c4e030615500c00a040d4003c51a5050300c4c0e00c4903842d0340001e503141d40b540912003044107400103000342607009604480000020130000d000000460300c01034000c0040d071051951600441c0e0032284480000f0046901440c001030056041c4808180d1102c0250050f850499461030b080303041e000454098420900001d0040b001040c003043d01d01d000409004d01a44658001ca10302410f200040d9680e8903004182c04040d50002c3c0b2940d00d06410600041e56401c98018211000100c00b0030700401200408034a0400e80321082c0316250700202a1036130404448100852440400810000d0031541110300c4020008001091 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 29978620 1250 29977370 29977373
    0xb100b310b040305030a020c010c1a0a180f03110111030a0b030a0f0c0f0509070c0209040305090a0f08010e0303090a0f050106050a140f010207120204020313140d0210090f0308070c 79
    0xd82e03401900140c0e039039440030680342c0825904210140c0e000d102803134969210803107642d8420060300ca03081c8080580c2c4052000442d0b004c496442400d0107403000108000101082c244820107a00868050b0b0000e82004a0440c01041c14020030503101c1c41d85c840d113403071641d03507005036001044102d541d00c0c1e05020f8500c44c10081800c03404d1503803000340102e1100c84414680411300b901100e156021902a41c1070504010f0900d0b0040e1080d0301d407a07016a040003007607880e1b2030300300c03800d1060844d1540e01010b00c0c140460812240c69504007074542e04002004200e4100030b001c1d81c0c0340000c49017821280e220380003c20009070107020658240303205000120f6842d480e0b90000e100139041d80c00040d401d542e80306101400f07180089440c41c40d00c1003070025140d41070400c10300000012224130080d00864001000c90710b841805505a0000c5400440404540c0071a407681c90b2100044820030005100c1c132502601000083d11038010020fa00c140e01d20b109035003e54080d5000780d002000c0c0030030301410101c0c02c0d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 29979870 1250 29978620 29978639
    0x40b060403021906080105010c021005091f050a02060f04020a0510030608010c030b03010b010e0907030b0619030902010206160207170f07180f090b0105060705190b100b31 75
    0x1507140c3d1810f15404030b81070400c1401030860034140c0c0910704001400b100d080141c1c8a201d581050181d01d07142c0282d450f254040400c110054601102c070480d13158410303885c1c1c1d82d82e000740580014101f550a03141c203515030494400e60300f00c050b18040d5000010000410261a0913400c02000d4142c0b0f040c0840e400f5640d603405030841c0e64003211000070036102c0c001460b5a14080c403500460301401d082903c3c005c2d0119002c2502d03080300600160a00d66500322800c610394920081d60350b6066003130b5080d034030750b88202001405044140b500302c0c090320444001c10300340d2a4107040d240740500c003907008004507868649854000c460b0400c04011602944503102e10a4800b4400310010384206074500794200403d250450440344402a01d4541a00e440004c05c00038078008032550440742c0071940240c070b40500741003035070800d0042c81c0314006d50008981d00108006c200f60034144500140c0101844940d600c01e81ca2040344281d1144081600e00c4080d070340c000088414407003405201070700d01900c0603a01c608059 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 29981120 1250 29979870 29979889
    0x302101b0b1608060d120e0f0901030501020706060b070b0a0c050d1407090602010c08041442010b073008010305010c090501021c0c171b0d0e040b06040302 68
    0x40240d00302e00d5244454894105824070f0b00200280d0782c0c000b40c41807980f600101c0010b1501c49008022008000c54503a660761100b200d443c2c0001800340c038855030360b4a4541d0003907015034411605142012000950a400581585e082c550004242c120341c0e030300c0301c410500812400c0881000d04c4001d01c0040b98890803440ba0007250f5032401200c804a082281c03000d040103440e58030410441e810138000501040e88405500d400a40c00014580d1034540c290a071810302c4503140c00740c08540c20320400100700311300b6032484152400686040c1000040d40a1420200c690240201030380103404111540c00130710101c140840240b1041d82110034240c2c43c80e5001e50115154a00074000b884a6006005220b42032143e02002c10503400c003038403a58030b0030380040d40381c204080c0040c0328041003544610400c0d0003007103030000081d400503400804242c004000055a00211840d030b4a988004517443c100c140c0c0010800e645441c0341c2c503540c50b0f4440090410010381484a1340e5a0444000d02001006071030301d4810 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 29982370 1250 29981120 29981131
    0x306050a2007030e06090a060c02040f020c060a0605030606090112172a01091a0403110304150201140103030813020102030912010504140a080403080f13080c0f0105040302101b0b 78
    0x41c035036200d0a9080c010140d592946030103125400800c0920056542c41e601102103c1560812400c19129400050020701c0c1c0c000114001500008261f140c030340d40400d107903116140e020410806070391520281540c0e0102141c03602c0d000106100184440e5841c0a4400401842841b10380c00d080c4442d40c0e40074407034100c040c0440c070801101c0a50b41910125104040180e1701c00380007006410340c2c60b2505803c85005843e000c04000a220118050512820b1a43d03041c404400c08c496965079a90b0804114000c40000403006502c2c01600c14504417880c42c035070741203d40580da040c8154039040c41180d01c54040d401c3c204d055200070440c260440e21590828501440340380000175151805081403550244016940250703a040005040700142d41c40007a80d0560350442166a226049264259440e1003680111b081e020b03603000c4000b03841c0d200040c14201d0f1101c140c403201c0381c0000c01001503130340f405a400000d5000b000c0b04812100b10744155001c404c20105e080448000702419141c5802511081e9007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 29983620 1250 29982370 29982431
    0xe1e0304060306090902060904020703020708010501141806010e06090103090203010f0203090d0807020303071b0b1906090204050a0b030403050702120309090c190e010e0307090b0a0501050a02070306050a 89
    0x80070012550503204000080480402c244041c1d0b9240c0e000501031b00c18000c605105981c085014014075100b0400310016080d420020001c80d6110322802c0107084948100c1480f8803150014222600c0029600074021081a1944061a40381d01d04101c0305420242005041598641e150300c0540c1c0c00340941c104000d03100100507524103080481ca41041c0740682a8400d1204000501c004a0b0380041125841440c91030803001c40312603048406544106480003614280d190004c3c0314a20780390030003a90b1140300140c41003040c0f5540e115600e0507401648203150380300b40782a40800c4806502c50045922038801d15086e0b2612840b64005040c8181006101a103a40b01083c1003201d81000d00500d5002603d00214030306040030740aa061800610104000c00c004111185000d5640111450641d50800a00380d403032143d281c0714607178000c0c0b03159480c00d8400d4250700c80000d525400340048524400880c0d01a055450035920b40c44007810300074002c41940d035595600104e17603006401c01825051803018 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 29984870 1250 29983620 29983627
    0xf0304050c0307030206040306050627060f040605060d021315170106080606040312020114090325020109030803070e03030403060c170631090308040201020f0307080d0e1e03 76
    0x10003a241c4412501c2980c02548102d5060001d03a031803809940440c3d6100001180d20740c0c074040130803901d0119020043e144c091844003008c50b101b401c2c540f64410380742540e17440c0c00c040465003004251030071b0303104003034101ca81040244200625074008040c055000240701c10201d6803030103403582c641708144096000030b044410700308100c1c16581016004012038a84a20142003010014140c0e12441c44004e0010018140d418030700ea000790413104101002e03290221461500641aa03141c0e48007103007041040f0170762041640c01a007940140d04003207130103943c0c3d940b03c0303405c0d61b480142c242d1001d8904018011180e020107559a0304000030006507100d18800301c2d2072014000068100b00342040950038481d1007104209140d1118200e669080120a84014105072201c1e4100000c0401140c141041401e108500c8145a00165440e0050f8400e9007103d202d80c0700d03007110a071a402016001407021004201c0320b5800c035480d800c07041d880010402039400b5100c41c01901c000700705a00a00304000d41010 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 29986120 1250 29984870 29984873
    0x4050a0b0a0c020c0607050f10020306040605040203090a020405180f10050105100e130908030108010212010b0a0507120e0d0c0e0603070f0302040203070903021903050c01030207110108040501110f0304 88
    0x200c24560007500c1e09805000742c8451210294540d01c0402400e80140e101003028014018100b0030300e4901a40901034405075014028080c01941c0221042401182060000261802c01d4030032030307228081800281c80d42c504e0a500f048040c04000d480d0306c5a030109044005010801031051108980c90b04000b810082414900d082c1903820503401503201d0b02110070741a07050b41c0c0060700c4c4801020100c40e4080ea00e02100b00b08401880c50301d401805207034020001045141055000340910f4001c016841030507a03035050144142e20544542c02c000800c24014400017034425901e40328101d0040c246030240d04071210100b590100f240340c2c03e94044440c0c3c0700801c11511100f09054100000381c0240c285941051000b01c018005440002c3c0a140c0c0000080c00542c800d801101c09160300a10410640d00000452044e100090000307071403601130121417000e5507010340708840c242c6901c80c1c0a80904203040005440340710300100243c0e030135529080240c104080007001801d00c0988050503980b242002e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 29987370 1250 29986120 29986133
    0x1080303160e090a1d03070f0204050a06050105070809030312090105040318081b0d0215070302010c09120b0603011b030606020f01021e070804120804030b0a0b010f0309050c030604050a 81
    0x1c4014407040c00300b41061001c0d19210308000c0d82c0d010b01c43d284045104612a17049155901c04100301c0c00c210b02000c81d0310740810600c2843d294040d4002c8500b80b2081c0c075400201411150f1922500b400b01c3c0080004200103401d01c4013a048081d0000d0a076400d2880715402805002d0040b240403603980d54a4041004254010b102a08148000080c8050312410a10503c0d55540412400f4050b00741c01c0c2d068081694407590000215a409803040c00021200030b18400d00347c001c2d40007203016500700a09014600d1160342c3d0041210301004607800c40b00030540302c540403c00c000d0044c40d01552512166500e0b83c0700c00c50326030b440d8003e66900060161405000a050905044c1143c2003640100502d10710500090810445041c0e00030b445541c0303407103c0c0740c403e1191007079602c20002c04da240704200c01844000006402140e01480f6184a40c2d512609040d0442c2d00461250b03010480d00480c805025200760b000c003d82070310a50840d900341c1268800a032500d0307003c0f0390484030f40d4816503114041186 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 29988620 1250 29987370 29987401
    0x1009030903050f071503150302150a0207090b03031c18230a020d0618051002030115030207020108010902030705070204020403060507030c05040e070810170609070b040803030408070809060301080303 87
    0x83d12028114582c1005c0c112081440c482c15014105038803412003601d0503d45044a4000750341c000c0142c29000c007803084a003104c1d009032841c10090701600310002220100340c0100b10401c0b000901451a140980c0c2170119403c4034070b50035003081c80d0b458540182c01039164042d004010b0140c40307601140001d0b804c4d91554010040711462103a08005c0403040140c5076941280c210303d1344003401280781c04031000010801d03145c000000c0d049206201c5210b69030000c5038010f5041e551150002042040611415000d03840342c103600a00080b9a04010401543e090303010703540203016403130f010b0302c1d00c0103580005082c1d030400d4001b47c95041c2d45030f061165254040c07244030150750075400c249007450b162510001c1c0d5903800030301610500003200001502852881c5400780517190300030410112200510440340c1d40e42c821601024a44100301e0f0218114001200f9103080b81c80d520003c41c5103580f00d648400090b08601d00450710314500340056145640ea50b00a10301a0210000441d1030745010b4107405c1c400034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 29989870 1250 29988620 29988643
    0x5030102040506070618050316030816021005060f040c030b100809030703050307050d060305010e0705060c0d272904030209010603020a020a0c0609030302070f08031b100903090305 79
    0x80c03042000b0440394407104140d60415130801000100502084456440e0405041e0018071500001542c1e46a29107a50540c006803802983e840300300d0340d030345000d007101d4181d519000e03005688540083c1007104c02c10b800c56544240d016054601c80107040c40403806445200142c00042a125038065a460420340400c0c1d901101502d0401401d0400400194036841a030340007030200b0400000140c2c1041c0614100c03499140700b9002002156a2820310030300070640310320300d140d190181e564001842d103041ba0aa442681084c00541001c2c421300806584a80e070907203404079200c1311011036444560140220b14000d1001480021500710300101c10160a460f1581400c4000018842800940c8412911506440860400599403000c1c0e0b14103900e005440b0100400c20302e038a54001c00d42d103500c50382a008580c030030380803a04225140d805200c1c40030100e00806005610900c0300143c00440c0c1c500b0a0b07080300c0c0341d80a464915910b0703d40d101c2034880c510802c0d408101d46080810410608004061841 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 29991120 1250 29989870 29989873
    0x62707020a06150302061e090901030f030e010c080307210504081902030f09060d09020301050103060c11030412022101020c010c11010b090420061204020406081204030204050c12130c0503 82
    0x3d0b0031580042c060b80256045202440f01301000a15200243e40c12520700c140006c00484203584d40e8501003a0715284c06104030b00050412508030003950003a0501011154002030382c609595904100700c81c00c00385000003481e080b003100d20350500113049214241c0070380e0007100c1c03803036580410015801d60b002d50071160300c00310341c010444003040305c86400a48941010031244541d40304481c0c014440070b0310091a0196044d4608400002001519400050440381d507455041c020820300c011203441c1c0c02148940030140c0d89c00041c88005151070401b80c01200d41b0b071540d00e18003064201c5031600b240c0100c00c407401244e550b951001d140541140c4c0d02184078680e140244201c114030404a081440050401040c0c2e00388820191820464031048080c4040c002d0b0103651204180400010313031702002da8060303001e180783c00408148254081a50750000641c0d4100c2490a8031b19405e0000500004180010824080c00000700a1094000050041c1c0049000303500704241400e080002e110164000c0b4400d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 29992370 1250 29991120 29991161
    0xb070806010c030c080901110d090602010506120304050906030313030309050906120c010e060d09030507150903170c0405040528020c0703150209030304030b0a050108030a08062707020a06 82
    0x2503120f8038104c4841e0340b00e039045884101800043e243c082650070b00401c1400f401030000710241c0e02c070a04100b1150b940d4005d11007501e41c1e82c2808090440044098041d0b00200700502c40c600b400440150000009000c40e4501503007082d1484c0c82400e03a4008800040030140308010301d01d030880d4040d41103c1e044503140102c03600382c0d010f40d555100c010903080c1800040c424280c407955589050344e0290322081c10074480d251085c0340041c191b52003a202290218040301041381c5000780340c41031603240c651640310010304051000c451516000001c1c20245441c03010840401d00ba25240199400b4400800c40b103c890030f61036400030202040031000c0b0726014418000b0300081000015414100e030f40000c10741c000c0006107003075580a4402d04131a40d401d4440060000104040b0490251103411002c208005603625103c00d10f49921030746091100080030700c07000c610f152900d00c84001c0500d01000703022000302040001c4004016088400f0030240c1c04c01c1c0e0740c030f60a00000d401050030900000200411 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 29993620 1250 29992370 29992373
    0x20918060106080c1605070e09100f06080312100312120b0102210901050d020a090611060108120913050103080a1b0c03080a18090603030905061e0a1b0b070806010c 72
    0x4850140b0009100e070a22417100c11781c2408010b00912001d402c0d07101d075104243c40c0400c80682da4414103a1001d141c1380c44d000700d40900a015200b0700b8103407103001c0090340c50445402c0d011040b020000c1c0c8412580303190100004001050460115a01940c5444d1019810348486c0e024080b1020150640d06640150016082c03440411a164010011401100b9100c5008200490703940c01442001075201d440011200c8099410503074000480308980ea41d50001c0800f40103a0340c44580a00c550559940070301c9589280300c0041025202c01303a80604403071001d031510091101551001c0e4002c0c0c4e030140c000541d400304550f204205e49514008030318074214001c2281c0d120221500640302c090314400c800b00f103402c98244505050b80c104454040d2119250361500f4100d8000e00b001c0c482207011814040c000203545c2404403e942c040502039144001c0100c0c8108059082e910080204080100c00d9040075604400554001c0e002402150440da15150680c0083d1003090003030141818004060514070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 29994870 1250 29993620 29993641
    0x60b070b0c03090a0506041a100b0f0a0c06050403090f0510080a05090304080a080d050708010501020604020d022d0406050102060f04031206030b0a09030807140a0e0a0302091806010608 81
    0x150041c409001c003969030303501c00240905200940300000e210b40200003d0006000f000340c1e01e45030102904038401290f80b1012910800c8016611402d03403510000d2000c41038000c07001000d0b10440d403150500310380748007141e91600c0031504100c400324080707042c40506008a04204c03403080043c1005950130001040ca6a1010b007901c5402460b2440355a1101c001901a40003801590002c1c1244022540e00e0032140c40c005051717812048039025024a001c0000740302c07030720980041c2e041380e2068015080d162615002c0c017958841c00c0781c099810034680d880303040e85410070030b81107a400b0b0041c80810784003054841c1040107858596010381d045610803070030322114080042401d900a81e05041c20400201001c80d071f100130340903682c00034210100b0b000410014030641d802c0604654800e6494040c1580c43c414195002c0000e80461080103205010340480f09002d0f40001c03a01182c0103011110856607a0700241042600704c03440704210340e00c1100c0b21100d420030003c0318050030070703414100d00a1400c2c04000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 29996120 1250 29994870 29994893
    0x80a0b0112020721050a0201052d090703051603031209030503011e0e07050901020609070303020c010f031d0102090a091a06030601050702040e0102030105031203011a0306030f01020705010609060b07 87
    0x1204002c0d400120402086031032444550b906800e1468105001d114010141054015213000300c003550819002481030b4004000c0070a000780d650340d50010110341041d0384201c204005200b01017503c00c584020004c5481000000340361241c0542d00c0b04a5410b40c40e0042100c012040c40400f9141030004a5000a8024003a64191031a581301103c480c03040c0201c0c5061620715501008500c0e0515040c8080164000c005080b40c200a030201c6405807105c15110350345001d1440040c0c010b0708a82c80b152581c0d845943e842c440b4130601d190209200c0003001d082014a4030a074a4401607a500140d2449281040f5460078010301c0c1c000740401c0043c060480c0d0082d11000200818402c602c00800100c05d603010743c096600a540181041007804c6021800f14000d602c203010305803103442a913043c0c41c00901d4900441c4e0581d0b00100c507288040d243c00c06255100d401c09405160326010300440c601c0d80760380900c09442054020000400c0e520300c0d161403141203501c80e410424900e01c013080401c0c04100c04d072200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 29997370 1250 29996120 29996147
    0x30403050712020604030b040b040c0b1315020114090f0f0d021f0207050a0b01080601080c01140304030309050d0507030906080903090d0201030b060d060302180f040605061c12080a0b01 81
    0xc0b0300607840240700041c078034032030350b00001c0c00c02480e44180014002804c03d454892481780c1c0c00440d105840c0d48403200316015408520103040308006050102440324000c200340700d0018000421205400382e00c901051100b12002d4200758841802406410030421500a0282f62140a0000d503c0141d2000b511006061610030b80c0311406050f03900011000c0d8101c0c0e08054000056507000c03c17003458881d80c2c4080a03c40c03842c5e548944400442d00d000b010640ca1a2484141c507489801c81c44002c0318040340c0c100a10580605681340e5004010482c14852940002c5142d51210ba0b684454600075010b481617402c00410410a102003140561000003212407040080b103403c006002d8a1004034050300c2c0e0b0401c100c0c0c0280c40858035103800d034000d4101d8800d0386d200320350182c0452a404840840c1000403030300540d441b82c103807002c100400e0099110580002c4050412521a110884ae0100c01280e008088070300c0c501c86940498083d40c050006504048092020b00005265400080c8050100e651 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 29998620 1250 29997370 29997389
    0x2030717040510020409021c0501050105040e04050f0604030f02010e010606051c1e0b0f0301022104050a0210050409051005130c030e07090603020907080405121606141501020304030507 81
    0x3080600c00b08000000000b0750440d015540c464031a040100a504201e5010b20340e00720704000c08003101c0301030143d64113135001a034076a8202403070030014901c1000080c0042d00c0b00d0103200011100312806100c614444c5001c4d0301d60028400501c1d400a0031529540602002030345071002c14441d00b51301004a41041c0d45400380c150341c4144803050b00340144502c0d259110703010901e074110b011949031608084c0b01d049007110407018050001003410700f0703071140221140314071100090404042d0740c8654800c6d0024002c10444c1d201010b29404201c10390401c1400d61b0200b540810304011851260180b194000034140c4000c01ca6440c0c2404181c80381004028500c080e901c580c07804544510070b0340300d034245580380400c0311b501035503c0074800d006201d90301080e4011254000010710240c09940412700556210000b060007120b50107241489030410320340001d801140d5105c4601240e0b050180c07024000140c20860101d00700000d0304107000281c2e41c5050f0541d00300744800c001003440807074079004481c0d1502 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 29999870 1250 29998620 29998667
    0x307020a020603041104060e070212040b04030f081903050406050108010903020c01050a0215011211010f020a060b13390207032d060501060e0a05031b0a08070b0c010f020307 76
    0x18101e0001d05c9119142030300030b07140c076030002132651300d1017401809000603809807444041c0c0c2803c401064400d81c01080c0d00310104100410004800121824085010791351031418900700300c1c0c081c050b00654102201c0040d4494040c4002e100d16407154900400b807000003042030288594007c1d440d0142c22480c14140000494414501ca000b400141081d132400740b0020455a110030303092505100d1482e00b56521065a02c0c101c03480d5015041490f402200d40d00188007107401c9a42c0d00300a000542c44081d080420110794102c201c1d101d02403d01c020300181130400c1800c1d50001042800085c041202441284152404200c90303000f04042069a1b0400c2a4000c8501080e02101e049001c1c0c010032080d20342950911014880507a1200d0b040e501c941d511600280c02c41000c00c20034001314059030385d06402641010b04209051504105403070400303400010419a1101114100015944003401001c2d000542d0081d060083c07003500040c2c03107400350850444c100340000621602641c04214520b50b2140c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30001120 1250 29999870 29999873
    0x2041416030e0f0d02100b0307060530090d080702060606040e100312050d0b03061905090a080d06091107080304020105030403050d0218030c01020706020c0d020406050402070b0105150307020a02060304 88
    0x2800514900d00070f2808a521040c1d1600e0025920f8240d100e900c42000d2401c6801021442d001c9050012140d0350f9450358200ba10400d03069114201d0340c501043c002c2070b2004009910b160488902d4804c86c05840500511020904007400c240c40013840b05045402900401c41903640365000d8409440d40480340d400c8640c1c545454a410010a03000038002810f40300400b805180d105004006003141c404042c0401c100603c05d0654031001070f14241103800564032062180308159018036801040b1204942d07100ba081d031540481d03940000701c0810003a0b1100803c1c014049a40503005e901503180c0001c07440c2070007d440301003c60001800080c1005000804542030611a509483c0d81e1103440508650f01c0001e801281083c215500480d402030080c140c1120103980041200c404880240d005014220f06030401c0000300c40f5420004c91384241e460401140c207446520241180a10560102d145541010200320341000c2013003411540c40ea0820402000c00d0740895000d5281c0da0645616403030b529203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30002370 1250 30001120 30001123
    0x2060f0a09060f090f020a0f05030d2a0303020a090b0702030705091f090507030c02010b0a030204051003140c0f0a0602100207060204030b0907090c0c0f0b09010e030f0702041416030e 80
    0x3825081c10f68181440e0280d0180024040c01d0740c0c806100f00c85407402c40d5500ca0072444407444600c00c042c1d05030001d11300600034074001d802e0702c4885048800c01400181c0b550000709020040d4550540010380c1c003086a034201a040103044007c2c0018054481c1400d0b05980020359500b210301405010b40c00203004120414032140001400c0c0715141e4440400395110100000206000c60344800003030300b801c0d003c8072580d00621500000d01c001900315600f080c19074081c0000340601426120792401c4030900000420443e91028076030b608994003501280d1040340c1044850540c2426040c86000d0701207040180307a03000516902904e50340306025071130f441d146c20310200a000b20b91002d403802000710104020880d021034041c0a0b104115400c0050400c00301d03086440000c084402040c02c00c2500408010560641405030720245c4100046044100c1040d0f00c3d095401c00f000090404c100442c00c0411440c217401110301100e039603c0c03010194500400c1038159100d02100d04000d060341c0d801041142c010 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30003620 1250 30002370 30002381
    0xb060412170403060c020601050604030b04020f03030d021309141015090b0f070c06030203100506090d02030a0f1104020a170613060605180604030206040626010b1902060f0a0906 78
    0x2601d81c106031100e6803420b05401400c5e4030002e4100501a410002c0341520382081600e0949400540c150801c0d61030340d003404140701011814540c180b20900100a10b401c3d41d0000344000380d10f400c0c0401189140000080075211705401c68ac000402d90703800c100646000b440501e0403502500300100500c607217248251201c2603e41c103c2090b83c0c074000b0314811032100312402001e00741c0c401e959150207541e641404504902041e80e80c6200090506803c000c81c0ca8841c000c1c2943d584010107040c000c0d04240e0000b8034050880200701d502c0ca4262181300103000d1030b02c0340901c1c031000a5409620340701000000038070b2680c00001b40c0d8094510100840c000d070b15201d030b9844d1100d0fa01401008425103815016045801141c48000c40041000e9108150306128060b2400c496010304401c0c03c15081c6101030b44c0c003207140c681c900c4a0b0b4044442c40c2102c008900911402880701c0900c050343c8616455400e20240c1e2007590341010f552007501844107840700300340100d5220850402c0040e00c80032030710b0300d0006480d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30004870 1250 30003620 30003653
    0xc080609100b04030b01031109060604050609030102120a090312050c070b07020a0204050405010b030705040603020604030605180604080403172d0705031c14071205040c030503030a09060f0b060412 86
    0x542c0420040100b05c214540705050781d0284001d400da0101401c00c202d180d6400b2140c00c0c0d007004060000300014141071014090b12100140050300b440c2020381042010078044903480100703500c030f1914a09050f045200c60361000560903080c0300c186001000f80895100c3c8140060500341d400c1e00140301244240b00160000740e00610a00081c101824468041c1a0100c8610700c24040e035070700060f452516219080403207074007526681c02d02d4a5512450010100241541245000000c0c5160442c00c00e11200d03100354420104180c40f40d081d8200005168032011080b0203296081108060744900b14000d0341c00d071003000b14007180030515021401094010742c0030003003da03c00811480030903c2e0f4860000c00c6034200040402c00e50040041c030052080d410b460840c049000c0400243c0040c02c141c0040e80d000d03004065007000b06030741c0d41e941031559004903400400e15075184021030030044640541c8410116849040c000300684030b0020701180f095100303414031184042c0b91042013002240c410590135 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30006120 1250 30004870 30004889
    0x100903021005160515060f03120a140c030408070e0108031605010e070e061201060608070f02070e070f0305011505091306050406030807061103010b0405040218031b03060a0c08060910 80
    0xf01d02d0352600c240d44014680781514103200c880c0c0018100e080151000000ea20011b00911840c0b5019070b08901c164445041b603010400b860340801c2001008030001c00748555490000c582c2c8a1a10354500d0a1000325045003241c20100c0c401048450400001d440c082c1c07030f03200c038a0a00100380e807a1041c0103200304501082c075402405070000340b24502c2d50280388103e00580b603144150858014140c22101240141c1000c00d02c100041b564040c40380049086950140c012110200d8850b0900054081d04407019000101070f4088100159414000c0070300520445444145803481000044c141c7c2c0640300540c0d01410034400681c00d420740503003007000103001c05881000015180d0510104e10390000d403013034400e1800c0100b01c0c0c0a01c090b1000700d07070480c3c0c000c8003040c4c01d00381070030201b0001c4d50103400300c08500c110b084000e9220396428001c04000340165070b0800b0702e000201c421306050007401080c2d1039005240c108443d49030342d08108807613401282210a440329550b480c0a04c4000d07a240c2c1c1026060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30007370 1250 30006120 30006157
    0xc0a09090605010b0702010203190509030615011d010912060b040f05040201020f0307020108060120070611010b090408070809031c020606010e030a03020a0303051504021314100903021005 82
    0xa0001a8042101a4014401406143e0702c521011100f0311136060024016032042010b000314100002078004c4202d01c9140c002d02c2c4c5500b0a0010749864010340d0b02003540c13041c60081c4080d41d078001e0a044208640440d288000e0300d10040082d00450042c400c0c0203140001504031010030505902101d08044010300070002000e540e440c0c0070050038111012809841020300150000e0000810f503005079034142d460070701d01c0c3d459000450f00d03100019400046920b101001c0380445405005078405403045554410002c980a01d649003034850140e0284d005107800814400440d030f04008465400307411005141d0360f41c41d110086031800100186001900c0e4080e024040c00c01d50100d0050f0042000340d81d01c000440308141015111000308070b000780503038000c03407500e40040d00981049a0040c41c1005014407490080b0108069038003100200c0b14003618414144144044428803a40e240800d4a481e290310356400700162503280b0901010344501403000140c0004e5125000721411180c407002001803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30008620 1250 30007370 30007379
    0x300702120708151b09150d1b0504030503090d0311030c061005040b01020c12030d090506010905090304050a030303020c011503060e010e030a020a060203060a05030a0f1a10170c0a 78
    0x211585580180b2681c1d000d014000d038044072850014900a8404607152001070b1854001440294410620544c00029030346c800f071500809040034000e1041c040b030003c02d40149680e509045201c1c003240c070b1000d101c01884240042031000003607900454055821002d400014117080d80e20b007450254080240c030000540121052000c14002e008a54206403100d900d038552007004291b079000c0c0740740381c0142d0040c001160a8984400083c400e0019101520302c0c2440e19210403080e00d0010405450b0b6501c880010004040203214071030b40085540302440c02c00b420900040d403030b0b46841c40041e0406801051120301c00c0c10a6004000c0007251401090460740e89280c40805050001c3c1001c52551900006100d1a0f002008031000303600240c1c007a080c00045c039500d9100079000a020690000e230600f0740484c0a0302d08001e100c45140c040d0280380f91440c95484c0c038100d0f942ca1b038140701341500c200c1014441c020200803000010394480d20707051010900458000352811001d9664154015a140310008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30009870 1250 30008620 30008623
    0x503040602010501080307020607060c03150f030209090a110d030302120709031101030608120d0207050102040e1609060207030b0703142406070209040204020a09030503030c0301090e30070212 84
    0x4403000c9400a00c082d0f82d840c5011600c0b0300800310003a40000d41000304000080c415802030074600314505001509034910083c4c0404614603800011070059007850900030351520221032a80991120014490b01c440e80c0e0f41d00071480034080c50603001d58964030b6000b04040c060340607500c0e4107203031120403c1d0a2901c542d00824011580c4400d96544151450308840355201c4e000c2e420a6401c55801800c8105c4c0034846800c243d0702104040c40445d81c2400b00a000443c00e0001f000140211860003c85051130654149214030940d50a03050000c0f0700c80411440b900460344104494126008400c0c1ea5181c038003d8024000d071415030b001045194040104070009201095400700581211050207400c007020b0000510610001a50164148000a005182c607030010406580c9910382004801c3ea0383c2c0c2d581e49150010356001c04203500201c0123111480081c45080d61296000d001401078080d0042131500c00345000203030a040442030314000001403807450440c1c40c0141d0250899100c1c0a085072001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30011120 1250 30009870 30009877
    0x30306030b0c07050606100c1509020103110a0f0509040f0c020a05060c13050409020103090c0308120a11070209090c03030a0201021c06080712021c060b0f0306151e060301030503 78
    0x3203904041c0200400e008240c040306540100d54030030000d0019858102c100020b0350801c141c52420400418460000a1940003690307121010254001c11100190b100160070382e09048640407008038140b01c0d030203c2581c0305140f22105081c6041c0b1590f100d801a0201d00038204100350304045600b81000084690750024484507424042c805940306511098928401c03441748003004144009030b25010711041c078160388000251441410006500e100b6596503144844199006580f110400b1400c121407215100036a0343c00700680310100704c002a0320554441c0b074042d40c20040c0c02960302c2030003d54119000c0101550001c0e0081c1182d48400312000028003075401410441200840989111440d02881c01071009441d41c09025010311406c01814107000000c2174020303030340701141611034015004001c00385014035015503004a1b104030300d801484803407020142e01c2400307a4002820011010036100c0f4103101c4031400c540a041400307412000700106000c000d03086130320843c000000000c00c40f0000c000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30012370 1250 30011120 30011123
    0x61103040228051908061305070510270512010221010e13030e041104060201050f0f01090908070203010203070c020102190b0103030f050d0603080d0b0906360403030603 74
    0xe01014a6034440c100b905141009901000a880070042c04107240120301c02001250702c2150b007041da555010401e00c0d2601c2921501600790101c035626003031050511822015010584070100388100101c4000c28500140207a01c200c420f1400c480f50059401c907540d01c005100c0108041c40d040d14903010a4000d61080301c0901542d04560f491394001000c0c2429207049608a00c2107032181d42c2c41315185c0102c05400300b000c60800003c4694000076550318411646000205d0043d2900c89090001c06400c58601501b9500e40c1c40995080000f02155000302c24107542002001207044505460440320601808100030746c50350010041000c0158403407029580709000760f088801603c06410303442808030300c2d0f400103008011301c40010710201e0b00031050001d8518040ca49203241070303000c15120081307400542080300c004e07000041640400c440c0c1e001e00701c203854045501c020541010800a0038407445651704646030451541d00140c102280c0c00d0490203025403c4c4115030a02e02450000c0c000d082c4c5000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30013620 1250 30012370 30012379
    0x20901021c0203090f030f06040f0507030b010605070b07031401060e030a290106080103050a020402031806090f0d030605010e0f040b090406020a03050c0a020604030c0c08030a02010b0a080d020a08070f0611030402 93
    0x807842c410f072500044504040300c001000d070030507482741d4881031640d180801d416112481445400800601c9c86102d0b9402440c255407540e848054914007420f2030000548028101420080900007070448108880d044494a0418890b00742444010a0820060400141070403c915580300c1d42e4910341d06245402c0c40c402c0705000c44a030381390380c025101c458080c0000740a03075203c03440480043c286a402580c0041c2080303894807281c92024003452a2140c22a10944940c001041c0d002111400300a80c0d07803003008500b4140202810200020072507151854560b00c980d985054402c1280c603680e0200c00205005000d50001d40b900303041c190003a42c4481e00800020b40b4010014061445040544400c0d00701c560141c8806e84442e00d046603001034042040d0350210001e6000035004000304000d000c000d84c03940001c110882ca8004205100c21a0340c00313441203400c0b9401e0608882e40c08a0944001e9a11140854680229040c541c00808020100901e214905020490f054000d003024501c0340f40301702c4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30014870 1250 30013620 30013639
    0xe03040f0b040602060112020402040f1202030708011109041d0303010b1b0601030804031112031306080f01050109170a06060902030a0b040902090106110c031506031203011503020901021c020309 85
    0x5984070554480d0f4410900140c110b00b006105a0f56211102443d0b81d00080003d401d09844824404040c5282c1e444002c000e5800700d0302204608080c07140d40010302d4624002c110700b40003c4070300c0c1041c0c800e980000c1d2141e80e554181c00c01e95003118075016840d40300e000c1241c2d105d43c3c4030700c041c81c040e50008a07183c00c0350610b40f42c4a400010000f034228182c80d0b000f00319904040c5540d0314000703064501ca0320341e84d12017100403040c00c100c082000139042d040550b00c0982211450210017a003c40d5014051008212000c1c00500660343c0000c0d04108a8501a80300c1c440b410300c541e042400c02e034405130010700311030400c440000c40d800180c019600445c1620b5003044014030b07200810040312140d00c0c00035001010302e0010400b542c0076002c1e000a082841f003da80381d14440b20002414110907841c08460b003c038030002d00030b4600302004094145200da500c100d155505010a42c500d481808144500301500018074002c980d00c01d1000300800b10600c002c182c098480c0e880080e4882c2c1200d0b114600401e50359 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30016120 1250 30014870 30014879
    0x203091305010612090809041a0f0301020711010c050703050313060e0102010513030e0303070209010e070e090c0301150e0909010606031112061e03060403020c04050c0c0606100908010e03040f 84
    0x244070300ca040751015110b01d000e684454010310040c0030780c0c450546030344000744103c0400c1e40315030152091070303151120300b0302200c8040020061a0307403c444016010340e00c18014480042d004408001a000090900c0503042d111464141e00c1c02d080358100401c0d03030202140e00301011015200b0744042d0341c920340b03d043d143c80c480c1c00120b00b21501118943e81122040b101107001c01d02410900d02c0804c0c0c06004d50789008c0003038000c1002000300307a00c000380400c0c0380020403512560065210041004c00c440c42e400da0700b03008076011140e0006000e4841847d80800b5a42c2559000b04d0b1040c041003805094044240b0305002400d0080c0820b20440e4042400c7c407403802e13091440a411108400c88062165816440d071506000050130103942540300f2540100100390355039800c00450b4400d5120380e000780141100d40d0f052000741c82c4c0140c0740b200c06003000d2048128403080800e4840d1b10840c103840390301030b18030207040803910b10303100342d01200031546040240c4800c0c10303000c0018800d440c0701c1e142e917507491a80c8 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30017370 1250 30016120 30016159
    0x50304030207060c03020a2d08070506070207060903081317060402030c030304180e0a050a05060103050c0a030807020603060409020402030709050a0e07020607180b030f0717010303050f0d0f0c020309 87
    0x1480000300183c00600390a13000070100024945239490b0018210550403204206103c40444c025054031140004500b49080000810507581e00014900c06020078a1a10f40060080d00d2217010040c01c0420124107034403e404822031030300050515281c40034426a10503102e0b500e50605540603030090080002900090400204031001ca4605004000345801c4030041c11004000c0c42907100031a00540c81420003244c13081103034811290044010304031079490361421502c2c20100441f014000c0c04840303801c0001c200c2034400e8500072601503074403503034036030b0713014000340082030b00c2d8070001d600a101005004041d03601c050b03088195641910311205441c4ca6604800304800102d40e0000180e00034800107485030320541c00741020480035010014020b403130f581000782540040703401086407070403507041080a903031144001801c0224050b9600a55046031402411446030484200e41040006980c020702c084a034400c40c0010314008080140c40c61000d0000d49030341c080c0401134850151003e018000d502c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30018620 1250 30017370 30017387
    0x1c0b041a100e060f1308120c0709060501050a0509220b0406060c0b040201140f0315010f11070501080711060406050108060903030108060103030c08120a09020103181e020402091005030403020706 85
    0x140144103600304a040d0304c0300005a44540c2e10603040503001800029010300411001e10030010340c0306002c0e100d00141020b14074256055004100d0b5030f0400504000e580d8029003100c0102003185030079543c0d42c008101088510f407600d60340100000c034486080446080c030742d110a29600b0112000c2c001d81c1c0e5100b004a0b841c01d070f503450180c168018200032500541c000e107a280000c82030022030700d06250740c0f284520519002102c00500d00522040070700c40303030340e03000c50090406055410815030190200102e65994000c5000780760520200c5404141c405004035580391b44800c103141200c4c19803a007071510a010301001e100b80c00c186d02c01e400c00301d03681d0b02c004003c0e40d050702c0380c500041078580e196440468445040c41429501000d040000768101d0a00c1440030303100741180d0301d0100b1214000c0c8001030454054003c070380900c0300c04200c2c82c2c00050001e8400356440101c6140c00c020801c050001030024410300c1c401c9684500410369010000c0d40000186216600a4090303410042d6240d10a464104 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30019870 1250 30018620 30018647
    0x10f0e0a0308131a070c06050106080405060f0c04180204080c04052a16030c03120218010302070804050307080604060501090501051003020a03140c0c071502031c0b041a10 75
    0x3070a9100080080400070350240042c3e000c4c1d0304042c503803403003c400c1102d014001d450141c00078801241c03007428043c60380241c5006280034500350398603141a440d141d88800c0040d083d102ca12412901140303900401505a6015061210000403003e448010101c0254400e00c51141b043c0074512407421300e17207070601c41c0503c900c051040300a11b0003244900880701c2c1d4003003035061402c03540c1840380881d140c540324500400e1038403035160a01c60f00064140a8a4951810321290142c2c0c0104034005e04081c80b84151041e0240070300300943c403400680303010b449c24020340d00300a401d480341c0b51001401300400100715010b640266010095030b41c940d00e00b00c05450003400340035000711409072000f410358400c2d0300422405034203140004040381203003a9200b10700c03c1510609011100402d003002130003010320411000306180d00d01441c00900341030b07010b0740386c0c020100980e80340822125240d08045103500943d411802c000c1007000b49109880300d03420340c100a030701400e0103101c00a80b540b082c280912020503008 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30021120 1250 30019870 30019877
    0x3030717070302040306020d06060e0301091e031101090803010e100509010308070213050406050901110903060c1b010509010218010e030a0602030c070c081b22020327010f0e0a03 78
    0x800031004004a000001e4034a41c209070b42008000041059440901507030400200701084c02e500e0a480244100c00b2201140d210780d150a84e00300009500480101650846000400d1a000e00c0d05060710001c04110181040b94203012701c0300e080101ba00b00850503a2110007000c440b5460300bc2054107900c0e198010150000c0000d030042c030210721185c02400ca12403004100307944141c0c0b45071201080c0d69007540c0858029850b4424406800c200f80198a6641c010b05003144c2413040d010002580c0d030070007801c00340079440c002541c40440c00d42c09500b43c0900300c1c40c0000f40410708000801500035448012480c030740c85038800a540c145d610940700c0e40461907006008051aa40a40704c110003948042c0c004d15140700100146030006034200680b400500900d000717402c80d040c0319020340380303c502118044c0707120f2030f03a00d024105015541c1c4984560000f030b07a80016100d03034410486501c0c0b040b0b1401e54061580c0f265015040c2580c0542007402c4440391103905010b20010ba11711070f0307525003040034000d010 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30022370 1250 30021120 30021137
    0x804050304270c03060320030303010e0901020f0304031e0f1215051801030c080303040c090b010c02090f0403121a04020903010f0203071e0f0f0e030a02060307050c0708030307 77
    0x4a140808240320708002699250100c0300040c004541200c3d0490104000f0070785030314042040c0305a0a00d201703d040300c01d81014a8035414507000a4603440140a10310300c2280c10380101d101004254180d510510b954a142a96401c0c00d0602500c01d00b0000c0030701d43c0130711160220f0010140b10300e203400c3d550341803900c0d845004403882c1090750141c10b1010405290142d8002c00052503601d29500000c44c00104070b0001c01175055061001c0512500d401110855204006001c0090301e00c41c41501220103103540011444440c1c40100d45901d820140a54480c1c080000d2003108240c0040b00ca0240b4401d80319540c081c0b01211040042d07030440c0c54401c0340355a041da422080c5c1e09007a0001c00e86908010000035a001d282c0e80780d0307022600191403103000107144919120145040c056450100102c0f800d10b0751b00d4000c02c400080a00303031012004401c000815001e4041610304000410704168010320b5151070b841c10450003041500500c010b80503500c505040042e0708036011040f2030040d5110b43d0f41c0307404d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30023620 1250 30022370 30022379
    0x1803090303030c0e0405010f050406080307020102061f0b0a030506010210051005060f0f0f09011202040b09040f090f05030d0f060302030c04090305040801060306020901092102040b0d05032101060804050304 90
    0x28400da039641418407001690318110b176900c6104080c003803e0380d01e0000204078100000c1c80100c03456a04002103d41c030400490000d0b030380025910354003910349444001401c141c0c9102c00851807260380280449a0045003603281e098041d0011441400300381d003100c11402d01000b804066031811b41c1d1280500d4a1010103100074205100100303002c0214405440c50410142c0705414147e002e600d4800f000e04004ca50020303103603030041100390b0b4580562019030070141810316400a601c01c81141038410740c1d0300c1640780b912400e00d4205003281a0406c1c01e503122508181400c5e905c0e035000d00d403640707803080c07a10040d040c0a0909220306c2050f00d4000d4001c0001004000921009000f452025000e1040500c000251207009004510242d0300c00e11000d070b110052440007500c102d1007134004926500011804040b02c42d80b081c4100c500030b4044402044400c030aa02050004204883c0580580000500d04480c082141e40056407101c44008002c05a80c0c0e43c4011118002c0a0300d0090094004005c00c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30024870 1250 30023620 30023627
    0xf0106030c030212100611120322020409050606010e06120103140f061005100305010509040f0618030c050c03010924060f03050f061513112b1803090303 67
    0x403040d0201d81401480e1401c808142000583c04413410f494420410605020f801d500134803c950240d1080300410b009060300520a009002c002d122290741452100e840c0345903664013400320791164014000b000030030f0b041c1c10709907182c1300e0858241d408221002c407951103908085040700c041c0c0004205110242e425959440c03280d10200c1d664030b149201d490840503038148103111483c000c907241c08140d02c656103418180258900c0785090003050501d0800108140e44070f0194a41c1d10a03449001455502c5203403610b207000f0090740303c3d001002402807481e2410582c0040c009107603e0f00071411035054040c0a000c1600b6207030500e20090051484200303100c20130390065901c424124219a02003105510752003d801c04104a920a458aa1060180804a010521800d50800d000c44140c000c8403c0c902e001c41ca080e2950a41c800704156184c46c903d1030981e180b001d4505080391650f003550440300090500e601c0100001689100911305141414040807104014410a0781611042d182d241340d51000c0c1c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30026120 1250 30024870 30024881
    0x102030a0e041401060504060e030703030c020d06090b090c04060504050108030703120603060219180e1303021608070501020706230306041407050408010e0307050a1209080307030c02090c030f010603 87
    0x260781240e1516001408107201c090f0860107004140c2e240c5881b1440e001006250b0444505064040d400c040c8042c40840c1e0f0000307003000750329010f480400200101e4034245c0018250b21350050301600d045400c0c01403220001c5107000b01d8407021201032180c6910341c0c1c200000c0311420310440e00180c2c802c001501c0001d005150b0743e0030254102800182c0c99950380ca1307100a0364001d42c05d4074038500204811200c056040419002d5400d0f650780c08450603030034000101c1a030b03070010304210b825081e010075580400d442000040041840501c88050071a5a0050280e070354001d40203a83c054000c1090210324988035000c25001c601c1a2031415480c8024800b401c8010380c001b40c00c1540068555a510b044042c94012042c094001640c645503503a140c100400e007110030800300300c5400d0300200604c50106400041e4218410342000f403841d080c00c0080f40a8a126144d64040031141c000400d254040c950020600b0140358004d41e07008180e03030340c0d002002d680c2c2e10044800c040c8a450f0400180f001c140310344e225 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30027370 1250 30026120 30026147
    0x7050306010e011e0b04060513151d0609040e1501170303060d03110312090d020a0317270303070306060305010303170c090a0f05030d020c010f110a02040905010b010306060e0102030a 80
    0x4c00381ca4032030300119a5988150400c0c4046139000070200c07480c5600c6881140181660610f002d64909500c0c00200000c034494210320f40007110051090090741c0344000c4230710340030b4000c00030080c1c4e8400c04030311519500c4c00c207a0903842c01c503035500009003510a0303c41088811041c0c005185195140000c1048000a1110a0b01081301c1c60051045105042004014049101307240031010320381103d0061414040c0c03100076085411404550001030b8104518074004d0041c01c4440e00d2541e280785002d0080c42c5040042c880881044e900403080d014080004c46c000c40103603070140b001c0c940f20542a0300780c03942840b00034005284071b131080030410750800c1b80a8015800151700d61405000800281e400320480d00104021020608200014030b13040240012404950000e0f18a00e0851030010708056000d03a55241407195100102c0b0b8505424003e4102c03840e401082045814102d0604500801085c00300501092800c01c0c0810b03a94042c2107018034074030f0140d0085251043c41842100d0380c007015201c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30028620 1250 30027370 30027419
    0x3080a020313082505030d0c0f021503040318050604050603040303110c0f060a200c0f0d050301080105070c050d110709060605071b050a060509010c06050708010807050306010e01 78
    0x80c0404440340e070003440140407500042200048800c2d00113542a003d082c44c240ca80342c6460700300000d80b00840e20b00c55400490618140c502e80e141001034500640c540001e43c003002910140f240c00b2201c0000d0b60080d4080c0d501c0703500450700420302030700e80202e070f0003078a0744188103001c100880e2074803100841c0c4c001d2091402242d040d100503072520890b0042102c8052030341040c00070f0303412043c0810a06501486010052003000380c0c5a2603d812860300c0b49074058090300001b4400c00707490042103585c4101c00840300325099603224250007410781d0402e000e503d0842d400c0c10042407159124541c41c3c85184e80100c09020308031200e410685030620051003070702c694020040002181c101e07500c1880001c0206840742d9680d140030b8604007201040072140712a0441d00c101c0d0900890b2a00c07041201551854204a50703035988a2005032074101c10300a00a1915080004000c02250300252690403038420904581d080c580390410191510824000c50760070100500040220039410070102c10092041032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30029870 1250 30028620 30028627
    0x41b030b0f07020328030c030204050609040905030f0d02030f070201090317060d0b040c03030801210b061c0501140705090102030d050c040509010f06020606010c051009080c10091101081003080a0203 87
    0x25191851414031701d020160669210702d400210540600421b007201502d89811803925040070300080f03031401502da080340503d544880100c1041810800c84a110610740001d42e100c0c81c40d100c407a00a13503c12100840340f001c541001ca2103150050140c120300d80c2e4151581130844840f011031008000005068503800094220080042241903030154041c4d401807090300304003811400c3c090460041a40b001d900e0342a95440c54410042c41d4007041082940200d00e403146446040000d901d0328105440020522102104c1c0b9082000540c4018130b08502c00683c1c0c8840c0e683c01005a5450243d80c0303003c1d0141e0000c1040c20080170441d80070342d90040701c0510b40b5003481c0d01c41300405c0006074246c000c0402401124000e1168580400100703912050920f840b03c108440d40e0742d450785402d64508036408042d120880074082112020a8a4a0750002d400310358014048803d15001f901c10083c065882c69240082658a94890420a03210b15040d84e11005690b2455680310259072180c0d841030114002813 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30031120 1250 30029870 30029887
    0x70501050703050345070e0f0c0705030405060c010b03070504060f09020c07030506040318080a0f03110c060d0b01090b040506040b030a02132c01030b0a0f0b03010203090303041b030b0f070203 84
    0x4400076007202e050030907250241080311740d4007442c1c603016800c85807004075102e08100500c84050821640480003401c0300341c440d0881d10300300340b2b1030045801466100602103010380c0c1c031340c005500403074181d01c0490450f0031882e80c0381c0902040fa001ca0150603004030100c1d10910a0036069001480e18040340e9007121350159070f03078807900c1c02c185061717400701d0002ea10194942d40088024030f0200c05410302501801d4005019034400c0c12911020500030300740100c1149403070b01c8072000c1c800c484c640040a05003031f0359134a140000a00400700c0d031080780e01141070004003185071101d00f070a8600391a00500b041e03107070504200075110f090300000c10700701b441c5408003c803003004020342000320020304240340e8420300030700c03000501746c0c0190710008040720403103129004101151990740e4554004011242c0002c403942da490341ca101800ba1044d015805600000178040025800801182304900816041c00020011000c070980d04026100141c68001e0000c007180700c180b1242045900b0200310300443e803802a52 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30032370 1250 30031120 30031201
    0x31603020a050109060203060307060905100e030f060103080408071707030204111b03030f0a0507080a051317030105010201050601050f0d0209010516030201090201030e0304080a080705150108010c020705010507030503 95
    0x201038003103880300c6c0c020080c040c1605081020101030606800e0a0323004509000104003e00c21481020080090515400c45e654909014810206880c079040d90141e41e12800c0041c0302d1303030080c815004d803440784100024504080c1003440d0810039041c00989225403440e000c2002030040070044200d00001008aa1018013150201201d0100c0c5c081c099503d0b0710703001010034454074009200d4080036003130104000b6520703401030780b080d0701c950318203070014168540420720504a050018000c1030100390712600034034160410080c504a8000b64001d0200d940d64030300440700c038001c1042e288024201488098140102500a0101c8880600d452418500a10541900022034081c1a03025075540d019540640d64940610b891490f01d14004500d001d01c1d080042d580c4111912000d441c0040c0444c0e2203080242c01e0020800d0300c032214941441d1561600209402040d0020442000d0b109000c0005510b50054068034062609602c4060550341c0d00c1103004180307015129105190702a5510455041e01c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30033620 1250 30032370 30032381
    0xa0510050324010e011d10051201020310060c120f030209270a060f030b0a020702060c0d080a0501180b010c1509030305090601150521040b0423031603020a0501 70
    0x241c03503980d96400b20001092a684240603008400d01d0b070310702c40041c0310b45507104207032101c0c1c044420314514039940c0700c04d00901c0010580d044143e005546080761426004150040c50013003000342e040c5921940d0702e24003501c0c0032801d80c1c0010440210320745400c403403e008031904203a605c5541009840d00c1c41c20b0000072409550002071132903000245402035001701030000d1140e80840043c03010010305040036134800007003440340700040c003052109000480344603c80e015a10b370550f01400d0652a0181c0c1c00c5255218543c03984c142001580502c0080c0c0306121a000302c504966486404a6140d138161114001800d85411000c0c1440350507034114000424000000b615011070900002d501c850350319005003503860207882c02103c1c0c1c2c00080140b022003043c80450b11410290304041d81e4030300041d120031031070b008240040e0301010315071002c010a00103907400140c4110b00c1449003509081004d0712424001191240d04181c039801070141d032034a42c03200d0315000c964502034012a28400b007aa6201820740b070 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30034870 1250 30033620 30033643
    0x90c0a030c06020609012a020717061602010c0c020d02030a020a0803030115030605090a090f0501050907050405090a051f0905030d020a090b0301031505150d12020c010c0b0a05100503 80
    0xd04100700007035039040c41140c3e0440803000003404841d00c20080004181c0c02406480201c04840c47c0c01a03020b0300802916008014443c1ca84501101020760b0b981c803030004844190100c0d419000640da058418802d0100d400c200780c5683c2080309054081c41880c0c1140030040f80c052181c40035090260383c881e1455401845254020b41e030740d6050030f08690000710405800020304d401c1502c140010760720500100da0220110100048039902410000900018414042c205520301418040d66070400b2401c00f00b51401510103110980324182801d03034800e44120081c100707812911000c86e6881e542c500103d02d0f241e12640c080380e8120140c881d40d046502480010a9281c0d00159803105141c012101c24004e18a400c1468117561440d00c40d143c5c0704901011525600b81c1d201e000503181c01d40140b814040540c05821800c990049140100e24036184080e00070151007054001000d540c80340c20a141c60350b038045038a400580385c100c14a8050100035003420000741c4a150041001e072030411502da00d00 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30035976 1106 30034870 30034883
    0x19031401060b040603020d1a031908190e0901050d0b010902070813090b01080a0203010501050403060b0301021908070f02030a05030411180703060806090604020315090c0a03 76
    0x1090700c0e401074101041d000c5400304000d0380c144d001c0c140001408104200d0207941c8005c6401c5640028002a8140e101c03480a100b03820789032a4012032035118045d10b9007462004110543d036005803d1010000500c1c1441070710b01d074540000154010314003650901c600e40c0b9030380c80e003007070b444014090424441c0d000503141c0d0411107044100c3d208401c840e240b90f560507031141c0d009005054481001c500140c2c1c49404290072404501c02c49040f500c050711400d00d81865680e0f644050140d9650450385554284800c500c0e601051a41c400000b200d036030341d12018030306043d002d4000d4001940480c1154400d0100701e0b1700c1c9800c0740840c4c1d00b264002d8080b141d8031041c4000550f40407000d0091a240081074000e0100c2c0700c0d050341203201072311030300001d54610740c1d21013240704d641e5007088034041c1d03141d401161240791844448110380e070030901400079070b807003a416600440c0b0f04401d0b95000b00c0d8507 = true := by decide +kernel

theorem cover : BRFrame.Cov 29856120 30035976 := by
  have h0 := BRFrame.cov_init 29856120
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 29856120 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 29856120 ≤ n) (h2 : n < 30035976) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
