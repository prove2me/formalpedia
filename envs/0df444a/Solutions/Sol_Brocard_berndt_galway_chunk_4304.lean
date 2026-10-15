-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4304
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:10:58.110741+00:00
-- url     : https://prove2.me/submissions/214c6116-920b-4e12-819f-cca8bab5e23c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773920863 ≤ n < 774100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773922113 1250 773920863 773920871
    0x206030f04031106070c0212060705250c06030207060c17180c090c0a1b02060703030f0212010b271021060602100f090f150209060c01050a0e0a050a0213 67
    0x50f1400c03501d0900100e9030030000a000b411541d0840c14032035045410100004000d2086041284006e844ca00901070490b20b0b15242c101e01910a1508080164060350003a90211540352a0360000340039501003001652005c0c00d0509218605224141c00700c500841207000350a951510030507030941d40d420b940071081a220b07115096030301d9a0341080301d500a403e913851181d80e846034000080d104024101b00412104084401000562a03100413905110ba2510f0005841d108a0107248000e019480d6000c100314003072070000c034440e0302d000020145440c28a818101000026002e01124480b0861542c1c22005010030040702a0154420010f00012003041e090412080018030084507500d601c1100141c1c000c40c82600c22224601c140740c2e400700c010b442840b0b404526100d40c40200001407008020b20014075020030b8000959050b0f410b070500c002c145550f66103482000038080c2c58151140c10920307260001854406100180341003003aa480b401400050141fa000c0003c00c40400d00c014a4254031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773923363 1250 773922113 773922137
    0xe0f0f01080c0403020315060307050d0c03060c0527090606040b0417120d06050913030203031506190203040509010f0513050618010305010509210409020304020402120702100f090206030f0403 84
    0x41440095120351f0315064020003890190101454940103a10641c00380300818102c0e0041000c0b442c1d80f206036500454003103a20300174044111080e114614038019400c140c071812200d01c4012150b003491100741150302d20082d0301c80e1401c02119110300d1081e0003080d0801c01003003050001a607812002e1400c0d541c142c07405245040700301041c44d0b01c550b8480009966641041c0081e14103408050340105410415026078003c07030fa0041d6891102402044071400c01c008402d16560f2400121510401003444002d4014074524010396a90000d004291250346030000100340d003e0103401640031140300410716030414041c40d41500081101901c1302c0d0308250203820f4161a10101480c0600035445140005178a14240b10030a0a1800b10080d2075480b100c00c40c00301c4200b0b599813060b14251180d130040141c0d2078545200140091094415483c58180c0807030410004980214000400340912013051024201101485088034640c28000354850014408181c4440800780b001d6801840f90030b2600d04464 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773924613 1250 773923363 773923369
    0x6010f06020a172118011b03050a0608030d33030305030403020703020d0b15040c082202030604060c0813080712271409090c0d030203190e010e0f0f01080c040302 71
    0x4c0040b408490020f070405021078a10324600f40c4001d4400c2d0802001040000c95004441e0841e401c071a40401d40c4400c04129400c000f40d00c0340300100584000c8a68031013030100d54401400c481c20030700074002103204401442645a019848042c0c03034981c000c1c00c4a60840e64150b4441d00050015011486801d40110050301d03595179a00241c0e0052564600c5032801000c04d00005042c103022078001d50070180c04046441d005032a0740d4205e84100c070350040842c8405501c1c0390488055401070b601d4400c810500c8184952030b0f10003850051103170750701009651400024090541141d4000342040c2d0200488408100e50074001d02c280301700c514105a4403842d4014001400030420907035415014007150400420700c245210300703920a4140c980380858030704008619100c030b5032418014040c1e942d101c02c000400d40300b403003100c56810004844a83e5500714000003040131703180921700c83c0461b100c4907244056103030204c0401801c00300281303801503100c02280110350110020745260075801d0b0601c40480165 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773925863 1250 773924613 773924647
    0x30706021b0307030201060e07050a09030b0603010b04020f0a030e1501030b2d06031915090311030a09060f03050c09040f021c0935131a070506010f06020a17 69
    0xe0196001013401230a1603403441d42100040d1400050201c00c0281d6042c0030703001808102180e070060004080ea5540401107405002d0028902d6803061000500300b010310224009400d82052694040203500122815903541e081800c02107601c50488000410014035800c2030300f036015071058a000c2e000c0116070100514a0030102a0440000e81e81040142600f030402c00304113096208906020304201d06d44540084610808800c0c000c031f030300c40c095181850b0041c9401e0004040c0481102d540d00da02d1200240990940c0c0911000035008022203c0310620a02450303000d420740c141c40d42d1810043e101000020550b100380d10700c4540e002e01034540e60900d02c0c110404051040c4601190348a2507281800d00904400785203400c000303d509214048040c8204000e6919006902e01a038030102c00d2045c185007103c40c1d001ca06d080f8480360003a45c200340e111004d404040d200c0c5040700c51701d03620b480c0340301da0040781d86c02100c00603448181c100000c10340700003c0e030501030500220700c1c0c6001c5500742c83d1034000f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773927113 1250 773925863 773925877
    0x161e020a020a15020622060b1513090507080c09011b02130c0201050a0c020601030b100b0403080a08061f050f0c100e0f12030402090c090405090f0c0a0305030706021b03 74
    0x7030f5540414501041e0180001540041c40e40c41c0300300709200a401200c0084550600600074030380e5400d8801007511802185002416224001500d134a22076215010b090038500480c620941801d0215068501132100940030310384081810b41814040e80044404000301c54082141400c5882811f0150f2078010131025207210030b070408219507500c40c40281c21344801400514600b460948001002075021030210305403544001074130b446840b2051400000c1955400c20700e02510001400000c1040d02d80090038000a180c444100c0c82d502c81042140c0a00c0103d11000450249444601070501c04c00081c04054001401c6904098001590303600d0300c1610a241c4401650f611079041c124030741000b0305240708036008011701c0c0304441e842d008160380c080500001c0c010012640840c46805050007a5030300c19002910030089450228011a92007150001e0f9078807500036500303e20781a0400700c010506403508800210b1401030960b855100a5203d0082e03d51046203800043e01c0720b0000348010100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773928363 1250 773927113 773927129
    0x62802090918190c060f0917060a06060e0a05010503060d0f1109010506030c0a030b061b07030605061816020a02150a0207090b0f150c01060e040605161e020a020a 71
    0x100302c641030300035142c5040e02c1c0340a224010003011400000340101014410388060f880c0500106081c90415601c0090b00d070040c603840505402035400c050700001b036440c442d00307003071109001c055540d9000380c40702c1428000a54009801032400d001e907501a500850300908040c1207022a035026807500310003d12403c104850102c100240c0e82214640700ea08140504411184140f840c2003403020f2620074482d018200c000c2c076490300c0c0c043c50b05507241c509680509980f801044142d00300a8240c0b07490314a00c0c00304980c03592500c0b01140079402d00410401aa041d2202d44041a8444010b500b401e03144441720a011445918515001070329554500701c40841d070342c154130b038660050040190a0940036085855402d14100d845c01c0300d581c1e680c0340004c24038819036021140e500070560b003074424410070700d040ea99582021303400540d04522440d01403003140281410000c40d00c6030001c0e441c82881c14030005002840d000c00d4840b00c45010820301561407c1801203030700f91311803640800e404016940c40b03040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773929613 1250 773928363 773928391
    0x71202040b04140f013203090606040e010b06040302060904200703020c03010b0f090601141308120a021e01020c06042010050a0f03020d06080106060f020628020909 72
    0x4401100b841d241109003c0455681a030140c0c000e0000b440200e80114900a02c10084e0112509540c444291620001e082030126603900e00710390b02a0380c9042c11b80d0428011482d026241100341010b103c0c00710681340c0280040d02d042e180d90208003140e00a220890360141c0d441401e6040e88040c010f00c24411412094030a407120900e00303010741004415080b4500a074101a9015a103a0340d443d000001140100c43c0036080c0d0700c4000040368601d69051040803001e40005880241412983d4010122002c84080301c1d941d000d00e15100c80c00d809801200310241e804208441c00c09403142010b0110704090100040c20030b850007000e1880c181c0c041e1811b03202d119010050047c0d85d0000e0300202e08140c0309486001d441102264018410b06c5102c1d12602000151005a076804e0300c40c0c4c0441e0140e40e00404107104071500e50b5101070091085204200115401c52401050280003103030007442142d900c00000d041c0440c222403000c1d580c611000031401158200710f01281d039a00ca61510f4080d200d0004186 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773930863 1250 773929613 773929619
    0x12011803020d0509030a080d0f0c0918090b0c07170414010e030a0b15032a040c080f06040f0b060d05180c2b0b04051501120218071202040b04 62
    0x19040501090814003000020044ca03e01d5803000205c00698940c08000c003030355202c009005074020490381010003100c90400b41d18502640c0e101c00060150b07903d07000d60403100400080920304450070114000d110b054104002141d0004030030281c40758500500c00f601d242d81201f008003002e64170036002214521242001c4025559000001c040600802d8009180000268036a00396802c801080c2d05c00600c2c6c0c16011500e691418003103402c060000407a40200c0002d50b0000ba03410350380040529010340d161041440ba86403281041c20700404554045007032540301e0300103000241048130ba02070681603c840384944562608030041004158903800081c66081540d0f03e174103080d0003015100065445030320315162aa41c1c46082050300d0007601c8411100e40c0b1401411210100c2405014280d0b1039a0170810080c840081380f004c4640c4900080400c00d603803503c804618402401202170342102c0b2800085a51500c0606016045a2181805640760b883c41c50000180d80c010f420568101e04041010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773932113 1250 773930863 773930867
    0x150a02040f0906050306060d030306080d170606040f17071d04110621040c0504091a16080a0f2a1205251101020304080703020c0f0102030d0b12011803 66
    0x901c0c0030b0107000d076003800603a19010000b42d440c1800b0b00700d02d1140c6280d03140541010b000b903100000070704604d02030324140d100d44035002c0c10140350360840e00343c49003240700016181d00d8110111801c1d01c050136089188a4180aa400001d200c400c1c2c0303941d214403030074070049400b0082c0546450b1248000b262445030f4039042ca0a81ca00c03400c03140486010b04028044ca01019a019000c1c201508081e00b100d403107641e603410b140c80c07090110f5000e01d030000d2500c00964280029186a00522003020040007141c1d00e504000e450b0049542042d1400902d0300030110351405c41c0d40d0407096100c84c6100c0c0205080c150529030080d20010304003034481e021402040c80c10b00390341019025400e01c0e0031000070041c51500508a00f18148170341a680300c00c019851032440424010000342c81000002070085440340307850714040c3c905501490701074002d4415100907010510345503047c1c83c40b421041c0c1c065418140103150620103840c0906401354000f03c64042100881403d00c03030400c0b1960982c014810060440c140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773933363 1250 773932113 773932139
    0xf05010f11030a14040302120a2112020a0e04060e01060f0318080901020a0c0b03061503090c130e0a0b160206010f050d0812090d02010c020307150509150a0204 70
    0x4414495601d041d424822004026200000440d040548034074140310114940c43c0700d107410003548030398100c11840c0d1514000038030800c03003445001f0481102c20682055020b548519240341c00192440c040341840445030b40140507400c9942c113102c0764071208a00010300f9903002d6005000c0d149400c40041060540c856010410281a03013002c100c01c1d18611030081c20a0055003003d0000c0342c0c0080d82843e035074420003080c141950440080040f10351154040101588142c80c46403290014400000c10700035a078003140d0046000303c0c01026842c1547c81484001c00c600c1c00003201c895a00d01d500e4030b419805011021040340700700301d080000c0c64842600184104030881c4942198480e00041c001d56404452420980e0011221000420a280f52130302e000d01c00e4007052008031350300c0e8082c4281000300003040b18002c081a00240001f43c0401ca040f6074038010904050031883d064403242c1a42d4440758003c80c0c0010440301500d0b0b04400d0040700000310f1105a50000d41e4550002d0108901464051 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773934613 1250 773933363 773933387
    0x10201050709050a0b0f0c0f03030907060e22181104060e01030c0603110904020a0e010e04020a0512090a02040507121103070801060324080c0405011d180114010f0501 73
    0x42c0440a141031002280810300b042c06802c005000000380b1800c20780000041d62082c8030040c00700c0d00d4101c1c991803e662203800558102a0314801c01c500070a10b20301402c025510501c014103d50420580e40c101800880c100d4003032142c2e25541c030b4401c451035403c1c6621a00502d40581c44080d018900101484120b5510341e2125050a2003030005000041c0484400800c1394010725001c1034038801d0304c43e0382e042440741e980d41940c824030028100c03010541101d54000341180076224080d00784040030034403091703218044044000803810068405540358031920142c1040841c0c0403039100644590115046800c01c2d41c428020070007400d404c8a040010380103d000c00f04402046170300f0750525910140030310714180140800e00d1b84400150500c0d8402030181400203000d51550704402d50341e0490980c90b840140100d82c021414036002040c21102c902c04180c0380d04146040b0344442e603d200d40013510004c0210540e5165480303040308503005800d0301d05103020f880d60380d0402c000503180034009064564009 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773935863 1250 773934613 773934617
    0x3010b1606060509130b0a06120210030e011503060509070602191712090601080106080a030c2103060609090203060d0b06030703080d020904050f36030d060501030b060c030307030f0b04020313020102010507 90
    0x23100034050141c000c40046c01d56541900e0340f0ad110408070030154064200c12030f006440b903103810b0540340150002e41c4550110b900a07107040142c0e451380c00074285c0b81d64640c0603000260f4468003801922031910340111a10134001c115a54282c50610ba61180c20340c0700ba42030b21498651403050064001c000e1024a0041c400c41d0b000300805441c02c040c252311803481d030501a0510640035040f0040c1b2840703030302d0714180d98070b0920342e1009001441e401134000c14241c000d03400081c1e4a004041841da0941c03088074001ca90080284903244655031750710710071500051403903415010300d400020000e08034030003900070000c661f8005a1200500c10030301045450007800c0d601d51240500c01d0200940c500f000d0003c0ca05610148220300390a540c003003215000c8030a00300c0b030f550300c0002026080e107900c0c0d9210314140c8501b41c0c8e041c0080100001005880d002d40c13001c0c40d03401e800810219901c18026030120402c4400701d4000300c0c144400b600003c00720703042168500107030132410241c2d500b15a420701c00c10358000014 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773937113 1250 773935863 773935871
    0x3110109060c0201030216060f09030f021618150303050904150b0d0b040617010605040c020c1e03010f180c05061e030a02070204020406110c0603010b1606060509130b0a 74
    0x150004220b0407030b09001a040c1a80054032422a854500c1e8422060340c11180078000c216000040350020728000e64150001840024860b410a1011480c0403040034000d603090344c0c00d4182030381d0074100d0301c02a1583d01c441c1e941c1d1482031001c0410541000040d0f01030344400380c4070024034051105649280740c8805a0700d008100601c83c2015180550711a050301c04c2000446189150205004002d640c0050455807000741102c55000c2054000c0340586000361024090170f0000f0030103980d04c18100040f158001403509a03400918500684410f411000500118054009030010f01c2114a0103141c0342d00e5440000f11401480000c181d010010081aa040751502010441441c0300c05220500c000c0c0000000020441a0a882d0140c852a60f00244115907a903600c0350050040c1c20311400e40c00c110f0260603812440d42c0382c07850980f81240c101c41400c81c6018182416511175082481b4100ca01c1507036007501050940b100003850744100e140001c0d1600075407890038441c00200000306240809420 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773938363 1250 773937113 773937119
    0xb090a05070b0a05160201090504050a200f09130b130e0d020c011407021801090917070209070813050706020c040e0115050402030c12070c02041116031b06110403110109 74
    0x4413000301e44107155142d240c1c100c006550b100480d1140801c0d40010742c0182002d00380a48452560700400d90b5151222000c503c403510400319580314058110410103543c1d0034090041e00e0300b40300f140c10f220790024503c002104a50240011000c480107882150026550700345086008420444824104054002800c01d140701e42c000070500300084807029050034000c41c1c1c080854451030a6260020350548020b40340e5038580d541d41008203e40c0c4801c0e6202c2c40c07140c203806001c810440440300055000340c02e01440d9174a00348191651100034044400c4130b40001102030100d1001c1c000d6201618056024000c4101000100015102000078039001c40e403600550004520b82115002c0c1214010b860168595032240210b02c424000c1a0529590000c240100078103075a0290001e1030043c82220304110400744e00c1400d2040b80908450000c50b00c0e01c099030140840d004811241c107944001d40222080c055607511001540c005c407003070400202c4086400c0c01008014604050408402c1c602649054a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773939613 1250 773938363 773938367
    0xf030f170f0109020d0e0111091c170304020a0b0d0501060305070e030303040615050303040b0a0201060b0702030a032d181e06080a020d020406023a080907030b090a05070b0a 76
    0x241c180714001034107500280041c5015040d8102200180c2050001c200e5031210640c0c0307456076440b651030140b10342001000c0310f0700d8002c007a5007c034150f40c11001300c00306002d0180c01c0c9820760303001400a81e4421a80c0000044d200f910034014950040413050205080d4901036024080d00d0011300100d05004a40701c030501a0340b000810b603940070342c00010203e06016040d105080340e8819401c0075415000000d0081101d941c0c0b00000d019040d0550f0080008a80e02c4c0718241da0340c001c213440254190061841100424840c003001710b603400c41d12428085d403441040302c0c0450341810380d8625008c110401c01958a86c102003107800024000d50094800300d10002c80603c0c141b240c640140400d016801020480c42d680c55411784030a59a0014215511525010040c0d592010400464612910100e81000368031306500060004407085107c07003000c1d1907440050712204030050416540e44907040d00000410b9446030501c0c0200303d02c00103000040310700d0408034102643c1d40c01c0840c60745810001e802c0569 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773940863 1250 773939613 773939641
    0xf011b0503060a050d0b0411060a0c0201080603120310061b2127140a05060a0e120102070602090310060608061c060c0e180907050402070c030f030f17 66
    0x500a40380c401c0ea295a030000049001c15581c03c41e80d040030780f1911707100c1041800d00450b0302683c051000380e0b0a0500347d10030130140d48551a111000591804074080042d4012440c0b141c0202c0001c060743c0d00a60605240421500308460001c0081500e238020040d4036001284440146013511980001c0d46030b944840c0c00702403800010b076980c08940c0800140d2184150480d158031501340840d01d900c100e11051a004100d0746008480852101c4818003001c0c0c42d145d0301d4482201c00c040c010608080c0f00081c2510000d254600b80c54100c6901c03031306459100028401041c500e44601030050300c0e408140140340c50002c071024484074181c60005d0510010750000081c0703602000481e6550441c00014034443c200303c402c034400034642d0707080c82c80c85540250442c80b2001044030507220720a6078090000e0111a40c0d00941e81b45d006a0081d03034040c091414550010800d46001c0d4141107040c55483d91081002e9002c80000d6000801000076124450390210943d8501250405410301034100120517910391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773942113 1250 773940863 773940911
    0x402090a140303120708010e0106021518030d020403060606090f120b040809120c0f18010905041a130c0b2104050709060b030f0901050c0313020612180f01 68
    0x2081940482072941e0b8040003100c42005601c1d4811029062856003d0301440007030140885001d81c010001c40c041d0710004a01003e40c00c503403014180b54880c0420711004590701d0707001d2019070108020b1203009418500091001f58411307500015142d1a1510090000480ea041042c4010948104204101035461045905c58218114543d240c0380e81c5040000b41c0700d680005904a045540701070101c0c0c001085088801f0340944c1c43c4002a4502d00800010452511003c0c001c40001801840284101d9024952051082c0030200700b402c0c2500804021100403140f14084441200ca03100400c10503001d004000c100c030440c000e041070150030051000b801680308548140240500040c18441c0130440700004246501c030410495480702036085040d03102303c90045c42d0325840008101e80e40e40c14450907120f194107030051810354481035819820380c0d8008000f40c1e4403900611030451600707080c0655034040e00c182c145480c400342d50340701c4040c108170311b00b12408903076454111502509a45a0000010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773943363 1250 773942113 773942129
    0x20a030b060616060c020c0301020c030d11090a0305030c101a041505120309040b06090108070c06111317010c1215080a050f300a031b021b0402090a 65
    0x186980c1c03603011030040d02034581414683c4140780300810a00031103034405003203644030340e098030910704602084c0f609030720603c00d910340f01d40e1042246100c540c440d9802080004140700d821481c1411a500250310b540142d002514580c2000901c00d03c400d00030028203101803182e16051240c0a140c0f441103150f405d43d04800c6005d19111800300c240000e004143c0400b40000404002d2050b0b01440c0c0c042d5280c01105160740200c0c40c1c41c2c0d00282c649005030540f48400c1c0d05a4803100556180d0b00100c0d00700313040c8001254a1902c9840701c0034180c115402506c03004c1120400c20317251b140b610410543e4040c4c80400303812283d1405194104455110800401301001840d0100c1c003404118a9103400c280103912046141c095889400100306021603001c2441d0000c0e01200c4890f6012019280d07400a1004050410b50745105002d0081000030041c0109160705e040005086000b40036a0381082c10400d007003001a0020b0300c90000030074144044a510540c2a50110b05004034140422440711541c015803074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773944613 1250 773943363 773943383
    0x1e0e06030a0c03060f1a060f0906120108330a0b01020f120318150402100903120909050c091309061104061e03020f190e10170108010603020a03 63
    0x441910200320030081d2aa004025024a559a0610038002c008010000e5211402e0020403600365808045504521a0003070205151030b0149603005000e51012610a4010006014240301c810021000030b00a08005010f407000034400d0340c2c0184000c00b50a20000e40d4001c801882d0a8940202151644090325050025a003808400180c0c0380ca61060700c0d1086a00c0366085800541c1c58020146000303594541e0600c10082040f407901b901c3d002d01294080482001400040c09131908440340e486001d00d03420f040e040c240d1642c4030b0040302102c0b03626800120302184400c21810407035210ba07980c0941c80c504400d06211031040051241036410058000140e2520400c0701813042c0d5074008141d0781c2514012a40c0c07159030b400041c100340d014004850540031904000da01007400307402141e02440c8035550403450800e02e0b00c1c076920156000072801007000003c50842c401921902d41000d1040c0044e20f072541c03400c940c4852a04e41c00c8050300005202e9060507800c000527158285100203890b844400c0329 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773945863 1250 773944613 773944621
    0x150304050c1908030d02040f05100c060f0b0d1a070809150a1407120b0a050a060815040c020115050315060603190f020d0f050c0414040b281e0e 63
    0x18015002d9400c507400f6404000740006506100f0341c01402120140180403c45130b60f00c5081084181a0044d088080381030b003903c0400082c000d61001160440a000c0025090001800f0031000130340f00c00200c034a583c20384144031301d9030960001c0c0c507070103031941c81d141d2100d01d0700c8140300352560f55100780f602c014000d00780480c980000c650401d112000c0000708d94221440e11000040c43c2c640d0048440e10303810302d0000c2d104840c0c2086071041c3e0507641c02a11340940245014421903d9041c01841030320300e10b000440300c8407550307240d0040546558aa03400441e40803503d400003c108401948000e200b507102940c8061320710f41c02c9000c540d0008003111440d840b9558004080b01d81406c8102100005151003090001c0d18641c2d40601001040454100618908500b00c84204c410503039a14520040c144000c010020428882003000d000c06080840c185044501017900441510301046820501d154542205c1003450341e4600103112100e02c40180003000c418132445543d0360b0181c100360705203140c001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773947113 1250 773945863 773945899
    0x405132a170a0b1503091903030b03010e0c0f0303031b03100305010e070f081f0c020a0f0b0f0705040b0d0f092103050105040209010912030e060c0309150304050c 71
    0x10300d00700d4004015255841c50b26425000040c50303454503840c131030340402203102e41e003041c2602a00d00c03600742d01c1c0040080c0812483c41c0342a501180c202241051380ba0401b08405440a000d003694022900b801840c4400d102e20811020045070b254042c000d500c140100844c0b0307614003055420425030f04925640da91201000c0d80341d428230a8001420a40c20704400c070400020004004d811180340e0341c408487e0b1519401119120100750888420f807048542d928034540c10301c2d1b403009996002900494504094580d0f500303005d25102a8140c0f0203101e07003030820001500d0141c034194000200c0c50185e01e05410007042c8a0140030327a0408240655855500c041c44251640c0040c1c442c541054181003242c0250780e000307441402c082c2c202d200090800000280f142800e00076122410016180c003501681070861001101c042e80c0000d40c10800d05541d0842ca5445000040c200d03040c402010b1359070b038003412080c8441c80341c0d20f80203900128800c10401003c101c02248001d80e1000854140c480d11071034090b5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773948363 1250 773947113 773947127
    0x120b0f030f06070e3109120903060b4f090203010b0103051303030e0a170702031b03030f0d060b0403030c0b1f1412030c0304080115061e05040305010606050405132a 72
    0x40c00502c1004187c000c150b000101c400449110b08024400090780700c040c00810044681040a5111985400c800c18513407404403121503845518603078820100203800110b041400c601c0c007559141c2e6415040d007541028001c198081d102828240202e0030890065101600c4c1041d0184c109aa2660510303a00441130104001d0701c0d412600342c010702c00ca54401003803243d10160040b8424030840c500410b48150300d011000c01410000c001c0e5092209412036064254464205a03a40707a50324000400d0b01c00018001d44003860007582c41025441180c6030032140404040c0c805405000c41466115171211111322030800d4900d80709064201200780004291400741c1d045412855020100b528000c10100101801c22114803000074480c0c54584007000500000a0040c2c00002c0c202c0e01110700300e442509401d80c0400340d2803070701030300d040d50f04e450b03040c21108550071010000304002020041860110005402c80700d024000b00044080561120310040708404442c160f60482409402d40c1d40c05141 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773949613 1250 773948363 773948381
    0x11209050607080f060a0e2202030a081e0c03030c07021f031e201e040603020d0b030d0f1404050d0503030105030d0f120b0f030f06070e31 61
    0x104641d2a42885003001d41100720072648070140e4610b03103001401c40e140c003143c1c4004542d000440c1c40847c0d1501801c1c09010301e5101740010404002c2e04034000181c03020441c1d5810b10b4000d004160321008090703034000d0300c1e6190080000c3c06440500c030b00e001046000c8120703900401c481500580d96400c5d0720114030301004000006402e01001440351030380b2909508494150086140403945d07850000c5130305001c035000f420340b4120110001054101d0448510000c10100c60101200c445407042d950040103a9805908038000198011030003011901c02d90142c40c5900c0e00480c042c0000c0421108002c2003014112044020003203441a104cd86c9500d00046501905000c0c025111259081c02c0c203607a264020302c501030182c400c0c2d2000322982c2c1e104002801d84004c1d59910f0000e106061542d40000e429100074243e446028050a034106590800003400207600702000b80c600b915100314068922074403500064040d0200e06202d4a980030340e101d10700109058107180f0712040340380d681e01c0401416100 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773950863 1250 773949613 773949623
    0x203010546172107030507082203060c080f04031715210727021c09050d0801050f060f0c0c0a081b010903020906041d0d180b0414011209 60
    0x1c040c1461507400441e0658008034480c14250f0f0a01100c140c00b0101d00c40c0500280020b1401d10014001509504c0140500701070158015a40e85a0510303030485241d16600449455564403c501d2540781c02800072644190420500b500c10f2170140c401500d100c01c00d0015546620f40c060004511070380d4010781e07c2c41010040d0405441058800201e1044410120314480340d129083c40041d0f07080400301c0d140320810441348541d62040940d00038030080e4000c1050302c1810300c0d94001c600181e00e001d101d07003160b980c060350040c65040d444082c050070841060300540c1c00740203e080350391003d0701d50800301d4080e8000102829513407280c40314098203040560031840e502101c840000104514000b503903906059101c120440c0801c122401940c0d000510302c070080d0480b4091340040c00e1440c2540c0050004511080c0300c5030742c1c80302627403501e05003020640710070081259000c2000310384440d10524000361059050003480c080c10403001004070310080668504103c0040c0001c018070751540c006a008a500c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773952113 1250 773950863 773950889
    0x9030c05010e0703062405240d02040e060901060f0e0a0f06020a0b130201210b0a090515010507020a05090702070b0a080142050403050307060203010546 67
    0x1c1c204503449110604c015a10a03040000049030200c0680e041210500405d5448460510f82800d100c5551482c10000f0101000c114004220a00c0e1034020501d92903005030040e5900d080600601000001518a0740101c00b69401404a1604070040345070030300c0c1c0d90401c040040c100400040e84940a40c01599002c500a80f00050054000a110490b0fa1141050610650306c001000504103803002b0040c2c00a05040d0034a000568140e42640d42102c500d100410114145000300c0e52030311039680008074082c0e43d50200b0140550418050001d18024680396280480680008100c00143e00a10384034400c401c0105480324020411a0010b200e0040d999413554440d030000f810030082403240304010412402a401441126140c00f00081c6021300000704104d0486404e020740707075403080340506001c0100008400300381c0c00c1014002080c4500c0e400741c0e8075810401440351886102c030081d148061101514006080005911107552500c00f00b803020750800c1c02c040c1c01032030401e540409415004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773953363 1250 773952113 773952131
    0x221070203071e0602060f04170d0e1c09050609040c021903050405040c0503250e030304090608010b04090c0b09030a020a03030e10110c01030b030708070b0301060e09011809030c0501 80
    0xc5901d0b4651039000c050703c0910030a5440304260b849202c03c03102c04245220440003e40000c40712100e12119004414905040c0f440b46482c20048498081d40340115a00800c043e000c01c485840d644903800110749092507990f4030340070218583c2d0280540301441140c84600d40d00f030b40ca01c2002404465450302801c80300c5464142805813056025008560080c0d09091010b24030900030350480c0e00410007000c06c1c09062541451501c580d00c510344800041001407440091160307000c1015001601d2140000101a80b0b0b00d42d03c2801c680141d4820350150342480300b00004540d20b14a110104c072428005190355480c280d00081c00c042100b01c0080d8044841d10002c41031540c0589882c94491054030801c400c080074000c155440f28002c50300e000142d1002002515035440780e008800b006c080642150217035900c40705a24105041c1d5005582c030070030040010006a0380c0700b08602c2c07002d602a500350300203504250907054806060502c9103102502d400c1c0b5402014480c0e45050503080e084030081144800c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773954613 1250 773953363 773953379
    0x1a1605160206091c1a0f0606070201020c03030415110c01050f0a02010b130b13050f0a15090e01020913060305060a090f05060411040b01020304050d170706060e0403110105040201022107020307 84
    0x210500c07064461285d01e0406004c0d095040b032501e0300820301e002c00c0450580e100002c1040e99403164070101d0450140c514406040e85003080074001070b0449000041d110f0507a05402800d040d151015401c0c60703030203100c0e10811a60040211813031117451014943c3c0c0c5519031001a8094801c1c1c48507185c004a0f601ca1f040880840e50f4806411134108849000e80c454094980ca000d589060f188610306c2c050400108411804551082d03007400d81c56406501150787d204071403001c0b01e010014219503a500040c0c800140c0c5404c001d2003001c4c802284040041c03608644a460381d802c802005082126607480d1028103106584841d14000ca034890200c500038985454a10350140704845610f010710f08008081600c0d40c0080161001e8641c042c0045213a240c09403a04000c610b03c01c3c40604030300c103041101c40c02084090003520081c207608401c1a50b28146454000e25844482c0842259079141c5414840141c0e404100858100c2e15221590200d800e000300300c0c40c691141d580d009503d480307018000220385c5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773955863 1250 773954613 773954659
    0xf06061302030702070e07092d17010f1a0306010e0f0c1c09060c02060705120a33061202190c020a0909030201060e01090212041713031a160516020609 66
    0x724850101c274094904965140c40d400f807000c3c00904c2032901281c05001c440e081183c498060b681c00c40011a4000142c0d4482045415104140b40400d02d105e003e16154201005110700500c0f60b110400701e5845d2080101408103006002e01044500000f00b140405021010f4082d00c0d8640d95001c210810b030340d1078000000c00c4200115000f6010342c000054505010314103031600d42c0c1d102e40b4000095528820560000d2503801d895100a400c011420041d181024403080c8145005119140c1d0050030028041c1000011681028603d8010000c01000e04640d240c07803145c1200781d041072803843c011840040c2c0c610a2581201c8086868a07a1003021f16505401c03d204403021603806042c16600c07968010141c0c860305602d40701c4a0410743c046030005044000a000c0d8842120025090180c41a000031a0744c00d15842510488140500e15007039500004140b50010440203001108840040d0040c0543c0905c070401c0941e6613483c186881503440c0c403012a00c040c0e40090140d04c01d6030a81c001d4205e04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773957113 1250 773955863 773955869
    0x30c0d0501060e030c010c1a0c0301060206061f08040c08061f1a0909071206120201020c011701060c020102012301031703060f0603040f050a060506030f06061302030702070e0709 78
    0x16a09150000402c54002d0781d08200081024000d010510b014200548444803014401c480300301c14915039400341c4408450160060440c820380e540d5a525116009240202c0901024841d080d542019a941400104801d010314071a0400d0b214695640c204282d81c80e001c1d91140902d0301030f41e000c000036131a80b1001c0c01410001184065020360f01c644900b000b0b81150240c0f902265800c10900109242241900f540b003003180c81c01c103a400321182164000d44580354081f01d821400740c2080c004568041c40360340f1607140c0a18005090b24078114010400715010704ca04000c1c058900e196a00f90b901c00e400c8107800000b550032030aa4040d952120031480107003444161041c41140d15104440d54241c0100c0340200700042c07015041140032010081a0b510180080341d44001c18841d00c0d00080090000100303403030060000003507510307089007814104008a00c0d84025504043c0030061103585100c0025038400d4607000060720799543c940140c0c034082c081d4002056030322400c030400825992086080080e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773958363 1250 773957113 773957137
    0x30316050309120c131d070b071707020d02010e031e0c012015060f0405070216170307060f0e07030b0403140301061e0e1c02030601080a05031c0b06030c 67
    0x603d42e403081007030b0700d1314692400700364050840c8019a05481d2903130410000680002c107201a0a0f4240255503c1e0401c01e500c1202c842c0702c0410382e0b0062082d50403c50003c960041182c03403900956500203451912003081c024180318914424807441c0c2c900300541d2007015008040c2c10001207608040791b554007410300e142070000320591042c040c8a40305050503c01408802c0083c00c03030340d4604a841a403010000c10b540c3c3c10400302e42c08012141d650380a0705018401131f8000d00400714007503840190b9000e103078101d000860180401b043c02c0c80b9000046401c20381e0051000103105141030b0752003010340743c03107501d41840e446016408424459103421080c0501d101e910354425141d1858000c0c006030000344603800102d4044011141049070343d254001e40d0301600e1429080c0d46445000180143c0c0d00040102d503490382e440c07624000c60804101d800e0141008a00610070700003140c4d80c3d15030b07a12803400d20442043e9011100e200300d0007650092210031100078416602c80c900347c60550407039000706610f040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773959613 1250 773958363 773958379
    0x320040f090b01020715020c1e041d07090b0409242a050c0a080d0207050c060705070b1b010603080c010b0d02010206060105070c0e160f03020405011d030316050309 72
    0x501c0310561094020244040e00902a900d28040d01580b926110b035090b01c05601540540050b61b507a806a02020321044e180703410303000b40300541403104075070ac0c00342e00729003000a50101212901c00040c0c98001c50b00f00400100d2101d4010f80070070b0203440080001406805c2d0b00c10581c516804e100b000021101039010100046222540748a80c100404549a5018100c04401e907006a205070000c103100314200c821560f4044040d91081651b90050440800356540440e0302420010103102d1100107803c125102c9040c81c200d600c42589801c141d11800783c02e40000184401007040c041940450002c4600080025541da401c00b400107900c03042901c2865441c20115107002d00d4418846820250103a0060074640d84d444010f40d0145d102801c140d54201d102100003910000c0044494401c44d1030154001c01d401046802a040c1c4007206c41132000d06005010500a590384690302c02c0c1c1810705568035244000d01c40740400c0c154458444a1031046c0000d4044500340180080148101c820541d2044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773960863 1250 773959613 773959619
    0xc0c06040b0405181e0601030207151a0607050d051605011401090509010903090509270f1218100306030b040f2d140c03100c080c0a05090405070320040f 67
    0x20b1030900102c85c200071012943c000c006142c2c45058199a1040301070500500e02040c40d01e4081030b000203200c051181903103d0503500314954040300c24040b240380540e031490401e842551030f1034649078100910400c00c04049070101d51146004060180035820000812140d42502c9c0034443d401802d0080b60040d42c01c0601082c0c07001014807442003c0364259a03948101b500300010801100c20250031a109c10004040552000c82c02030400c00c040d520402c0104440f080768061a410704c07810301001201c8400c244424030b082c44100c04403070380f000d20466000c4339005c03000d18154003d041c0c0750400340c01041e03448100800c0041c103044980c411400f51941007800c074002600704840090204810b500c1d0031741740382030b170000800300030340c2120102682059410016589010a2030512811325101080361510f50f00350640f80c1110350b007500706103d42c5c54103151407a18140a041c0303118007001c20740190390342c0001410252090340702c03182810260b01c5101c007c21100001c11042e0b0050b02038a481101d001d4800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773962113 1250 773960863 773960899
    0x1e0210050603191b050a14040b280e06090106020607261906150e010c11150a0906091208070c0812070309050904020a0b0d020405041805011805030d020c0c06040b0405 73
    0x901180d8100c01c8a01c01d00502009000190144035849070700071240c01682b0388030881790b08d109200e1542c581246801d0616001000017030302400b60005008400090047c401c0c4c2d980426602c0d8172280b40d04103915403042c041802c40340c4802500551100500c140d040c40302c5802101c0800c0c0320703c0b80007401409100e8441d003c1b650300304654645103022410034449510154000c0c0c03101a0382e507005107c400700911600c000306203082440e5240c140315103000a141d0341c2403508445010050002840c20360825410445211550100b091019090b81320100d454420014804046005451490180c5070504003229100003550480c80045011a00402c800300c0c43d818140600761081e5001002c0070304140c6083d1000ca4194800184907640d141c0800c00030840707403914021084030a5803000e44c010705d00b4a600b482402c4903040e001c1d0300702006800004c400451400016078290f59444400140e4132120140d0720380c5009201601245c11150214001a59141c048080d1045690668540c00f22907001010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773963363 1250 773962113 773962129
    0x41518091409151b120109051008061003030c02130e03031e10090209060d05040807170307080f0a0b0a0305070812341407061e0210050603191b05 64
    0x600d003c500319a0000b480c1c000c45901c11031101c4844002540c6001c07200364400c42541c0098205034031300c0b915074040c011003039100f2041c1002400058064440307420500040050b00080d0300c000340070080c06112110039581c4403030285587d80301071582042445c600c81c4019869800455526280c0020150510300007009211110310441c4103501c122002800d04080000a4200c032a0071a0000760078403455200e103a051180c5409140150f00e17107502c1c4d2103a45810500e02d8600b4500c039140a03030034004e201009030440c01440d08a00010144030190f43c80300f50942c001d0031502e50450340450334440c00400d00001050200135650541c1c00d890081e01105e0300724100e481142000a0b4000001c1c10110125062401081d840074180c0d03c441019017094031b401030f4846407140e140102c3c2e0030206c006c020064020000848c500d60f07880c000c4032010403400c0081d48401c10701c034614008544550005405c0d13503080c005182e0803860700488001e00e29683c1418420600c5c4003010756212a1004004510352a040003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773964613 1250 773963363 773963383
    0x180109020307050616080a09240f080619180b0910031506051f02010b09070c1e050f03070c051903060e0a06020a020a060f02090303041518091409 64
    0x9191692a102c1448480e5011031099169103440d40410390001b0204402026101215030750450303c07500b82820743d00703800340402d040606640035000005605810102c5e030440c1c1040c42c1001000b0340d90703c1c1e010604184805207444800300b444000440c15003c460518244001d0590302000760700800b5080c4400c14006407621028102200010000a121010741880c075000c10000490303c0e0707641d4000b00344680405040c420b000c050500105100941c24410104005d00488660215042000c00a401c084000d0000341c020000c0c0c0b42403440d0049659039903c9055804400c50701c1d031300b554000c03082e2650421501221a90204040000c2034907102c0401190701d2840300c28541c00030b1540d61994000c003d80c1c0e02c041c0041c0954824000410a244081c00100c100ca401030300c0302c0c1c005031410360f0440700c0ad280201031417071061004809075140001a2800d80320b00350b50a21281c0c0340c003881034900d901c8a4011110503068520041350884868000300041c1004180303002c507a44440c1201c50726800400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773965863 1250 773964613 773964619
    0xb01022b1d0d020d1109010303090806070315051c0f0602041e03020102100c17010305010e0c0909071707030c0b122d130206120f060d1109060f060705010518010902 72
    0x400c032000361070070301c500e00c0740a4400c0d5222031061581802042d040e00c808d9000f1b134007081c6041030810154800b402a29449034040c9400c000403041e4101c410220341072805218007801059641d204a4000d141c03200104540105402d02682c2c51884c00201a40c028000c0710603071840480e1907006000c00400da0403d40358142c018040010119170000028010030384000c0402919100100c51040c01c0409c00c1d020350f00840000c982c0c9112030211500e002c11307140c0400d00600c0944108a001030010414000350b8407421a903143c010100c101040c60031005400241c02251000c900041c80224140201805140808052000e42c0c6400040c0c03440c000c010000d1084100721408a078031110359440302c680c02003504d80200b0701903c194004c18810740088100844081c40f8001344201500800d02456200300c048500f4100e4688503966850050581b038030041c02524141c02103000d550700c084011480d49005000f0503119052401c025000e0b240980d510101e50100124060f245001806402c20b2141c004d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773967113 1250 773965863 773965879
    0x10303080615030712061502030415050405100914040908090d0c090f090203071e0e070201180b0402040b0a050612130f050d09080703030e040b01022b1d 67
    0x6450a8408150080030164080d602c9540300c0412481040034600a2a2070f076141101601c807040020100c0d0f00d61b400481c49130390000a1642c0b010b50000460342540c40d01a08104041820320381603840c0c3c01203811195010704028110380c00c0c50f03400741c0304104480345603000c00c0400920300103100c1101d10014024158010800801c80b0505040c4500c0c00c0040c8100a01580c1995031000201201c0441a412540b00e440c2c0794400c040d4075003007000340054810554074002d5150301100d00f0024003071900c03031450f003103401340300081c400c0703000b9800110840251104540ea9808500c0c0010b0302500c00c8408901c82c501c1c0c01c4000e03045050905c6001c0640f60050007552500050301d0120f02403002c000c5c1400781d90000b518211002881c0e100e15000c4c1d07144100020086040807040252103105aa00014556800800208042517003c2c0501c084002d054038009556281f800040303003400fa03c580d05903c0444103c00c0f0100c0c6824401807024402c0850b980e9103410001458040d501c2840c00f6501076002c901 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773968363 1250 773967113 773967119
    0xc0509040b01092601060b0405211603151527060306241406030103030c080c01110406030c020102180910090e07230916171303021c0801 60
    0x42980a4034045078141890b061a075518484004140214204400d00800c0826081401c00c0240201c6000d00f604070f601504041c249401705040c44208a0548081c03104280000441c1d481441644210800c1e00d8180f030342d583c0c0303d06249a690070f010403203a001070300d003c80325403a8001803a203076004d840c40e0004491000c20b103054404000403c600307401d082c8075500c0c0c80003c001072184c890130081d0406d8900001010403081441c01c4040c0d6075a111454403294851103c8240c1c0d281801c80e419242d05041424240f142400c203d001c80c024a01100307034039882c01c2039605409540c100a00112070342030754203003c0700142c094100c0c240c3c01501d541e513a600401400c5426503207001e1b6046a840320741e080040c02955520182901035440c0700e4400005504904810f0150445000901000a0b42400d04070302c810603820103d848850010060403002c08a03100c0f814110784281c08034180408442c90201186c20030b9250310354aa07036041e81c11800752041344050f4111480011401c410200540c40e5038550f40c0c030b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773969613 1250 773968363 773968369
    0x123101502100501080d11120f0304081606060f050307030203030d0e0a0503040609031208010509040b04020f060403060506030709090302030f1c020f09090a060b0417280302060a0c0509 81
    0x281450400c194002d60000248601d0248075441c02483c82030010305800407042401b0b040c002d92038003141d406070441c10400004659481c01c981074000c0315420540e484e966810900e915004062500c40c9036040c440c21402480f0003908983c06541c1c1c1c020300a00d040c2e0769101007658a14541c44000d41580050041300d09071242613011040008254003074070700c0d0800d06d1740d4071815940a0f40041c4080b0303400940c10300a014001003c41022a85428180740950500c40000c100c10300042c001400c1c080d0380c400040464503512000e920080000e404942c86544901e40300003c0c000440b815402803040705000200c046040c014040740c2c0d0b82503000343d031070078040d41000740541c3e100042291040020421401403407041d0701c003c01c800f0142c1c4a80c0d0340c1355034108003040301c3d8040c0604203011703560815409000071800c41c01240c9c101d4a00303a58680041030051030b80360901c11606155890050321100740514140380319112890148245e00703035011036403407a91240448560a844400003030061144020b182 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773970863 1250 773969613 773969639
    0xf06031002180307060215010504020313060b04150906030201021b241c1b14090607020f0a120b1e0105060706020705010c090501090f0e040305131205012310 69
    0x1d0401c00c8208002d01041001c40d1906510b43c0c042e6006a0040955070179510728442d442d4054a02140c0039440c40c10b01c001801b0182615013000b80c00140d440a41078030640d2144d0100c0840c1808401600000c2eaa8820700002803015200580c09800344004d010380b1040c1d10a08100006402031982115840040250303116903c1d40c5901c4010032810070128849016101a198840400000108102600954080c04e14100311a01802c1c0a1048580d11760700c001e0409a6078400d00031790301e007a10343c0038500019540c400124591a0441c80d140b4001c1145000d80000ca28010b0081e42d00924036100d0710324504d1159502c05c1ca0900702d6000350010320807031801b00c006251943c000c10016043c2641510f88030301315440c030000b0300b0201b01107000401241d43c000985038010100d4046085002d07142c21803000045000030401003c0100016082d00f40b101c9085403070018205807880200340400603d8030a000b05031a00360541da0003600e10b501110f40c9041514903110307190100e0b02d490a280b03006000107000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773972113 1250 773970863 773970877
    0x1061a040308071415060f030c0109033509010201060e090c01052110050307050301020a080a09050109080f09010e040e0a030f030b041401031506050d1b0e07030509060f06031002 78
    0x8030307120600c40030403100f04000103c02149a000712204c2c506020080245140c081c0c1f013107500075040250b40f071901d40e8101c1304c00c504403500410840ea20b101020030002d0321200c110401c08803a02c41406031801642c3c0e12010f8915000300703030000c004d481c0d00e501c45a60701c060116441107041d4445484841554421000b51000c607802034828400003040c0c80b4030491408044a2400d039604448404200ca8541008602c00500d42034000318075140103180e00800000f401885848602c0c0c0b20f03505101002001d61207203500540200c1c2142c1c58940e400784214042d13200001003030004128002c000030720301c0d0a101e21040c01d91450700501c500d41ca1941c0642c0e0400302004840c0c00d150b0384001c0e100c3c131610346020321f445c03649801c2c49040082d03045142146071208502c0650b410b0502d059018403280e100e0f9000c0601c059000096442c04203544000030f60740d014290000000314510310180210543c25400050040315800309440745540e908001d4001004d04594684d0b1540c4904044415209698020004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773973363 1250 773972113 773972123
    0x60e0304030807120302070c1211090c0703080402030708071706060411120402040b120109050111070f0312060810060510140f0f070c0305060f100e0403050c031b0d0201061a04030807 80
    0x81c200c00c6e0301e030402030700b0459100c8510294200c89c8a410445540360380c07656a02c08482c03c1100341000880d05000b0300404034014144080d280104055580c01c11030305000740800007c6450060b164510302c0d91200118041d45150b02c1503c000c00d540b850980280010340d548414040c0c20103808201c6841048000b0740140d03041950f416040c10b0075115110355240c001c07030350b00011500c103403941b41441c00c44403130016103040f1540130f200400003d1181b1400001883e09407900e40e150038504882c1100410250340101214800d190700c0383c10a0005420050403101d04a40e0039141420720790090f01d8002503034951700940d40c030820032012404460005403003110f140e01c2c2910b04245c002e507907a81c05c00031160402d4841c0da001d4400c000080c503148445d01d90140624007005c0000c0d20708101034a43c500050401414450082140b110000080050b00c940b800c00c4850208503191900c28162110000200b0344015420410046405080d6401c84007100340d844d840756181900c0c5445500f2150050344080b90 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773974613 1250 773973363 773973367
    0x20312070f030b12010516090803040302041d0307110a05011e18050a030f0b01050d0c06030f2403050607180308070204140a0f06050904050618160b07060e0304030807120302 76
    0x20350341d26441031380b4090198080001805007449a10f40900c01c00c800b215030100104008188213081c0040203035000c50358180d03400b04c2c5225504202e8201450b034611202c0c401d100100d0090706204001c112541d041800396000016691100f00445078200102c041d6a0034803460003034071060612410001900700d80d800b04020a107602e9000140100910703610945a4413800c0050340e05001c800c5404500400c011142c81903240301c10754994522018a200c3cac2000d0540d00e0003100e04081c025002031410f5040c024102901d210210a940e000700c0c0030340400c0c0c4040c4505000100b40d0f9000e00c100c40b0a0060502071414a240347d80e40b005160f500044080783c201351203004061551585100d424041c0808071401b20f100101c4445030b0088440c4c0d81d000b640b049014105020200350042450342c4c104161089036110241401850b40c5450400039805442d140006e40014500c007002015100591040d00180209420100703041d50704d004901000d00222010880400022141c2c1c0d4030500c038054504000d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773975863 1250 773974613 773974631
    0x804021012090b160c020d1b09020703080405010b03030405151605070e070210020909010501030e01110a0c030e0301050402150c1006150305100303080c090a0b0d0219020312070f03 79
    0x106444001c401151000003100500c0b0190b288084211018081464817003a40c0e5941d80000e6003140610700013070088120100c01c0a00c07200b200310054064158020195501d0b0b6481c600140140c2045800769455403034110100420f14021040b1411030b64010103841651242c2540c004166201012104242200800b0720700003070301c1070100c000101140018071000749060240039007800d54040442c804684100507145041e5218000300d810344200f803a0001c1d2061a4014041c014442215804285d0f070700412100c210f0369008207120180761180c0d484444618481c0141400c5c2e85041e10025404042d580495004082d0705010703040c10703821803003241c4c120b0001007018400c076103464003c2c02c410000a13034803000007509402241d4000608a4010340b00c2869601e005000c030f90701406004c4e2924000910f03840c26501c584981000d00b090701101940c5004c482c48800095000d2410032404070384000707001c001180088280c6014407080e003030b18006642ca1180807600314040e9150b8400349070b9210144 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773977113 1250 773975863 773975897
    0x15030c090f091b06080f040305030703051302151e0309120f07140a060509030c100b0f04020d050103120f020307060b0d080a030524010c021002070e0c0304060605040b0108040210 78
    0x20b01c640d14541c4080c403c09041204c0104201002440721400759600800d1200003540042101d41c441100c1c03400044640340c800c81c075a003140e810100694800c1104454810814083e0300912030b0b03103101840c404100c413503048508036501088440d00f00c43d0304030b098800c80c0091301c40700a100340a80ca4000900e800700c2640c8990030804208951505584045100c1c410880a4070407960000c403404011400c102c00070340d00c039039a46502c3c000041017a88039980c0e040103455500c203501000c00020001d6481e400205e4020000f84003d1009072981d0307901110b241075030b074000c80b103034400390040f0b034091490308040b0f4403180007030f1900321055134101e82d81c9018200072440c98009441c000740c4079503000c03925050140d04443e18101440400e02502c0640f0070b04075441c3c1e00f0910b14000e0a5056685650b4030f2040c0d40300fa8104112948130340711000748007003000404000c0c6c00c0118842d0744182800c04c583c5444400380422a2404980c05010850090115001d803418200702000c1790082d2520545440c01c01441c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773978363 1250 773977113 773977133
    0xb010f02011515110f010c0f0327050717010207021504050a090911060f0a08010503061611032a010c030207030801030b0402120316020103050c0906040b0f040b0f0c0115030c090f09 79
    0x10743d4459540b0b01804146a034004d145186841d01327441c003070141c0ca0000042c0d40103401c00c40c00e42a449180081c1030001c01c01c05100d030200074030354901d40c1085201d074504524040c1d404040e04030300c1365100d0220600312185a006482c240d5501401085c2c02c14127142031100240740c0e8500640b14201180c032400056038440e0014010390707800200c01c580b6046d4260000c0c042c0041a04070b40d01c00e80007002040410844007104400a14162a00f50f140180c90a0010305612450013284404800b01c2802154000051040c603800b0a61030020012220220340480481c042c080c0d00a000840c2c0303000400201d0040d4101a822038001443c00b040d840040050a140d60700004031220395041004040c0c041d5a00740c4142e0341d102081c040c48600e0403100710001402c0f0f20845c00f40a600900200d000f600d985110401d6501078420111a29900d1500c41c9500c3d959400082070b5881c2c80d030801c0c480021683c845040b00003280c0d44070240d46007040c01c065064020302155000a82c10599032020f000c0810342c5608 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773979613 1250 773978363 773978383
    0xe010308040302130618020702120703080919050d080d1e0f0e070308070f1e0507140f0f1002151503010e0a0308060d030c0204020d0b010f0201151511 66
    0x4041e68440c9944184200395a0031041c9440080c90300c00100f040c00103445070480c02c81200040140e88d42c80c03910000d48030186e1102040d100c2d200b49a408400c220010000b06840041122141d0681208100c02411103482d0700425400c0040c40f6911000549444054192009000303408660750013a1b03403100c0c940e100d2070f0407041810741d05c507201920112020711410350102641e40140c4240e600310784a00840c0c0c031541a00601c40c2440103c40d0051001d904a50600c0c902800071b116000485424400d45e500d10902503c200311007581c4445001d4500f83d030888a81600140c04158603004039020041c01624000c688401e40c0203880207503044461038000c15110342c2803200504619100c8dc014107013164150f50614006600003400341001c030b41c000079078540c0840200c0b0390106090151404460103800120002d421900101d13015142c142e440c0c02c100400e403001e81e80c16007595030742e09089081c2e401c505a80510503200380d10174098a805000789280082103400d00d0310b1502483c003101841e00e10f40e49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773980863 1250 773979613 773979623
    0x32d2909061015080c07020f0a06020f060f01060c03080a0b03030412050d21090804270b100c0303051b0c06011e0e01061b0506093306100302040e0103 66
    0x3404020b2101407a600d03040c080c140c030110031003203d111600301a00d40071000d02407003007400000c141d2400f1540c4010300c0403500c8001500f2644025501c0b48069910720181003d44801e02566000078950303e64594001e0407140b0541d40c00302c00002c6a101524000c001030000d02c1916107a54034008d01c0d8404000500c0140400700c0448c400a1450501c20309000345160b05000b000a20200403001c824290003c5017814248040003d046408d490098030701c3c8540c0d8001c0701c0c566542030b038284000460001c14000302e071002c035080c4554071600081000a480340769101000c10403121081000c28440c0d0300c066400800181404c050282e106000d1525410441e20180c1aa0000c0018410111a2030810202d0040000400046410002c51072010b090501815080160030040c0c51074424070040d440c2d1405420800762012410000040ca40396004216207801c030343c50010f0f0380c01d0285d540c10508485001c60512041050301c4603001c000c80c2c00507152000c0205502403102083c036000f50071100340214414 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773982113 1250 773980863 773980873
    0x9100c020a21031d01050415030e0d0903110a0503030a0e030109150606020714060a03090302162c0f16020f03031014061201051005040f0f032d2909 65
    0x30f02e00141105041500b440840f191008074218590300301041e1805d0b10b0351840a05107075801e01100310020111800d5581c681d01c81c40c1252401950001d420b14103407030080d109114013010010a000b01c1054500c00e030b40d0942e00030080d003403d07284910401140741c44024004290090f42e07454800e291100d400200407103580d148410040203404224060042000654070150390752080c00241c15401000c270240c0501d61038807021000c0510a000010541c00101c13180304401d41c0b07030425449002501c804c111a00e8000c04460000c2c0b20981c448103220341d501d82c42040c5155210302c0c80182c158182d0324041c00b50f203e030302100130604000f0301c05903104041c00d24150610f9485c6c080301003c100e41440c1041c0c018130307041003922901c1d540165041c0c19903400340d40d03101e00340c0c2040c40300312800d11640d8444101c1d01c9132100085081c100b11070100b41140d0003100c00302c0d082007000b2400b030200303c000602c0303a0001400142d1b1000091015017403d4420000885480c5c840c0312421a40002c00402c5498032410707080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773983363 1250 773982113 773982179
    0xc17130305010203070f0804030906080717040f1203090803040611041802030703050c040503032b06030b0402090c090603010e04030e09010e0403021e0c13020412050304090e0309100c020a 82
    0x2004281b011008164a03010595040c0380d2000b420740c602078080c890030407203000001981140203000c07010002c01c00304140744c2c2d0307840c15060250190f0302c080800c6545003060120110541d1090282010300f5820500051840e00c0e1943da8000501c2588003003045441c0520000414200f2003103141202c010707283c3d000d0313a00c0c585400010704488006214002d003a45c03d010a01003034500100307590710420145124603050302d1103450341200d10817003080799040a00340b21001c010020018100f0303002d203100780c412104680390f540f0594a01e0040c680314940005051004000b00d501d00d0b040a501f060003130601c0c161042c4404007040c451403090b00a1b8100c002c04606020425a04001400341d45800b000c00e11030502440e81c080d0f84408080003c5445075480d001514098405581254000c0490264586030030406240c0a0389a030410b10481d4a26807916003a1072210001004680d03510b20001d028840450500605482125a10078142e0b082891400081018001e4111074410303404103c041c080740c2d4003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773984613 1250 773983363 773983367
    0x5090d180e101a160b0a060b030106030f1b1b060b041b081302060301060e030c120c0a2304020a0c020d200a3803070f0f0f0c1713030501020307 63
    0x1d01c1c5581a80e03401d0f402c02c01c1d0810364988a40070303e0350960040a05400b81c646c6580d040140104c0d40001020358000000010080e130968408400d0555024080c001d06031810488082480d10032135072004103148190464002d00034401400715540b1610b03001591142c0c00b00031800315444600d00d005098980c1c43e12070231050304003140c5030f8086000c3c0c805910006160b40171503490f00041c8500400d02002d9000e003000396a0601808507078280180c22003543c1201861019a10841c1c01001c3d030003506038a40c0490820344000e00031005a02d104ca030311300d50b0210003051000942c041c28007401040b100302c0300c0f1001a40d4500b01124035501640c245d41960340342c644102d2070056010000c0344144991041003000e110002d14690381c419098810449052070340156004413600da08010f21074040000c10070034002e801510300000c01c0015030710030110f40e05e9034109403611880c0c3c15400020600c0700c040b54000401c4111282c181100b00c510642c100b11300d80341c1c003454041c21034004a40303d075004001c00c003031b4035 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773985863 1250 773984613 773984639
    0x203070201120209010c0206030a0603060f14091218040209040f051f080a140a02030303070f02060c030f0f07020309040c2001051b0a020a022e020105090d180e10 71
    0x10500b95411441c011410740041d001c407121460090040e8004000a840c010080d40704000954004809012010617a90f4030401021201c6814020071082d502080b1410f80000d5120702c40308142d0003080ca002d4158100040085100346900d510903001c000c000804e0700c0e10300a0044440b035905001c2441d0a005058192030102e5882c2da90643c503440008020000e0001011a0341d40e41184401101003080c484103030400520f01000f80d0988000401c1c00704c0141e100400d00c85200e0158240c45440e10f62903015000c038030041c1c819082101019002c5059600c0c8411010382214181c01164640a05c0340e0206003951008440480403403c1290080300307040407403100c0300e181c080c0d800003089680341c10500d0501c0704091004030140032802041c00c8070418000c10081510f0b5070020402d400d00010f4250700100c45121400392415008040c4000da540d42c014012070703000e000454050050340000780f404441801013480700079450404140005034103114440564040c2221000e4040c1c828181502e4000b45 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773987113 1250 773985863 773985887
    0x9022205011514251b0503010c050301091e060801060e18030a120e03132408010b071a0c1306020307030207121b06110d02160506030405030f0a0203070201 68
    0x203941c50a660070b0503511040c80b1a52808040c506070f00c2d001d24035416078001d514040c0c00303a0310444492500302402044213120f24142e0403410f05104080d00c400c181400d0f111460fa511000c21002e000600c10040c50750000b00f11404078100c0c801c120b1060341105d40507240e050b0322440c0315964078241807050300d00300342c40140d12540896140126941000d41c441e501c1c41210885401c02c00745500038841185a034000722065465881142d0301c3e1008124010b060f020356108403500001503030313041c1c90203504500a0f480c1300f070f0160b1507a000607031070030b07881e13251941c40700d0310889490001d49a0b42c8405408d820b85103000f86c0c0724581c0075803514290400a00170440941001b0f06645c0280105030000f540010f0302c800b0b0725040040383d14416a90b180000007e210340d480e144140c07030043c4021603066800340b15081080c050000f142d58840d504c3d40b042e43c413011440c00c00c0e101001b0b292020700c2182480c800451b0800d00c124112890070615148035800f540255200e6401600b0024140b400d641e8411014141 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773988363 1250 773987113 773987129
    0xa06031523030d2a02090103080f19090f060c110108060319140c120706050d090f030f030506041a06031f0f180c0804020409080c16080d0f0c03080a0902220501 70
    0x4c1e00996000242c52510500c00108498000a00c00041d01d46a000396902c442c084444018000321040000e010400c1074000c882c02c00010200019030281b003540703144440c9410004854200b40320200444151900030304103501072040f81034040c916048a8080343c1e0640c0294030400281454140c913a00302011407061520824070079132104600100440c1c0c1e80100e4041d82800b030790711034005032440040c02001c03902810301e0691090300b405258102d42d4030140f44415079400c12440e83c802c8200401c0b5100001c00c0580b10b96020601c140a0a0607802540c0003000c00d06400c41c44414289040b074402c0084e080091070b6007520300108581040743e442010311025049061241da0000d4000801c20080188060312880d2901a1700040c00502c00c210741d80c0301c2c0400142c54440203440510300b0b80304000d1141150310301c29081b001005034464283e000c0704440703d540300f00503c8020b44007101c40b11f00c01f410031450340d0703690703410100140e41301c29401c0c400b488002e0b55a02e10080c5040c2800444105901c6424 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773989613 1250 773988363 773988437
    0x5090702030a031a04050106050901030e070602282405060906151e0d061806050315090c041b1101090b06130204090c0207050a06031523030d 62
    0x15416008010ba030440410b503e000140e002d252000c89440021802d40150410302d041c0c00405c11030751020041c40140c0702030b03c2c103000c0040c04080c2c0c642d8400701e0744036040051300681d04030416000003413104e0000306108142884030001646824a0702004404100040400c0c0d103412581c18003540592980402c0803660741d082032900102003400d051040034004449000041c40441100f4580420220b607c1c000f00c0c1ca940b50321032683d0b000002c01d2a40907240d580a280310070807844a0582c0a14002d59401030007074004200c08103010381d1341c030b000541408400d001782881c2d050300f91034070701c80c605a800119040c440310580d6004050465480e002803844244d04112a800105148410464010b182078a40d08916021411201c0003070003103401c00c101083c2004220456a40e002a0f6401074032011507047c650b20380e83c1ca005a0407030320965024010185a81c02c00c10004a11036000d840c2c008030554040c6181d40d8a500003400c0c688420800c8002c2403450911010510a1110300102456400102c403 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773990863 1250 773989613 773989621
    0x5180603070329010e180a080405150c0a030f0915081915182a0309020105191101150509131b0b030411151c060f030510060509 56
    0x40d465142070300001d0042c6000549584046040ba4072840e06100c0302c00010b5650758580c0000c0c142640280d888080b80300b000e04151b1307100800451002c050f2644044454501844c02c400d0140c6800d440306102c04100061280d064884010b20500404520950707481a10380c8084801500d81c05460b08100002043e068181040356000032155800101e40c2c407a068a10344c80c0d61581c00601a02c20816401c070700c40010000301d0b9038080c0e0004075941c0040300c0c1809568189aa1108003480302410002d540348601000b1600d41d0080d84802881d600600d007561401d40035100c140d10304032207180d0400000d8124102660250000e203e40e900c004000303925804078074a00380004a50020162003102d101d0750802c44030041225600201c0410503006a008600030383e24000c0b118150000c481c20703103103584801e054a24601d4030900720f400344e0b00c0e181ea58604000d01149503210642c002d46800b02a1a0340303000124001000706e0501008621078002014050701c0c14440c4000c0d0b03452644150b0140340c0440501c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773992113 1250 773990863 773990869
    0x203030a0b060c0a0f1406060a1403281b08070b0919031415010501200c0a080102040504060b0313080f040513020301140306010b030c0f0c0d0801051806 67
    0x8030303040441403901150000780c00d40020703031500c140c1d0a0f0300310380c0c0f05074403021041040b42d0400030385441c020802403602d2104c004032070b92600000c582c203541c001402174082c0150310906681e180c0041000e411182403608102c40381e44982d41c2260300d804100ca41548400c10061120544869500000c60006e0945e02d41090b0960b1842140030b004151040071035004001d0700e0740c1400c48501c00081709070b004540c0ea0f80c24030b00180c40c4800760b42e01c02d9020300e4110009621032658924100e42042c1d60b00d801c1c0c0c041c02c9840c40200c0c01d030107180384014001e016100c849591214034240c0984602000181e50794030b8107042000300e89040d03118242020303041c4101700b454540c241d1001d06103500600019500e6040c910240e040380300c0c60704100d91280c01800340050340380e86580a58107071000000d000c20310301c566403301942c45400340300c1c07200140720400000741501c180c4c2c00544a0280c449440f141012820f107045420419611041c000245004004228500d011400006c100e20340458010702c0b41401004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773993363 1250 773992113 773992117
    0xc03180933050d030509030307060c090b040305070506030c130602060604060e1b090a031e1203050405061603091e0b0601050c030703030b010c0602070609050c03010e070312020c060d0213060f0203 86
    0x401c2d11071100700c002c3c030341410300840498003a480020300b620340d03c101da890114003c0c042483c0c0354000036080c09020913040520804c840649411a0061410300d140000308901580020400c0c850307144144403941200b5601c00d00c0340058032450300600200c1c0b9080d401d01084a82a500c00d0300c02009200502102d042241c007140008000c00d281642e07200700410108400625540c030060440a02a01d407644103c412020684864850034038020b40c80c88403107085050b101c0c11b480141c4113401c00008a13100e8124089041407020040c203000c0780d000e14a0710344a0314622a8a551540158103010070010090302402450344240242000d44c20400420300c040d40d80c0c016440c004041c10740d00c00080103c0da025480c1d1001071640150b007959a2101e03440c007940030b024040c40844940c400c6a485a03190b19060080103040a4100014224540f454480501c0c840c000349081065000741138103440a501d980004100c0c1240340389001da0358042401c02032000c604154041c1081051040c020300e105580402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773994613 1250 773993363 773993369
    0x2030d050a0e0d024009031b050111070b040b160f11010609050a0c111902060d020d020703051e040b071b150e040f020310060c03180933 60
    0x60019048a41413020400d6a2104503c00a075080700e440b02d4407110f810f2007142903001c2e00804003021104400c4001005441a4171401808547d20b140c009080c1032108000103402c5008100202e010b142c5c0208003107082c0d11100c4140c0703003240408108814041092000d40d00074800c0340e00d85041703006981d0024a81064202c1100070400c2c1e51003010341d6600e007508008003400c84a8010059070800c140144000c1141d05505808111a0341000d01c45ca040460042454800e900e4010342d1416160b081182c150301a0b45040441c0d0740c03d0012501c02c0030b80c0e101500d2106e10a4a466039940310700071540d030040e01079151044010208005c10703c42d54003071009803105690301040200e458280036404081c1052140c10500c4140d400d11402ca0700c181d407101140c0580c0e84207803400c00081d41015801000d03880111180c0d46000c00d07440e001c002141c0b0a1502104880c000d20708000080a1614189540761155020800142d2115203110451a141080e0152012101250b803000a6003030f0f1101202d0f103040c4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773995863 1250 773994613 773994619
    0x90b1912050a2102010f0b01050301120c031a010819030e060702120d200c030c01050f1612030c05031003031d031005070e100516061b0c02030d050a0e 66
    0x1000e030800c100d001c101c0c2e00382e00740d44480c035100808400c1c03402145100c03601140d20015030804a541c46000400e128101012a041c0d569a02d56824132404100008170f4040864044071080c00c0000407507801c540740b8140360030b102d0041b102c5516005000c1d14101e015520641d401d2018800800040d400800c44410004191540c0b0348902280c0001901d1341d18004c04041680204000410059130040a040c1e00e500b241c410354009148030001140d071008030301005078242c2e0003101b80200942c050009400808180d22000d880c0000e0188002c52501c2e2031203088030f0245021014030341c41501800340f480151868070300b890031458042810140c07100e00344800f406100d0074120304045040c4504402c18401d0f4041c046441030b03d00010140c004003412291030000074446215200c0c1880c03e1350f141050080f150355414204046208003044c16000841c0480e2911f030354881d03d6027080b94004840c15102241d458100c3c401000e03006050411071524100020400c0420400d603100d0b402550365442c0039429 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773997113 1250 773995863 773995889
    0x131e03030c0c0815040302011805151f030503040342020c0d1d030705030a060506010504051f12150b07020f03070e04030e0102030403032a060510090b19 67
    0xa08000301c07a00b84035003207101030303024189241c82c01004142150780143c1c801c1e8000c10401c0100d07074540b001a50240d0000b1301c140c02880018901400c0d109807141c2240e81041c0100f1044c05c80480442149546c0d030044496820100c3c04105201c0c68665002c080ca071090200000c00c605203103074240c24410f0303948084e885080d08504241c07064403941074400c2500785070221400305c080c0180181c1041041103a02000c12200440754505090100d13081003110385c0640189400c81c815034422020303080041072036040280074003000660f5525802c20440806180a88111004600384020200d000a0000d0f052140c18200301100407000100c1090880344c0b00c0b25410340381c1d001d61001542d014030a40da101c0d814401d50b00d012980c100802c060f140118480c0c1c07140e0031513015030700c0107903100d005520028020a40540ca5010145030000303042186801c000306502d4034095a42d0b40e003088031411317203008618203260507040c8103054903845651a41502100c0210480032001e2b000c15020000303014444880c011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773998363 1250 773997113 773997137
    0x60a290607050a020423010801110f0322061e091203090602120109050f0a1401090519091218080601060c030c0b041109070507050a030f020a080f131e0303 68
    0x100b40000c0a00d9a40184103002c41c0020f45007010000c1c1c06c09114202200d001c034000964464144284c8015007051100300e410401200070f808000d41000b800000c29403011481480440419801c00210030303c24100011116001c1484000300880d884807044140d18000410021a2041c004210103441916000c6040b035076501e440d0340030f40101d03461200300c0480304001003009041500903e22400d007191440001d0365420605030192400014001ca00d800804014041d11109800c0194080484c602e03500d203000490342a0b004070b44008a0945512a854010852041d4800700c800e442c00c00c1c210706d40995a0600c4c1ca450349585041c89003805116404181004046c0600e604800c4150010815180342c541781c1000d50741072188048851280142400107010329000d0000c3c3d46680d41c200000307080c018403da4080e10a442c0400408055200e10703540b400010b00050000c007042501842401e44030261f00361179001e2085550854521030f0302d40130324003202c0b00b00b5191000480c0c0d0146040b2900d508 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773999613 1250 773998363 773998373
    0x9020a1505040905100302090714071e022205160801090f0b100804020108060607120c111306140307060518150c0102031b031504090809040e060a290607 67
    0x4a154084403a91342041e04001082c1a1081c0443c100c2c3d0083d560940c03680c2d10f80030115441d18800a245100d103106201440100e4403220307130021000c5d01590009081c410b280c00161004140124164440007600034000191045000e2240c00801001c000c2c0b4105640410151078000c05005e03101d40180d469102c5404403800750405e50042e0806484041a40300001008220035400c403001d90109613080301150050501004442913140c00c02480e581c1645102003c6481035028102130300c02d100c130300716050140e070746509111004800019000582c00d10f02011004441c111907403040c42500414020042641c0003801c850f8800c244544d40b01a04184e200003d01305800c503404000a040c003c0756001d061030056000314020000c19400c24808151001d40a205110458281000004000c215200e03410a50000400c491155510034241249503001c1811909031551988280d4800d509005102d00b56100d020304c00c4142c500c040c1b58000034a0000244d000c0000380da107009417000100001409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 774000863 1250 773999613 773999617
    0xe030a0219090c080c18040605060408101113290304110f1203090d03031404230d1706011205010b13080c0f0409020d0b07050304060c0309020a1505 65
    0x950003414450351040141d0205400711840c0500009249044074103403080d40110780680c031501c1ca5010882c54a51000d0649070302c00c0641c56010f030400d4981c280070035555500f2020b00003505c0440c008003084070901c114a01550125107401460303440c00c10612601e05000c1c0c0c00402559520702c844003604400b240c1c1001000d181c005000b0131500d011040c04104000c0c05000000300c20206d426413581e42c00101040b40342c40100d07110b035000c4d40c81000f0581c0345080c449a610340103070080c00d0019201c204601c00010446007140c0403580010b802c90f242400401c4840210700d2412000700a141200380044c0103014500f0b00007865003a00602c1002a0160f8030820104142c00d4032500c0911455079655400c00240d0020018080028846e002c00316400c9000501c00b81003000050503405444500000d000c014400f242090760016444140c6a0200b50501d40c00c41c000c1c1119951550390789000e080032001c0755000c9050400701410003001c04007594651002006071861450300300000074130080207540368 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 774002113 1250 774000863 774000883
    0x150e0109050405101e051609090507030e0a080301060f0908030a0806130e010e0c010f02101107120807080a06080303070f180806010e0109060f12150f0920030d0e03 72
    0x5410003a160194000100410490070b8605400b4041a220120041e412030440241c07c0300181040e0020400d00034690445030704039007941400211500b82c4c85051b814042c20680a0f600420300000401c0a40d40c8000d05801c8802c0c0c5140c0390070b4050a040c4210380b00d01c02c240c501c404120804020445640c1c40c21148000b101c403288080010f2070a015980d800b808136040c42450328000c00d001001c055004604080700c0c03525a81c0540519040441f0010003010201300300c04200c0c505020000006401c0c1d44600c2d032200307080e180d0341294589404000c1c20420024190f024881c2010000c0008000010036241c004050342449900110307a4a411102a2205ca4138007c1040ca1100b0001d000d8401061640c107a60801e0000c6040b030780c0f80c10b0071034191040c500c24402c54044407501000301e640d4028862114a1040141c0b180b00c0c1c03101848003065a40758041d1149180d503403101c0c502000000410401100c0c510300e00035038507444c01c60020b501c0f034a08840c48000e005200d407405049940900c401032031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 774003363 1250 774002113 774002143
    0x26120c040803183010021903090507120b0f010803090a030308041a0c07050c03060609070c05030415030b040c140a140708030705070309080a020a09110c01060315150e0109050405 78
    0x60b00100c0c3c80c024603071110404e030324440c0507041c03000020305454001c80303a019206039180040b412241d9000c800400c0c0340c0d50155004e005008000c5070360440403d41c03044842c0580b14000752401c21403200300d82c2d00010f9000303d4030b40d441004940040d440381041030040342d41500300119039a8484c107012700d0204a1805002484c600401013141d200b00c0034001d8102036015604449940610070141603440c807003500c0d041d50080707181002940031445a02c2040c07245102d01c2c25a41065510280c0900000c0c14683d2940807980340e81401101e401d10344107021310001140760096a0142d06000444a88111018502000100b803240307035605400b542241c11443d445060300e46d0b68a00134400809070340008c50704400081030604001160440001c44241003500140394900085c03074007000e6402098040100b81d89280c041c00358007400c280c00c2c85070740d00850280211010b20081e05d01071400302c0b445140ca040348030035041c00c180326035204000c440d410f44281c582d0020b00c075100c038100f842c81d180810601a07a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 774004613 1250 774003363 774003409
    0x621120e0f12030c0d180306020307050c0616080906071e140327030a050409090228090f0c0e0d060605030d111006080d0c26120c04080318 61
    0x403064008004c0a6a9503100c2c2921014001e54804403004403500c2a504c0c000f44c4038034018004180694001e68020301d0a0610501e010100700d0030a00700307102200e40200c10540e61401c103c000340c10001465105050344003070b260701e00e014000a001c0d400c64401c2000e040d80111142842640602203440020380c034903100315200e2801071102402d0003000c50701054600c2d41d850307440741c0481000041e2620b0510030345400303080c207040c001a08000c2c109248160f80c892600c0b0b11000e0205502400c0d000c01078082c11b01e040d051400d03c40c1030301c02d90f03c1c021420740800d4901403003100210381c020090300b14010b00310303a8001c16818500f0a48040c0c40241c200031780c136000b0000c040050381d1f00030b031229404a40075001d58003400000e800040132140103200c0d4425a03003000000b001124171030343c14804414400c4110301c079688069207001c81483d0716414621044c150004101e100c0c0d030b445c0050a0b502c03000d0300007024030302814070740d9070f40c3c89008880f2061140d910031079155903e0758a80f40100d04145c1c3e01050300e1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 774005863 1250 774004613 774004639
    0x4151a060f03090c0d0548030606030d0f0c080c070e010906090203010303080619170c090f010b0702190b0d021215090c16060c030621120e0f 62
    0x1840542c000e940c0358107503210300da032404042e0802c103410074519a04a0040c10344449201c40c6098020081c2503440c1c00d00b5401c00c100020084c14a00810110010a01001c0303034070724a0041c1403034948080c012500ca540700511842d000c5500400d50300400415203400203c1516915140c10030b40504074040c40e850003106008140740c45110a8a81203800b02441400402e41c6c0b1000c1d04120301c820b0001800264144c00003640364280030503080858441c100c4c2c030201103640c0e41c980440c60880d81d407000546401207a0403410f0341c41c20030040d40c0c010307a010401c00d070154540f103d882400d12178200005c1c01030b6002c507502034001c60014103603c0108581541c0554070110351030503600170742c80003200c10707900303442a004200d00641040451070340d860003410003e210b494660000341e41c0c0c0c006003c0040142d040800980c0010914003900b4038041b404c0d00d010642c141050104c000300992000c440032000101940d54000c00c000d058580134000c082c0c1850b0038811a43e0b008543c0c900c0029100603000103540d0400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 774007113 1250 774005863 774005887
    0x5090d0302091c0b040309060c08030109230c0a1d1c020112110927150604080a0c03060501170a0f061d06040302070b0a0212030a1413020f0904151a06 66
    0x180c1c8190300c47e81e14100c0094540c841510300c100e000d08050003400d4140700501410449070302c0b025074602e800401c20050006500d000034881421190a0032038140844d5400050340c00010309000e00b00402d140001140303c110200e0349031300300f116042030b180541c16544410759000c3d11a040352aa0320000600c00c159a02c2c81c1003003e50b02090100380540138116602c243d0003242d800382030001603038400c030a0745500d40203020b00041405611a542c094020000015403010810074045500d10511840500e2841c60034120102c44050740442169810102071810015012a1501609a104500184002140c03c0107c01040600d544400511010f41e5414550400003240c51103107209a007102c802e1500e031811b0041500a44410b90096480000100703440c402d102c000e164032030051000007a86039040300000d1041003054a030306525030078a44200c002d43c1400c01080703c1e4404151009600381c1015a183c0b180420104000142c0994401c040307203083d12050035050902e000200500d4032050312802c2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 774008363 1250 774007113 774007133
    0x30204080a05060601021c02060f04050304080d0305150603060d0813030807030e040e0705030703151812120603021302031803030c04170a080316030b060a0e1305090d0302091c 77
    0x44503000d485192010701c0d903280203094400e82d211f002e42c00752620781c0310300600a0200c2e40181003112640400e11010800d06010440300d02810311681d00807035541004802c0d484100361090403107005a204104001c03540d200c01c0b003068815a8841c01c2a075480c4100c01d1741c02543d20b80b9410061091000007035580901d6801450744c8984241102c0c1000140411040565201c050f403107842e40680004c1800c001041c110203261088080645011400071140c0d0000256050018000c90355480d500e6245000c1641c0420030a40e24100100100900307070a540000760002c7c540343c003103100960000000b4449280b0b03440207a000c4068030003103030f841c1c1c10a601d5002441e00f184c00784180e414601d0072200100407000880c00600e07078010010740e01d1070701c076080c569041e010a14218020306172180156206916428014030700390074141c0c1c84161101d407000c00c20104009240c83d1214540c18003040c42005000842c8400341c0c540780e420016a5191f1070300204031042e82c0904c1102c10307050942015000d100c21140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 774009613 1250 774008363 774008371
    0x5040b01210f08091c0c140102010f050c2701140c010216031d24030601200102030f01082b090509040501020c010b031b0d150203041103100b030c060307030204080a0506 74
    0x14100174101040501c098034002800019040300061401041060800000441c03503040c10301c0045140003452602c00c1c280e0b20140c0d65840c01d0080042c242c111500c0ca1003103204e0080d2140c80c102c6085c1039060008016054040c002c00803043d000032165042d0009604403844082204c01e20f20948005080103050090b500451003d17183c0c0174541d00281d40b4210049c08200b01101c1d00c100c42c401c0a005070049a0b4100400007414032210005414030f9103060145121400c036141d0016a40385410681e03100f200720107a00105059005284e004100c40001c0101c000403225501d015001d220490702c00c43d07419072980c1c0110341126880b0207201c01d020301074005041d0f010f03401009201c840c0f106418990354001900c03071380e02d00e07504504200b80217107420301d0581400c501444d102642c1034807068030041240e0064408580038408000d0000881c28103114403800c6020019042000a032507401003511910301b214000c1c86050700200051030a4081d83c10740d405005200116031036917489183c843d40d1010300380d07 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 774010863 1250 774009613 774009619
    0x130905090d020705061e07110307030503131208070323130819030804060506061c02070203060106020f0714060c072c0115050a0c050d09030c0905040b01210f0809 71
    0x40105241c105039044406c80300115000009411005045c0b00c90f40d00044021240d400100d500142030b903a080003041c1c0518092405150317150094000500314a20380ea100c1030500d6280210395001c00c00c0b500903510a2a01030910705150554914070f44490074005007803540d40d50003c115015080740c443e42c110300b030f600220201c42d00c040050400b0b07000c1c411001c0300140042c0000c00014005140c0b03812160300300ca00907000754202684207036080c2d1a042e131101650102c1b45d021454105600e01002002c1c010039007400600000005200b9031500c840c0740380101001c1c403110304811036030b5848401c225002000e01e0320548007034940315201d0b4060810b00000c001680d0040b107070b01e80300849064071864129081c402520602005252046d02c903500a175000c0000d2210b01d240500c0460401d01c41103401c60038030f64410b00503a003146001c8008586070780107a5502d525140802c4001600d8110344c60548450502c2c00442800001100c81e03110740c0040300800031030080c1a0300d01002214400ba01c2041c03c11 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 774012113 1250 774010863 774010873
    0x2070603110f09060a02030c1516030605011e171806010603020405011d03030d06030b01150e030a0b0613060303020d081e01030602090a0504060b1e040602070b130905090d02 76
    0x80d050101c15025a031142d005840040000404a241c100010f040010013130041d207003003d410001c2c460400780c5004008107070032540da00b001a2412407406035143c40f282030400300841d50034500001c051100c2c2e41c00880c210909041c6003500325005601221003030f20800c2140b2007a00d0445841e6542c3e000550081d40e0500c600000410700030b00a0003a507080c0d60040c0d40b0000c100b041d54043c843e1002d1001800e94140c0030170001e070181c01a1900812002d0b50051480c004c495250110f08140488000c281c0780c108510700b880c0d05010340d40402c908030b4035500f10f1450081078840000040c4a40070340c90381c0540c082d262140c000b00b0141c01240d004244601c0303840d200820b64641c0380900d04045088088071002800c9030040c0002343e86503002c2c008101000d00b5902d030f21619000820f0464078260019220144003042c000e142018513007000712000900954a42002d10b8a100650359103c1e5004155403032034041004148000c171030310307810018140f00f0700500450411400050b204c0caa0f00034200014010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 774013363 1250 774012113 774012131
    0x30415050708090606150c0303150a052209051e0c0307060c02030d03200409020c06010506160b130f030e0901050103020c0d0305061c1a060409080301170a02040c02070603 75
    0x981c082d07a2003544444090040d0340d460344100065078604010a0407121b40c248003555000c44200080c61080031840226114107254808004254584d82d0100f4030424500503c18203c41440c00303500481081010041409015031420505100c00c0601130310b03550a000e0a10383c20890006a8010000320603410f03100e019440b0709046555100301d440103501075200d26078030440d80740720f6804147c08402c1c1d60b1b100ca210030614070031000c49034800d5200800c611b8010071098107891303041c081c4e54010141180c00300d01d00291000e200c5400e904610703010b402c080000000460000c3d00d001a8100c95034096070501e0300110314034000d02b10036010846680030303414031390004c0ac140d4024030071219008000c01c000c0c0301c0d0200000b411030240c40010442c580085071501002160388100c1e4035440214420741004000c0d06000030508100031008006a00c00c44c1061b102c04049107810b0112819190300c2c661801c0c81c42e29034801e861410f416404000e4100e80342203541d2000d25804600c120968046075028001e1b000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 774014613 1250 774013363 774013367
    0x114160509150a09030c0b040303021209280308070b220b06041e0f0c12020a05071104021603081504020702031b0a08010e1f0513030e030f030304150507 67
    0x4400086422510260b4a01210b41e04480a404a81c2051400c540321917100e03680c907a450622a40811f0b030352840880c081c010180c05001c41c0c8410340d500d13400103040c508040d001542d41400000c0e00d8801c000c811403592100590946100c0155801c510301340d80d44e4800e851721569020003210400100005801c1810045100040e511141504140f8042264448004100c01050741d0800300903c80404500c0042050490260f8140708018000000d1490000d040151071020071040c200c2c1c41c00d204001220599410106441c41e030350304a040300104010550200e0024401c0c0203021185261101054042640c80416144513030030001d104011000e454003404140d000f1510001d41c9900610305446ca44852503d8500398000d0080c65812005d64440500e42120504500301040e5046000c802d0341e450240e10075218210900b19080181c1d00d0003030092680d01400000003801c10810907030300b540b00c0c1e84c10000e00446411a0042d641e59041614100c8041d1140c0f5009174202810310000680d017078 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 774015863 1250 774014613 774014617
    0x507170a17060a1212031b0207031e21480807050105010e0f07270f090f0e0a0b040308070207170606121f0f02090301141605 55
    0x84141d45a55031041515200c48010420050441c0c1d00b00030500c1000801007000245154014040c3c081c0c050f000d04a500001c044d80c4074916101c01007000c980d0041d65556000801030b0842c0c0e00485600149025040785505c420106000502500300c044064035000c402c2a400c1c4c1100c01280d02e601410480b103000309a00c0d04110100c0742c0341d4620104c800045401105106040c0324554070300c0c3c5c01e8208e025a5400e0154001d180161456959072005001511000e410540c111182010340c0c00289040107000b0004080b958002e00308201086100090b0300b660000180a800c00c01307080c0031283d8668004400401743c643c3d19481c0c50f814140b015001c5080880d940c06030a17000038402d00955110b4400f40c1d003c28000d0014030451042314000900012242c141340d100125000103031019003031200400148030381201c109506030f0004080b038103c1250800e200c6000080c03100d00410241412180d40d4003d0003000e020350340550034000018030344a4502d0002c1d101d11040e030f01d118490714042d43c08462074 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 774017113 1250 774015863 774015877
    0xd060c2019020307030b0907060206150f040903021218091f150e06040905010e06091510140c0a0302150f0604020702060706060603020a030b1206040b0c0c010507050717 74
    0x1034100315040c4182107400c200962815002400f241e08013a66542c0e68511030f8030440c0e4803900e03508002d00a2101030307814410b81d9049655011580110f10908000030f0b0044140c00b17002d8400d542d9901080308050007880f501030101b194a02d116112480f0381d800b00c0340599254400351040007160002103212a0100c0c5032114031415050a245460030302e04480b0503400400ca0031420b000284c1c1e5100340070340da1580204003030303c42c850000c9410351405410b02e091080107808144561248010404200b00700c440d840080842140c0d02d4000710301e44402070302c60542c02c40c0c01c07001d20764001070740b549501000603030114034034440d13400c8810202d900c1412110800080d0381c7d403880e07a06c07044042610391500e0b030082c050441c0020000e07440d0103041e90b550001c84501da030000000c2a0003080040183c0d40520500618031010340d0f61300509444010a9034891100500c014074204c20b007004038581c0c00384801034070801d00f4610003c00450418110240c4250000402151103107950039002c44d44019032030a0b601c103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 774018363 1250 774017113 774017177
    0x50304090203070c05030d061802070203120a030f0515120604030806010c0804050603131502070209040204020d0617071e0806070f02190602090405010b0f0a0f09050d060c 75
    0x20a4288031191000c0e50000c2c241004006050f40075001082051004007494907140c100040c16600c1c1c595046a00d901e41d2031080c071350314814002000541c60200c2e200c1030781203c4404066482101c14819401007a0b08401505883d1400007081080741c030003180001b030070000b16852141507049ea1030050741c1d050308440042c0041c95103000710f02c555000f8848144400d1040c0b0680f42440d80b41c03004136045030011076800403080c400c0c044d0801408414264401100c0c0520020351410078650086045141c0181c4028000c690001d0090100300c0c581d803007080030b084c490293728940d10780500c1302e0b561041c20740a280c03041248503040c01c2d41160b05031484003c4604540c0500303003580c0d54000944144013174500d504158000c5c5540224000d84001c104103005200b00030051f2150400c5040c0002c03144142c01c00d59a1180403c100c6182c6030b50002a29111203071842d080340d040b9401c0204403101403c660203290051610902c20b410001c10b0303045201010141d075120600c07000142d1a00201c149138a500382c2c1c03 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 774019613 1250 774018363 774018367
    0x37020706023109090f1212050a02090d02090411040e030309010c05040e01050f13020f0c100b01140708041215050f010f06032004031101021b220f0f020309010c0c0503 73
    0xc03100750641c1011a010380159a1305200540700d440d042080504240000000394071f040070f69000f503c03a4850366410008000c411800c0080721008507441d1075100741d0191003802210009000c100d02000c2061040354050000d0000701c000901e03003942c0740c10940d4502d90344d50070107002c00b40c0188540c0030b07034046406180280d0341e40e03440c2034144003a50100c1c1c40a140c000b01c50a03d5501d03500341900042451000c0c0014117503907034014089240c281400070703040c031000794100400b81b030060b0b03405101c1c4001c1d050080714082d512070062404030450300c00c40d070005030030351a040301900501201a420329008004440c0500403555540090f850001c401d01030003000545691b81400018460303446001c2044810322500d0304c070302c0e0507070307030421035400640c4110380160a101e01d43d00107503814000002110381d003e03000c05078030718441c0008842c0391350b241d0000110f88412010040e04031803900140206149158104022400a050580a980201d61202613507007481b160303000b0907204400c620411038000000c0d40c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 774020863 1250 774019613 774019619
    0xd150807240e0402070b071806030615050a020703050f0105220201020a060b01050909250212180402040905040c030b06220e010e0f030d14370207060231 67
    0x19881c001c000b544550082c0d400d0280034000b6000e9600c2a001f1100390300c40c40c2429540e0b404058001c1c1c816000001054181a020028841c18845003a2440c159080403904c2e0b2610320000c030710303003c074650010f4024480d25102542100b810340c010360003071610310001d0425510103011004504d596010003401a4820300c110390104039035030300003980c16405151041c0392036000400200c3c0c0d032000351481b40c0f0048a0704100320074120216005800035209002820a02c01080c0401e0410b01a000c1c01c254403200e501484880742c0d4481d070444005c0c0100800401c85800d150415a88080a500013206ca00040c02d0102e9414982511000507020800161400750b0b104010700e040500304c000303280c00f03482d07485001561012805005220750407032800001d51f01d820510100405a03614004c144403002e19000502c46030301c406032a55400210b0310503d11562411030301c50b104450940108050b449480030079030900b0085d01e0b400a01b43e0941411000703895940c040c02c07010200078403826030313000441140410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 774022113 1250 774020863 774020867
    0x12020106060c081c06150210181e080d05010602061008010203010b16080c062514070f150501090b241c09170409051b041a0d15080724 59
    0x4c0030150040d14041741d010354484000c501818074884200150300110a81059010548944200215008456610303d00542c075014000306681502212600b144c941c900213000d04a01150b0b0401c4080c07008116542c1e4440d00251940c5042d01c01e10fa104000b0f040010341d0100500942e03042c0d4017400c0c0e14074031b4096050300d18850804e410303100b10f0710f101d810f01c44454045401e1000d00c0c41503041d440d00c1c1c01a1028542848130002d0b50b048a00244040300c51801ca11071041001c0e1038105038400d0017481a008071307090a0700c1810410803038100c50340c02c00e40040380042d03030346d0044c004882065440c00c6104901e440d81a0304000078081d00ba82c404c206000d9800380c0708001003210f085221014001861605545540c1040024409101508540001c0802c1241418071402e0380c4040c10030032200003040e440281500c24132440c80b403c3e10b105e0402e5802d80200c07120004413468a111464100f0004201d035040b801003c20f00c4c0304892142c081c0f00000202070100c1c801185007090900244001c0504603401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 774023363 1250 774022113 774022147
    0xc0902090a08010207050606090a0213050607052505031605151e040902030f0c0c0a2612040506010501020a170307050714070302040c18090e0a02090412020106060c08 73
    0x40c80d0351000e141c1c40300180000c800e100510310705003e44081d11031444c0410501504400140500d91414410000e90b003200783c060155400313458089500d40e40e2002d06003005e51410002000c0000d4811800b1081200100203110140455001f0750075241204441860001896a903200d501c2d003164541c00700a80c2410000010300c00d020740300c00d0707910705001c8058511076650816005004500c1c1c0c000700f800384070f5800004003035001c1c0c810482c035480d102c0e40c6680703d500c8000c4044001c104502d43c0b00b0003076003684032503c2d1009413402039110135116540340141345064001503c0589060103100000f190552003c10b505034603a8100301c03030507800b048081c5103002075400203000404000c402d0000100140c14000c050101000304401014100e085004020450704144030003024040040c6440e10541c50048404045a8244000007406e58904595030b04020030100025480003403181000200a281c44e01552403050903802042a142c071041c0944240c0c1602001030241482440410034131086000c07 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 774024613 1250 774023363 774023377
    0x906020715050c030a0c150614010305060609040e0a0218010608070c0809130f0b09060a031104020403080a051801080c1c06080313061701030f0b0403050c07062a0c0902 74
    0x150041c40c1c81d00443d02da03400c1da0001e0a11a0005802c17400300014060121926003101010040800800d49000c0b1842d082006064059043c552154000758042d42e0f00c0050750030140020700280455884000700c50b880304450340c8c0892207028982c0b400081c0031800700100741a569940c44010198903143c4040e100c4408800741202c2600301041203000a4861110301c401d800c07401040418803400c0b6410800c2030701e05440c041801880e0f602c04000f000c2e81c8041403201140c0c0c218107021104611080410b020744a0340e00060f203500c40001c2c444100d590722800038401e03011168240d11a0745020300044a6003002540c1702c00403100c0c00d00c00b44030007109403020110009040200043c10a642e0f0000d0350a58004181c00300d445441403208120458002c01222610001110300380030a43c1181d0301c01140700700481c07014004c0c400040025003054010070072034450002074030440b40840d84c3d0301c0b402021343c071002081c81040740d402000c082e440101c010302604801e40c00150640d81340c2c10450100001c1d00058 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 774025863 1250 774024613 774024617
    0x7090303111c05030106110c0a060e0307081207020a0b12041e0f0507090c02060402060d0c180f14030303060d030e0312030108010204210b0a0209040b090f040308070906020715 77
    0x522010740c0782c0100200c0d0b40304020703a03101d0580303a40c90004d024180d240c0c01100940c09070800403850b04a652a40c03808002e851460400c143d0324810b28000c00c1ca04070641d0008001c900c505102c15400448541c06802c0543c030882c5c05034141c0e521420b2264060241e0032030441312264800104001410300e41c07042016008103402680c4122140d00c640d80c03c540c40c0002652103802410041c0480b00c1c0500800720f12075558001000c1508090340400c0c1103109004040b00c0182c2d5036404043c1e8144501a00e030070b0190388205d1030140c81e40340d90108104000c0e901c1038405d40f070052030000d4000c1c06e010040c1d9114250082282400c070525480030b403401e02d514581c1640c540554203032a09075198480c00b840c0600560400140c0315414080701c0341038030b070115901e498105020070f212000a04401c09050b40519120005629a54071401041c003410178813050320f42c0200c40c5000c001e8403000042c0018800c9010b66a2840f003500d9000c4e0584080c1007d000d15401604412010b112820f0640c40010200800d8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 774027113 1250 774025863 774025873
    0x180304120201210f09020307140a1e050607050318181b0c0a08070b0c0f0a1407020414070906030e0c12101d0f1f090c050306070203210709030311 64
    0xd240c83c01101d50311803002089540d40e61118066050401c0400b010f81901c40070041e120030340c03900140e0340121622031354098028030700c1c2e001045e40782c0400b400300502000d000e26454030528607002d0b403240c1200014200f405a000003051052401c046400e65032505401101010303241e841c268040307180182c1d003005502004000001c6003110820100302c4003070151040944030509840c200801000240000c0c0c005c40045c0080200d42800b14211000302003e030070403144d0482500700c5800b95000340c0300040d5101c1c1ca40000249286940c1007842d10038004e547da0840703002d4031420144c086455640c5080c00700e81c40b68101c10000d0a1111015010900301803c0314010f0388041442010341d400100080808942e904101e4034921080101404810110018045d215894111554250b40e1490540049a150390401052200344400503000d4034001d002d0b9a001c0c985003001941da07034172120015501d2960819198041c40c00030200c82e004040c03540c6c481d0200c0740303151012a03c0249040c02c0e20450300907 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 774028363 1250 774027113 774027167
    0x7031b0c090906050606030717070c0b0c04030b0f1b07030905060d0608071406071217090d121509021b010603030806010e030a210323180304120201 65
    0x1080e0510401412608000320381d640070340c40c260007501c0d000b0b40701314002e074414400c2c8802030340c002151000b415800e4104002e140e0322410115125804558042c0c8811000780c00e01c180c0341e414100500550380108123803002d58a4080c03140061003011100b0310300010341c85070884521031518009004c81c601a14101ca140b0780c40b2070000c3c5080e48484280c903071842ea0340340100480c20b801e0024030018401120102280144900812058401d20700014210000f5107558140b13a03014000c242c03035a80740703400f043d40c3c2480c004079080c0e80c542d07c40203032034041850702c842c1003908013103401240100b452070300c0e1415100d45007551450180d0042c40c000e11100c2c1088943c0303454034030240f14880007140241d03181161801c0607000907040051a401181c081d0300110071010108100d610f60a5101c10f814040209030842c90f88210300402140300720010703d1610391004403040d1540f8110502640e103d4071070b060464807541002d03a881c071030f900c200c11614003084800310240d8000e502071110104c5000244003c116 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 774029613 1250 774028363 774028373
    0x20f04111309060306150b03190e03120f0c0403020d1e051207170f030423010c03051504050103150f090c0b120c0c03161a01080a1505070507031b 64
    0x4090b040200ca0382e079510010014007003540603012071804454880200b1504003c40030700244001028104507802d6083e613400701e0f6480c0d50207403041c40144810b403903c0328030038140160512416504032a1710410f5501160000c00d00306c04441c203c940c000c08040c10440310341c0e550200b01090b2a000010301e034017400d801c008140c09001500d80e5000c24603001c0d41d2909a4a0440e82c03021885c1d11a185081c420b01107031003103015500840741c0140d001000340d110300140c1d19034644c5d005e100400e020561350810818084143c0c00d40c101301d005d0000d50340081c0804480005101c200e400074440501040030180b10b5400310010703079001c0010001804404907065410f45c8500d070016095904c40c2e500c1410004185c140c0034815803e10703401c900c515400514003442c03000204c0c0e407130280702042615641d00c81c1301002041400c4e141c2c651801c50400b0161525039440c20303407a84400702540140c0c1c0490320011000309804483c8600ca20039100380d02c5c1e50b07051440e50340b4226802c0a0000500d0048403000c1c0500020030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 774030863 1250 774029613 774029647
    0x506031203010f08150103030905012f01020705060f060108010e1f03210903110103020f091504030b0a0e07060804081e0901090503150a051308070f0c060c020f0411 72
    0x400e00a643c160751501d24014581403042c02c040720007a2250006000181d03110140300f049030001d05e045240e004158810388003021001c03103049203c41c100c080f0209104010740140c040d542c052410b942c00c5940d94240a10030007000c440650008851100510900308003080e12a0030a1141682c40440c10384050b03010500103181e0000c1d03c541e842c0d1424800d0806155110088440d80d91810700e00361031441d91065480402e001c3c8507414181c01040720001c101000c0140c843c0620010004c01d05240100085801980b2600081d69200340040c0040e014070854061102007a0904000300103091400208561030703070010340f044607041e00800110f0302c00b00203001c07030035011126078100361342c0c6404d61000074204684540c8514003a0308501400b8400d208504c0d0003551003e90300d5404103e59841c8a88550320720826070b00200381f68408503040044c42644141208803d1088107480c091644a090543d144506035030029442101030002c00301a007801d8005401004035141400c0c00d000e03403908621015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 774032113 1250 774030863 774030869
    0x40e09010f1b12020f0306061333110d0e040e0316030e090f0105010c0212030a020619150909050f190b060a050310110c0d11010609050601080c0c031e0304120306060f03050603120301 80
    0x26080c0141d00350000d04c07441305240ac0014036050014480e01d0400155450b0360780231180300107101c00d850044000b500c2d56007044891003801c00c107803580c03080a802c8080540812500c260002000381ca01d2160314200125084d00407885420742c3e8089030702c1d12004481e03480e490070040380c10000403501440000d00401c003034101c5027035580190810b440c0c024903410101c900070b000010038500b04003003019684005c4c1e1100c419030b81c0788000400c4585841c20140e01c7d2000155100109120302000d81c911210305c410380202d018400d15041c0400e484543c10008502d119002d0203034107411501c882080f043c0303e07900240340382540010071400c01340d400d010281070844080090000c28041019015000401e1051101804110781e04000600746103000803c19200103241e14148800003403822a0a07900b0000c5c0c4007482d0402202c445a83c105100c8079000e80c205030b40488140d428082c80340e070694003070700a5500344d49451742c480c40101d0002b6807c6000d0407000d82129054015241c0d86142048404015030103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 774033363 1250 774032113 774032159
    0xa0311040f0524010e0f0d14070605030907061d2e0e010315060e0613030605070f0f020106030803130c030204180213050606040e09010f1b12020f03060613 68
    0x1180d03da2078407101c000b00004125504000310342000d2840396940100c0c07904500e070152142c003a842d080d444c1ca130700c824555070500603261080c044001002c580c014000d601c40c0002c1816a003145135120810755851100340d40020300b41c03901ca900400c1c541858402e81c1445400c4140129600030f645042d003401d190a030300b40e40b000030880c1c02c0002c000d503018000c2480300e0071050306401440c1d140c540c00400c144151000320b4807545001843d101d0720703100720565801a58000608105074141000c018099905c2d009510b40070072548450750b0403941c0184122002c894201c00128138550b00c0101030946002100b0045074114644140071026072a648110407207081402c942c04d1004809004100c0d40009101e07042014508050400000f0b4542e001a20304641010700600030903100e450001e4054150300764841851131804804524440a01c100030745004000c2c0c4480c60307014030445150081c0e103e0b41350381800207041080811a5820b1100061400e45c05180380003041c1c03074850140e010f550410044c00c0c0d031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 774034613 1250 774033363 774033391
    0x4031b030801232206170d141c0501260606040203070c0606030b06090606130b030c0c010c230a09031e0213020c0d0801050d0605090c060a17010503010603020a0311040f05 75
    0x90400c480d20400e00a041112003425124a0402c51559903030352807070b80d2008011740c0c291003a4504034480c00f81c034040314000c5803181c010180c41c010b27400182000d00c1929210000c04110500c90110804030b41d1000440c280640700326070b00c04040c000a588042d201d2820402d908680c0d6010039180c4c1704d000c0143d81316003400c08943c10840b041000040014001c84d10a0b00100002806440032078001803c6918485022792a0380d200c5607850518040c04000701a00d5003026102c402c1e50342d01c00e850100c0c1900008401c0d030704502c1c1c0070800450b40642d00c440d101240b180b90003840410404882c21b10090704c603030401091041031744e000c1400d900d0303c032620321036003a004155400040414400b101c2c0411842ca00114151314001c0011070307405000d1806094195a030010910080c0305200d010918600604810340d19010f4550041200440c0c0e040c80d00342c040040c0002c2424901801031204032500109414003160450319070203807032885690302d0307070b44140d8030f03040e00000140a000e624819034805014030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 774035863 1250 774034613 774034669
    0x50304050a0e1009020c0a120e06210c0c07060c060e0f10060801090b01170c0402191808070b0a05042115050124090e0f04031b03080123 60
    0x4010803c41e4000e8100b00340107000e0440035060004000750b805401200703499400e00d5a280680300e0300c0209000c50307000480000c1c510f11194156280d4821a41c801055507600c4e510385d814600c8500075000540c05680100104001d040d10422405034220300820001070f00040c1d103816145455a52110260107411544074401010a07500c904401800034800912020a01d59116207282405004802d82190006007a651440042140120a04d4060403c560386c0c01180b40610400443c000d0b6400082c9410304008510340d605040e40084410580003000d03500d060002c58026900502e0701c403010000d00f400005049404107c8050505a11a9642d11240308078207002e00e101c074042907040029818000100a03126454000c178038282403000c0c000e10340654000d801c583c690700c568403c4540c0000b840602c40c603a500304101078042c40c80707501c407189d140d0450340c140000d01c01907900240100d80f072040104002d1030003480004440d6141ca410701e40002840002801d08244452140103044000f001d01e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 774037113 1250 774035863 774035881
    0xc02010f020102120105060325020c0a092f0d15030c0b0a0f050903121209010e07150e04090209040302010c080705040807050411090901030503192604050304050a0e 72
    0x1114031105100a504c0c002c0500280d0310b030818107204050007000004005818418010304694030041e070006604042c04040100a585021140044e48541e10020000556600c0e40c801d10349000c07642900d410110080c10310071110111400f0011516110400182d07002c05000c3c0b05d17031090081003000b102c95950460a140f040c0d0102ca0b000080049805c1007030940040e00841c0113070044001d0b01e40281e40303099140c0444c0c01d00c500e03110107121a120206891601000718000c3c0c911840b49800204003e09e030650141d0341e02d0000b4410300703d158240c60544c1802603c00c03800e000c0c200b40c0252001c9581c141541c0402c40009080b40d003540180d40d69458888031035480400960013900d10720784030341801d04001e0155129142c2d8480d80d8440ca0b61000c460708444842e00030b88902d404014540d201c1580d40c1e041c1903443e540400200e10310780103480071118055015070f01d014021041d180c000296141d6a6840210050001c0c0080d03072684010b0100007542d0703540b802084060301c1c02e202030211a091000300 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 774038363 1250 774037113 774037127
    0x81b010507030c0806191a0304060b0105070210050708120c0c010b090114060309190c0e0109061a03040c05100c06050105030312220501060e1501031a010c050c0d030c0201 75
    0x1010400d41000c00040009610848075500300c402242c60304050309000480202404c055404564044070780f28071f0700c81c600da002c00a184903a005120501c1507200c00c8004550b00c1c41000786c000e60200d104140301174550b101c1d1028000c0f107071003441c106262418084182c05140002c940030882d0740d0000031001c648203030a01801801b48826280e690495042c0300300e43c2c0c1c00b030b842c1004141c0144404000194065420041035000d01e4510203c94102c50b05800c08502d490170b03030300404c030f507841c00f007800043e22055511a01c01240d0031000002c80c00e9040c180ca82d8111b600150040e0b030f002d06816008103280c1e4503485d60000f1284103803900c0807607072180d103052420381e80141c0c8203520941041c07000132002c4000e17040503944681d03900f0020007183c20102c280c0d040e40008500c00b070401c0d840c1600220b261500341101500800d9990a00c81560101e04c00442c1690300d440216489004038406942040d400f074900c1034140c80c03090040d030f0010000130000c00c03d84401400150001001500c10105658000127 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 774039613 1250 774038363 774038371
    0x1e0b06041506020d05310602061012121107140a0906081b01021203010b0a0909150306150b070501060504050108030708180a090207140106060318080a0c081b0105 71
    0x45054821860200c010b92100140540314080c01700005621002040e40c6d5101d0130040c401c5100c0354030b01951200e02c0c000c060b8a0307000381400340c0300700c0700414984801444188211032030038001241100f5503541b2240903000509030102801482d1000c4050003409000101c003400c03c8a40358008030020000304010040e036640030640b45844e001c0c0c05c2c041c9040200e05d00301c001900d0207003001c051248000407450b10a80e0a00c119031900044004074001c1d12810041c22070b81040d694070304416403a08888012078204100c400d451203207004d41000090010340041c0581c00164038a0920156140d042c0000c59000c01800c030343c039940d02d001c20300c07052505100c2c43d405854000c001b181810b0f86a130f03071600d680c810f08142c895500984000c0810f5962400c0e03042010b001202c1e8259200d5803941750502202c41c0d0701105c0cd0b129424000c003c00d1448c440d228203518100400040301c45a01c29485003039a0368441d00030302d030800011011100108401c3c00090a0b04107036070426480c00a1101d003a2030840f0302c003038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 774040863 1250 774039613 774039641
    0x10902040c0c0b0a0b031c0e0316060507030810090e0a14070f180b0618090f070903060509100212100b04050d03051c0f0c35041e0b0604 60
    0x40c2c529404603000f003d0381a4000c3c01c2c46400104442c004001a2800001e0000c02c01d1124454910000c490381c400880300c200002681103918058071a0340c83c0304124600d0245000061040c049480070a105011a68001500c2e800e00745070603403103104500540d251803162400a6114118000c10040701d4504100c485a14402a01d0b40c103081009075031403210300344a0304903510090781c041c081d036005603071101d41e1412009000d20f6458401d1484440c2e2103601e0010513100e070103d400011018004000800c0c030800140d91100d41d040d0442d501c0324002d08001c3c00c060454071907241c3c0c80b802c1080703900c000e10b42e40e8583e40b9031040600c2c3c50601000009000e800a401d0444103100820140c0c8810350080c04e00355041c03d040f91502d00074111b08000324090900105950f0800109000400c295400089a4056a6030300004000492001801a02c0c10110414100742210f80d4a0140402518042d042403294800000c0d642d11203d030b61090900d12801030310300f1100201444060314041c450800c0d0080c0c1d40b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 774042113 1250 774040863 774040877
    0xb06040b0a0f050312120c0a021501170f0d0f0f110a06051008010204080d030209041515090506090a030f0f060c03050105011e0e06180d0804030b0907030b0103020d080c0f010902040c 80
    0x307040084002000901f03400d80750350000c20000b0f80d0600038042051089907580309480c666948003c0180c007545400756000e041e000d100c8420f1000c000c041040407080905440343c42c40803142090890b41c0c004095280c208110340391001d018032500900c40003c025005560201d9242043e41c101d280880c0540e1004202c1d130720411081014031400b041510000b01c85003001a04e1310b4116010901a0003484402501800c0400000c5225100d0200e0300961300c40903507130115102d0721042170005501c284034803070b907112341560001c02c0001c1c0350400494050340b1030380c40704094540c680d90381019210900380c0d10000c40e4035040180419603000828034a2003140800c0541851a0540d01611292243d905c20303005180c00604032050100032190744007100f074041c3c000c8002183c0c42c24561032503005404111201c2c0700c0000803c0c00000009290700640e50802d4800000b0391840e42000301512281c041210301d83c0c0e00b03001031a40b0380000e1000d056040d40c04000441c0c1120103204100132038074100c1c5500140011 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 774043363 1250 774042113 774042127
    0xc0a080105030615060a09080102072003011e0c0c1208010e0c0405130507020f0a060603111503150118120308060625020609040507050d0e07120b06040b0a0f050312 72
    0x40b40c1c2c4840304c0358002c0d1001a9103d164076001c031800c01d865003141106600024450040005404404000300b587c121901c5011900c90200f40c2610a9940d400b41d8410290802d03142800465001301e80c0649942042111122180d407100c018800107020b00c0003142d440001082018003c10324242e10081c1040d51501c0c00b420440000d142c04903c503001040e079651007000881c018000c014000c401155401290721038101c510700314024200c50b0004480c50301000289401c14103041d03660041c41c082000702d44d400d5588850800c504008040c150604010007810282c1403022140c2e001c0024014210381080106402d040c040d150520181002e8094441006400e40c0941011004000340b09820101c0014110900006280f400b4052050750700034074090a0011f030b43d8110000b0701c00c802c1044414000d001c100d00155803240064840d0307200c140d00d108d42804c0010701503280164000b4004000240c00d64503080407800e560303155000800c003103000c50814401854200066030388804490031803864411 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 774044613 1250 774043363 774043381
    0x6010803041d13051e10020307020706050c0106091b020613081e0408010e0625021b0103140103050601090b120a03110a060218011e021e150c0a0801050306 68
    0x940d52007628502c8601e04040780b041c0b80000d4001c0806504241128602d41c4468001218200b00f10402d841903c80c000301d20006514500940384990f107260050711545213842c01c00d8031307a41c1c0003440f000b94956803180e002c40c103100c4a204140300400302220b8050000c4040c0b80c040d192140160082242c00b808107220b03400076091008480280c1c2500742c0c102c0e40740a1103038484003d40210b8000035559400d1030b54400f007003400000c0040c462090070000d403140c06500d54000e482000d030307492000011303003200c1e040c8135a2080a240404d40d840c07040c5400140007001c7d520201e0318150a0b0800c45544e04a030004120140650040c0303801114226000001c3c001c5a40010381d03142d0748200020103104818102c5070000c081485804030b0b0b40e401001c10356542400904070080d2920488103580816051415072154611640e40b1482a4840b41c00030b00514020f803a000800c0c480c07401d50300c199841102e20700202103c819640602800c41940321a407140c800c03c0c005495164142c03c5280240d00441c2003180c441 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 774045863 1250 774044613 774044639
    0x1e04032303040f021003091e031e02030f03061507050109020306011a04090504110901090903091703090114520f02010c0209011806140d061107021c050601080304 71
    0x82d034105d030034501c05030800340158003400c4003042c003420f4100c28101031003544003140091b5140e1031190792a0300c8010f10313120440300c8007a180b040600040e481403001c0401036802d100116003003403006104040341e0300007502081d401e500071201180c15075160403151007142001c02c102405001b40280c00d034103040d0f144681440754069031050070255a20b4601040a00440101060f201070014040790015a142e400280140116420460016020003030016074004002c07038109800b1550f0008d9072034203010030011581042003103140884c8000c100203407450084040708621001500241d04031800190240821500700080c03c400a80090000040041000c1c005591203003503101c50310000003440da0004a030507103a03003400203410010200011600c103007040010701c01900040000c1c81250b441c0c003201c1d0601100c2d000455040700300006002e0020707401d13400205000410f152450700b01341c1c482d00001c4a0036100c0c1c802c0e40643c0360083c0500c0500100b440014003503c180001036182528020a40d0300b00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 774047113 1250 774045863 774045893
    0xa0e1002162c13020a1d010509040209151f0e01110a03091e09050c07020405090f0c0f150d1d0604020d1104021c050a0c1d01081e0403230304 62
    0x58022000058091202c0e038071038501c0c3c20f40190503c00c0c0b0344e480d58540c110031000340804081d09010440002498a040d61a0520440c0c1c040d1035880191511048042031031150703101e840c2d104034410200d6070b0442c0070b07106840903041c0e40d5071203401070085035002600a038007009404d50075030015104100400e81000c5960221240703400054100c440e081449203402c0b0803500318418142c00d100078031100d03c0d03005c8003410505008a904001c01d860300f071000356070703904405810f00c07003600542c081044500d040060303d01d00d160003070312044c626094800d0a00301c0354084000c0601c11581c0c0c070304150b111071001408a0812003142c004140505087c0c0000b0ba400381c082d03000600300c02c1c0d0343c0c103107c4654440d0b40655041d61141041c0c0113241e100341402d1409400304460216400e840e20281c0d940940c0b19204120011500c0e290750320804c0801c200444040c607004000403040f40d150b04410b10a00c60404d001e52085003e59181c000307058a80400700482815044281008007080c0240408901e4207007540c041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 774048363 1250 774047113 774047189
    0x40b1005040512062e03050a030e012601050f0d0b0a0c1b200402040902161704060c02210a030e18010b09040b030106090c0c02040c11060406020a0e100216 68
    0x141c00d1041490305c4440490303000148540a090486410035810110f40000007500341c94039044080b0070031114184a1060202051441c01d820042000b81401e04002c0c0784000060081d030151a003540b29907401030f01c1030300c07502e0080d540d0794580403580fa4040055244c800315503850042400c0503803224501e03604000a000003050844000c0c401c1c41e1f40340e0341220010503031101c0540d1240002c4505244441c1daa1000b6034880b00c003005956000d000540c116420344103d6202c0c0400d80c03000b50242f000c0381c9030114401200728480185020005400c216001c13507030780b090340c81000003c04503041c8486045151114112020040c0041c40308540c1c3c6410f9484400e415240060500407010029024040d5944802000c0b4a0500d008000544c0582d50003181c9000307440034001006d40342401c607a404c41c2240e08945541100001c10f0026034a40c00034201c400480c603040a505481d5000150031303c402d00d11010140e446080442e0350580e48801800081c034007004844040041c20a200300251080c50031000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 774049613 1250 774048363 774048421
    0x503060120150411090108190f06020f040b04150e150309070b180a17120c03040503030d0504110a05061b10020a0f0206010803030114090402040b100504051206 70
    0x4009408102400d6800c0d04010711824074249404c007202481184c2c202e290082d003e6500104007800005110098801419400d100200c000d07150b010044100c00c200b2108141c0070405460104290303000340000e08001422607988510f00100c412141072400c0c2640240400903084038265a9014001ca503101c1000b490903540759202070529041080b107400c4002d060700c2c00728400001e45052000034044601c241c400030102c1e1f8940500c0b600c004440703078060281e940610a41a0030710840300207004110010f0b000ca03030030130340c807880000c0c1150081c81000580a50b524104414040c4601c1d041c4031031603007a240c00070080e0070140440c4103441240e418440e02605a140880d05070700811040c00291401e03c0d0454444411500040690760b20101c01c1e0018440c0ca80007007129035011040742d048034002c40c00d0f21503141d292410b01180c4100180180d0340655102840c0700d09403989181182d0007089a69560b03906c508050400c20f5174603c09240a0703641c1d11000400c141d03040d4901100e0801d9842c00e80b281c03 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 774050863 1250 774049613 774049667
    0x90507020307050604060e07090204032102100e101d06061c02030a0c030204150b0904090602040504090b0603160e060409060e120d06060309111207090e0312060105030601 75
    0x1914502c140040100148508030410043c003095501c62004415840241c1d42040c2c0c3d42c1089400340e01a074000030b41122840e04c183d601b090601b00070b10756075588c54015200b8444482d000282126017a00e00121a03410881314182c1c5203105215030294140c540720b42c00303c0c034801c0160190341c40100404c2680103171030340d01d120050040d881841904955000f41241d481341c0702880d1007400500c851004a00a40c20501ca05c1001196002c103141a03036148072050b070512154070304005c06450f650384243d80d0036501b000085115100d60168071000c50050030300303140700d08180c814540303803041d17224400b000b000b8080300a010020f404a02c1540151044078041400302003410001c0040030101000c0c40588520541403102d8803002d00a04036010041d030080011b9507842e1820381c1a141101d80050040340c10122030000c5141c01c2c07000b00c84030500503080351400f0391150503800032200c1050207000a40e201003603400c480210411302e542c0c01102031800782c0c21030810400103405002c10081044004059a02003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 774052113 1250 774050863 774050867
    0x100c0f0308060121090614040b0408030c04180509100e1504020a090504380105040203100906060504050306010909020105030115120c030b120c031b040b190f0603050907090507 77
    0x2030700d04401807440c0e101514182813011004240c410000c580c264141a80e90380c548802c1558107102d0f1b90410807001507607039617a031050308542c40107000010101c0d0070704c000300b82554102c5000c020700748101e40015080c10702170f40881c54081858044158141059a01d0440b18008a41000c1035200100540070a460360b20010b0307907640711604505103041c03030300d001c01052041e003841811210240707404600b4030091884501011001010581c50711094ac8070040005007000d50041d40d00c1885c000780f901c07a194451402c1002d0750f40c542d0110b0005080890b090207185418001a40140503281041001104950018000b408144074010300c0740300220b10760107210301516403011101c2400c2e00801c00b208441001900800386042c7e42401032003010400700c00d81900281c20720b56800010018a041d180c1003008042115141d20306075005a00c41086000644036420790381c1ca0003c030f030040c82481034100094409110940d500c1107080500340001c1c04042200030039200181c039512903021440382d07504982 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 774053363 1250 774052113 774052127
    0x5040c06410d11031815010314010e0d0e10091202122e06080613060209032803141905090a0e040b0402040513050322080307060b100c0f03080601 64
    0x702c191400c2032030004825058000840c410070226040c0041103840c0e02c801551a48880c500b0784007240283d00500119288240f014546004034001040c1c104500c0051414001020008001300f0341c2c85408081615000108a40f0340c503851515040c25803a1131100c12042e28400d070041d02a8052030400c0c0342c45001401354260361000c003440d001d8007503c03215a0f1030032040d03844001c00c0c2c02840d00d00c01147c40100813270340718080d804160407000145460b444000003948200c03a103507814815a40030f48951052442d661501403a40040c8210f10000c038200600550441028081032560400162621811100400301d940d255882c0443d2034582c0c601c00300b101c4c441c45420070104107884404000c200300401c0c144d148038500c2954180800d40703800349000700710f08800c1c8001300560000c0c0042d48066004e50415040c1d2540ac8104004007079841c9442c50a6900143e02a503101d91a00c40d41000b41c180850700300c00c4e4944034a400866107034261200100090900c034000d007001264004605546e1103410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 774054613 1250 774053363 774053377
    0xe06090111070602074106090d03081006020601060c03180506041e090b01090902181f0e01020a02101b05190b0c0f1b0f0105040c0641 59
    0x812180c2c699200c010296441c0d8481c80351344483c0303402880c6215002250815001480d0401d100c000841138003003140c070780210860711415005141070003c3d0396a0f54811b0403840602c0d00940b00c2c507500381403401c070325000038850f900b01d4401d640c84500100700340c17548841d840300d4840e003518102c03030b0596111014500c2c0302041d078070890b44130070041004500350424049807040407088480c3ca00000d036880c05030606840744030280501203036142c182081509400e070014032075050000e24407118a00448001950b88070b5622409540c0b1410a00450309283c0000d0301d049156401d0004200c02a0755600250541013050107035002c0103806101c0d2809206d013150700340c2c150b903032000c143c0f07504803d88c0146c400c5074454250261030b440401004074092001c01c100f00c81c103254171481210724000222000b0110a40d4524410400e40700b20b002c02419440203220b03c0e80a00d01c601d546000840c5407020003000c001d081040d40700f1000d10050880002010321325100589160151400840c807804d040192080c09114 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 774055863 1250 774054613 774054647
    0xb0310050901060f0f0215010603020a020c031e07090207170a0c0507080609011104080a1407091401050f010806030d11070e01090e0f030703020303071404030501020c060403080a0c0e060901 83
    0x4030303c0580000c800b02001e030296445c80806903030110202d1b640c0d80700c0d034120b031501007a000041c8030407482600245280d4481e401141c04001c0b0aa0210303142045811001d10000c15509011316003a0090040744020700f0003400c29800c12205441e00708039000c4106001d003402200081d0862524026280b003a0480c0c3c102c410b132042c1d075641e0960f40707403518812030300b03c090340d46407000f61a050030481c400c0e0b8040d0307910f000c010544c841031a40c80281412000c103a088a520407004d001070043d00c0b034001d011072051700d07198040840d4902018440c04001101c0081d0502c43c2c61001c100c5540c0740018601420700a600c1c0050102980000603400c2c500b040c0c01c00c0c0c103102101c0002103242900c0ea041407800102c002c040b55121028119000c1d00c034040c071200280180c0003000802c4036107200c8c1a0150f10788000d01c903494a81507032a60303014226032024030400c403e50000001c00c82030540110032240c1c4924140c20600020504010081034503810b44101751080f40301103032070400c1d640703c2d0440c03908842c004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 774057113 1250 774055863 774055879
    0x6050303070b060a06022b020309092d01050603041704091503021503010b0417031c0e0d09151214180c030d171f120c05090405070b031005 61
    0x7038244089030720011510f480c01a0700596001640c18030008102c0c3c08129a89101c400400003500c400414032040c11550b4210722040c48070030701994482e00f546003d4000c001c44071030703815130541d41d1010b40d40389588040e4040c9000001001f140d16200d00b1241d111743c2c04085140c000b01e2017042e488042c000c54000e4a01a450540140c003001010b0001c141a280211001c0380408070202203423107548024060714014140610080200c1c028040003c0241c4000f1003d403802e0201482403240c811035401110188545c803011203507004107060001c004d0054980c42e11034126800c00e61013a15010160340d181040041042000f400d0482a038800264118040d003a480320b07091000d084800c010f94000c10300c900317001c1c0710400b040b90710b40041d00070b01c000c03500c1d280d6a041c28202200c0710260b9200400d1b001d20b030005803101c510301c0e040c41c00516014204820300c44a00940d030341404122030105e500003500583d6801d040c080403403030004400003296001006140c0c1c0303590b400c0501c00300b5500c03540520b0b0800e0203 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 774058363 1250 774057113 774057127
    0xa030b040906050106030b0901090902030a03081b0d091104091e0602040e091e0a0308060904020319080c07050102011a06031801060b0711060921011103010e040227061306050303 78
    0xc187c00c40d02203203404462124491f42c8980a4100f200d5440d80000d50551001b00301c003001034091039426900450119414058000001035048290b100350b10341c108407903441c1640010000142e4212448074810780e02000841160350720b120055802c582c00d103074480c0307426034068100200758040b6070140040c0c0f00c040e5900c0c1092000b00d41d50300301510800042a00407000300d040c03070780002070720345400d9010760f2030140903281c680501000010180c026a01805540040d6031130600f8070a503014024418541d0966840d40150710034200441c03074000c03604590600080d0112801c41050540ba03a80040b07070415176076100ca102e4415144140d103c0340d03951f5402c00c40c0c0003411800c4034020740b24503805414108018170402c3c0070080ea61051551040e8080001d04180d41141d00015101118207a910000a21030f1801411041150004d07400000007107103400801007141803203c101c01030740b83c640707101e0100200220645c850f54a401851075001d0400d05000322103c040300d800c0180140405015269142b031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 774059613 1250 774058363 774058367
    0x1080403030203280c0801060503040c1202041b090302040c0207061d010302091909050c070f0f1506030c080705191a0d09030c060e070b0f1309060602151b0a030b040906050106 77
    0x405640885d0100f003000340005132090080d0101e03407155600582207480d050038900d815207e005e80d0b10007aa0400c1c1e548071680d0441100d031105814644207611800106840e610403c829640c42c82072010841d0008541044240e4101c46101d05911044210340085101000101c0090103640c484a87c415003001954140d0380c5120071201c15644940c03024405560b42103c50308191051900c0185505052000c440114000103489103c5911a48038100240318901c00c0c00151001da0b001580c20490142007000006001c00c0090000c142c1542e9680340e05688801d440601ea9442c4981004040d90b0181c0c450581c8030f4408580185812520811a1500c0740c180203203441202c480c1210911726003600041c20500000b40030080340c01c000105407505143d5080000c03203070070595100261010f047c20202e2102d55030301821010f04078660040c15141c40ba007025000400c1c0240c440c01e44044800c0e0800e01494140c1b04031071202039242400328098100c000400d0040c0702c105001307400186460b001103900b507 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 774060863 1250 774059613 774059621
    0x20f101805070605070c060c030c120e0423010915150203120106050c0c030a150b0a0e1501120b030606010f1107180b0901181104410108040303020328 66
    0x5001d8494000c045454420680d042c452230440074000c195a415400300007121000e52800e02d4103e4541200c00020500c00f080c00e40d0f5261301200e40c40d540e208031184150084c1c2c1d4496004002d940410301203019050304201100e440f50040da0f840000702903201802900800c1110440e0500070f180b4002e541e90348100070b11580140c0c082e0405406590075440c071a1500080d88005542c00403100015412110591801841107041c11500a44900300025507201021a448d00c5058413640c1c9003803450415000400d01e01003105010035461416100c0c0354a42c50014040781c1c881c81c00e0800003107004803042e041d0344080100014000320300c01c20340c02180b0650328a290544a0002c204244005541001000f491082c00d00410b541c0c1058151041d10081ca203402c0410200803144059260035158101d2582d006048105821290360000011100d441007164100303641944605102c00702488030f0001709206d0024001070201a004030100700c0e032540300d4901d106110146460860004c00009521003d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 774062113 1250 774060863 774060877
    0x303120a05061507031409210a0b01121203020d0902040504060b0a0b0a050f0906070b01060f12060e180f010905100c08070c120905130219020f101805070605 69
    0x81c50790b0281c488103d481031020b855007030794580c946284280c070070524032042c0d401c080c0311540d005942c0c1e81c0f10000c1503010500b03007102042c4800941303484401340c10074000164060380701081c00c65074031203100085058071119100d002030354a000750b5104856100c0c040a4018184060350043c508030038401080481d502040900d4010381e0389001031640c0c0c03002c0500d1802040130210105104001030144280074600400030241300528050500d806a140c48444000980104000c42d03c40640d040502e50007d0001c0f02d010381c0d4041c10701c4482d050124900811101070104101d2103180070000d82c555405108000000003990000c0111040328100f01d903681c0765514021103c0340c17a1182d40002144680c510a20401c440d0310355003200009556050b0740351110f4403410080244000300071903540d4940f40a0b0009600200003d0b0300c40310346e070b1903842441755040000801d41d03001e1345a103201b000b00031502c1e2001a0810300006490242c8031340b4202d8440141c20014450b014445001c614207410002070100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 774063363 1250 774062113 774062119
    0x3020a0c080c0a0b0c270604030c06080f090106060906030b13150603050f1b1c0f060302010e0a1a070203010e0d03020a1205091002030403170901020d0e01140103110303120a0506 78
    0x1041e11503401c580d01c180f05041800c02c4101d400103c14650303500c01000800300310f50180c10740785865a00cad1140240d1601c0c94121400080030981407040d03040c410304c96590801405002000098039100028011140b40c0c0702d41c500b8561109084480b5907207010742050b00a00031344040c42492a40c0c0302c441c04451031401180c4c003092601c070200300d101013140a29403040d4011448440b0603030581c0503140460304402102c400701003446c1910201c00b038081c060321580421100d00852980e05520016100d030031031994840c019102e0807410040303400c4000b070241340d07000810102ca55601860020030701500e51001409890f00c144000303006c1e15507055000307005815590fa80d075448201d48900d441c080e11340680e1400a02d50020b941880f9460b0203074001d5800c06d10034101031180190b403032046030ba00d040c00c59030000607940c041008101000c0b503004494032030b01c00c0d00007044600e40740e0042040200c1c040c00041d040701c0c80f500d07c1c0c05030358030100b013180e804018046680310b007407505488040240204442d0b841c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 774064613 1250 774063363 774063383
    0x6050c1b010e01110f0a2304030c0e090d1e0c02030109050705010e060403050706030f1d06070809070609031104060302150309070e0f190b06210c030903040603020a0c080c0a 76
    0xb50200400c0507690448041c0c17980170714220341d03548110307081107607040c1c1c0c0285925240c4000c006581c441c0b0080005500c915500400589044001c910301c00004050400f51342080c151801410341c0005e00c41d01a030b216035030400d41c7d41c0b05c2910491f00d401b421400250990b180680d044107100c4002081001c541c030903600c00007544050302c207126580c01244402007142c0d02201050114500a400c0400300485041c80000c00f03829406030020208411304200f000b640101052000311984070100c2913100c48004d00030310349d043c07408400800100c0c0c2031001600a081220070003a4a540300c0d0005401141c00611240e400c02491070a000c055005480003500d034454510009481d40c00034400da440b0301c4552500508581d1013201c031141c030318100d000d0304100c0e50b03a804c0c540b0700c51341d80d29004d070103408c848145141c2d8034011040c455501050190600184100034800c1112000d000000c68007650031603c1c0240c0c80e242c0f980070907544000d6032a0020440e8070045100a8040e50002c0c2159109015200c151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 774065863 1250 774064613 774064631
    0x3010f050f0c040506040b0d11040909050f210306060403050106080f1908040315090210050909100807030305071b0603230609010b07020a08060c03040201020d020d050706050c1b010e01 81
    0xb45244502d00c62a43c1111042c0010421900c62001502000c10403207404141e0135055826030b0f51903030060b0040205217985000280500c0810021042541002e90050861180c1c95940da10914524030300401620400400203849840381815540219403000003845056112803c0985400441d002100315100d410080300d81550404c00b02d002407038000e506c0c185003a0854450303011480c1001c5080c0710340d580740c9124200603201da6409008200d001e03590551601c0540003000b8001c0da000d4900d200a800e0b003c414081c088022603c802121707410704103c0e40e252001d142c00030a84091a400c500c0c103d8a000c0b0000b1080d400d5000b41c600c90400091002014212242c0a007603402c043d503c4d550000301420060025600300341c01802498002024000650f40c0d03281040c1c41e01c002160050840d500100c2808111358040204034130b000900d0002e8011104a86401003081c0145000988800d490308c01290820000d0400c545058003d07071080002044007035604c0703020305801c0c9100351b45586043c0c111 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 774067113 1250 774065863 774065881
    0x1803090a090608331f091a03030c0d0c03020703061803080108010203161d0301240e160509010e0603100e090c01120b0301110d1505060f19050903010f050f 68
    0x204924011000c03070554000344000355200e007100300030003902c034031403000f80003c850700b1440800340024008050b011420310042541c1c0901d02d070301344c41f45a000307078402c2c4900001c0746008500712141491515260307100100d1420100d00d0030003254809403400e450b2011070f40b11005000c502d080740034029250303605181d0b1b03155286801c030f100c110380e010001c03140c0481c9440d9051051604a00391014001c0401118200000081c212562030415218804003080805020300600207000010580900014074900d480c0c2250445141184040c0040010001c3c09219503805014000514071010b01840d88038600403200440c038804034012800b0382c080e5000058016000021420080c0c0810b0b5a400d03003200e141041c600180c05e1a5a03d5689035480d62902c00c500a0540050840c0250045020820000c007545107412a903194108500a1b042040b00e0040c8502d541704540194050508100d2001c034118021541030040700e008903815400c0803800d081e8000719800c654000d80c041002c45825071030340340741 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 774068363 1250 774067113 774067153
    0x12080103200103020c0d1e0c031211070b04080a02061006050a0305090304050312190f05091c1203140c041d090106150c05010b01080606031803090a090608 68
    0x1010140214895564000c0d90301d5000e565003010304000d420542182c0d1990b040400752000c85000685a4001b211402c0104522003800112420407a805044944008106c50003c03042c00c1015522450307504048403030342c41103c4032190009003500180c1001d15104050f5804240d80a005120700d0000c500c240b0b5035105002c048680c079880d840e1400c1c1540717800b54050030b0300410441d0030b400140000603054809000101c071114021100c00d40c0c4850120a415254034080c10110810138480c000e5146150400c04445c004202111740e01c1d14000100c62141034a6041c440042207406200c40c0601d4643d00340d00441c02c50404040480c5456580307841e19480c1b4040e510418042411043d800700c2e07154a21440103420500c4840046000c0d0b850300300d403502c07400d052a980000204044100414460f0a106030318440d80c1c03d10300717140a4246400000c000340000f90040c0d1040410031012071810070200121031810b076028010140307140e40c4050b480010140383c86100c0742d81c00707102c0c80448d00030a1005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 774069613 1250 774068363 774068369
    0x10302130e03030a1805012309010608030403020130050a06051807030e0a0f0b0709050102010504020d12051b01050609011d130309120b19090503090f1906030207120801 74
    0x1c0190309550f649803d404c003a105640d04122100c0a801200d00410310a001e00c10710403001213204031840d502055600d041c807100405104aa9140c001c060025000100413103040300d0302441c00700480601c0356806600007003002000d408c100b01c43c103c040700c64034854000911900c44000c0030410a07507120207100d12104401554040c80201d000050580b034000d42c898010100b60008607605520b5542d41d4601a00140c0002c0e124030740c0035000c0089042d4841c19600c003900b8284000d112a041c41d40c041307040144a00300082000300f038025009007131407089040e5441c01c401000b01e00a129418800c6070f00030b14090f41c5580c003428994001040e0795000080e070f03140d10002484030b641c581d40c80c4141c403820b111000908404014034a0400148611004482c2c14928051502810b150030040048032150740008841c0b802c0600b4044900003084c2c005c001d2ba0341c0c90b501940e1100d202440c001c0020980701a9024900480200b00000708910b6415405040c0c000d03c02c90745c240b0020641407080e07035550300900c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 774070863 1250 774069613 774069641
    0x90b0604090504081303050c0a1a19031517010605010c0f081806030403030518073212160b090913051c0e1305011d1005060a0801030213 60
    0x220410031501c481e80031a90181c001c5540b5410440d40f2507411495800ea80c3c000d0b143c07580311801c0100c681c98061440c0c0c00800e0352003060945035521800090183c01085d807801d1109076040400d89109000c2d03007066032090445a121400d65444100c0c199511100d00740c2c0901d030f90700e000da000c40c265001c0d071005100ea40e017203211b200c8040100e981d01400c3c2c0d4081c2c030700c900c1c4661500c030048074252908005540903a100380c40c04a102c0c941041c070524180d005130104442a80a0101007141c040c10404c0d1250421048244885e046107503401c0d01503485101201c035400c080c0502450322594001309840034074127000101c03491030381c0c0e035201e084105005d020407003a4007882d407502260300420b02c000200c3c203080c07007241904c0c40d01c100000c019480c001208c54503400b15072040300c00d256074a0700a80c202088a540384040180b0b504100814058030b8044201da2801034421001c21b00c0000d615000390010600100016501d100281000b40034180a01c0228000c003007451001901d68400c5c000c3ca02000510 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 774072113 1250 774070863 774070867
    0x9171e03160f15090b0420010813030c0507060306150216051219081c05150f0604090e0709180209222f0a0e0f2508010609090b06 57
    0x580c54582d410203441c030302214030001c140107803840c1c80380c1d5000d800301142c01114808464542070904085540070391131482e40c404841d00201100741c1c3c10403c070942042d0800045da101d000d4a11b81540c104006020203003203441021000113025503d41c016500f524651500100030078403a4000381d03a03c0f0610b01005200c40c047d20340c03c3c0641e0804001c1d11214680100448501c19010500d4080c0145544010340d46c02d4000035113032044139034036022008459820b9104100d070703103454242921007088424400c1d2241d10640ca00c020681d5840381a03c0103840719142c200401d2811008a583d10a40e074452058003d0070b03e046c0303081e0b10f0100c00c2c00d4000c00d038003c0e041036041c1d0381c3c0d0100354040c81480f1a845c014815920f440d03002103514003102c1c00c0c00e144d0182c095001141c040d141010308500d00117904d4441d402c0a0000d00010391400c00d030a42104100d41103028a0f2206001c204500c45003039100d010464900151591a65200e03d00034102c500c207882c6c103079000e5107a80e000402e071800d802c403844c4c0060007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 774073363 1250 774072113 774072157
    0x1050103301209060b040c120c090e0406051e09060604111611040f02040b041e0302211c0c0c05031b010c140a0b01030605150d1209171e03 61
    0x1143c20215406120b820000303400d8054000080454404c1a049000a10b095686100075450391040603004109400d002c0000b91400b504a1800400140001c128a885401241c0034001402e202400303030040340010030341c0d45001d2100e142c1c0c031481154100d105070704010b8188000c10704041111461781c00d42c1c0100080b13505039141c142880010000403a003046c0da480041c492074a4500c05032002d0102c214813542c1e0382c2c1c41c1071100c03034030003028801030800c01c1c0c0c10000030401603617502d141c09880b5404107255100700006100f807608000840320308088480102444502080d80074010314030280c420741c40e01c1246512801490390390107008400030314003804550402850742c044c6054004540c410580501c110030940e04041c100343e00f124040310300030000001441088194042d142d40140240041a41100765000050003070080f000d015200c6c8640c28040341009110700102c03806402d0814501c2c410722041c035100d5030342c0d8584a03000560881c407141590b02400c408000c503000c0040840d260180510 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 774074613 1250 774073363 774073397
    0x6060504051005160c30031b111f020124030308040305130306090b0f060319081308010501150201020a0827010c211a010e0109090e0c0a1202100806030c030105010330 73
    0xa01400c081d2191a9127030090042035880c0d824096081d05450701e542400344101c0740190030b498101d01d044400c060fa000c01c04134804008080241102d0b0586010072041d121824203032a103100f00804000c040d1800540030062221680040341c03100d10481442c2e0f0250380341c04e05c2141c496006e484055054100300700d400c2901c00e130300b461681020700642d181c40c41c1440420360462002c0ea41da12002c074994480c4010098401e468442c0b02e8000c000780001d42c501021800c0081c41000000c0032a10240c94071005a6001c0c948a07000f010307a015064002c00c41c80d9010b030710183c90303d20601c0340d0091540040b484012030740114002d00401e400302d100140d4268501d6001901e05c02c4032078500a04004240500042c54841c50040c056081c0044001c0c219141003042030003005074003034120503401069030726040016180d050321180210081e00e042c446a44039040028140061a42d030f0607455801e00001005002a030303010000d2160301100b000140c0d8054101c8100d1140050760940c01180d062100025050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 774075863 1250 774074613 774074657
    0x40f0e040b0a15120b09070b040e010308031312030b030c040b090115260103020f04023108010c08150a030201080c0304150501030b0a06060504051005160c3003 70
    0x810303c40362001460301e0328070100301154000000ea510102030b10038004954000c2c8940006055002606860941442540c0c115810180301c014400b030310000010b0386250104050304007540d03004e521203044010004006016002108911f0700c41e02552407054000d00d000e114411200e03802a10948040e0300e4804060521680c1000c40824012503100c13880c0c01003540702000504c4403094518010325411401407103480142103114901031881004a52071041d050300075180450102d003064000b01c0d11060101034089410f41c08840258240034031000c49036003184120344600e400111558251911070b04216010005c1e200190201d1080c06c003066540856a006603030090080d40200d0800c040215410300301e4000364401d844802411013445020303801030103044c000f080c6520708a820b00d4180400148180c040d9680790f014010700040e1194804e102043c400f0459800118100e40c0503a24030901450a4102d51805131071040c440403040d89034402d06881e010950141c0d903202d0590039805030b4074a10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 774077113 1250 774075863 774075881
    0x5040e031308060907122d02062a070b120705120103200301090c060e0409151b0201020408030d054b01030b0615120c040f0e040b0a 58
    0x1800308015a2188428801041000300140d10003804207141c004559410300d11560000741d448240207a000001c181c0c2c03c00060324030b0800c0509146070842c0903c00c02c070042540a0300a410140c01301c2c10300428800c60800c1190150f0944400f83c0c480c00708060301d506d40740c9501444544000074081025085401c0365941d9004031242001450008002c40014081070241c2c01121400540080500f40a0f075a401540d048101030303001340828182c039070301c0c102e0014950040f1020840c00808040e4165510b4120340c0701d107500a40352a4121b85108810000f504005e44c0494590029030303000c6041300c0c414806c81d400c4603940800345041ca105040460040c0c40d011380860b0440e40201c2002c4c81d103170b600c0d003882541c03466900141045055044081c9001c001c018403001425040140100042401000010b07888282240c03141081e08506d5904509409481d410b07806002a05080000041011006005481021150b510541d40c0d0390382c881600d0504803401001c0d09905004503212062030342281c100c0b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 774078363 1250 774077113 774077141
    0xc0711060f04090204260c0909030f180a06020a05030901050304060902031b0f030c01080f040201021c09180c0e010c0204110a05070605090a021e031c03020a080610090504 75
    0x2078020003401d00c5001e5000398002412943c0e00180820101a01606582c0b5103140f81024001c031588620205e515100a401c1c164000c007512400039086c50014000c8070f51101030f0301c1003035884688040310f441030300c2920502180210301808003c03901c81d000140b601c2c09640d00800540c9404990401100c590b000039008a95554542c4514001030380d0038410400000840200140c86041c4030b1b04100d2120a90240789020b90071081c2000d2007a40c0c07018259038040b140300b8100c5031588861004034a40700c0815142a4904a0402ca1460003a0310400c044100d9503030600a9260005120f01d5204175070113000b900010460741d680060103540a00f002000240c00103000180c51b001350b61001340300e54840c2c13440c64000360000980310108040703031060384d030030003803031801400485c0c0c0c103070301003200c948034a005045e0b100c0d0f40c024480801d917410001180214810304000d120345c0d90f5614050040d400c492003070400318003400300041c507504141541da000116a503449011284ca02030500c802020123080e4121 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 774079613 1250 774078363 774078367
    0x307090b032e140f1005031005130b010f0e1005011d03070b0a02030c010f0e0a02061806070b0603010b03010507080106030c0207050316360f0b040e0606180c071106 72
    0x300c2642e892007490b1112071004020546894404c00d04c0480f40c800900921403113500c09802d000350344001680b100002c0300b00d58006503d0b00c8803040d40d0340301100840020041d8a13480004200c1020564090f000c80c1c5001e44080120b8a40800b0080c8004a502429001852819000b00d644403040111405c1c17050140655905a0310360002c2c8019601030030110740942d0ec00240c80031000000d21400904400b61442000041c0182c03859548906164401a11403034001c519030b4440500d02242d140d402c2c3c00280416510310f0145800f901442046406138425440d2542444203030906004d068413a550300e9851010f2682410000c0d0010151000154214401c0000116039500c0400048044244c0d4440800f100381c60150208030408180143c0055644009200d0710b0081ea480d00407102c1000d5220003107004018182c0035030052a584110baa402800e1400740c00700f10354003081c0c0301c0c00b844003590350040c090000540f0342039494003510070144201c0104418804280c8240384400c0c014401041d2078 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 774080863 1250 774079613 774079693
    0x40503281217090606032b080924070806030d080106050a030b03160e071d1507020409030309050f0706050f07110a080601060914130c120609020304020307090b03 71
    0x866a00b00484001c04035a008205024080c83c0421a00100701c00f4864040c1d520b141004202c0c030050040011241441901d4000c18802d038000d1210080c2046003824000701f09000814401e9500f40c1540c0301c20201d49442e01185250030040f1300001c151001e5100c0d0555070346801000c82d80703580051410f0742055503440c501c8006a50034400040091069180d1100203030401c11001040c28010b4164401d02002c181b00701c624008800c0d40000340c6200701c40c1d18074100f4907207449803168800c0d014000e42c000e00e04a00c9204040e019400001d42900490881e00c081c4a205515580c035060390141c10302041d024044800c2d04102d1138000c0140903c140c45205005400501141590031503410160341a008540144106944880150300070104080302046903003400012802628010b80401340b407075290f40f10807000a008403013104007070140700c40c1040003eaa5081150094009540803842401410700000301039480d80030f0b074040407100a002d40311780510707900315401c0d0301c0c0004188001089064545 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 774082113 1250 774080863 774080897
    0x30c021c050604060c02210705030d180c06050f0912030708030f0414012309070b0406020a1511030f180d0305061f08191806020405032812 61
    0x1140c003261140d002050282464588001500e550f100311000b150300080d002400f44603540c400303030300e08440c8401c2d01d540c0c1e045c1401e125041d48907015040e008182000503c05295034140441000207005900c0001c0480e25002c0442e0148034918a0799060002401909000d1030b121a910001c01d0420084a141402d95912419940c108a0348034122003a00da040000340040380d0306980c0d520140f403008100c88200100000095001c0e4001c10300e8081c01d001c0050703040d61040000d2409000341d010350b103803156a0380100a40d5181800400c072440b400002e960300390300b203250240d440500402e0030346501b150f45d803584089585d50000e1201000141400400f400d401c028016405034080390f036000302c0c0b036242044c18080f060006d00c0742c0d200003250700043c403010542e02c0103810f0f41040d41d000044081a0190500710301a00bd00141d1724002002250714000700480e0781d00400480d034040d002d450f010005107450702d1400c3c126404808002030b10702c03618800109100142d105ca00414204406041900421 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 774083363 1250 774082113 774082159
    0x20c0609031b06040201020714130e10060e06090105010c080409060f091116110a03170a020c0d08090f0402120a0b01030b030c01050d0c0c140c040c0507020d030c02 72
    0x32094581c1000450440d82c590108006000c918040014035440c10507a0000b59955214410300d490408010042c40a0350b8036250400c510000504041c0040d80554041c40c1d1118156208401d07050300d04440044e8010f86900207030320a8500034520788440e881d1400555241180d60030454600c6420400401c043e540c0e0700c207100180030443c1350740b143c071824a013562040303030b0761a140100304440030300c0403100c4072824081c0b00c001d2a6001c6d002031039a0f003824000c15440c0035141c0008203800c810003060b03001160020003500802c00581e088407041c42d404010b000c940c0c80d007900090510401040004031034102246100080c400c0501b00500d4400b08680c03818546405036910988151200c561f8031240da818003070245a4601100a800d40e0032810303002800910403107076445070b082d40b00d240403511240070f016182d031a26040342e951b02c0b0001100151540307603194850716900c0355207005402000944140d0640351256800340003071002a810380c03401d4a840000c040200d0340001c030403804903005006061 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 774084613 1250 774083363 774083371
    0x2180114010212190c05010b060403050a020a212a03140c040510140a0504020c0709051b122502070306110c0c013c080a060e0604020a0201020c06 64
    0x40c000c485020600009060031000031035541c0d03840090290f1250800140c0340544120440e050800440c82207151103070250603191400f40c1e000a0200b0000144a00403940c540303103600c00c4075038100103611251948480e40d400f04d003603a01c5a01150001c4000742c1c0d0400000482c81d050104d022205000041d00040101c40d50811540640d0300b860304101c00c1020800260b0400c0112418045850310300d4044001e220148030b1002c6142c020055021281c64281c0b00390084d040c00303802551b40b0f1940281c8155102d10503c1002900c038605400154442170020315603102601081d502450320000c8820781035910000b500d04003503c1c00340c080e107501c0b00610300c0c140710012072180c0241010a10b141010301c200da042d413082002c40301c010090f080240ca0082f54100030084242002c8902001e00380803050185191815170032200d1002400d801c007450041d0ba0809104215982c0c04516034401c200d400543c0e026101c2d83e5044c141d5880812568a80f50b0040c00024000e44001030504030200b14091034a80c09403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 774085863 1250 774084613 774084629
    0x180304050a03030f1214060607020a0914040c090903050306040b180a06061101060810110f1204020901051e0405090c030313090c05120f040c0510020114070201090308040f021801 78
    0x550307500c01c201c0d000114211483c5c0c264404200c08517803c1c10207141c00e540100582d10440300041e211b400c43d82e8421a90010b814a100100019850700c1004200800b05480981e00d071141c2c1c84001516403020b0154000081e40f5540b02401c40d100d00c1c05210280c015444255840782070507140008403038141403030070700c00c1c0b0000002181e11131500d200034203946181904030358180d060000600c480d050006450b5011403030940c001400740c000c00300307556442c051004840c08010340040c100c0122201c000d5854001c40c02102e020315541da1319000c000180355840840300503032440c1ea40c482441d19003a17200680c003001041c180d134041545080000d0460340047d0b02405c1d20980c01205119608451040381249085414418505622030f10a0b84000b20002c1c0000f0b082c0304181d000070204140d1440c00c50087c980030301071380604558207801070701a044400e41790503052504c49c0000c0400344140941001e903501526602c1d41d50b21541c0303c4c2485001c611034140d80000c00074500100010000461030300820401f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 774087113 1250 774085863 774085877
    0x4020f12100602070f0b03090312041406330a120803040c12050303010312021c0e10030b0d020d060b120d022a04181506060e0301020a08180304050a0303 67
    0x40c00044201d0840d5411080071903004800a0012500344441030041c1d512000d4550b4503503860784c1c6194038511401d065070010311085030038031007000310101025250b1000c1f041610800e41e0b642102c0c112540c50361002d101100c5c0c82000c0c440c0c1d030740628810b003150700e0005400b5260441d26481030000c03001c204d980c1218416400801c002c00e1120f800480e1016009400c5c040d13007146003503103c91380e80303000600001d400c0da00f18030008030415008100c080003d40910130080a000d8007040043c0000e140c100d03000d401049000001c0070028030030f1140e000050750003010801200d08640038010b40e200020b404880c415520000e00174a0381d82c10240c07940d0132440c0001002c1d6908403c10090a0400442000040c0000302c14442c2c0c0007041405c07801c070183c0703007030b5400540ca0300001807460310402c0d0b110014200019152a00005c010207400481c00c0d29001d80340c6040700c0584000781800c0f8850b0300c6a03400020041400306c0c480204801d4080000510071040f40d0529448000150a89149038000c401081c0d513 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 774088363 1250 774087113 774087121
    0x8071b1805010801092a0510030f18051911040509071a03062416150e0c09370b010f1b02060a090807181103130204050604020f12 57
    0x129009082c05070109200a0207081500d540e80341c9400401d190180011060100107210900b2003501903004040c000c001ca24400990301000c0c0080c44034001844040341441009410121003c2031054100d506c10014a40340dc503050501c22140107802007140e41c07880c003460050940d600d030b020f014054540741c5c018101491410b0441b400601804585808000d0280200002d56480c0c801c0402011010114a519840c00c0070072080a0322465506402d00362840c1030840c1800351311100e0914004c2d01c8082000340d0460003400315903406540901a034001c40c6207000600007194040881d150180c0b0081100b21148400e580c9110004107281000c80f40c4d03a0350b40b0000056a00860f0200040c076542403080c1500c1403080c044e0002c2541030b030082d0055078001070307046110f44200b01da076008094240581c2c03045904ca460301100b9003017071301907900764a052045108480440b00e013201c0c003d0480080740403005403160300b8031029000061185078010746c02e1202c503184810400080000004813941410701e4070f8 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 774089613 1250 774088363 774088409
    0x408010204060f0906210e0607020a030201050114061920010b100512070c170c1b04060803120901060b0f030a0e0708030702060306040612050f070603140408071b 71
    0x10480c4680403c40360030010040740d508071540c41d1440010908032080300c1d2603002c0882c00342140c1d87c0304251920031003003041249036001c51481d0403207110394002c2c041a6610181c4115504031988103542c00042008900043c100a405102c02240c541c102800c00880080f80d4081d41d10b504141c007841ca135103580d0003c460f41340c03842c4903d95030821030800768102500f0300c0c2d0034550b40c007004158409000c2260038100c1804140018a060109080101e5545000120003243c40da00c685101c0a60b01203d00f841042070316080c0140b0068482e241d0041d400d2a082d00682c90031000017130200c0c00f0955884602060307868540e002803040300542041d9542c1da0400099580c12100c1e0f40341d18560680044405000f8041e020080320b0300950102d0300b1940700d0301d565000a0081125600803030146149503144000c2210100e82d105c0c64104080540d256199104c405406032040211800300c68118000020001010180900710103809441c9101000c00d504061020701c10103034000352691498840e42503140a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 774090863 1250 774089613 774089627
    0x510030f1a161202390609030711010f051201030b150d030e010f0e061605060a050601140705010905011508010e03090307051c050709320f100b040801020406 69
    0x4070320b8400328000c4041c2200020001d15020010480e8590000b1303c11012850612441801d03030900c0242006241c0702c020341540e100b64948190519005420006c0d01401011080c0d034549908142072200e940311403401115003c0d1009400b005000040c810300c50b00c0b20050700914040d6124090800713090400041c000c542c8200303903048604c075a111090702030000b54487c144183d1080b00782460390001501e4003060307501070b02d400d1880313800c2007001c01d03041d500c04101542204418015401d4600e1501d0303103082142562400c03a14603000c6000321107603508081c0c4200007009407501400000544074810b030340700c5087d40c41b00304020b51200024081400280300a00c900c0c2e0107020402c00540c54121410b0200c2c0d10b83c00948a5280b1403000c003480c040740d074048230501d55229907010064030b0529465043c0e480090203550081e13812807400c4203000004034440c000d038050a5565070034420440c1c0d078003084007480e018028184d0b1024500020000344540080010344040c18048001589460420310024005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 774092113 1250 774090863 774090871
    0x5010606031a0a0b0a0207330c051504030e100e030c06041404050406060e0c070308130f020907030f06080a06050919111518040e1b040510030f1a 64
    0x2d5004660454425034070309100c0411140b40540f031035214840c1c408141e08100b142e07407000c0301400315402056100000707109a80e15012440d040c60700080c2c00540c08403844c010000d40105aa4495184148844040905560700bd8483d01c0d01c6030482d244903020880c10300700000e41e4408500081c3c07210980340b03014085a00241d0b03040d10428109032400e055a41041c03481071b45640641e944401160a03c1a150010400781920501d00030240c140703400d2008499200100170b5001550841c080360440b03c40100401c1019042091244046c8440d02003100f04840603201d442031695035240341090007a140164001000e082029180b810114140b032810303508028000107244d0800c0201000e40c10460a600800c00d4100b20501454000d000100744200481e44c0011490200031444c00c048801d0032045800950060701d00b07014082c98980382c0c66881031195009061040040000502405c00c0e60181d54800c2d681c94080b0310150750394488459107400d0740c1c130944000c0d224943c4001c0c0113030300005050300 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 774093363 1250 774092113 774092141
    0xa1d060412050709150311130204080715021204261905010b0a03170f041d061002060106080a0b0303090a060c0c120c060c11040e030414090c090f0315040501060603 72
    0x4400c10445d1005011121404003c0015103485641400c07600d80c604c032000c81500c40c480440d6100d0711803e88590354a0340c0d2054508a041d4890040741c4584045102422520800070150415050490608159042262051208020510300c401e50901004030070f4018032002044100307403103141451401d40d07006000360790140142400800004041c0310560112150070740c2d546840340c402e03241c0030f07030381d4441c170780c008001000105048101010020b030784c3c2d8000c100403943c2c92040703e50584241c0e1950400d104000104169900250540c0c1560304041c000460040603a40f4102101d00000c0755980590813840002e041509114100301c00e9016201c041c15260458650340c1e8110780e03c1c00e000c00094001c1c0010004400d41101c00c04c60342d03080c00c0ca450040100180b0115000034000d03641c9030424482c065410802ca140c0704038500749258103a004121070b000d610f243c01421000d01c0ba000c492008460740500c01e9001103c46001d101d00071038003461044c400400c6052420701c00038151150041c503044 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 774094613 1250 774093363 774093371
    0x9130501031101030207031209061406031605010503060a030f12080127021c1a09010f080709020a05070b0c0304060507030c0c12140a02060f09010e030a1d060412050709 74
    0x12484940418000b200b0034a805a90f42400d4071703045034042503810030703080e03205d080c030b038440b0304110780c135000103440540301c1811440039500c40040507600c100082d070b07902028440100600c00c65100d0402181c1c0603034060050381d4903a43e259aa40fa409a24950030307680610440c0e0188201c80d400502e032801406501c0b0a804500d100702c68103102d1080b64002d031540d040d800103004a44640e02d0b1020742800e085024108207888a96103084280ba44401d00144280740c17140000c034118508601050540749800002d00d80b085c1031001c2c0d84000e501075030040381448018080a8001901a000c0700d2003107050321003140e107a0030945840d2044d10360291a20090604010542c2507131548031103551603035500040028070305800c41d40155440600340d058400d001034001004d01c0d0030380d00000c1550041e03030f12580c04409a0b03901e1094508940e48420140303040d400c10014510307080d1003140001100c1c0e01c03030f10490340119000d0000514540c0305510030007040040b2810034080c4041407001000510b94608144 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 774095863 1250 774094613 774094619
    0x1205011506020f030a05030601140c01020a020f0601080a03050d110c0706030c08150607060906240504060302010203070f0303110d0b0306091f09060207060c0e030708120d021c090809130501 83
    0xf0b0340740c0c002d484190080280110014216038814074100d850240c014400c41e5072001e01c022b06c2c41c084e520100c03152025104000114002c40c5001a00504030380c0c142c8060007040005680c1200d05520124807240340644600255500241e04001009500d0852000b01a4549070681c0502900c0c40c0c0d03001d040a0251200400c012602903140c018101101155126600c112502d0100c0080140040140070180f60410a50858207400d844041703840d03410748040381503035a44c0100010703958240002401070300140401c000055501d820340300c801d4131074100423400d045156041c150359000501d244000f40c3c0c0f192545515820148001c0c2d820000c0c1c00046c010640c82d00300911a0b05d4184044000083c1e0360b0303120301c01400040d9042e10001035201c6e00900078074524a000801010740044143c0c440e00540e040043c81000001c0c001d41001810f0380704a003001c00140e00c4d0700c000d4100018110080c1c90000d200340c010701d001d03c50302c00c0305807148044603211820300302800b0307450484c130703440f129180d207860014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 774097113 1250 774095863 774095893
    0x30103030504120f051218040501032a1a07150b030c12120313050106120b160c14100c02011a100207050a0e01090513080a0c0c120501150602 62
    0x8030b080c0ca50403001008080080c0c90a240303100e1040c440900b080c01440300310441048400002c09040c0e10f001c1c0c08095883d008000c00044800078071000b443c0c174120f9020382c0c041003d1034859030408160382034040c018654a0a1036440ba500314031046054580000390708003009900e0070002c3c810503001c1000c0000e00403120101b55924820051548100701c00060f50f800c925041002008141c0c56000c00350b22400e011245848035030043d00105c0e81c035402c002001c144804010f11540600350072070b110030500d071207641c004245810426440410010724403500740c081072011001201c0f10700b500c401000103580714503074001294040070030b603c21a41040c6024003022002008071842d40780440303103a00b18541c40030050746017011a90040750401040c071400a001110b5504041c125051500184804d585900004165541c0c03034000801006013440000350042c03140b15010116031143d0740040c401034590f24151032007141076104440e40c3e9141d010a0f01601c04200c0c00740300038400c1c6d00041510340c2d1034010b2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 774098363 1250 774097113 774097117
    0x1030b130b13080409020c010603050706020a08040b160c0e04051e2109040e1f02121603090b0c04031a04030f08091906020705010b120d0c0203120c01051602030301030305 75
    0x11400b0035000003100405100f208401c40e0018040000119030b118011800300d4040c1102c1e2100f542c41d80505a40054400d0012500031a1564028455031815051400060440d00110165500300b01d503c9464400940001c038100040c14880000c000140780030f00d07080c0e20340400c842d101c105c406588507140350240c0001850080c15819000c1d1028112800c2d403280d040c0f8000c11401541c814200322140600035004107289400300e01d51880b50000e0038022902106900c0743c0d4600c1103500700498000f801150311031594402e00001c5d480c010829480c142c540b905880c1c02610790403640c034000181081008a07070800b0030000c45249504038039902d0541c0300079201d12141c01c40403090091190010707059040c14006190440304d8500e9950005185007480c1c0e00a401094049440c0e42ca404281ca00b5803801541c504050b0302200010080c044110b1012102c8640700700d001c0341c061103000c004620bd0507407840581440608400001124a044480c2d4180501c2c0051040155001040140082039000d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 774099613 1250 774098363 774098371
    0xf0501030902010c170301151704020d0201030e070618061b1b080a12080c03040f03030c021002030a020705071203021c11060a050a06080706080a0f18050601030b130b 73
    0x200020001c4035400140c03504202510010a02542d60000c0d40c41010250701840c1681d2120000422001d45000151480c60f40e41d0444c2c554050250006401850603244050700c0714810f1401041003141e80801503d400d03200d4001074003107460880749501c00c44070b501060300200a20f141a62000d8243d0707480502d5044210005003030081144081502071841034000b41c010021641124030b03019440c10b0541c1803c200300c10200c005000c02e00460801c1504100380c0c2d024a8000c400401016a23954003500184540070010065010f86103c0d140f0803943e501c09544070303402611003da0f0300c840318034040d414001103400c90070455110f12404c0010a600040d0400b00e020400d240d400310f5444030200380e81c0d2a4202c80084258411141080300301003503504018010302451600303004851f240d000071611004039004140004812000040540076a6005825108154600081d585d00104244c070004040c6542c240c1d80da0340080e00410802110228a0794800031500b42040007945070baa620511400241c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 774100719 1106 774099613 774099617
    0x70306061115092d060609010605030f060d0212010f200d05150604080a121e050318070927170f0705011104140a0f0501 53
    0x206800406401d09024101c20241c0358588a4910801465003020780300c0c0820100300700301d02c0807003a1319401c00c01c440c0d03032009281d090b10700307281c040003400e0640113180c403600400880350702209480e00200c581003000015200c070000912540314181c0041d6219102d4010340c4017a00341580f106035410326820301032007010388003800e014524180c14002e0300074900400003681d0362282c0c2e6001c2c9512605210b08802c0e492041c8011071425000b9030441c0c041ca510410081c010700c10b1710711241d04886540d2138461041101c4542c218080240d100701e602c1400008400711300c0c0c8a6407095000705041d850002c95841030354580f40f65014103c0202d6445440721041d2101400e00c41d0000b0111649801907403c40e50100c101e00281d11b20340c0b0224034080c20740700074006040000c3c002e01031525120031400e1140c0d2030700e00708001000c11214180c1514460200304200304607003801c07002c20348202c850034 = true := by decide +kernel

theorem cover : BRFrame.Cov 773920863 774100719 := by
  have h0 := BRFrame.cov_init 773920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773920863 ≤ n) (h2 : n < 774100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
