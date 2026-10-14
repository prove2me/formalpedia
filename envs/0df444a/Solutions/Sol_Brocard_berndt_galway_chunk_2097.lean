-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2097
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:38:40.44401+00:00
-- url     : https://prove2.me/submissions/3165f937-69c3-4e00-bb3e-64279895412f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 376978417 ≤ n < 377158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 376979667 1250 376978417 376978423
    0x11060703020a0b0601020706050d0506010c080d0606031103040302060f0402190e0114031603080307051207020c010f110a151119090504050601080106030e0f0f0d0210050103050705190503 82
    0x10680a41e006090038101482c01074283d00e030107080c01e070640d44562020400c669001003282c40c0015076400214550b25910700503660401d150300c00400500c00441c13242203068095010304211102e5507414041248105001c40a03403100713407400750040e00310748006132482c0300d02d00155421500c0070303203010485001c51420302c07010042600045019102c91004210403003010031800030540c4101c002d0001d2011000d8485580c4640c1d10008000e14408400a40103500031016200d401903001d981c07540515010900079100c3c0740320b050381c5000c10400b41e218401c43e0300c2040c20041024480000b0701d52501d4a032606045803402100c2c07406020707201c6040207084140200505440d60320b41c0a041074600b80b20700007415801c1140c000e9130090345050200805680c0c0a00e0705c07811100e403405c00040d220b180444c4c07a801c000c03845548424a12410200a481030070001e4803e50f166405c1d0b00303a840040580c090751059a41c01c3c4009051759100203c2803040d81f4010703131a448050071103e1400701040d503820100382 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 376980917 1250 376979667 376979677
    0x905011e0b210403090306180c0803030108030403170c0a0807050d0305010e060d0602160507030b0106080c1603030e06010e06150f0702060a02030d110a1707080411030c040906020408190803131106 86
    0x40e6030351285614000c00100100210103405942b018504540c180750072141c0d00e005900c4043c0540c07141e108907048440c5048116206a004002501e1121401d802e10751910380c40200f0488492141561601c01940f0920406042c0c03407402c400d03514039851f8202041200a03246009031040c90b401c0107030246007501c40708140d000511820207414540e04c0c504001c0c900e004140e200600784440041007003100c0c604602250b015075166402600240c699040031002803038408000e116500c664000460300c0f50081c1da0380d5100f070004464981003090b9803000f0b80ea1502030394812449007042031040d01d0040c580680500100d4940b481183d003400700780c9043c802034404a80808605900004030441840c1d0300003002e002c0d25840c4048000207041c0400300030304004004002501480304000c3c1c0100c2542d090210a048850080051007190203505040e4000c1d4018882d05203070b48114404007503049003440c41c00148a03084400d65085a4510710414600c114003e0101c8007442c3c2466594465640c0801500d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 376982167 1250 376980917 376980941
    0xa150e1504090f02040b100203191106240a03020a03020607080f070b0402012c011817010227090411040b090c0315190b0f040905011e0b210403090306 66
    0x1907180c070b0f003401800f085420301707441d860240080d42c0401c07602e41e80010440700b50030040d80d40340078507100e101d4049405800c861403005560040405011480b10851b10520480103820494608020903008004030381c3d015100003900140528010005440d04d0380245c038002d402000c000b460011904c5850f6116403200d0742c01c440c84400705040c0015540d000c50704a03009081031458010400b504200800c1c0000004441810002c1c3d500400c0c801d124040f890100030040e0742ca94603104204c0d8403e1703c0c081d400100400002d000840203176206092000c0c0c900c50886400740030310100c2e40300ca40b90000300a0300e03008400d0b089074070340d881030391941c4a40d404c603840340c0340a41d60b8646a00346100011035800e200000e02d44108128980420451403d0503207000b20380e01c0c4807000c1d075074504000c00007649000b01e07480f1941480c03404e0300003c1c10701c05004513103000704107100d200c6507200c0d12001c2000340303401400c0200721035103031141e80341c0e0740518050b0b61300d07810900a06102c2c18081e500d9441d1019601110808 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 376983417 1250 376982167 376982183
    0x21200a08150a12020d05100507030903270b0c0307051504061409030a05090d02090f04170a09050d050312101a090904300203030f0a150e150409 63
    0x31803054150041c01510440c1118406891450000c1504440c011100301921548624003000c0410404001354800d40e0400a8144102e29204e00050003c2015100640100e4219540781d1054102c504941400401c80b0180580c500c2c01c2413a002440d412a01002e0b90502c000c008c40341c08038100308603584195140200840a514107458154107030707800d42c818910355022000078092010300100507219030450501d0004c0d101c03050b010028600058101001e50082100e10070f20400c940c1c1440414852800760740c40050544841c2982d88051041e4040400002c00b400424005490402001c1050a000784200c90609900350b80c01c80c20400e094070b581c0c095400e50201081300d40b070200da031008412400c07401c043c107064800000c65058400200010150030080804a9004191840c0c3c1407a2081ca030341007060b2500000342c0650390394400c3d159081950395003000100d01800b0b9000c2c04100c1400300e1943e00d5003a280c070404403a9204060f00700b81315440a0040020946c9884c855549400d00401d44 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 376984667 1250 376983417 376983421
    0x40306050411011b0b15150304260c15040f20011107030203070e09071a07030314010501020c0103050a2d0b031603150906050a02030f0721200a08 64
    0xf5040003004541001d016581c40c4508000c5003a181c01c140c0e000c1070224a024801030b0200000b00b0100782d002881f880c2c1100401440248150b02205907407500086158001180401c402a681030192a40f207088561260008410040300c4482041c0c010380b00e00c540c2c282d80201c540e1501c2c2c607000c24805e20400842070450100080d80c0c0301d8000c000b004a2000606495130640e000b0a45130150344c0201030340a210000412a6810108090002418040c514456401d0504050401f83d44050700c242c0c0041c0c1025503c0c070780304c0f1a148030303181200c805070010625072450314010741c040d000003084652014ada64428449101403410041d0306007200400301c550421460031014215046840300c039010354899400c141c1000d030103400c13a0040e03d4001103811305807030014074680d02401011304002c0a135402c2c80c00303210f5448002e030080c44c001d001c3d070a28012259a030110032116500d10380305901d40d4095000300f165807001ca070b6114420724043c0042d0011100084044100568082989400040d0389801 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 376985917 1250 376984667 376984669
    0x110405010303020d140315010302091309050703110301050f0106031503170a03050903030903031f18020735130f0b070506070f0f050309010906150f05011701060305040503040306050411 81
    0x201c1101c61700d080625641981407601014000d564011041418076600041003103d13a0341c0c200404501041510040c4004040c502d0500d45030b150b41c0c17004a80c01d003030803070017a580c514041c00347d24030485a507000c160741a03203415421000b80c14a8142c1c110b4194400d413000c40840c0607003207102c0700c1295081c5025942c0c011024010204c4d400200124170f81c2d0010300070310800f80c601008030f0b500050204022228480c0840c1e0400101c98641d114003904203410410316080c174115005008094000c0074200c8820210091114070021120300b00214030400c06110700d20759804102815044040114040703500d51186030303090b0807240c01e1f0000019102e0100d2004100141048225841000c5103050b04941c00d0303480014100354028244031061100200018504d00c000358009450a030300220180042c9039445039a91002d480c50050005860200348041402e500954914405d0072030341c0c04124039a031078200114001c201c040d00495030b0740020480080401d08900645010b02d020300c00c0c00807400d41400c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 376987167 1250 376985917 376985927
    0x11a2e02060916050d0b180303090604060b0102011b1206050603150f1c0b0711160603050a090b18030f281b150b0d0b010509150d0f110405010303020d 66
    0xc1101d07020581c1c0b120052011744c8030548a5282e882d030007a812001034071505086401040520303000b401c188008000c00c04448000100380340150300480b810480c0303607400c03401207003a200c481510a881001803031252820f1441141c180c1801c00c07442200080042e225400940302e90b0050b2004d0700440600a0032010514101c58241150042140c3e60405000c283c61031243d0859141e0002d09592549000651400d018045d000840c0140809551441b10010703031a04035407009019107400603150074000740441085101e42c105054004042000903036424000411200c80e044451206000c00d000641191020714081c100241f8581e03000250344029244510400f4100010340041020750012001107100303501e031890145400c8464404a40c01854000014101c071646007504800c205108406001c0c0b841c5125041e1541110b0782ca8280c0c440341c103608041d03107614039115480070300356803802c00290300d00100c00c4401d486000c4485140e010380c00024100d0700c00341d00507009600041c00d10404907600c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 376988417 1250 376987167 376987183
    0x3010c0203030a140907180b2101060f0f050d020f060a05030f0609040b0606070609020907020a0318140d0303060f1d092d0c04051512011a2e020609 65
    0x3c0c42030313103600345014440e041d61603041d84204aa50100c503c40d103118060b0030703082140920f102410384102d40101d05820002001490f08504041d4039045001c503210211500c2841221f2828810810701030034181040294050048220f0744072000701d04c003100f0354460002900e540c0c6415250240c42c0d01d010100b2001d600401410144241d141004001c0016034440005401030000d5038100d0311400107107465401001ea803640a58000070000c1044500c0e0b41c0040e0410600d071190795600002000c40b603000168521500900c3d40040e1401a000742600740900d584504c107029140c0860f220703660345841942c0da1820b070010260403103140b0000d15401c1c144524960070072107140c02411540010302c1e40298602450701400101c00c0c030049071019100c010003c0414480c00240100158140588100a24600c0c050454010209400e80701920b80b01845222180d0f003841d900c02b00c09500c4d460030040c4c005103c882452a81a1021900680d4054841c0140d00c50351160028402820110202c5140c0707214 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 376989667 1250 376988417 376988441
    0x180603020405030f150a0221011e0909020d1704210201030506220209030304050306090303071404060801030305160614010609091505060306150c010b1009080d0c050c03010c0203030a 80
    0x1009800c020884404d0004590044224500603242c458080c41914990076900308019607614234400800d00c40d00b80d1011052040b0918890400250750f40040c2c1d064513100c8401035403081c048030303e06c40400c1421000b401d01042c24485149480d4440583c1543c08a04100c1d44c2c041c2641d10102204650300351240d5500075408130f529030a08001c8895140c0035030810131400d800c0b80d4003c10044c1181c0c070100265005044000c05403800d61808079909a80d0360801c0300c800000580b0b0764400d02084050004480a84000c4c1d42c42a02c26829500c00340c0e51a0b02103141c4a0f0550720004001010071041d109080115400b141c41c0c0041d5450010024080825900560f28180c03504002d80400c600441032031084820690380345d0f440b5030b207820000e226031514a03a803042c0128001001c8c41c07401c6042d4840202040201c0300c142d10b81c420354800301d81100080c041c408895100101d1a60094000e0441c546003d1069040318418820000820b00b52500e2440e4580541d001005100c0f186000f80202c03180900 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 376990917 1250 376989667 376989673
    0x33060e030c010e12190501050c07020102030703080717040302100b030106121407090e0312150d0b040f051605030c030c0d030813050d0f020c030a02100e01180603020405030f 76
    0x2210001030384034680300030400d0620607035000812458955001c4002e01904840541c0c1d081c07601050307041d20781e07000f0358000c0301d007940380c04001a103030510074042c0c030400b0b40c0603402507040c0034050b40c00b941e1412020f050b81090042012a50b01c1034074100104030300c6103210354007500e0904500244401a940900702c01071003070b41002c03403e02038155000c21420400ea001058858a501c0088405040c03a0130754104400d03007401c1c03004a2065000000003440f001d00c041761041a03d907514003001c04a00d585031401d65000d1030b85540d42010503012002150898040c2807000301c44034203662460310b0200510000f001034400e440c410007581ca8248030034200c0420942c050041143e11000040e10a91189001003d00004c0c00100740e04c1d00c51800c00300384039a80041115000495844003822500b030030b140401c0144030300406034055003804070b60128210b0f4003504000b04890032480544044958002d0f190401916080c51038410151100c1d00380180903584005a50314180742c141400d0120f0407240000391b134 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 376992167 1250 376990917 376990937
    0x8040206030a090303020c0303090f07060c2112151a04120b0919030c02330a03020d05040c1a07081911010e1006050a0303140d3306 58
    0x2031244021290310030703001d0800207280301c101d00d0260000d0141d004100703030a100100401070700c05000510b0705008200041102c03140da42e01da204581c0200015002003051102d0483d140f58094008980b81d100c0c80c031230425101c5242c004480004545503000030410b00d403541a81007104414501070100c0b50050009001e107058100500c0003810038054a0050000c1c0e60040054a030420a008400141603044000000803280e8100149a11894032050b0300c155141147c052182c080c00240c581c1c10080800c201002202019035401d00b500a8041d0b802030580030071140d0041003c0e1310a03117128500c0b43c04034051035030622a07007400280109024284006003080801d003ca00d0020560b030324661400001c00c1c4a00400070b00322070310070f507040200c7c01541c00c00500402e000b4011455211504c0c01c0202000340542c1d580c10400c0d01e0045210140c041101c0c8907400000e20900ca0040c985900001d2006c9030f100d00c0f240f14240c600012000032038042554009500c420554010f00d00c00901c0e00b0700d0031040301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 376993417 1250 376992167 376992169
    0xa0518011a0720010e15070506130201020c040f0b0a0b120610120e0705060f0901080901021c051f0612050903030105091317040909020a05030102040e0601080c0c03040311010f080402 80
    0x100301094420f8400d80c10480c80b00490b40e1060313400310440500070384059000705400482c2180340d00042c0049800c2d004450000707002210b510003182e8002c0e01640101251442d803018040180341e5201d00d00005071300c42a41c0446a164168150018403016980e01d035211111105811080d00140030340d0f02c10b0326400140c0680c1940020b480b068603142d0fa100064401e49545071519119441c2c0c461904100d010808103203140320f06010b0039100c00280c9402060b5035540b00000d00301c1c4510700302e281c002c8070025030044801c580ca62050b80e0040b4964900950381249144003a0038000d103500a00c0015541c02d0441c04040c00d5018064000321020b00840c02d550400340001c6000342c00400b420245001039000005110280c10b1000000c260903500998594541d41d410700034003020003080e4040d40e0050070000746070605100b220100ca480380582074040c0c550000441c2d00741405001d056404109008458074020144014030041d03106000c84409070601c4000900700d0084008048184150300c004c00000d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 376994667 1250 376993417 376993433
    0x1050c0a05120a180f02191a160218011503060302030a02010f05091f090611210d020a020d030e010203090706050d180c081c0906030b0a0518011a07 65
    0x1209034240d010b02c80ea55080c00b10340100044280801d2486880716a04188850101c909118600a54609051041c3c020205a2850f8544500201588001c00d46e05500c9040000380001c005d440d0311700c44d81c1c290a60006407500c1440018041100600801000108500c8060100b07030441070074107002262850700040c1c1c641011f10b201905014101c500d20380d1241c0304000312500c181e001407000c6548159207028142041c00c0400799800b00b0b071600c0022076002e01503907000f0a40007819008281500d9411b00100112484501135116001c00307020080c0b00300701d10700140c422016203a006020074280100001c2c150741d202010303c06d160340b040050200300d090220708441a1200d90421564814009680500420307a1400038140034503442009010800710300043c400f201d507040c0895200d509544011080c0c001002c88031000b08840302c0c002c101c1c4070b000340c11100791124001c0540081654450114030211030f01036070703041515000c0c00144407000c20026550320b00155802c07074509140c07843ea203100c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 376995917 1250 376994667 376994677
    0x11b0f0509010903060207241104260304030303020909011703091e0a062d1b02040609060b070c06050f160c080d050d0b0108100902030417031003020301050c0a05 71
    0x100040003078008081d9008007000c100031035000c42c0442d0b5403000c0741000ea050400300c0c002d4800509800041820066080c06800708486180c1021840e261a21078120880d12480d1010a54648000000011200144003800046000c0c0d140907070703558081420410b492005030000000100034101e2110300b02c50010640384048400c0e11116132085052050500d4010301e500b10541c083c025000102d91554000004141c440103050105901a00030f111140910b0740c0c680f24500058442445081c0700c01d6850345090501d001520005841e41c40720502030548005404c0000d08400c0001ca01e03040100052020000340402c6c5884ca00b01648c1c841032802500c1400800c0c054cc46e28601070b60148517040b0030400003070550904860280d03082910107802030304100e0901d42854604421100c40354000c110710b600c144143d440301c4103001d003803e00d02002500068030540c0c00c81130140c950810034600030001d50003800e40304111150b00f40703548101401e440c0001e104880031203007804004503198000003a54 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 376997167 1250 376995917 376995947
    0x5010215070503150310020703021002160b18010501060f0f09080607031a030106090903110d0906120905011e11130902071410050a0f180209060d080c0708011b 70
    0xd599031611100d00c90f00c60361360b004099260007220240c1d499041d50364001d1201910035001d80e041c4030382c001c19110032170142c00c9800c440c2049180c0c10304002400c1c030f1f11880e4860b120340c507214450001100407a08580f0240c20040105402ca90b8805549030003010030000d0013410700e401d081050030100f0300b540369000501018145a00c0707000d00074011501410482c1c03000c802a00070480c0b42c4d661113100380641000002a00030540810802690a0b804a264540201c103070300c3c1c1500d00351406008a07651011860f4454134559600140d40020f05e080c02444404d8000281c013000e6913841d8486c000484245541050300010204468040c55030000e07082c034110380f111540141c81e1a49420120a030b50701c401d45007401809141041c034444601680240d015038007020080140000320404802250740080d40200300807940d40000d0010300d0b10100c019032108010b00040c45858640d91207170101c5e00440144492a0400a030500084e1003d01c240010382e01c461403280042203076184043d000d0840001c40d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 376998417 1250 376997167 376997177
    0x170a03120c121406011803050c09060a230405090304030201082a19021902090a09061805010209030c030a0c0605070303020f071505010e2205070b120a060501021507 72
    0x6100e282e02501c05000d819a100209100d03107030040101d10358019003118401d0100b8020700140b05902802d1081c03030184ea6000005201c02142e0740704011039000000c011030b5220700c014401140801440403e49180b565074080701d800903090404102c00d940e4001c207001d405030b0050008202603a8040c80441c0c000342d030103400e24500e08a2138100090080c3d00042d014140310005189190019500c6180300307505c4007079080d208969001a010042a4a0b2110103944a24403002081c0e01320081da100f1a01140705981c001264645000c00e082c00e0000000d040c0c41c1a5808240c0d80b1103424140045078030031000b20054420000541d8508002036264023418040110214000007010301990442d41a40d0f40b66800355142d800d07a00c1c1441301390051040c3c0c59492414440009104103240c1130040c000d03c00c0e11074808a15406100b08001c0890088055440d40300741500041c1b1a61400010401c40c02c0c1d0b220140303440c3c0b0b4100030712030a4421a03840141154400007400f0041141031940c82c4c0c0003510fa00d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 376999667 1250 376998417 376998431
    0x210604290f0622030507151233051e22020c060f01031b050603060f0d06320105060307050702010c02030d08150904080d050705040909080301170a0312 66
    0x402c840307001c0d50726941c481d2a5800c500448040907142c0200884e40b150342280c090945582ca070411141146174040c001c030346040390314102980e050700540d50510070b02c00c0c00b41a11000c00244074180f010103c0346450918080c3c02071200d41001845244401d010030052018900c066000c203901c03404880362780c1c07020345000010020034801c0390101d07512949081c040f2549410054058240f2101c20f100c00c45100035907401103080140301ca6540011500014821030030742da96030040c0243d4180c91000158440e107a40320040002d1030b40d00c00c3c5d4106000840c030500c0051104103200500c561048244900c070044c19004004640c0d415089944c40071451811700e40b2401d0600c010b803529050460000c0d81402043c461074400c81d81310100520400044090303802d1503c80c88288082c0703984c295005000703024204071030744601e603117508010b820029074a4003601d029501c410b04000c0b201e119804545079800013004000100c104804042d2012001d005404884550f55020305a0501d00c4107100c0015100c4035 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 377000917 1250 376999667 376999669
    0x30c07030c120305010e0f07020607120920010e061326010c020a060510080709020309120d0603060605040b060702130f2307080c1e210604290f 63
    0x20984107410b5210a0450794101d05a4018016003001d003d03c8040402c8400082c0d2000e010f216243d004800940242c4802d407141071044560300102e1440521031900e506041c070015141045c400c0c1020489803804e0745181d41040014030340591000b40501c80d4601740105080b442c031250706201101d5444101c509172078074802880a40d00101041c119540d468508040d0856801240c01c0ea461031081c00b0410441d0f8070010f40a003020a0b03402001c045070f10080d0288141540366000b103812150190482c1d440c0004171517440e0030f6a2151003a106240e40310982003007001801d00480b0f01901c01203078180301850071840070410a0140c400060710070110040c50380380450326640403600d480f20f800f1007404910484040c06500640d002075040c12030400030006000c0c540319058450048480040c918070340520f58180046101d40031010380b0310b0203030400c50b80040010309c3c1c02420000e50308140483c507e2524400704003c1b5140c02480040300c650300c004415147d2081e200c01060302c1412075a007005000144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 377002167 1250 377000917 377000927
    0x10b03070905040c03150503011b111504290c030447060402030402060a0f1e030c08090a0302030a030f0605150301050a060512061c0c15030c03060b030c0703 69
    0x342c025500035240022043d40d181e03041c2c002076201070000203846089540c07807090500b00d80d540407441c818803070801e20055407103208580c8551080c800208482c28001015030f01d41c90604299002c5070750b6000d6443c600420010300107101d80c46c000c41110b00c0380c0f80c40e00d0343c0411114440240020301c074031803030781811741c010000b240f1010744070110014590209080300c810500c00e410750b11400d036580075940f001810307030b1800b402180c1c0705542c040c5c00d0509100070070005031135a0300368a0a21083c081850340c404501e105200344002d0085059502081016521030301616403c0d0160034254039802c000c2461020980000c1258030900302d615000a0501986098100511094220640c001c07803040c1a11100402c280145047e41c1044400b03045442d030b02c000030f548922922203160444024040040c509140503243d9940c001d01400f40c00e07000200640d240300d55044071349c000000b094241802501140da15102e660030200355414100b14013801e200c5806080e000007400d140704138100068100c00c040c415 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 377003417 1250 377002167 377002169
    0x12080306031e0c03010b0d050307030c020315130320060408030c0408010f0603031e0909092901091a0a0b0904111308120412021201110703031d07060206010b030709 72
    0x1100805a44010b500106440f0b508040805119601b040d181008034900340c404d902299501c03000852401060355801e60300441080c001b41d81c180550400003503014a80c0c00864840c0d090105000301002d100d290180140c00510341c0c5201c03500c0e1603401d03401c443da000101107402070f802100703554881c0d480c02c0015400f4030450704034000c154204030104013420702c540c0000c400c1e40e1103604c403080c03105a01c3c2600e03c508c018544070800000c01c1401c0401100d081e6a01c02c03180c9a01495890704180c1e0142c160202c00025607030b06807948440800100840407481c4550344200243d49491111040e4034400075084095a0140d44410140060003004650316640001040748203110341e030b0f8450099603141c01c100c4a86124020f120b000d0386022005105843c01140c041c3ca0b01008200f034500059024407815400c8851003d1440d9a0f803d000682e0620100c00350408520035540400d00f100400a20800f21540ca141010903078007144041c08066004200300b0f05681c420f81c1919180c0e92040d00850b406202c2d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 377004667 1250 377003417 377003443
    0x112081b0c0307030318141c0318030b04060e19060f15060c060605030106180e01062409080c0d02120a020406030b0708090d0801050613080d02061602071208030603 72
    0xc244000041682264034915116582c2801d5000642e55240e4108482803140ca910307400141d5623040f10304c00e04c1c200b2103400214040c0c030703001000c007540b426046078148558001762800b100c64000c100400c0224014a0601c00010016140200d1810017a452040400d07200400890711100b241070381c41020361140340f600c1c0b00803001c505069a42d030303c042c004000700f20050369421705020001c10349080500030300c4211036506038582000700385400c1c0400204242d200452039552205400210760442c2c04034001014030850110b50074502c2560701034200c41955101030110340015200c0c0d0565901e84804000c09030f010340d200c4480f00380480885041031145400294858a80b04001c81031003141c549051041034140c840c00074680f10052240e548403440c10908002803c003800502150400d4400303800c6014030f103181c00e80c4498039122101d04140da03650304030340141d02000400ca600d100d5401010321000d43d600150403458100110417110740c0c0f420340081d101c100c0000115010b520308100616160b02e03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 377005917 1250 377004667 377004673
    0xa0e0d08040905070206091902040f15030804090e0c130203070c0b07121a1012060807080a170c071a0d0c030510050303041d07030b1201140112081b0c03 67
    0x61a03840c0c0c2c0c0000c00c1e0941d48080140715500008080240001c0c1d5040048040708100c0301604555003040042e00c5400704029015480e501e4451070310305000da41d0700103540300d42d106a848508005403401140c030301d0500200150b0244295a84640f94a104601804082c10000d40c0c2c0c0d68074100d0903941060150383c0140020101001c10040960001d081d224030b1007102018800080a0011118101110a4078550005010b40343e84c45450003120328800504401401150390f84e1f0b520041030074040709511400c1c540d000f1100c030004115043c1041046401103820311400c0c10030ba40c01941e522441d5004000200c0031444511140e0032004c01a165010b503040300500121360040c1000307000d02029180e080007481a44e41c0802d0030f10b00401590151002c00540c000c1c403040001c105220150060300710740c20302d0346c1c513441a401030f01c461030203c00603000b004c0003103a61064a10004d40304081648a44040142506030030b001440107000c4556060070158000029001c002000b03051104020781540d0501c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 377007167 1250 377005917 377005919
    0x3050a060905010606080c1218072301050a0f05090d170904050a1806050c07060516080601020a030e0f0a05030304091a0f030a140a05031201080d0f050a0e0d0804 71
    0x305a0064a100c40c402d1000b0300503142c3d035800503105c15809844407000c50000380103069405280c2200103a026511464000d001100e01106605051107600400c00102142990500c03085092012181f800030a00c0c02c1c51500b07800c2107004001c0b500748588138040190004807400c455481002e03000a490b00040030030b01040000d8080c003616804800420300450829001810381f0286d441075100e4590b0000381005107081599495001f060000d141d01c0e8400014070000d00414464400c042c4141c240180074107120b422f800010345a444000c241a0465000544590000707502008140d10b10009a500105042c42a40052804c0c940c0343c0004c4e405110201d070001e1020300c00c1e0004410301500c03822982801620070140501a0b900341c141d150141d000c2d0300b018000840801f41d2104400c0c002080d03031880f00d003a550707250555100c1c1c001c4e000288902001407200c03040601c8121303c1c03d010341c01d0940d11210b03422805000303805005011000d00804092840141d11a604200307403065222400b25662 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 377008417 1250 377007167 377007173
    0x105060715140a1d07030c05120a0b040318080303090319020109021e0a060804021f0513090501060906030504110603090f060c03041106130b0904091e0213020f04030f020a03050a 78
    0x2451a400e4080045444c00c5900304090404140704007526000f5412240e03d074240401e00402c601e40002800d0140318070071084000c80c00d40102c00d40218880c1da00c503000c1080014103440740c00000d40100601e03420070014840c1c100c0001040b035a1401c0003180f000c03c4002d01c810240d005240c40e004c081d4010a6885c4410801440440440c403c05002c80d42d0707042c41c42d111041105c5107801214029040200e11008005042e021006810b1080e11860702d545003201c1034040d000c1d102c3c959408980042e45820052060b00d420038034100103040c0030f14040210b4074064444030007640342c10b12081d00595000010500c02002130141e41e807181654421603074a800c000300e0003602680111000c1d00c9050201062070107600e040fa08450f403441c100401aa01c0c5820100500d000e98040613109900c1a901d01d180000200609003c520310f040740f0781d80c40c41e0401e032401413140d003000c02202482d40b64410019000d0640b4400240d400f5aa0446940c0044003500e00c0032402820f0240c0000d001072107841c000c1020 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 377009667 1250 377008417 377008421
    0xb040b0901030b121516020d090b0d27060507030902010c020d021309110f01090807060305070302090901080604020f061905071704080307151104090906090602190e090105060715140a 80
    0xb42600c0154611410581b80101d0725041d03007150350301c00604141810080d050b4200054000c0112481c00028803420941120760b00341d6010040360842c0600560700d1052003e02c1c820f01d070740490705040c280440005940000c00b2641c505100921580348000080e055454007a200202d08005c10020051041d0700e04094222900c50205a413003202128104c04640d4801c1001ca41110302510043c0313051410710500b98042c110040c80201010707402c1c00301079040d6681e480d005000748080760241c00d560902c0d005011022031a8520140142d0042150400b800180792030030600b5801840c0c036039103640b040d00c0d2030340c000440b60703032494021500403501081002c000300041041c80c0c40b030f009054030b14075a1103100703050380c01c41100c40340050401d101c200540c901d6038001c12842d42c40b6080015807516595502c9040360050122803851a10496483c0c0c02da94022001d0038051101b201d032065a90b00d410b002400510503190010034038103c111030140c1c00402c1d44c1000030030381c0c0c91078140b8145162900c11440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 377010917 1250 377009667 377009671
    0x1707030204051e010917120706024b22081608060109020f0d141506040f0b0f1306260702101808030a09020301060b040b0901030b1215 59
    0x22160140f02c8603900c00384000004604407800684a92204901d401610b940301d400e4029819200d001e030b2030f500301c003440c0050000c4c24080e2184200603121700c41d04562248140030301214442c64459420282c1c500108103000110301000805850780180a141c114030203805120804a8030102c1001c40c120400864240182980d40740c1d8100c9044070b0017043c58804900c058850602107030818001403280e440150010031007280760074921440d00550941890407200300889500b584800e0000340880641d8028400503801c1c022165030b8101810420025061f20451040c40c0c81960b0000700d203c0040319100a41741c041e030400f0f049104640d500d001c06841c650044601c00340301503c1100700b8080186460620b8011076041c1e004020b1510550424070050040c0d0030a4506401d80b0311010000400680c0290301c1002c1855020440d83d041d0310616082d0741e1a90440d50000100340700c10302211644005a69030100d092034046820502c0c031000c106d003118030801d01d02540c000c0309401c1d803941c1074404c0c280d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 377012167 1250 377010917 377010919
    0x604050703061a030a021207030812342d0e010305060d080d09030c170a0206060406060f080403050c1608010c03050c250f0f050607020613031d0a0602070807050108010501080610170703020405 84
    0x46c00f0044116000714001c442c3c908141603200104490030040e0f100b544080f912001103246404006000d14603042c40d81c40d50400c3702d0024062042e4804e080d60b15008141c1c1200c0305607001d1201000300d51726401640202d8201d803640b544d580400c001490f2003106461079a68204030f2690054852900000340350384944100c0e00540701e090049200c0781841d10030340d402c070340650f600d410040e81c2d412320880e100f0360080c10903010003005102c09110004140800b9501d030341c04410a0703801525100c030003804e6901040740c980500d80741c40204807071142520f040301c041e03000e08840c04910f284800c6661070300030707038654024182c3c0d0700c00c55505080002a00918594a02071001ca440c1640c9015080380c1d580d00461700c0340c000d11a140c180c040000c0c041c40042c0151401c1005941c4080c4141d0042500d521881e482940142c3c00f500040181c5282405903802600c800c0c40d02000541c18100003904510024000601402040009000e0b0512501c0d0700c2d40001d0001d06161500d05004100070042c0d00540611 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 377013417 1250 377012167 377012191
    0x30604061512050c120f1b1803060c0f03131b0b07140c01050d0b18070507230705010516170405120a05100513050604050703061a030a021207030812 65
    0x10540148081043c0e80442000b5040c5400725980c0302c09070070040c180034040a034080e0804d500c1f00c8052402001901103204508030406040001c00209454841c0181c000d070346100003040380659801c1101d045070b070300141c03003111119015031134a40640e03c2075482c0901e030401040070f90302290100c05400200411030041c404203080b524045011034075040b003811080d000c14410094596417451640100d0115900106a0001400804500708505070221890030000d0790000d5034004011829600d14001c000c0b0440c0410300d8644204882e550300007600403a030500c00045008070b9881000d600304000300b81c0c0050900031000e0606244441d0390090700805100e0380321404000806240001c0410220360002d0092250481d9003511100401000e402e070b28140e80012208401700324100080c6024900c110020300c4514a1800e007001101d1500701c4080b03094040001c0b0700b1507a500010b41c1802103804036480425020061034103844c00d152070380003d00114022070b2803441090b040400a20407810b41c0d8139 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 377014667 1250 377013417 377013421
    0x5030a081612111605060a0e0601030c12060e1006061b0c030b040c03020a03080c06060405010323160f170c060304110a0b0c0a030e010216060503060406151205 70
    0x421000704070040c4558009125550a24501c1c2501c0e00300c90f04510b1001c000c54a0484400a41045001ca400060300d45500403006c0c010840200d11441e1a0000d116006d0062541540d0700d210302c4480c1c0d8071540300418800220902404a80d91000b0a03002c0c601e011943d114011540400260803a80b2030722010440b00000310891058000020030003542c01004215800d04540c1c8072040c6070303006007040c1d94484001d640400140c07501941e49001d140100304964940950600d05c914120000b81001d00440c20b280040001900a4202445036070710b800c005444602418103039442e20685510b0114409020303100041e0943c044141581520803007005018401e90040e091075440d40e40821140d0007040400001d004910b280ca000f215031400103080440d99503031801e81541d540c015040118141d0030807066641007542141d0101340c0d60b02c0a0014210100c11145120506003040c0700d16014003100100051f01030b07803540d00040c00f501c0d110780003040c01c03040201e0050060240b03402409103e40b0b0940 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 377015917 1250 377014667 377014681
    0x180901051008060712020f0d0c09180c170a0902190906080105060d021e220e0705031209040b090115082202010309240b010207051c030e01020f01020705030a08 70
    0x42c0040c803a01c0307545c4804049281c9908a01d0080d4000303070035815071480c1030281510342601400b48609485680d13540d000d541d410a405560b12888480600f0709040c0f500785402c0c0c0d2981c10080c412000d0b4102e00314000d0582c2c0301c500302000740c04805002540034980ba03004074040c0d91206400323000d4400c103007410807801d0340342c59503a800c031941901d4051b40320701d8003031044005141c84400c81c4400519081c024641c41030b14030200c0e0046d0301c1c44498440280410412081c0f41c48039102e028007000c02400100b4080d841d141c08252100c10b20a08171650714030008644e002500c8a401c603100601000e00034103031079a0351b00c0c0308603048000c100700c06000961201c0481d00c182552620310881c1d5440c100e00702c038107940590041d07005140e512004ca44146490190360304046449403001200207400c0702c00701390b00d0510000241880d03859080319204204000c00c00c000c208004e16408240c075450300304403200fa07001c840180e00e444505d1400031203640c000100f2004108003c000b40202026035100c0c200f454a0301d43c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 377017167 1250 377015917 377015923
    0x41d0f030c240619030506240d0f020103050603030702060304120906020a030e010503190f0c020d03110904050403140708071106070b0708070908070f0816081506180901051008 77
    0x116402d042c220101142203483c02c2102d0b007004203510440004502c0d0780ea5642c6040200481704c014403254003404d082c00400001c25a056407060442d04006e081245648210038560400006410076985100003801c07510108100c0c0c00c0d031038004020035100c1c40c142c5003540c80030006464840010707160820008080303000052403003a51740e00da00d51711046071320344004440c29040108603000d50200c004101c081080b1512441c41c0c000051080420350341d54039100a0310340896a002c030b50130140303010301241c0351360038150035691602400c58022806460303a0804540c1c100080d213020411000c00510b03001001081802420010b1154900b450300c10f4507001005400c1c001e030007000d4207000403000001d02c05445014169803040560500707481c010385448005280c000603421200f1560785814041c040140204012400c2d14004000240c1003810031008944034401e4030200c080b0100207c0108145640e010b0780c20203011916081c5108514040c55424040c0c54152524030499601443c045030801c404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 377018417 1250 377017167 377017213
    0x302041b050f0c011803110f03030106090611011b050c01050a1b050c2107060b06070c03080703020c15030a0515030705190506040305030c10020406080105041d0f030c 73
    0x152a103030308007000c2d40c0e000e500356844240d10f0465556511140c19610645030042c510303207030203a03880706214070172082424645010030000c207070554028001041a40d03031150103101941d80c146055000012840d84440c090071005103d10070b80240841e8040140b83e0100241001810307900080c8440d46036140f4030012502100e602109010716403000c90300710790007040100a400101401c4a1407031a081540e07015810b01542d070b00c0008440044c149080c0122070140212107502201c0da00d1a01150366508a5044000d01c00104056008503a9005250003440501803106000e06150288010301001c2c08582e0b204036100c00c2800c0c50640840c540680c0a0f581f00440308020740104450383c1000c013004904245c102c8030251814080b0000700d13645d22903a028200943c8101c00541e19141d002c200241043c00034440400c038548148400c0026992104280d41101e4040e07500081c1000300e4103240348000c1e0700300c10040c03130751140546458080710000000c045414424068492601010751020520001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 377019667 1250 377018417 377018471
    0x1141b03220311060702120a050303100608190c021501060c151509053d0617011a16030e040f110d0c0c02100f0905150318160f030204 59
    0xa07030800d40f42402c00350300901c20140010410569000303030074030440c50004189401c440340e4101009000c249050015078001030086410107511500d02408107404056142e05208106512006108000c0d4002e2041c448002d00c10f14411203d03685940c03000d021802558400c40d00380140c035003104190311241c8115256040645048002c0c1d0b881d10343c020001c0c11019082d080701c80503061424034488110310480d07003004000c8205a220340c0304035400e00c3c6003a15175409074007801348004042c4000e000f01218507054451242440b030200319a0300c0305403e6806020807101c0011510603101c400d054000754100d410601c100c40c10f2114041e20210790f42910207031007905891403410300c0340541e40001c80d046100b40e40310505e80034154210a8000034805004081204d01140001c0800c0d0074159100c181000580415180141c0000701e43c1c041500f10b20000740254a192402c0c41070910b148001e224441e1007001e12412502001d03201ea030798158040c1c0c9448120700c0f0b11701e00320103148581800c0c04a8604811 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 377020917 1250 377019667 377019683
    0x1050304030e030f0d08100f060503130614040f05010f060b0403110d0b0f0708070c0f0b070e120d1119020d030e060a09090f1a01141b032203 62
    0xc80756020356200e40500100c9034540182800c258561004002040c0303150070320343e00e04246040c02c40001013049002c3e080116001003112090004c5030300706044942164000c00c50005040280c06c10301c00800b08031201f21402d1407a01c062000b402810380b04000c10074003c6000308030129070303072482d081281e1241c4141112807405110402c0030501252414074100000b8241c44a26105035848200c010f108a07101075070075801c203081c00552a03000c88401c3e4420858105044250358a46610400c0313101c0c3c49004007404400303400103141a111b540d992800c4140581034a141c3e0031785a40240e15040501130180010f2181d461071841010000b4661103e0100554042c035403644039000d00c1101d445a1605805108103889400303841d0311058002c0900c00300507900c6401d104d0901001c030054408031441c112415041c00b00c00e001ea03d0b91001105071125003400e1500c04440c031400d15900718069100c00000c00c44a10742c980403e010048014800d003078003a020400741030000e210b44003e040d001e010192806d6 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 377022167 1250 377020917 377020921
    0x10201150603090302010e061303021209010c0f020303120403030b180f0c0912030a0c060506040b0906040f090c0f320402160b040c060311040803030a09020f090c03040c090b010503 79
    0x42c003940c0904089400391001289801d01c174244140b8004094410075031071404180380d0000d1581c144410244100c94620881c40c0c0380b40c11300000e25940d0421005411a01c0d9016a0700455030702b00225a1900c103681c5030314400b031030141005001001110003007030242e06032a1001924511440701d0340c1c4141919821004c4a450390030007060786401c1480c4107900301050390380920307685404201405001000d40d44d001280c601c140b90072410782c7d4001e051140100d007002000360ba91b40c1c0722100700340e011a0994001440350004850075018040003903000c0c114007034004000c1032455002003203501b81e032038107186842001c0c4a03034690300049035010b451064582043c019407030030f0b2130310350000c1542200d011907002510307080e80c4540090700419a02241c002150050801001d50180a0000030030b49062080d0304061805051340e880380301c000d100300c3c030b03890b80d504c031300e9045540300c00001c0710192000d0706a404178a0035040c3c1c80015881a0307401e903a02059a00e0015039801203008900303807084180c0d9494116 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 377023417 1250 377022167 377022179
    0xc050a0503100213030f0b0a0b0d2a0504060b030412050a0206130206040902030c03071d0109090914030309060703050a0506100e0102012403060b03190b100b07030e030c01020115 78
    0x2900001310651001c0c10003070b40000410607291420031094001c8290110f181003442e0240c084640f403a9400d070150340c607000c0c043e01048600311080d50030700c8100310a20f0f18940c29513a000002c1004d400c00d56205190030804100411218043d41c030841c0318003171030301200c4406103050310300740a00f41d22840140e10010005148107449420740017402d20150030306080540300d540328020303070b003084610b100e20b5100401000710303c543c000c803040410314505160070040d11801700004c1c541d80300c50103118500e0381c461090b90200008a0401400d0380d080300144d945038200002c46540f600b0041c0d0303007040041c3c248800300e05400d0181c4205400350070028546405010015800d481c0e150010a02c581595a185403400021000c0101040384013500c80c003841e4202d00b5460010100c4aa04220314084da02844c41c1c804034028065014000580010310031880da50b40c1111017080c4011a0041c0c100c804000ca409020141c00c00005010004118282c0d40218200b0b0012400c99000d8001c40b48000100d1000b000b903 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 377024667 1250 377023417 377023421
    0xa020a0b070519081911100e030f0c0604020112060b120406021309201e090d0606060305062704021002070f080c0420031b0c0a03030501030c050a050310 67
    0x2d1003001036400a01114141c40c100070810f140583e00c42c07800103021418160742c525100307544185404c0005904048103200d6540700c3da0341c582e4601c142d03541c9800ca0202801082900c81c15560100d60303580c1c0310058109903817505415503049002c0303845440c0e00b40f03650165005100541d01d001c46000d040c4142c0d041c1c5c103420180c01030010780d040c940c204941481d8100600d0084003a0415090102d40c1c1d0458445002000044400b446065413060000140f04090440b1001b0364039422400c858840d0346060005d40c9032140c03400014881c0b8030345000050310b15099005288600d00865840f07070a40020202c010f003900058988407066000300b0300082c018500f9240e1800c25003800d01c1243c403116224654207402000540001000d0740c424005218a4903250150318800040140381ca011600340040526a03800040c00741d540128a102651007134111b00703006c5d5098404800308450145c042401c0c050000c150a02040e181c81c0c682c903070041058240789070a0002c50f100540285022241c50b161280 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 377025917 1250 377024667 377024677
    0x61017180d0f021b1c050f07080a23030f07060506030606100f0f0e1806030d0e01080121060501090c090b040b09060310150819050408040909030908100218030a020a0b 73
    0x82d0017171110341000c0c3c00c01140f04a141060384194000d0031a0030032002500c1c6010615402848541e000c145000002003403c0c0d03040784c0580003400520303c440102031304075040d4003d807241c183e0f2000012844900307020403908a06d0050400f9410380d406a11510300340090071507144038003400b04001496010380b0910840540ea4100d0390740c0750080da1030b21150001003185200f14280413540481d01d09105d42450140110780d5280c1e0b031420300083c0c01807d400082c1c088101482040002d05e1a1078489500c2100c00000361146a4001410499903071224034842c000d0818903400e0001643d000c0000c04d020034404101c1e0b0666044000003820410900100f00940e030004080f580b501150910000d41c0040a0382e01c00984134640d21504028900701c3e900b055007070382d07c0c0602c05a05040200b480003040070b6000300e4003503804150011518110600b010340b02503005902c003001c03c3c404c51031000300070006a40500403418514003800c0002880908140e81c500c051710019521122010013001802c0001e00101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 377027167 1250 377025917 377025919
    0x140f0f1305060a020d021b0918010f02070b1602010501240c0203010f0b1509010c06091b082131150305061314061017180d0f021b 57
    0x840c42a200c01c0812220340041c0040405640205030382d9442c031381c040c0300c51400009403480c003120303212040d0000740035078801a04849034202e9020142803400801e4209844a1b01100000d555940c9245841115000100c80f1080c9043c01d000d0b08624091060003564100c0710141e48036001c07001500394641007a0209980c0c401409100c0c1c0c14a00161000c0c05032400311858603078009043c40303441052240c8907400051030b4050b2102003005101c2070f07070441007181490350044030000711400545010310481c86003400843e000c4603503003000202480700061008840c0701e000c042180f0302c0180040309903d4041c19868600c0c441903000f030300c040c00b5000c3d800000d03840c901307541c40d8083c16a5003414502144100c000480000e80b200c0c00c0180b03070309044000c0d000e00c0c2c440d90420050705d20100c01d0605105005040c83c0d21a0340c1c41c590b4042c500b8407e101c000c025920600b400850740c1016030340003501924100a0007070902070780001d0200039000c3d40740161074000c190003810342c1c034692111008030048018402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 377028417 1250 377027167 377027197
    0xf0f210b16121506080601140301030b100e0a090203010e2a010201110406030204050f010c12110c04021c0516020a151805030c0105090105130b34140f0f 67
    0x10004201d500600184a03445103c0402075410050000e0441400408103030600101c120483e800b4880f034030031a41120341100f9031801d10740310302e040c80e901c00f0880d0344500c0280c0a9001801034002c926172000e041c0500c00c9000700f005000360b00c4510b03141c54400792950700004d00c400750f400744050020007040c20302405200020700340d42d030044c940c240d64009404c02c90000b64003003414400f9051410403c03d546c0001d0134802040a203503500e6030a10000105140108588080c44912041042016011001e0001d00c00e54441d0b400c2800710791402100803000c01c44030f0410323002c202c000f0300c003a42048461803c0da008e080505501c0d1a83c4502283e0070750200e01590340d80180039101d0072210742c4143ca9600c030700055540e81d00301c034156500b5200c2c06001d900d05d80c0d03d0304083c00003a401c0d07101144841d0380c0c0b2004c1d120165030f80d114156456118100c03015002808610014445525202c841c100d116040c1c4075441103030611802000c09019140f00010750705010006e803410854040054003148201300d4107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 377029667 1250 377028417 377028437
    0x60307170f0a030c0512030f0a0209010e060a03090b0c030c0304020d05070e010b030f070306062c100503060901060e090406090f050f010c0219020f040b06040f0f210b16 74
    0x1600b40751070424401500050072031801c40e4200700c0b050084085c81e06402e0001030031800c01c00001c4000c08405003200b0a03c60f40010030148607402504c001146010050445031603d42c21000034001d0070030010300701d44201a244c001014004c1c0c02003070324065500c90400c1e42c00d5548540c280070303041c0740c1ca1005584904c500741d0001040c203d58080240030b84000200141c4905290b00740070180ea5000d40603905140c1000418460b00343e0101120701d289a8000d81e00c24180c0b48135503244030b030880c0301901c10b8102c0442040e01202c5a044801180103d40c01d682c002042d80c1d980104031104c1ca000e940455001b400c02c0085004115503800207407003036028200d41b420205207661031a11300f094080e4a51510307511005d170a140c86406000400b012070154130410b9071400c0380ea0018400d0382c000107041d803140b035903800d8140c03442d00d074081543c010f441340110700800942c455800c940d04407903505c26802d10381d500ca0034541c07070401800721b10301405510500c07650251300c5148112403d188581c10b244208080695 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 377030917 1250 377029667 377029693
    0x200307020d15020c031b01200306041d0105100609030302150415021206040c021b190513020d050601210e240a06061b061109061206031506030717 64
    0x401011901d60004c000d41c1e46018141c044203c42549900c0e59007941d140c02c02e4001070f982e02c04100482411500c0c111940c0baa84d036070014000340b0200d103510801902025421030b902d4015030055000b50f15100004400c10341e00c076422214464180001030060b0445078400e80c80c001840300700c1d50458450920203004504000d4410102c2c3c00190710081c01c5c41419003840310500301442014000310036403001d0300030078035001410805180036669030b9004600703a00344d060850300211400e2000d0b11004040406106452419030041d42020846d07007919440d03d40070841c13544c010383e08200710b0403415200740c18600000722890000c141984d2000014000c9011000f103020025001107004242a1117404150400b09522000c0320240d41104041c0a1491152444030280e00c03803a403500ca510820129040c01a05580082400f03807000c12a00302202081003002c4403001410a0302c40c45081d400c950181903590a07084060005545442c1c00d034210342010300c007082011200b03d000001d0001100c50920b9180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 377032167 1250 377030917 377030921
    0x9010b0406050a0e1e0906060c03040302010e210604052404140a0605190e19080a110307030c140111180a210b0a110a3507200307020d15 60
    0x2000c102d0451000c0605d80728518000884a07000b00d000c2d2801070400c002c9921081d5a0b100d0b5010203814840405203180740c076501d41001c030959520400765200c2024540307101555810701910304a95a01408880e401c001043c00001569443c4400c091207840d142c03920f955400705540d0b036506440c0c4c005e47c0b01000101e81c550241c180107074000c442243d0008084940c071011a400c0780c4441c50160068401500c04011070554105130700e8004821384c3c2c2d01d442601d419685240c1400010ac01c6010101b00c41040c1604100703104080d5000e6803403520001d012100c09400c0358008440c0c440b4100702071008112030110070300c036032210040140105000c0c03a255803035081102d11700c034003072aa00d102c014050820030044101c1c01d5000401501c3c00c1c40032422900841c0310314040c07148401d0410900500110000101c80710f40d03203079441c1c499500f841c2d6034201da00b0061507040c02c85124000ca048001c07450f808a101070b040b8080705580b00007941c10011503a081001a1500304400d07a81080c18140360400c1c1740d01380c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 377033417 1250 377032167 377032189
    0x2101716020f01020301050307090b060d05090d120c020709020d0e0a050f0705060307050702060a0306030602030a0b0a08070b0711121b010e0d050d08060312040305070302090609010b0406050a0e 85
    0x85810852145604034002d28020401d15034640c42c1e401030004105a890001b4401e064520542c3c0210344190180b000c070b4903501032203035003000c080e01700703c2480b01302100420410f02250b015034403815103980200f0741d501580c00859400c80140e000040800c240c0c00c1580c05489121140342010513241d1164903564544104005c2c2625107400c00d500b044110f0408101c100010581510168294604030501801c24060104042d0003a240043e20f0a4014442d921070b80182d42d01c00011922410201410802492100c09882c013950f51498042a110320010784882144c207800c040901d04a404e5031a4460b810808400d65000180c91a5010005070f0034412100340600c20078010742c404800500040c02d5030340c0041e115000d9000c1c03a500c1e101041c00402e2041d41856141094642900c90b000882e01d00002c0c003005c0c403484040820040100200800d8075011039008880072609900d40700c040041200c0c080c400c501c04003d08000c2000814051030190080b0201800c0900c0500310a2003c80c04403000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 377034667 1250 377033417 377033431
    0x3010e030904060e01080304030f02036a0b030d08070f09030c05190302040213030c0828080d14010e0a06140f041e020415051204021017 60
    0x1007010300c481d08051041038020900e0001c0c400b001d5240c60700c50303034881c412400007600c0c0003490030482003552000c105088106070b02000e540b0240a00300d00d05261028103106080c41c81a502c0e54070702401100000742d080148a881c8501030181401065a0607a4800c0442c2034003a07071211401038080d60705100c1262a2070b455103d5161038a0800402042401c4010908041c130642100601c00300e492038001e4401d495040e20700c107101903c030890b060600082d03548000e41c41800000c440b00703160103500140341200d22412865241c2e0f5100c4481c01d8488801c4c0950f48c49041c0080c1c101055840c0c00b5070782c464502e0007500481c0c80c00d000584520141c8801112658108591000402c0302e0703050085003d42c00300720110708121480c10444080c51a1800da0030491080b02d0012040c440ca542e503500c18080085079400e0403c040e110804420b010b9000352107210700d1140100740f0624502c0c0250100c1d10900440c401403c10342d51aa42000340f40e5102c10007080030040980220301035140381c10030f400e0103151 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 377035917 1250 377034667 377034673
    0x10e0606010801090504030c150209131b02070e0f1816170d17060a12060c020105071106060907050c0604050106031b0605030610020a0b0f040611040e0a05040c0503010e 74
    0x40c10328005841d07084103074000066030389001c1c10000400c0d032007030040c40082e50055050f44a44034002c08031020f800f8110075141c5c4418000304000c0d50528540c85501005a00c0c800c8200e605002141641c0300c0c0c21510900f010500c0c0300c40000e0801007089011b9600c150f120b04540f0340b00000c082d03083e1410142211400c80f080c3c00c80c00c00e100300c0310001c40307403c610741c11740c4010403012030b90b036500a24544488002103c840280804160746564034141c41016144a40b10201c1400c46070070b00b80c000d04070900c0c0c2440554a480c02248080b807042078048540000603001b0801a11a4024070000d044018824010004107200044000d0003d1003014003490084001207400d900b10705209101100c4000d0b50204101601e50401c0044d810a01303480d444030080300d0201518440300c00c103904080108200400c1410303010200b005484030215518010b81c05032004104012201c0788803c000e110340c2c01640000781c02180002c0300403030f844e00415801031240301301225169030707100400d0039034182c103d012819070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 377037167 1250 377035917 377035921
    0x9061e050a0f0204031e02041b03050f06010c020d110105070804031b0611100b060c070303021b030c1e040902060d020409050f04030c082b0b19030c05060d0b03010e06 73
    0x440715014803258a10503036002c514003450740c0c2c1ea400d084400300c00c110148200710144038040d540c0302d42c44480c0d10070b695904440e00d11801e4034002d00030001101e2a680c0b400c0e8010100d0015440341c0c000081c1c00d070707005d0480c02e8010300d42d07243c040c079a80c1403a1505040160400810000401c408061300065102d90b80c000c019049120301d181310006250010410840036205860410400165140c0c400300d0102000841104017408184148940b1507010041d01c10b107a400004c05600041e000b050802c4480e885001489034403c06842d21880103500f64442449650186000380c4031000c10b41043c0001c01c00207011a403503010032219002041c800b9006680820100480446805101e50000186aa5041c0351a1543e4098001d04905a0242019070702003a404990206140d000b8840b40054514040b4401c00d1544031000d40384448800e130080607c0640041c40e03055492030b08095070b03840078012007818204001d120075500440d9510507001e480781441e091544003845800e5100a414000d0132041c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 377038417 1250 377037167 377037181
    0x40605040305151005040f02040b0a02060105011704020312180a2304090f120c05010e0105011d1b0f0d0227061606110c250609120609061e05 62
    0x800007083c0d010040b800d0040020400513144404280c2c0e070100c400240c80c03181c41d02c81e00c00038055a00b01442c2402c000400b109950b800090130760480f4000d03a505080c4032101841c0c1000800180c90083d0150f002e82d0840240301c1410300a48055a40111002d00701e000c19400241d9070000740d03012541c500c01104a00c004030380c00c40300d00b000c1400c06a8091206a080742d403406200500c00c140a4281c1980d0202861100e02c58940604029040402400f02c0c40658007000d0003040207204154504013040b40f2100031210f0345038550b1042c070b04882480d066000d128507034010b5620031020020b6540007004107200d225030a00c064203980324504808082078560b038950440d2500d011501c1407168206100c580354141060390400301c81584900d01003506a28001a1501c81c06001d50740d409602903a8070341c024034103580b038868103111110350100303075071a82d1358409032021043d5000c3c031810900f000f02041c02180301c6030001da855a1040100090078241a126031707000d801c400c0d0180c803031a03407100c0a00c296 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 377039667 1250 377038417 377038423
    0x6010324140607030c021201090c0e01050901050d02100f05040b04080606031213060e06131514091008040f060c0507030e0627040e0d2609061911040605040305 70
    0xd10100392020b030b10340b0543d924090210200004003c0c403891890984400000080d000030000c5584060f4014249459150400030841309014240c0510003003400040c9525100d01c9002020b500507000302d1598a040d20107c9484070072081f10401d01c02d0410001955804440040000f01019005044030b81020400c1500b400f80840400c0a0070304140a082001c501c042c0802d02203a40508040c69403c1c6600003003502400383d05100703011040e40c4040094102c20f51444074041d0f00b006e945a441ea4100d030083d500342c030700600f21110f40103080c4005071100b803800360310701d00d40146c018030f40c82d1400030541c0e562000343e410040b00c20000800102e0405c003003503044080740107003400846005043c11a248942194500c5a0315190701448000300141030300c2c0c6490340604404031031101034610030395461402a219210003002282040414170285014490214605000b07030290400340070f2640f220300920030205001490320769580d03942c0180054194070200140001c00301c5849581e100d910398209142 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 377040917 1250 377039667 377039699
    0x1502070b150604170f010204090c020d0c121101090203010e0c010801080102030103120804031e02031e0408070303050c150906010f090e0a080c0c090f1510140306010324 74
    0x5035403221014811041c0d480c0b500b59015505202c0384100750311604000079181072510030481445520001e0b011a290b009074200c2c80442026400b1150501d110240c11666440040800f5101e000030102207202c01d8803825042004020b98000840c449065800003801c641c101c40d14810194010301941049503040407002c0e00601c0a0300085081d585507880710200d095061500f142000301800000e0300305030041c9030841070b910300544900110702c508440a5560703400943c03160285c40035614003600500c00c107404c40d41600c1840028000c9985155410740ea80c1e044501d441d8254091001c0c5140358000c01c44143d44a0407210000708a41d501d40b06001200d2042078110759051424401d808000020006400510035072100e400d6a64100502c3d8403410f1908840e1110341c010850b80502001d03d40c0d00c05450300641d085036080722054001e80030840f0000b60f40164001154048604000c0e864445020350f52012042c1004641c2d8014016040025900050b00800301421000c0034000300c3d1a0a201c00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 377042167 1250 377040917 377040931
    0x1002070f230909070e0615071a01140612280221010303020a121101020c0109020a090e0a06050406060f030303020c070e01080c1905030a08071403040b0306060c07031502070b 76
    0x10468108814295141c1c01c0300d015212410340f1100c04200b803502d45e480d11020400030814030ba500d410741c5103007522401c50780200e00800f102701d0500116049489080041080d100208074525001111601d40c0c00f05400401111a0040b500303125000d807038000d08802c2601c1c1d2001001039a0700582c001c202c5484900d000400f1402d048640103000007a000686038904642280400e4500f01020504940301c9007100510862540042080c8101003c15001450814804c58064044d20f440350003000864442014403052640103500380004154140e014580060250001007000d80d150b0840c408c00780082c0d4400c40001364002000074841405001c803001a01c4050044045035140c440d80c00d940b42d2410030702c6031041201c500c03000b240d560002ca032500104006420f48810303200c0ca00b0f1905072600145c41c1a2904400040c901164180100031a0141c5649144881c03c1d40c40b814180841034002b46401c4082d48210350f404004103c03100b0301102c007401d51410141c4d85d0700d10307850301a03012030010340304e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 377043417 1250 377042167 377042179
    0x1050c0a0c261209160b04030b0a0e0115031a100608040302010b0a320f1009051005070309080f060a0902180a0b030c0a0302090604090507030b04050a0308090307050a021002070f23 79
    0x6d200c8401401c0c2150212600003a641055890300d9800c0c9000f022013a140241542c40c2c0f484450020408a44420440f4050b10b5001c9082c0e03040c1c2442d0741c1d049001c40e00701c501c0540c4410240061401420070b2034000d402440002603e81c001c001003040303001c02d03400c0f01c42c0300c05501980d400e034201c4000741d0140002c202103083c0c0110407403002240a054284034510b10a8840501e01028944107010480081c01c008080300c14043c80d250000c0c00e20b900c404410b0340001c2c030f954400314034020700090b0080d071601460b0050000380c1d120050311000f050001412030384422803944444143c01c842c011180512024030000a110b041c2070301b0140340c01c0c1032071141c5000304401c3c10204096600c0d184030560245040c0c0780440c41c482903141032820882560001401116900140000e00c000040d21444a43c86a00d03040016103c001140c1e13921f01550000808540c000101c0e44d0060a00f06000200040e0900450300c4282d00c0f2143c0b0b9081c241141c20141c040380f01d001e0884040e01500c2801c00c6404e0040d501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 377044667 1250 377043417 377043419
    0xd0c030b1510021c0503220f03170f280c0206070f0f0207050d061107030302090301061a031810180b0f010b07080307020a02130c0201050c0a0c26120916 67
    0x1120132040c000c500c000051050100000c2e042907201c110103030758140500ca0045d4510850b1816046482d01032070103800140c1250760806080035039031041806010b400c2e8407500e9035542e80340f0f41010040c400c200080081ea2101c0300c0301112106010725440c405158028080c58544400c0080281c0e0051071040b0810000d0f5080c20300ea01d0300803510605440d003c1d41c50205080701410b000c0040e107285191008134a000296010502d907059000e04043c00f400c400a01a09170342d2052012601c0c145407400750307600002c2002c2030030b25804881c4031309201041030546800c4161400304d0000c845c842403019411901c0d03407940f1000c002d90141c44035440031503c01128259410b01c210a10f0900801400519100340040480c070864000c20501c20380f56801858800e62114554580700504441100b80016600307080201c2c4440f1696000c1d00c4250707520ba59072076811425034595062542c4c65024054034035210300c0c05075015230340d40001032000c14580c011150b500d0604904061400280346055a40700c54003d0b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 377045917 1250 377044667 377044693
    0x50f0702010c09171c09210206160c080f0a06060b03070903030f11060103030509030f010603030f050d090803040620040503102c0c010201060e10050d0c030b151002 72
    0x1c1c3c80050310340c0003103c200301140c4200750a14105850350f10726040b041140303c00303860542c42001d4005503403d0303001c0c0019082080307800014000322108020360054090185400504084414111090240c2000709210360345e10740150038410340c02201d1005400100f0540240801801040020094205c000b171551030440c000130010702980c08000c081200c8149010700b40c80c03003080314064465000054a08950b9285030281040e405241d1190007401600c02c21401550184940821240c054460004280000d80308031101d602c40d00020a0140e9600d00e8800410b0105025503c5070348074220024214942d40440340d001001c0c41e06113040300c4810002405035803004a110000c0c0c8880e40000304241507001c034243c3d10070451030a260701e4410042c03400d401c52800002c054440e0300081c3c000300320403030300c444040c0b00ea00000c60382901008030f02e040800013400c00e498111900d0f400f500414100944170b607540340c2498000c2d164107101c1400340d81d40c7c0c0e40d03504d08141c49550488c0d203400100090700740e8172 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 377047167 1250 377045917 377045927
    0x5090c0108101401110303100312111f110403061d06070207030204270f0c05040902010e06030703290a050a0303020a0605090f0a0311120c0601030605090a080a03050f0702010c 77
    0x401071001c80d50025043c1c0f55264061440150140c51860a8030340720b04d8110240d4410070032070b100c2503400354843c01020f44081d0190606c60000c00f0120060f00e1010243c15408074419800c88801c00081d945601c407410300b0f407128001e000030710b10548010404840b03000c01504e80c242d094080e800c66401220601c034007580c00062440469a058801107034507044d007100c540541290303401252031801e51134040803c000c43d14607290031092203180900e82036600c1d01c043c07004980c000c080080c0403c0b404070500700d1900d00003029603030006c05880c0204044900c40401c012481483c1c000394080c55804590506500e4004140000b400c02901d4a110061654400030350380c520122026010590b103401045080c40c0610108000600600c1108e291038114580104050345080312014240980c40a0303042e4118110101c640403000c44c8018012a400c41c0c81d010010039014040400e680310b55480d0100090042014108501650301c0020b0b41c0d2602000403102c040d002000c640459160840c80300d0707015006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 377048417 1250 377047167 377047169
    0x150b03010506010516030c1a04021219030507060b0312370c020307050a060918061511030d0510060206130b1308040302060403050304180b01050a030513120305090c010810 75
    0x7810b0948080c0c024142a68111011070340030b0000341711543c607484800200323411f1500035442030f541c0d0041c210319104000d072188481c1450b40000005d882076030340883c2c8650082c240260080c2c0c0002440034881340001d2808200c0c82081c0c03a09940411552200c68005040d04800801c0c0e008400154070348041140301624140c4401050103640c00022095440800c80a0058840038184200381500c450001e0281009031082e0410340c0310814003e81d2546070740c05003000310f51101d6030b104030034017a201c4107946281c01402d000c070303142c8002d0018021a840d98003030b46029142c1c5404844086003005030080c03d0500013403c5d0100d81403140c03540d000084e44400070aa20284680c08400c2c0d0286520f40550740e88900da10103540a80040303004800e020012005100315110107145056403d050780180c41503030321710006c041c00714005108085965009400c140d030300031000040e10b010003d2a41e01c000c1c2694607081070f40000b9039078508009940307908210200b8400d41c01d080c0004545070541c4084440049 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 377049667 1250 377048417 377048437
    0x50f0705061b010f0f0e07170c0907140307030b0108280b0307050d0b01140d0302100b010302091305060103050c070c050d020409020916090506070305220909150b030105060105 77
    0xc00310100c4608000f07510040303130318245042c2400700c44011a03211014214000381e02c01140500d2a000410074102d84080340760780441401307886d40e40c42d1501003040f03001000780050103101c3d11102c030000da50b882038011403007649186c0b000509403031080c000410030320000748429000e0000181e64840e20b000800c00008416540c040410030802000120703041c16015031040350014107444214080002c1003501505071103003000c94106c01c4801d6000c025801d01e0130800540940c100c00d032100d402c0f04203a000b0754107414041c1005450b1001c00000706185a2418210248c140e41e900c060080d1584c2c58003455812010300c4000600b090724039203c4200c60115031203894412481ea004540071511942c00c01c105030740d0001d0100115141c2044c161880c5000c0c1c40300007000031401c50000c5030707a10348007060b40c1c02c1d03c2e099134070541070048100c21401712400118418014100c5140c0c00581403605008244c0b00c240304a000410030940300205001381e0790381800803031090741030504200d0103903805000e6603800a2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 377050917 1250 377049667 377049697
    0x160602150622110a0e030d0e152b021305041a0d06060902040b040e01060c0312051b040b09041b0e150c010c0801060e011106070c02061207080103050f070506 69
    0x782e284101000341a030041000400602040341c2c0281c1c0c0d00103903a000c04a40036015560f90a40c01c40342100c5140da840c50840c0d1004074030f202c010202c0c4146000e00958074400b103410740d0411b000c2c000d00c2200401070300c20144003600010301541c803992f00c2403420014202560180955580c481c2060800c030340303460600d0700901710701c4201c0060003c1600508000c001100c8110750700c0d500c0d09040c51069105001d60740c21560404000074004e44a120309070701c07058055503810440c002d800c1c484009068007030701c05004024205000040701c540d410003003004108860a240d500d884e40030600c41622141d038640d60b0b5110b40f0681c003450280d0445003800c1c8081080325004020b00550000307400300c0c0031341502c0d000c2c1d941c60700a61f59145500287c0446c10f03922940c4503024005282c01c01110b030003071001d0307555145030009800701d0400343c09002803042843c4020042030800f280880080884d00c412529600090400f00040091000912503104040d5130071000d1701260b810040814511f11810501c107a03a11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 377052167 1250 377050917 377050969
    0xb040b07110616031d212a040605010e130506010210090c0302090c070c0b0f0d0e070314030307050414011202071101030506030a020901090b060702031606021506 71
    0x1a40028072240342004041030345a020f90721044510118142040300868090041110505410030425011a50040c40008410417030980e184c420f210301b41e01c2d8401c510400341c820218081d001c3e52011150001c014107440c08007000c08202c2038468544c006410303c01d5480c811011a180ca100e0141310701606100891551a031400407403620b0a40c040d2a0500d07440e21641c1001c1050100b509400c81c4d0003119600070700e80b181c540d128400c0c405e400c001010b0540420341000120840e602400c41000800c1c0090709100008079180b00792003c2d14109801070704035080600c1007010307446252541003003507030056095207025000500144214000c1c030302c01c01c80444264400c0d80c401d0030910210a1112402c2d504c400c042d29100001c900a1410507000c20f0400c00001c615040011f1011045500200424203a0b440d01b00d8613001407000004c403582003541049108091381b000c100b030003400c520b028001c124840c41c029009040035000599058002807840600c1265510386a82c0c07440102c2110300c40c2a10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 377053417 1250 377052167 377052173
    0x907170a0c0e100201020307083304110403060e010f020c150603070f08030901080106031506050702120102070c080c100c11030a06050c091203040f030b041401050c220b040b07 77
    0x10400701c01c0c40c0c5500040f68282c40705a140d064002d94007031212611043e49039141c03598140c2e0b410600c10400301071604214ac2c0310062500e84607030b82d464908050b00000d050041801c4002090748a5042036400300d4603600300030446403003440b500188281440e0214140030741800c400e920b031600c2e607810184000d60000840c41c2c035076080c80010018042c010301d089100365100c90f815100e820941807a80031881500c000039405000b809045208441440700000c05814000c0940b4150880780050741c00c002e685423000c0c0c40f90030034801000954061480c416005180000803031800780c01c0c0481c2e9005105100112940c2c54010100d044140e07400070489800c00d000901103403400e80d0034800505120b041100f400300c0400342000800f20301c00c042d5030b409400e0b40340400c40350303480c462841210395594510208001080e1030710344007500a480388a00c942d60180320716138142543d0040d1210109440001500214501e000414240e032504100e000c808040c40e251005803103004a11480d0300b110340c0041d0756020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 377054667 1250 377053417 377053427
    0x30711240c0a1418100f02030307030c0315140a061b020d061b09081e12030606040905070302030720070303050901200606010801080601140609040e031204020907170a0c 74
    0x3600605400203484a001c282c010f03228410840d0740c68005c0c40c80055402aa62268440101c8030019030011480c6480308642240280680000c050030596618641c000000904010304000c064012850602400c0c601c1017007686600da0707004405110f8041c0b0110382c1d1200040b24550aa6012210307120040c07014240f0a0140420038030301c581c008a00006803040d681c01c01c100314252171180c011248071000001a102040c013065032080d5403a13010b40ca6214450b107450000715800034001e4403481c10556142c0406068620581e00080400e8000c0704202103645d000d10562800246450b54440c0c03003c034001c0894407500c0500015003001000140b000840e409102110002c08080c480c4c400780d04c00d0068031640b65802038419a000800d140000610860001a461705890904600c111900021010400ca607848100b0460b040358547c42000c0d4102d0060000c3c05400c030715111080d03c0d503e0284100030840d00c00030f2640c0b061100300c0403c4001554131030a6503920003000000018013030030000003954 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 377055917 1250 377054667 377054687
    0x7061b150507030614060910090f08060105030d14031306270b070305010515031b040e180115140612071d01080402010c020405150402030711240c0a 65
    0x441003050000c241400c4200d584964400d580c0c030769040108540701d1007440104c90240d09050b40c0314800740003880b400d24042140c4030550350f00c1d040089083d035540d01e40850303400107544070345519003041e80100038a007014041a0560f400c240780c02014614007055000d0301c1d0001a040303503c540d030250703020340c00c2140550100c9100031208000702241949210100034030800c540d001c54541001d000440c02150080c014541a2a0014068204c0d441c00c442050391a42008002e03c070a07007020215412095014001400a06100383c1d40a0141c40d000d2002041c016a207000440540c0c03400c0d1111070310100f850100301c260f03496440e400d41210b04040020303001c0d0250041e07000d11010100248400c10b9040048044455030005a0082401c030f01001074600c11000c0b00c02a0214103119003a80051070a94041c0f94001503100d2030180c12060a400b16040360011603200020a280703800485800100b081102035030603c01d80038649030b01c103005d1640d0750b5a10107410704191082c003050087c1440e014000c014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 377057167 1250 377055917 377055923
    0x60203100b0f0c0c0a150804031b110f03070f05060c01060308040605040303090b04050a03021302071209080f0705030a0f0825120e090f09070e0405010509010c1107061b 74
    0x1549510302c0d0310041c80c26030300ca0040071042c0d228000c00c1d01164141003070100c04845805c55100c13000005840c0544030010010320440c100588031042040c1c4400030030002024902a24221032038103801814804000504605244a81d002000401029403800384407000e481042d2580c984400800242502400180d04020400d40020502180c103583c820060003ca0f40299190850580d4034814524a031240340940c0340c00c042000428400b60400390540009078100c4400145808071a443d50208014001500c400240038800c00b00014002008140b4440200802801c000f070b00c0d2400090303680300c01c10b1005002e840c1110100b414804c910301a40d00c0901919000060b121001000c00c0303c5240c00ca0b41115101d80c0941c90301d490920070b840b1210032040244c0b0311101c41d180c152030071030a45002000c0c00d03214841e58401150504107091b045008521540c0040ba4900b0445041c0c3d003900c280a103403030200061030016102003000066180100d86982c24011081e05c2c420240b0b49a0955070346000e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 377058417 1250 377057167 377057189
    0xe280b03190b090c0a0305031e09030f010b0103051e18120a09030c0b0702181005151305040c02100c050d050403110609160b1804090804061e050706020310 68
    0x56050103140030002d84180295400d98820007031440070015000d500f4000581946c3c0140000f050b254a840d9001010781c40d50204941001c0a8030b002901c2c1c00c84d10850110b85035112403029100f960940507042d041a40c0c0e40c2d0011b402e01c00c5403041000c214000b0030508072400701c0161030700c071050f041c4140200041c412003920b60350646400042e100074840e110440e128192006c0009a40b06442d09075058168020300700045010003000030560b510018000100074515101c0000719a641c074030b0001c4142d01c82c2ca140e20b41703826031b40c80d172030b402c029040d403161f0301507401c11001c084584d50103d000c0100c929000c000040c072000010003180c1c180900800c50b58068640018071081c1900110071400380e040581c11a503c45c2d9400821070f0315045c140d0302c10300c0710065035282444898289005844142c101c080c100000c240c83c8000035090782c002c580d040e12044d10000701400400c0d40441014401501c2e00c2200701540340c061802401c0384580c1c2c0001d040503a0110206250041ea006008010040d0b070401d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 377059667 1250 377058417 377058463
    0x6080c0702060f0708121608010605040e0901060902030106020a11030c0123070c030c0503100e0d111903051201080606060304030807180306022a03070206070201090b030c040e280b03 80
    0x80d422044426a4409402c41e112a03820281234860044039042e11182d540d614103042c03501c806100c44c501d01070052011552240d0b00411019900d1010b18020a030b5580102030007003c031b003044005e1004010020f4000d401c110340d000f51076604001941600c2e562518103880c43d10308010b2848680c003401c40000c07c00c141c252000028007a4030150401602c004805403110703d8201f040041c101e40d20700708244140d0300104a41105240500100b2854607200401c0e50040b46002c400071914840064003200030510104001d07401c030901c6440c40317003d0f00a10740201007a0805400144450100030002400c101c1007074001121584101c0128400c04600c18060700460b8880c540175000c0c2d00044062403241d146021014440100b01d40844008007121010394581044c540a204d4203503c0f03072000341d060200ba2600041c084c034100340158811002280f6540d15a81410050590f0000c054001841082c51250700f86e400600b030321113030561509448001900305942e00100e41003c090050503113589044202d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 377060917 1250 377059667 377059687
    0xa120818010e0a020906040b10271509081501210605090c030d030b010801090e1e0304062618010e2b090810020a0519110706080c0702060f0708 63
    0x40c3c3d500b00c07910850b8030728410340d603180030721085404070188590b000da100c01c1c0a4a02c14002c1240b114403c1c01c108031034641c410440d101001d40e96080d8462060b502514480000c0c5503401074104014081792000f5000400f003003401181d1454042c046c0d544010102c0c503440d410600b071018840b28203075200d801449940f40c1541842c1c0c54400d4100350f18060300074100390f01c1543e4031031b10522120301816114590a82d003840b00000081c104100001000d20070a040e92540c107580004003034000c00713011700450781d642c00c2c100000e04e5007214400c1303107402d142e200f1220001c9108002103650300008000505140001c12010503000d0703e004c2407041031f2400b6a01c0900015032441c92201110583d40082d0250f000b410001151300c1090313842034a0064101c0f22148141035640c1c0c0050840700c10b0761078400c2c10885a0400100c1020040e0a40d02c046508154080c4503d6002d000c07802c01170a1078103000c0003524051400c1c560303911800d00001d2203411b000500003458a0f00f28165940c150700060840e8841074009 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 377062167 1250 377060917 377060923
    0x20904110a0908010605180c04030f12020f01111b1002030c0405030105090303010b3a09030e1e06091909050601110a050309100e2e020a120818010e 65
    0x90000d020828046083c2c10f050289000f01c031009841c02e24007841c50090151111405410400b0712442007000001246085c1c0c002840a030090001c1d0f604910044400b83c504a10700000f11010b07410980300c006515100815146101500d030f40b00e240104a90020a084c0041d43d00307034903141440401840604200d0a001c2c100b039402c10344c020059912503c1103d59a80003d1081c214030500c20004010004507010602508042c094190400c101d03289100031022083d000940300341c56650b01101003031650088880c94900c1d002e44180701402181d00c50741c4001c669452142d4029040025020710503214145e50310304100f649800704800a441d108088041c0000381c0e02c05000034807920b0f03000380480001c54007040c1c40380d00100440c40c0c9200038091019100f81d0018060604c800d1402043d80b81e200c04145500810051001041c09030310781c40700000b5000c610840f0b40440d80884031b880d00180039000382d86083c40d41414081e019503a081c0d0760b410120030398040068207500307103201041414400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 377063417 1250 377062167 377062177
    0x1b100b030c0603090703110a0e04030831140f030c0a0605061801030f0804051905030714092212080114010509030d0c140118020a062309030102090411 66
    0x4030151200c0c07048000801001d80000e9413080005d41124004000042110280c0050404041d1001c3c0340b9955038580a000f000c02181c06801041210307081000301004501580814000e070580044c0d070382001c2e584200d0035020100010280e240303c03004a1041b081c01c00c80840e8032a80c00044a9441e1114102503441c0c180c4140b0031142182054007044451a00360000c0c4001e01b4803038070b00c548aa00c2c58507110403c030b02004c002d44818000300f1010880792504400424032880c0c600702c0d1079850345840c0505141c1031050f4003103200d207078800310b1494466594807919504292a04e81c5562484800408141c50b20760b0020010944102c0e90404a4100d40060072a07049030612000c40a994640100558680c81203a1030b160b4190810401a0340035401428803003011800788020111301c52460b03c49500311400481204203108181411800310300d0f2102405010301160b1600c6190003003100c0c440400113450100d50100700c00041103010041d1000d41c1510003c1c070009000b131002c0800461000030036403003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 377064667 1250 377063417 377063419
    0xf031e05100e0312070905010c110607120521150f03010b100216060804030504090221010f17010905030412050a06061706150102030f130f030501050603060f01030b07051b100b 77
    0x14071000545001d01624801c007c403503041c0c40b030801c216038a50307038000c203c0c8841070300c0e680c0003006108603004580d0a844001249605441d03582c1e80e00050742d540310f008048008406282080302d4200800c80d805482c2e00c418400303095503c880041440b40001c0d0141c1425030840f42c0001481210220555000855040c480d110081403581243c0b2090101c80c0d5410850f000740108200704070401140c401c690050000e0740d0542c0500f151b0030040c000c0f100031040280c1c0021903d41c000d120603c2845d0b0700345d6812402010300300c001c000010196031a0741d12801a841941d5104c0d02e15007042c23041c0301c2d0074032144d044258084401c109881d104d511010481b0440c01c9805ea59214000005010f06001c114007164618140c00540c24a00c0b0000750a4442c0c0c0445080d800e601064900001c450075800c5038000a140b14000104d0341d407402c0c5003418503103c8018000c01c00b03480d16a0040010a001d100303802d0b0890010310f8900d03503440e0391040c11076001104541b201d40b117100c2d203c0c814a8001a581c450a20800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 377065917 1250 377064667 377064697
    0xd0e030c1e130506060a0c1b06050a030b0303032707150201090b0f040f080d06080f0a060c090e0c0304081b1e0307030503010509070309120503060103060f031e05100e03 74
    0x5900b014100403940100c0380a17411800810400001900030148280460f202c0c10903860a0480083c0440d0302c01c0440c0e010f007001c104040f60000d2419014000c1020618003038009500b9441c20b0210031600c103541000140902c0141030345554086014030801010b0039100060040040074400020300810390305400340c4420201d00301140d4100700441000d4066074201c1c01203400c140050700c41c52160b61001c230001e00c00c01d40d90000003c40000a000d1075003d02c5d812805028003200900b421419200d071443d0072010045050014804010110462900584551802034a80d50b07185840c1d407451055043c105120700701ca40b20303d5602140058403a035152540100000c4505148810f26900d0245100003408208248014825420712001059000c3c05914010a8880140e00c1d03140c403114140043d880047c4000042180c1541c0500400006201401d080c24030549562210001d48441e94448008507071101d1200052000411031849000d045035000c010100704965119a654492044412608 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 377067167 1250 377065917 377065939
    0xa0c0f1a100302030631060203040b060a061e090306110a02010c08090c19050603180106060c320d050a02010b040e151f0b0c010b0d02030d0e030c1e 65
    0x800569107102207990280007011181c07101c064040411200f14113109044650035001ea00e030001e01c0600054150142e28016601d080030f06007603d501c0c0e0020a017500403404100c040002540c0031452003580300355090f0245003201d45600440d208486544060066420b0070042031021403840010604044140c00030010781d206202e0503281c3ca0401c58486c1c1c03c40c3c0120740403500e1410720002c1c03c4460040c0c4802d0454940d01c4a0006d8030360303001a104592495800f0160681400d802d1241e80050016800c00035040103041e62030f0600721b40d00403003d000c020503030752240c1d0a4104a4607808003042d6080306546158181086c000c0c229000103076040015802e01c84110258106032107138204440d25500989046807400484201e481e80140990490144503100040001c980b169110081d0881030035140d9110a182240e03425030b1003160b42e80d80301d110004030600c0182d500045008132000c19041900056003640c00180c02c040034000403d411084031030274044040444444070806500032100c1ea16a0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 377068417 1250 377067167 377067181
    0x10216210309020109180e030a09171518030c07090203060102010b0d020603060d14150132090c040f09021b0304030807080f09040905070510020c0102070504020a0c0f1a 74
    0xe60391a801c003074081110712006021006c50102d03401480d41e0034100c0460710125004200d032540d84511004400911020130510242c0619031451100035402c0d0020100c00c01c061074415880340f0003420720030340038486180b03089200304240240c2e605810040e060390406640e8045640c060b43c402c80b2143d0040d40703459010a080d10b06103d0080e0129009040a8203603543c20051000c0d03940003c2d03003580c103030002e920343c0f01811808005580450b0040020f10115503d003082041441c0c8170010154402451050380b00c0d407003d040010410a8641120300f030742c10352118042400f8038820758118840d012039140707010401a282e5001019481c50404082c41c081119202d5103859004030702006210760800c01514010428407009880d0054688201c1454101c1c110002012200c59107822642504913030702c200328a1403d144080e51092031800581a91240a80001e450b44564007405119640c081110280c0920991103000c5090340011082c4103025142020300b001320b4614268016001044c0005e901 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 377069667 1250 377068417 377068421
    0x9030b1311060406020a080702041401031a01090903020606010c03050405040c03020c0f01150603050a060b0d050a1119051612110f03090612180601140102070909020102120c0102162103 81
    0x1c950145d030140100300800e40e01e041c55070740301c560140d078403d4071003158a0780328000041060003584035003030340341411000122148094505902c02e881643c030384655000440e0b000300c0d582c2d900010920b01400c0c40501441e0540d418082e503081160031501d0982a45d0406800da402071449250039012a00d10003c21040326082c0d40c0c04003e4019440c4a2035810004280203030000c1d03030805010040410201c0d15114030030680d030061a907250300c035500c1e2010320404590314400d010a0302150394501e8601403500c608115800d40410b00102000130028a00a480c900251410041780d03002907607242d52052804001c080c2849494201d0702401580c0449907811000801c447c400c40c000382602e0b05010310300e415800800002088440c0c40c40480c8400a02e1070000d029441c082c1229414082031006050002441e00c41c1e250000301035070b0710700303000b0381c5c0940e0300003c1001d00c8020b600303980f69554a185203018064010b0514441104406060a0040016100f078004142c0040c07421710400013011076044007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 377070917 1250 377069667 377069669
    0xa0f140901090b0c010e030a08041112030901051c020c0105061f090b03090102070c080601061107051c0302160602031903052e08070306050a0b1002120a09030b13110604 74
    0x702140301c422003006410496400350283d000c80c14000110400c40381803a42c1590300c14203032140082c100e4001c110401c03881c402c611996a000344e032010000d44600041c0343d664481c644505041c07000115014580c102c01000483c20003000078420340d00c441801148074041c0c24140d0b4003601c81c0491540907071401c60049030a000017080341e034511840318940448200c850b0310280406100d5502048003501040c0170340c89040092030303044014402985052402445145011100790682e081a201005180e8650880a6101e01c04040080d05140d444c03400760b2602021001039280c030300282000140258010024100986e007005000401400050b001c404580e8100c5d4030000c3c0913070303e0440c0d61000c50801c0d00c401c40425a02001001d0703503200c0011a252201c039600840b0b00315198805c100e4121030f13502442583e1201902c1900b072022440750040d403030300c005100304e84e1000d1011035102e40706480b0340c66400c01590050240c081d5400d10141403181c517201c1305816103116640510380c0c0040d0400a013250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 377072167 1250 377070917 377070919
    0x1c0c090605010f050901031116150b01020c0d060b0a08060f040605060109081c2007181b08090a060207080d0501080f0a200a080a14010b090a200a0f1409 67
    0xb17032500d1035078401507000703081028640b1101e14090241c2120522100b2400345118042d00700701e503214415140c10025110a10718440c1103410944524440c2c1d120724840060341c940c88980403e0b0b0754401c5000c20780c022503d40c03241e00b07070744111000d000b00e034034448807034074051406060300780f01503903130440107444520711440713042c600358001c0d5006c0412000c200001501d4080914042000110303090200c003100f101c540403440980c00c419002c01504002c908041d00254a116084c45902010344210302403201c001801024412841d000070f000c90f000b88000b086a030b0303200304115140d60300381c10304640c0d6802c9106090702a80c54400042019580090783c0501c24250000400081300a036485040e510602c06c0c0560b00e45405880d006103550b221641040900b0b03461000b8034101210341400f0000707801701021803407164036081300d0f400243c40b50190282d00041c500e0000c2072118898082590f10001c1d1050b00c82841c00200d010f1032610b9004d8044400c40c2aa41e070364811404030f44840101d5413085140031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 377073417 1250 377072167 377072177
    0x150f0310060804020631062714010c05010b03060406060e09010b0306010504150e09030304030f05120103060b032103010f21030c140307030c0309091e05061c0c090605010f 75
    0x1100342d0940c6c01303100c0314285900d412449410100214900c05d1400396410402c017160130140100700c008480d824003074180d9122034004032031900c0c200170301e8803044000132084c1c10040300c0340001040c40f1007500040c00285d07020b022150316103032500740381004240f64059210f0780d483c0b04000c104041c41c1406140c0200d007000303024100307036468602000010140222000c0a490b2078050024100d0300011a140c86480d103000079540c1c0b8545840c0c010301441160764100300303100c800c3c010207940242c0320350710a041d00c1c2d02520004600b41c210001902d0600140200d12403201e500f0fa0f07011a9880640186040307800241c0f0310000c1c2521800c0303108061b07510340e506c1ca81103010f291104021074404d500c80c1d0700990155100c001d0b1008804101c4c0d0855000d2241034020801107480d100805612407141c00040968950421442c1c080c401030102100070011441a02915003022a4480c0d803201c5045020035100340072108840304501d0701594020462003000059481c24400003050f5010303000a000d4044240e5035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 377074667 1250 377073417 377073427
    0x1270905060f04110a030513200d0b150109062303130507030305190c0b180f030703030608010c080601170403020a1a18030406020318150f03100608040206 68
    0x151000510005144a40c00b0801e00b490804a03211845802c64800c1d0328a4082e5560080400250942e400504a251443d90f0300e401c1c1d001195046c003005c810070400e8611441c65004030000078002c40039143c806402100f102e801e118459492409450504000ba203800320f1307072580ca031030688032000854003521020480889550f12081d40300010740e40442062034076840080d443d03d40600d0041c161b0000c0300403500008000041703c0c0e50009140360380380d403442c0c00292503240d1b84c0e13501c00303002020f0013603111040c1203040483ea40303030701307001801500e0b1641e401c0b00c0d181c3c002c80c20000c0c081c021900c2101d5442d40303000c107410302d49482400c01d00d11131801030b100d0801507a42041d540e0014031000304144d046003e230351308440c00903040990f0003410369690342e1401c20600740417a5012100001c01d0a8161541c03082104000c00b0f40c0200603103024200c005c0c05005180540404151108010f401005a24000281c0000c08904441c060350080c9204c0c0803101c40d00c1c0d120a8142c411a10036140a03500206c2482 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 377075917 1250 377074667 377074679
    0x1e0c020a0504061d06150c070906080a02060a030207050a061104090608160605280c02040e07031205280305010305060a05041e030203071a09010b150d150f06030b0127 73
    0x130506400240c042d00720031703804080100c01050364110311412040d582180004011740b201d42d010f0302002c0c1a02101a02424142e580000d0311841014038031000e0540105040d424024184085280320b40c00c200140541500c1085500c3c059206000da580414070342100400c0004c40020f4032019a4140c90100c00700c241024015201c5400404040301021420002c04c07170321180c10a0a82994035440e115008080900d00c100001d40e451480c10300d140344c2c000d40c410008543d28900101946000e0b0801d00e580304103010340b0000180d50611055500d441903007666100d20b50550100d030486e030180041d07900640b1226415020f0741c07410758024090441d00d8100b04040700d0a50104c102c10307446401240c1c505212545d030725001481e02c0004031143d000520070444143e070f0a000d49103a1010486402e40c2190344045040c015016001802810541c1c4107403410441c40c2d0842500050b020811001c0500e0780c2c0c0c4c01d801070103009242c18a40c00150040c80d14029150078002002d0328a030103420700554542012 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 377077167 1250 377075917 377075969
    0x10e070b07080708132301020706201902010201180f031d0306040c140102030406120e01110d06090c0c05100e030f16021c150504031e0c020a050406 65
    0x2580c181d64051042108600141c50b0000820003c1c03148228000503511b0035513400d0840c050b8a04000a480660050044680c0d002c02c05005603069414010340e02c2c508100c5000e43c11144600740a80c42c881c00080082a19520f180200806e100b6402800481801200c800c04c1c3c0b202d049004004031178003041d1000103030240c003120303000008111a805c200300c24000040e1a00400742d9090740c00caa141c98040c81035129240500b095050280029445c1c10b240c007174000c100510a91080306210ba07101c1705842e001d002034100b01a22030200c030106485511290607400203001510400814515003071103600000c3c0905034508510303811201030610190303604d0200d40a002c4480281c0900e01040000420143c180030260490800648034031801340202c0c814401d0072241c0d0342c19407407a4081984120000340204101d440a10410000403465442d58642510f090403107407500c10f0303421600e180594140c4d40c001d078455203140c000c4a0350788201d0355403001d0000b103545074040c4840d00b440481c1c03906c81841d001c2c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 377078417 1250 377077167 377077177
    0xb0703030b030312010308031e070903110d06021218010c0e0907020f1002040e090111042106050f1e0601050d0b03120301080106050109151b060f0507050318010e070b 73
    0x5400e69190203444d00d0400c51000e02604100c505860100901513074220056210790441100c07050200e0a00388500c1c013a100b60391902c401042807812880c00b8500b0b031100b0204038410355000400395101c10b981520031034455000c5500b140300c10f070389144040c0c80d414140248403c55003030b42c0300c420350f00400106000034030000818032419441107410740c1d68002c1040010980403070304404d0041e1114100751040e00d0080c0050a030000580c140700021110701240d0040718222800288510840d82940c1d44205441b150801c029012520b401c081040008541000070f00c584407003011100e58901c48100d08a00e0041a0f43c403600040040c84080062001607120310280100101210142c2c02c52050801160f8002d0b0000c80b41c1c1c2e5100c4000b0441960000034078000707014291004c6400d0244664020442d00320442c80504200c2202c58071014441240c1c045503041c140314405100510700040c02914661054070b0f011012001c1c800c0e22450140d040c40303002400400c000250095500d04890241c850b080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 377079667 1250 377078417 377078419
    0x1a0112080f120a0b010f0924110d030f051303090314011e06090506010503010303050f09060d2412020a03020d0302120429032e1707030605100b0703030b 67
    0x8200b0248142001501e1910300c10702e0301401c0401d4546204000629162640b100d020502a0312441806402494004034000c100c2801c10841c20030580c4030101c50110340403801071140e0261450051030554950051240480d5a00050020f6101e0500da0b2101841800e00500002c80c0c0c1e401c14000540c0c1c4850092070f6002050010030049215030024100001104d1201080780da101000c0204017024007d0030781c000b409007404da09642c0b451f02d01401c0d6200c0e60485000ca0500095144081d07070f00d85007521034558022804014905038521103003120552550b1224695000c044001480604840c1407450035070301515120a0314a10341c00d002079203807015411800d50007000e1071030250850300300c0500f0081030340444113002c40e044004460000c1d10080710416900504000700500e6218540c913948855402904d032032541078680203c00409220354006000c00d40b02030300b080c405084000341000a0340c0c001c00d808c02c11a22014156005003242d4882c81050300c505004e10804030340254020451010 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 377080917 1250 377079667 377079697
    0x603050705040e07200d030207060501060c0f08130b04080a05070503030c0c01030e030708030c0406080702010515010c110613140a030506010b0703090308030106090e0906010f120c080102161a011208 87
    0x20401200381403030b40305c80346c9900295020840300c1c18462603008680c010300340d40c00c01a12078a101e4a5600320050500d0002e08070703500000784a080c07045e031001500f0040084002c134a80b0b403610758100a072107900510003952240700b41c69020030301e490040b0032981404804402805280300740d00064000d0440d00010499900050051401098220008521603ca40e0001564590500314060600003026010408581c50803082007501041c40120900b884000d00340070f0b80050281c03504a015095001c2000d80080c004112104040a440c40b440d0a45148804021141c03860806000c4e07010b074140b00183c0168400e600411150390020020181b15009103020b400343e684036261202182e0003a4440c10016039a03080c200320004140440c3c03600000303c5000342c80790b540350180445c0c400c14580075428028000c502003004001d41200c401000300702000c02991101300c448620300d080c00030000c090303030340003c51540c06514205403010075060700ca0368000b5441e01e40356a224811190000c200030341281d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 377082167 1250 377080917 377080967
    0x609010504091e06020c060705160b04020f030a030f030e060f0106141303051b040b0a03020f1c050a02010207060f02030d020304020105071b091a0102030301140303090a0f0603050705040e07 83
    0x8601d0f0028801030034001c820160b60350340060000c0346001402040f2200300607080c400102c0c80d0381440480b0300c582d9000b00100040391560b00000345000144070280e5410f21038001506d0030150085220110460140c504204000e02c2840c9551038020881304041644542c3c00140100c80c0520103441950031030100d040d05202120080031001e5404c0d80041d565039010700c08800c984128840c1300880900199000d205140e80c08000c00c0a08900b400001d05c03403130600c1b0210290703440d40580315001204203c003c0344113401d10300b0010385030840d28000341d005014001c00462614024074061400d81019030056203010b4000103200000d40010b44100e0402c0400c0005801299542c403800e003c02071026105440c103031500003080e003207507030440c40350100314408003072200c40707a03004010b49044840821a484014490200007800e40c81402400d69101c12841408101044c800072070320b090b5601a01d0070001c036120f0341d405651600451144400c815800c80000f8400c510504141742c0c1038901042c080e100c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 377083417 1250 377082167 377082203
    0x806041506120803011806030f0201030b01030213170c010807080f04170301081506030c0303040501030b06071b090b0301061401050726070c120302060c16081b010e06060901050409 79
    0x440014002d40f1041c03808401800401190000a0441082d09000300201c030701c0c554507620903051141d4040d0600d5030720403c4412990094045a0104000082c0e030003905445003181070a000c001c403072044603803040000c4890654000e8800c6801100207490310031569845410300c40180304007c1045030314015810b441c00c110303005100994040c25162000d0440504010b0f40d0075802da50091640e8440d5101840322849a1000b104071005e5030401e190200e45251a030022402600c1450401440300380d002d80c1500340c0c0c041e440402c0301981e61404050141042c12020542a102180a041624141c00500b0324082d0f00071802041c05500c200020755032888004008512480c000c039070303600c03030f240000340c0f100c100202c408110000d030000c000c144082d510203490095a84170b004100f1040400000743d51840c01c0c8510180c05119544144101d0743c409590360f41d40c1c044011100c1680b1290700308400c0440602021132030a218050150a98050782e11741001c21001d4203120304141c1e01c1915000103a428 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 377084667 1250 377083417 377083439
    0x622020705030316022b1b0510021c02041d130b0a1a01020334080307050405040e0c13051503060f041202280812101701060806041506 59
    0x1180c0318601c2200812288000d01034107050110a0400c504111030100c245186c8004403070303007030006042c900340d00440c80c01c4c032680102024105000e00188141001a10001c240d0380080040c01100c00100b100141034841d10002c1e80510700030482410034038005210701c000c42d0760b034152380080c0b140d100c4540c42e86a500da88091301b00c181d80440d140c40e218650805600380e280301c8624009000c2c4011403070001e080800341445886500141c0855034407200b401c207d03142c1b81c03401040458000c040a41d590034011000350181e40325102d0180100d0908184100748403010801001d143c10182028450382c2441451a0040c2002064148185030114407121070f5201000058401c45030122880030a00b024109414104100c0c025881190b01c8400316048003000b80c00c0c2414a20105d94810703289000915100c2c410380150516031003803540c40c104001820b144420898126042d9100080d01041c103030600509032080c90145403500d41c44440424001030300b40111143d100300c01607002a90544480360164 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 377085917 1250 377084667 377084671
    0x302160b0403022503110307050a0602010c09050a0303050717040f0303080f06060702030d0c0c090f0b041a0315090307140a050601090c12020c010f0e012306220207050303 75
    0x800410312001c020070507804100c440d0450310000c805101e0004000c0c5503011020707403804018444030942c0390002c281d8404200c030b0310161100400b5213503059140c1a0003030080010030360500000b4140c400014403400c28020101c1601c2c0c00d65120b0340f6003100ca8903a0030300c0780e86140e0a00040b0008110000d07800c40004241e20246100740d0702c3e00c50600b0495650120f00c00302401b020300c100310400c84100141c0e03000481404007059403c1800c480c4856091855282079903901c500b8625080003100b4140c80003903800710040c150111004c02480300106600880503c8000000d60554040110300d503034182603a90355a849070311041240e28107402c5950b0b842d038840d0050041e00d0300f40c1c040b840325010400c0902042d030140800c20307410001e00708900c4008003c040e440352245d02145d400540e088249400b90805546254461410721021040c00141c9000701003c180e20b425030150a0041c2c14200c2d0352646560003540000c2071440c0007414480c80d4090901e412066000c00d540c200328120001d40d0503c00742d8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 377087167 1250 377085917 377085923
    0x90b25081c0b0901080c10030b030604320607030b06070206040b07020a08010e07061b02191a0903030406030213030f1112030703140a110a0b0a0e030a0c0210030216 72
    0x60591104000001c1682d41d001e1029105594100041c8078075540080e488050301c0080390b0086d0b800004200580041c40c00303500007070701401604100f000307106681ca0892880c2200080d681d800841400c415888802003c1c0745041341e4200d800443d10003446900082100301005200b80c2c40c000d0b071540094055405680700c082501008520501580b51200c0040010404400240b1030355008a0f5005d4175051240110000d1290002c2c0c0000d12540200c400382d54940d0240401c502c00c802d0460240400403544141d0311342c0c299005007600090381010507071303429002c081e0086040904084c0309138040e41011000e00a40c0b5030641d4000302185c0001c07080c2406034018901d04000d8201c001c00e200500d050b81a207142994000c0100c100001c1e17221039071400200d0051074507916071604000881d4000c1c540220707244184982c1080005008192400a0040c9403001c81000100b40d042e21854590040c0000c080200b80c2c48960310b0090f0420050302d5001400c907140043c42c000c16800100110300700c010081d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 377088417 1250 377087167 377087197
    0x30a110303121801050709030507090f020910031b0f170a110d0b0102010b0d02030303040b04080c07080c0301060801050403120207032309010e091314030d02160b07090b2508 76
    0x2480d4014005e00c16035030410042d1908082403800c60300c801c0d50701c0846101d16505c1a1b540e894032061810b2542c180d540c100001048200101201923000f40901580700c420240c140521035a000c2c001e0141c07480b00061441c544400c80100c0c08028104401800207088580030780c0c80c0d021850186a14000405060550590026061003550002421900902219070007103080314410400b40c0d40010980e980030385e01c0500091250f60382c1c40c1c240303070a000d10700000000c0c0c07043c01c03000305640501084a40322000b013074008000059858100300e090b242c0560b00a004075450031160410070781160000d14180d4001e00307004070100c040c44c0300d040103140b03140c450083c516800714030b0300c40c01d42e44414095003020007102c01c0003a5040c84c07000350122110303a171b9000f800c0184030302d080018074005005403114003030160b804640f00c0d105a0301b08040e9003100d00e0b00302c850b000c811000130b100c6400340b0203550981703800040341814840c00a02c4015007507220102c1c151642c003005482c800042e2640d00425454500d0582c1d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 377089667 1250 377088417 377088451
    0x218030a0c0f080304211103010608030d050604020909061c0210050a11060708071d03120919060f050702030a02130e070b0f0a0318170304030914030a11030312 70
    0x2000e1110703940e4000030f00b01e8204000401544030400c444450022051b00240c04080941c50302080f0304000b900034030f4055007449000a0360300c1c008809000345585809050006070380740401c0000724814807020a40c400201d40c08664030f800e183c5000082107040c08401d0300298802c0c1c0001c1c000301d40203060100003640c00900700b1060740d88900f8a14403603800e40002d10307190414050103030940074010001004c0040c1d401c01c2c07140080380000003681040c4042d064890074602c0440d40b0001d40e000c5070500340643c03124003516001c914440d020904881c010360b111340003c02c2e51481142c856000007026070349132041c034a8010160751207070024000300360142c00000301020b01e00d00160800d00207030310100940c2c10a100d6140224044001ca842c1d80342103250010301001d5039161401d8900510501404040321840d103000500c41107001940218000e80703500154965a0070300889008840b04050b0700750b0018031851001030140d0758040010040102901d040c206124003d00303096804444401021005800c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 377090917 1250 377089667 377089679
    0xa0203060412110712120827010908040810060501050f07030e040e0f100c0c020d06050a140702030406090902160b04021c031806050702010206010e2203110d1b03030218030a0c 77
    0x508644d94000a04001c145850700c5071003174003015522140c030340c52111582c2340f24044040030342c025100241e1089889d520b440d180c9107101c0d900c2c0c100d801c41c40301c80d07458058042095801075066400d00951201401d1900029a804440307203050345c030505402c5900c0350881000d50340300b0300240358807100c003c0052510054205100781540c03004060003052241da541c248000d41c841c8140202c0403a000b8802282607201e442103031008220f501c41c07104e1448140c00921080700c3d80030009008031880d6a0301e140e401c40d103840548089120303c2c01120600d44000a4640001d91810821079100c0c0c001402100c000304000010914500e8440f412070000702190004807044e070a140500000d4546490140c0c2003d01c1540080e41e1440c060041c2c0c101854590001110081e581d86040e1020031883c099484074612494050110720001c0303c8803610340151074103140820320a0008200015500341c41101400703294030260001d503c4801c00c2c40964442d441c2031082c1e501e0400c280354105210301e582507007141c5011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 377092167 1250 377090917 377090933
    0x130605070b01091107020120120408010f02040f090b12010c09050405011401020a030c05070312030911040903210f020f070c06030209010f2f06010510020a0203060412110712 76
    0x103000010002c0c5001071302c414100c0400241d50702250b0a08186105107024000006035581488c5060064410308100c1e10034880450050000c82da4288024030950b1000307075004041e8062400f801101241c50b02c410080119990403034004c0103005030036a82085802e50180342075441d81040080811801001001306007010b2007241d004001e98080d2421200d000e0340000e44800c0030410103020443c08080703410070301c402401084021a405035010141861114c4040c002e0154100c050f03c410326204045441800c01e801078943e020750650312a00d940d4a0b001401d40504000b4001134006680c42201c020240c58a20041502c0d454600c40a61211202c1c5480c1c012008160080000c050040c0b100c1300141c0d8024058907a540742501b0800c403400d045c000c00503041c03481484010074030801c0c15a83c00e1200804128581a00c505a07810340c2c0b04203a1060a076503070720b20070000a405074072900010b004540da408101100e1181854a407046074406242c4c82d15010340d5411405044010341d000208201401c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 377093417 1250 377092167 377092169
    0xf190f02070b0903071202130501090f0e06040b071214090f07081b06030a0e0a14160b180604030f050d0f030e0c281d06040207200303130605070b01 65
    0xb0541c01e403038844038001080e03c038102c0e032041030b11803102100f0020855648041d4443c2d078480c4002d003009190382d5100c4400160030a0300c00c440543c0d140407940c00754100c000c20568407458000d200078149844912044480400803901101c00d9a0b651034070404c40074070064000c2c0070f801c40c68001c200d01c040d09511103040c008a0340c400c280700d074000f05158013160400c090007103200e4412141a0749a9441415100c0509054100c0184a02413203810104001c40c0310801c0008260394000c8540c501900d08003051760700190702812003010b01c203001c90080000c4030303807a95003010005032156080c680c3d255151019808189400c5901ea080b00c55445140d40d404100440b2080140c9400e00c003400fa03040000c0d84036021944c4450040741c4404244145220b07035420a064000d0804920f507400f5611007800c482d07680030b00002c1c5000c0041e440421101d1501e80203552802d50041c500c08080c02052900e010072030708240c2a640c040c0010301a16500509400d51100101210b403140d40d41c1d00124901032841c0001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 377094667 1250 377093417 377093429
    0x60f11041a030115030c1b06091502040b1c06031e030206070503100311040b060d0b01121b08041103010204060905030f0d05030705070c1809051b0102060c0f190f0207 73
    0x2051004000c00c4a110801d004130301182d06000039410952041115155082001880e010460181000400c01e0aa01412246010b54410701035010b002082100b41c1c0700c1c3c3c0c420f00c518200c090002031105458500c4001c00700e451135a00090030741d5a0743e58080e681ca210420319544616418600d4207041d01800345941c82152880d2543c913600e800444c191400a044c08007a0621445501800098485c0c1d4004d804109004200030f485503d0100300f040034011005c00b540c0021852071503007016050070302442007a103000e96074175241c203c4007210440340307050014010344240200041e480200c0d10284014000303001c00d41c2e02c1a507805d04240a05103810700c0601c0c0c401840c0d014040d40e164540e0b02c101034035004441e901e00580d03141c00701d05024903028042c0c0c1180d11a1103401c603401e02040c41d0b43d8000110507214005581c0015110020171100c10007a6080c1400341c0c0002002440c1001c0030401800003207419184a4101905014004803560b0401c1003240880e0003e400110055010072441e001040 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 377095917 1250 377094667 377094719
    0x20a080901180303020d0213090204080f19290a09021c03020706082e0504050106080405030406050a1709062a0405040906020408100f1422060f1104 65
    0x10442001e0031400b08107240c0681056404034908115090640455500300c0b4100c1403d00ca168035240c6100c002c0d0311511807041244908241c07049080c8000c01c4071402102c4110680c06d4074101d46e2240603007194404035120002041440c11055002c0003050640900c4c0d0110000402e200c00d44140b18020102c01c00000b060f11142130f002c00029070000f00c0384140c40322440d0540c05070b12020900b01d13031305a02c0307010070412405d540d0702080b0540c0300c41881c4c1d040b60701c00c640074492640c0c1e44c031054a400030151406400b6800801c01408030b180168001c05e5241072600d410701028510400c0054007030411b454010300b0750011810300403106d5000d840303010341810240020380070403654000c0040511540c0f00d800d001310780310f4040006000e51941a00d00400b0800c003500c041c14040214503000b01800000e10001034641b0703035988440c10200400307502c20001c0320010b00d10701e80c14000c07020704a6003110080300d940c0d80b0b80044c00c13811074043c013910740250b6000e00800d4650742058400c074980d104101c820f241180c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 377097167 1250 377095917 377095931
    0x150603020909060f0a1a030a0507051c020315041803030b06031302090603030c0a0c08060a2009130c020d02010b0d1e050a051614031b13060e0109020a080901 69
    0x141e40c5220340360304400103ca004d00d90b00c04c040c0c042484000c0310b03480000200301050010a0007540c401c000e510441060a0400c1542c1d903c4c00155400c6c003030040f2500150161540d078040310034256000710f40100ca60001805c02125490000e02518031003501e50416504a00f410020140c260003500f03088a030440d102d038210f280a85001c038603010543d001912074040540410390b0b40d00c0a1003101c640c0300d100c0d415180c00c1c030000d00b0042e240e000d0f035201c0d4115030f100f8680001c0c5d610b06144104203141d410040744d0f102000041b034003102c164201d20041035008c0f10f055440c0305210840c4c0b00d9035a2892031900501913440c444500a803c50703200600d102d02491a00e0341400024071319161544c01c402805640204091840c10200d24241a00c07800034403034071400c0845014000c4400c220001c07104603540000101c0b101c4410301d07458600d0014440b10960a100440096192001002900018180c00040c02659451500c81c0d0f0f400e00b1390002514540c001031800c825980407242c25030100318000244000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 377098417 1250 377097167 377097169
    0x8010b040c05161703040f0c1d0a05090f01060306052e050d15140f011d0f070e090f0402010905030303090a0f0606050306040309080d1416020418061506030209 70
    0xf8032401e2803441c402e400c060443d0041020046000144215441000303483e49000c1c5481e14804139241010707903401100642c0001c0c5203149400180307107031941113400e1a198542604250140002030204400f0b40522000d8035040c51003445031000850142d80d001c03e04c0d040401c104d245c83e00302030f000c40c0c4440855041d0519001040e40e515011a0700584132074000b80d03403c0c01c0150701c822509401013020382c2401a41d0100c18001c6d0442c03030250f5403c0e0000042c0e03176660005035100029600c0b12032040080383d00040d13402048060869808000340c01d1501c0d50f6445440002c440e0001118240c6060640300c1c180825542c2c440424409440709500651450414140e0301e030b5030b0741d820f02004102c01d802d031241e542000803640000008001c098110340c242d003032515000d002282c1c1c03030103248424422280c0781e8041c5881203c6408401e088040994a0311003001080c42d021100181c00b0b0780c203d92a00246070700302c6030841040f403a16025880c0007482006142d05e5000c1001554808410140180244502 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 377099667 1250 377098417 377098427
    0x6030b0d03140c070506041202010801060c0f141011180103090f2603090a050105070e0109050d0602391b0105132102010e0a12020d24020408010b040c 66
    0x3060300000b4001d40300c01c5442002460400c0301d41000750440c1011400140b0503851080e4052400d1003603d81e244d0790f0781c9035881201c00e4100c0e4840903007a640d8051449010481490500d451800758000751200c1429101c151015039580c0e000b11480c00c00000744818055000c2d80184001b802c0c24601448180700c02c0d104c40d0381c40c018812001c3d201107900345880900a1424003148408906c5645043d200e141604900c0c0d29250940019910f035400c0200041d10a40f107401000c0322034405840e03521140d414081804102041d16004a4109070b081069180413008114481c60305441c81040e6050326907140d0080200f00003100306403003568480d030340d19012010701011000c2c0ca20340038a05a5114103200c071402e51183c00e41c0c1d204607995942c484210b04808100b20000d6034180c000c1e210004e11855440600200082c284510a603610140700c0721401850061004221107000d4103500d200d523042e038001c005100164500420380bc0303900250402c0054000e000b1103a94903002c940401c81741c1c000483c0944 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 377100917 1250 377099667 377099687
    0xc2a0303070f0e100807030b0411030a200301090903170114060c0c0409050309010e0306060904120c060e060103020112330b0f0d060b040b09010c0f050607020706030b0d03 75
    0x81c482c0908005401d940701e20005486040c0040c038803200d0f80d90204018019940a90707418001a0810749220b0070f5040601030242c04a1140045519581d41c0c040d2180003400200b0380e90120b640900030401000610b00091800b03090120b5000584458620300682000c5805070203021046c0d1680041140340710248a035400c0d400142c4100355100c80d03d0030018244400751854640c854500700c90703c0103000001000d44a04482a20341840a44812080540d1101c0482d882076001d288040010005641e4074662180c01038181031201c0041410703560042a140d528003140050361202004105542c3d000700c25224415000e40104000c40445c1610b050400c422032086150001d00d462100b142c0710042c003250020181e02644989a0852960150301607000e02070800d500e0307051a81c041400980c5130110390450380d000c020b81e45003944820042d5060714090710107481106910720700030702184007844110321803135444d8042c001c83c03400d10710040c4c11500580c00c00f9000380009083d40002a0f08000815 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 377102167 1250 377100917 377100931
    0x8090709090804090e01060501020d0201020702130c14040e0403080c030402030613150212191404140304050a0608070f08070c03030510051002030a030c1b0206070f0602030c2a0303 79
    0xc14030344090b0500001e00e10455110030b007028a805485041c864040d803000064403426800c0c0c502e03951601d00102d0903800b0303146010754014402179805a413802282c1c03100b5060b0034075080007030303c00c0341c004807081030780e0000d6100c94134045c1c904080000b01603200d07484070b500c02c059034100c80c2142896000b087e51200c0007001a0341c40304400c0040e405015601e108181c0360100b8210035903540e00c042c0203191001409403039094042e6080d821115a03244680a12007200102c0d041140083c1ea4a4132400e00c5009201d01d0540c0718003040201080503215152075001814090301d03020f102c1d052105c0e0040002040c89404410002d5810078864031683c001d02ca03000d50f40e014600421030303880381c80d00090b00702416484598400d0480070030028a80d00800a01103942c81610f0401032800b003148241c406100909040341018203548a641c01454101c0c05443c109002d920740e60401c428039511081240d04c180c480201c3c8071004205642400000c01e01512206408503500d00242650101e507980ca0101500f04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 377103417 1250 377102167 377102171
    0xf1b0301050f1906030b0f030a11011803080d05070e030d080703020a4b021f09020d06060801060611060a0c022401060f0503040f140a0c1401020d08090709 68
    0x20340c4243d440c2c0f044500400314444001040319030307868010f4000e1814441881c000d0060810325000c5150211305003c1e201c0d0028840103000403500c0044941d040140e51000c0480321055012021809c1e00f80507049031020307890700081d1410802d070041d01c044e1191083d0361007580880b291180b01548002c0341da400100b00d0502588a072440e001c20f46510711820700b26514030001c01021200401041d0740440342c4100c60040c03081c20401c171000034906020010040002d40d100c28031044081c504628804c0c0d90502400d400518a000399001a4048205d84c0060f20402d469100600c803e55082c070807040180241d082c2804880343d0044d05a465010003800c10b0100703a81c0c3c0302046d5249000348415080e0900300000b11015181c52072124805140a000e440000381c6c0003100020701c1c80c0154200c1e4002e030380040700500e0074085c42c1d403000da02d400c043e400403643e8012104074400207003070044120041c0507416102c6804984401c00203240541c10498041013100c08024071504603070200d820000e0703404400c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 377104667 1250 377103417 377103439
    0x1507051e131a1606060e1602071a0f0c0f0c01030209010e09151512070c020319050115090b040c230304020102011e0f0605101202180a030305030f1b030105 68
    0x4840a03c2c00b58085070a03842ca201d42c1c8240c100180d544c4040c0c15101061041030b015103419006002d11641a121030000d43c2c05401c0502c0740320854024000e501c401d41c05110f180c40309400309030410b40c1041000d40c0c090750188070a0703901d5200c244084041240d00786400c6080c550540c0000303017502d042c00c1005000b02d030300902007a10344542c41c01c030b411140c401a100b8004400e8035600380c0f01c241d021184064020100038046046e46200f941901c100380d8004005182024a00c5c442440304e900e880c100300c42541d41c601c814103c90b20001c0106004005002d00050101400002c2c80141d070391750f040e000e04000032002c182001c0380c0f40c200d901e20000e0340d2062154407641c8a10050740100144a42c025024440100241c44c0145035080b00e03242d15103000c0140413156079141842064a44c1c00022804100c2039428500e28000301e6001e0038008809401155981c521400407580c0311007541c000350001a8000708000c5041101041c803a00005000382a0f41c1c510001008400140010700840340701b542c039010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 377105917 1250 377104667 377104709
    0x21023060a0e07050d0e03120c16021c03031104060206070c0302121201031e080f070f020613030c0f050609010e010302090a09150803130608091507051e13 68
    0x300c1d502401da034580b400200c1c10b043d2400343c100e801c03e5001c0703d40c843c01c00200b142d500c10003000303440066115007400c8205444942e001c80c0c11740c10420200c0c00ba04a0022101d002d603403141d817690f07440d0300c0c281130321f581038407071414001c040da20119008900c00c801000304002c1c4c40e03400104640d000d4120318001d5078082d881c2c54102d04115800304200c56500000c21001c00d200c0310b440b907a80c12248511581140c900003040d040d40000010800075082034014000d241080341d51000508142d80b1550101400400b15030000d02c440d0441c0010710743c10705c02c0342000c0c010005c424000b0406045c80900c088092483c00c0e0018002c2e1040303c00803410401a1840c0001c0c51340030340c040e02c81d0084024005410541c8490190b030041000c007000710340303020807128005a003002c0413040310419548111600345450a1400540e040d8030080d1641c00e55226890384034444076444c038220340c02403070244e45c1d003a500c04401d015080500c066800d401c0325124200b21100c003888902d00e008084a038003881c0b1000e4151644 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 377107167 1250 377105917 377105929
    0xf0f27080a050f0d06090c082a07140102030406050912030105150d0515040c170406021605060403020604051b01020a030305060a120c09051308160807080d05060102102306 75
    0x683c6003942d40502048004c0300181d55040042500c551910421054003041c3c4210b95261080c0d509a001d0210f0f02c01009a036a00318172100b00e0b00015040307440c60a12583d03241002d6900402c0d4030407090758080300388010003502e80541a0400c0c408002003050b00d0340100705000318401881003900c02e5103a081c00da10100040c030251002068101c01c20003092400500d00c82400882c00002072007140b420b520040e038103005504541070301203006800d030403955a030b81c0d4650003036200c00780c80300c64001e019003200c002407010801c0a01c5244a640039000314202441c0080c94001800807194901030100118134081c0d138006140510b013601460007280030340f03808021540c000059001420b410070441e07102810b00008164680843d8121002004a9618441400058006030b41e00600100040061000801d551100c5080140c000c0801d81d103081203907982d903c02c1707900c488074241481d41c4950820100c1c0d80c05100085a0320305001c0140101c5000e05100b8401300000010740f0007e000c00c20100e01a51185 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 377108417 1250 377107167 377107177
    0xb0f06030c0d0f02040c03060f06030b041b18080606100f0903050316050f030f04170c180402121f0903050d02040902090306070513060e010309060f0f27080a05 70
    0x29180d01400b14540c20800d84400030420184d00030390500801d0101288280300340c0702118003101407224034909184045000e00a280083c582c0503884440104031160319020780c214a112944442d041141d40b0803902d480b0000c1c1d0790001160b5002034040044903260840025002501d41c41d011000606040d01611704660981000d81240320105144050b040c1044000304540e000350200c0c4d9421000c81e1040350381e44607000c80710002c030005000412261064800401c00e004c014000e80f100c6800d02000300303106035400d0088079206503a0f0020311003507003001d02100c00a02180000ba24202020115846031201d00075010017100da91803120780140b5224500351840303847d82000035981c5036aa03c1540c80650031580ea1706200e805044003045409008008481000c02e01210051680b460900240c1e00100c1e040311084c113040d194210a000240e45200e40142051517010004c0c181854030440b804403505070300840c3c2c19143c6191060301450282801c4908158894a410703038824030300004036694012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 377109667 1250 377108417 377108419
    0x20c0307060903122f1309110d0c0c030e0f040212040605010501020f03040e191d0604050706030b0f040c02390105070b1911040b041806030b0f06030c 66
    0x2402d8802c4040562040001440d407241c00f405220a5030400d201d508000414000c0010b104031000e4081811340a0102404001c42d6001800004d10764801503102507450038008041081c60006410016008521520400e8081490000301404043e600a0000840c0800b2284190f04005d0050210740d0b50790100c42080b0b0705010203050782d080074982000682402e01409025001e151955203445c0e4000058808585419035201c98944a0b00614208900c0400c41c4106164854100d0f00c400403034000c1c2c0441c0005c8200052501d442c00e41803607070900e062a00102d007054180941034056035212804c0f1031981004550004480d422040705900d044400450184020f220100c132200301038081140c0c010842001b5460340c1486030307010045600e0f03c200817005007034000070750103d0100040010a0f600703070b00460000140802850061042c00c0d0455400703d014040005010300c42c0c8600c40c000e2040c1040a42000c3c80440c5c2143d07287c50b0396034001040802481c4c071034400640b603603070200201100010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 377110917 1250 377109667 377109671
    0x30c01020d140105030307080d0b0a050a1205070614040e092803020606010822020d0804080c012a0206030a06090903050c06090703030905060a140d020405100f020a0303020c030706 79
    0x400c4041e01d0002c2c2c440409045105521100002698140030003100c2186a00030010707403400c2050b44c22840100481d43c0030903040088000c0210b001c9e100d102c3d1804c054141c1d403d214a01500e203281441c903180b8103800c0b503002c101983c0c40481020004005450507594000c4254020b59281d0b441203142000c594031502400c2902c4403213440c0032402480680c9054020380c240e5100359121001918006400d5a0b11210184201e400440c2c2074008000e44680c18402400f01144030810340718100b140d0095045010250042814040e0540e0411043c035199880c0481d0080b4480c0b620241c40e03100c01090101070f009640000008050300c0da150701c80340203030680c000d04010300c0800b400c0003001500001c024420341d04c5000041f034003004000490380308984c0e05580e003c40c80390404044c000c00c0d07001280e031141800120a80e03c04441540c81c003607c0d491a216100503100d0385024104640101c028010f281406003401000c440c860b8045100000c9903018100035980b40f110598261451042d008040c24441c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 377112167 1250 377110917 377110927
    0x11502151e0c040e060d03050c06100503010c0c080304170408030d0b09061c11030c120d09050603040c061d0301021821070302041505030d02060412050405010f11030c0102 75
    0x56050303142030200405040c04030035640c01c2074001651083e40100c40d2180d03100300000ea180c2c40e06001c0745406074440d03c1c0041c200b541c540000c91074042c0a41e02480300c0600f120b014443c90509200d01e0403d14494546181e80c09015264903c0342d110107400038001c00c1d250410b600703043d0000412a40100070800c1126580e640103418280103000c0c1d032040e14441c011a902264882c5044a030f0400714450716000c06104540c036030b8030580310010030400680c041c05041c0030140e850349c0380c1c1d041c1c9500000e002d015000705100b84030b006080991540149104000034824080483d541c045140706550f45030615160f04038441042a4000c1e6060080991642c00014164000580000d4141c207540e400e4a1030319945003c6426081d9150b03641e01c0d00f643c158850141080546015040303411302d00c03c40d00c80441c00c00d0b00d92010909184090100402590201c001e202c00c11040d0420300d4101855803410605082c107107000280b034070b515103620104212400400b0501008240b003210034010300000215500c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 377113417 1250 377112167 377112181
    0xf0a030803040c0509061804030306050a03060609060801050708041b03150f0506010201022b0b0301062306031510021006230402030708070516240b0d02030601150215 73
    0x541e00441e02140c0510f00440002000c0c00d000b40305a00440c0d00521440da0580090b40c6402440d500034402e404050305c1e82400030755520b413024020007a500400000c01e5941c24500d0000030740b8425030200c400c40c0c0c540010480030342d600030070a9400c02c1c0e02442161204000c4401d40ba16409260000703018022030540080428110313500c01d12402d5001c540a00c0103580710401a0700f00e001d001c034920081680b44084860504107a4142c070700300384034103500007449280c08002c00e08480a54200d028040c00c482d507a005241c400c20200320b42d52404941803480d52414400301b403440c01054402d24084c107001991031801c0c3c0d009000103454801c102400b08072966680031014108890799884030354500034040c16404a013410700850b03215a1064845604545402008942c65032150f02620950300003103600a0000e0380201c07241980c41e8404481858450340b8101c0c02c0e0448103032204062140800182072401030314040b07070340342c1199009040c5a102a052403016402c00f0040102c2200c0c01100000300410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 377114667 1250 377113417 377113433
    0x1021201080c09280f0c0504031b0b09010f120c0206160201090b0117031c021209010207030c060b1305340c1b120c141507110f0a03 58
    0x40301d40316811508111004000d114446105407007000300c920354825004aa408048450349655000100010317140e030501d01000200c590822507600020302c009410018082440c9526200044440415800b1454112420316a1040b0040706041c0032a5070030441b0824020204811041c00690040c40603056400c0001d44840044412101c9513440c039804c258010310510400032220b038400f4401220ba400d00c1c43c0804070300c0170b02800310400d00c400c2054030a1603004507123034aa80303000c103500944c40b15041002d40703415240040840d5403d07031042c001070010136407104880c3c0340c0c107421210000780303103d403030300468000720407d0040c214407824141407002205444003150030302c2c5540180030300d05215100d0200c4111306080c100b000090142d022031008100346540a1a0a00604c020b07100741c16620011056819108041982c8208410340c0c10400b00c820301d01441940713001114008042d810030304025040b8091107070050b09414030130303100b0390080d03c440f5030b07003420040003c111888043e500d02d08008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 377115917 1250 377114667 377114669
    0xf0d0501051003090b0a0b0307080715030614060d0510260d3002070b0702010e0c06030907090e030c030301081b0103090201270b1b07050a0605091003060801021201 72
    0x4042e40c0740c0034509409910030700c00c41c1401584850040603035100d14030b45202616040d599203078540103101c80021003200c10030502d80180f0004203140380440313145001408844040d4400741e40021440e034030040703550352101226541c06002000003a213484404900382d000c06150004041c0100e80341c024003081c0c2c201b240707807000138070312a04030341143c0c218001c115104a00c0b0404012003200360300b5040090180e900d01c5a8410396045d400509201150302d813a0902d0030196810320160b5903894201008007020b0240003040c803402e6601c5461810140e1203640c5d1280c5a125000c219039980942c1011000144116410703030500004580d00c0756100d540d00790f00c4842c1c89050341080c4000c440202c2c102d500074003400b154990141c44010780595041c01610a25441070000e003100324008001244804d046400384c00314030706841c1c80c0d041c1325180d112402c1c40c140e40c1d500918820b54401d201040800da115044951205096030455480300c0b4401e802d074042c0540385c0200c01594004284010b680301c1120b040c1e4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 377117167 1250 377115917 377115919
    0x1c0e0316050601120804061d09130b100605090607050c030709051f0b18040e070b0a0906031a0d080418020910030b030c0405130203030c0d03050702070b0d050406020f0d050105 77
    0x9002d6903680c0300404142602003400509143c418402080107601480181e814070311103040241c890341402c0005184030b001142d41c003010340c4403d100320082c000c1c04040c01c0d40c0000014203c00c005402c012028184c0d0040e1070405114403c0043ea510801209104211525801400300d50005840f8043d44010703200031036140c05803007181c0601040215100004030116400c04080034681142c2c0800c0768400701892140c43d0700640c81740b81c0c02041e520104003a00042c80d80000141c0c070303041c00f01e50040100c07515521010805003440c2c0000807039036241c182c441c10030740200c480d0501000a0b1400c00024007807980004500f42254a040030018802d400a08100f1421180204c04000f03190040d002c86181090460301540044003070740460074181e01194024402c45581c08000c41282d000030314561000c0510f0001d90080026142125058003e0382d41128550010713018503407c0c0080c0340043d020300f03d240d12035036444030007280074400a070b41190b650b912540344403035450341404903130f50140c0000c0c0b08403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 377118417 1250 377117167 377117173
    0x602040602011b0c060504140a030e0301051602061501021c0809011103040f150e19050c090915040c09090305091e0d080d1b08040c1202061c0e031605 66
    0x80e4068038900d282d0042e080e007143c840e00416500d90300c85e40010400188100e03040b41d16040404881035040201d511000d109030b454481ca04044400d050039108007400405800e0060115901c0481d004980d07254841d4921140c0c0d1105846200100e21301036174884205d002d045031103049190181d100d0785e11072003202200020301000e401c00c0500c0301c80748003c0b0340240600f22139040190014002c16060003e1340380e519008203904c0107c0e0703003490606900296154400c24901c020508000050084604114044400480307a19001e84510344070000b400230940000b9000000408024404148002070720b80c4840400c1100f1407803a018000342e2210395480c0c8a01d000949030403c3c01c05502c000d1515100c05810103814058a940c0d005458105076500c200443e2554400d030540c18030740d61001403894841e590000981042e042003d0341145c0c0da00840841d00b07411800e0f0000d030302e0748801c80b0b254154200ea0304898030860b0800c10b0090501821081c103900001035208c6070300900c0f0080c543c03914068415 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 377119667 1250 377118417 377118431
    0xb03210f1306110a03080c070c0509010f090b09070207120f0506010b040305160f180615090e090604080304021c0f0c080c01110d0309081605010501090c050909011e090504060204060201 81
    0x10f2183c1d2070a184100078000786504e000545044031160150403440e1140c18021611521540064011542600312800b4030340c6190082202403418010900c0004041d200104e90781080f000080d11080c943c002d07601c0c004050400b000420101c40c014440283d041b000b82d41c46540c48540c800d0b4594401c0c801030b14188038100c07000d11051103d1180318111450004801c0001d032808003012864010f42541c2456156100760010303003042410b01303180c7c441203d9500da8142500b07024030071800703020103011106183c1c444010040012051030440e03400c550120f8070215404e4065450048030f0707102d01d82c006d1011035440c0080040041c4d10107130f40d040d140c030a01a90488d002d040d00458103946680610b250725446a0701034a103040c003940c05074415501a55085d1b1a100c41070884188400341e85078200c078982c6d0b450004020040f001c0c4150880349805242441c9040e440d0000255011818000d51030003a02c191440d48036420290341c4c0d600201800030091042d89400e0500d20025000780c800c0d007025500b44a0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 377120917 1250 377119667 377119697
    0x60506010e0f10020f06010b071209030b070509060d140f06100c0611130b0a1b0201053f0a06060206040807080f090a03060b0a090b03210f1306 63
    0x300c40400d144090010b40e4614808410420328803003099190040d0300440e86440014a420310001e4080d28802801c0d03655000b040c644540c04c07403801d000003030400c11681c40a0000411301c50032030380c01c85010320b0055201c840c4080060341510502e1134080701a441c0401451486030401e0016100ba4404100780c81550f4440c0c0501184d100340340c1d5800300186060751440c0003d820303544a8400040c60721402401c282c034540c020010000141c00c0000582d001041840c1c0040e0301103c0d03c0954910742d0105901e01c4215400a0703c940280712500501d0850130b4801c0c84241d030440050f81c19204000c0c2000305a0040300000c174141c010a1304c03030b50505402c0c410003142e1140002150741c0215440a00545005200d0302d42107075035000b01030700405102c1c080104581d6507640c41c0d0104007540c02040c1c002543c5c090141000820500c0b0780c4000e480c1404d102a5401c80c2d1340c00f1030004551100c5c8000c021807484185c9007030080b4880c0b05080d90a0080c085252009164100007110540741640c58009000319158 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 377122167 1250 377120917 377120927
    0x1e030412081605070b100f0b130807050a12060b0901060c1110020d080711030403030f021b100c0606120807030f0206150d020607060504030503071409030a02010e061c0906050601 78
    0xd2070b03480410b800300802c0300014100310034142d0103d21459014826038440c1d0b071403034016059511a144080021801c0140c503e080708200c8024088640104209441d00003c90150b400c14821010701504148a03c0d09100150b000f410500c000280111403540c3c4501024024120380581512002d618030340e0f102d002e0500103030740202c010294004144450342c244040340d031070000a0130342c010840c0040000090480800c040d00c081e40c82078a8910815040306d000900d401410b031903141859804014046454940b05080e10310414285000c11112041d8240300c0054401503001800f545000d000c0d003010b100000c000b80503202e10079610b14449124030361003241d80c0c103016980d154020144100d0148d01e07190408410803283e201070407041c00c01c3c10079211b9808072081120103401040c0c00004100d00a80d1100050010041b0700384000c1c1003507200c4000ca50780b08800e04000741481034640c040c0600d0303030310b810945410041032520b1a1210000f0100d84000c1e0450303e004449103410000030600da98012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 377123417 1250 377122167 377122201
    0x105030903040b070516030b060405071d01120e19021009140f0a08030d0c0311161209030f060b0f1503040303091103030a1706010819021e03041208 65
    0x21402c0600303028005000307510021080b64588941064458001e02c44c2001900840c0904070042c6a85045814041500d800408071000c01041780030341c04641080e035458022015080c64101050010100160028070b4110700200c0f940c89140d14100300e071071002710b0b401421442985c520016490110003524070480381c2c01000d404c00c440e0040a8050b0509000d5400d00340001000c910301181e540e81110300319031260002405054032101e07000251901409680c2804580102d090300d841d10221910001c03416840004041e468490304007181203228051003000345800c40d06161641c90b25141100041902c072240500406515403900098904a64000e4090142c544558a980d9403940c0c00c60042040c41070440359000c991516000301c1c6c40c1080034003825891a00c401140503880720420441d0400144503d0410400c0f2040045c141c0308000400b0300c00c070b441c10015880b9006555800303524121445d24195081000c4104001e10844001100008000362a00c0344151140c40d441c000d05501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 377124667 1250 377123417 377123431
    0xf15041b050604180f181403040515090312040605181e040c140c010204090f11070f050a0f03270e0c071112060610020105010e0f0a14010e010602010b010503 69
    0x418041005400b189850f4203140f0341300c9020000d02100c219a04400320380001c800b1150480d4040400007c01482ca0b645003508240d100056041618003c001201d500078000145840200401c0440f140c2c0c0b81004202d198140e1000744548468a485004046030044024285122280c1810941500300080013040b1031850784449050f40c1015070501001e03123091002c0d502003202c0c84c20807400000740003010b0081980c09000150b03890746031100d6907042c1c50100c2100d6124510300341c0c0b80a0740820040464104580c0000300550804003401d240d400c10b0301c505c6001d07100c80800c14801e0200b40c0d1001c104220701d251624006c10241d003852400801024900403000001002d01c0855079164003403019000481c4035001c000000c1c031011300400e4614400c4883c1400540c811010301260f4540204542c58124051008000540c9031146042075003401034083c2e050758544c0c00204030f4030102900006100b11100002600d5542c0d0703040b414940c0c0609200e05001075181440075403044d0300c02e00032280940c103 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 377125917 1250 377124667 377124679
    0x6100806010603050403020c0d0c051314040605190f0203011a0319020c0c150d0c050705060408180612061201020a0e040e1906020711100503070e030f15041b05 70
    0x2082c510181c000b0440900140e0a52180b80b44503000e0f81d9070041e45c0030000380310b41280014185801c040c004940c5405840c20f9100c0c1c00c1101d00142580502c0625a0081d0800004200f40d2108542101d02c680e80b000b6004d0080c0c1000c800588080c42c680003103048403c00001c02c11103002542d0072043c680030903a90561944159a0140ca641c80b942d0080c01c13085000f07600f85e440f180200b400050451014104010100e0700115100d45411994492202100d1090411615100150740d03000d448900c001c00040480324049411840d13584142c00f500c0f0301400103080640d5800c0341103580310410008032551032058041d0360a0329102071060081d01c20b6000f0580b11100911710510811015200b222044600b910940c03800318a0060100b820b42041c5001303000050750b031841e40c06d000c50300400c8400891700407481080b1030001d056201302120740c062454600342c4a81c000c0800000e0802c0b07580740c803001c418480e1000b0100646a4140c84c6400b985c4181200408800d24020700d1144041034468035038440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 377127167 1250 377125917 377125919
    0x13110a060e09100321110a050a1104020304020a0b0c01021b1506060c031e0909010b220b030a09020109050301020c011406330705031303120c0203032b020711030610080601 75
    0x51100002c40148445e01d00f4038070034411080442c05d1070104002d00c16120b81e44806030134000d0101010700304180a01c00d40302549545045d03000304000310403503c1014180c2d400041d420342c00709401c3d41503800362440b0380c1c20310014000c8286a95540c440e0302c2c188000b20720f140740106a051070210200c80101c0040c4014600b0b100c840200c1c802d102c60b00d40e10f484101c580030803803002c2030358400e81154081d02c821240d0b540c94200306014a0b50f480c10343c1120708000b4000f8102401490154000d40c1c2c3d01c440503903004600f0035914801260760300040c0c2c0c0000e42540c00840c900c0211101034119403c04010211400280d584c3c035001c20031400820080d4141e11440242c11041c032002c0c0c00140c3d4480030000d80a107143c459141c0d9282d00d940c1c44503c50005518070340d0350030b00410940094401e4400b43c03d02d4420074150725900003a45034450380c90b2212001040e1000c0d8545a481c0d64805104000c03010003c6480c0c0244e0f040c0000e03255600d50103944203004000003d40c15200013031a200648802000400c080d07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 377128417 1250 377127167 377127203
    0x30603110d1e0f050d020601050d140115080303070311040312140c0a1a011e060e030c04062c25030204030209040c0806010b04060813110a060e091003 66
    0x90141016100d942e0000780390b02c0c42010320b88034400303424480c500ea040740e0030300b40c20204d0514520360f036008115080180108200d03a503007150224116040101400921100581c1600401f504403403480544a59403000521120210103544902400e031010310810a49001c00f081c94411400300901c510b11b550080c4603820300c1070000c00c100c403000d0803506240c80a40410b045c03821803020b17012a42b80302d1010662150012120400d8010040300c17810b0841041002040643d040c4580100703810014901c0987d080c81c2d40130816100c1c1400007030010052140c03600b060a0511407011a1510000322800603c070424004c50501482010010381400d040c407592401000f079104600181000c240d0248804005603507601d15907401903102ea506d408400f45800e64031410520164005511080140402c00140d6080105180e01c100400c0740d03031010f0025494410500c2c0e0801030b4041c0c02103a10700c80418003903003140000c001c0f80c2c4100e601a4041d0b44040314640b80c07040c4c1c0c2c0001019600204a05000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 377129667 1250 377128417 377128429
    0x409230105070e031005280b3c150d051005060901020307060c030f0501060f181202010537141c021606050a0c090819030503040305090604140f0103060311 68
    0x7160303280380143c105443c40c451243e1090150f0360070348500356680341030305007138074280040d80d1100702410742c480c0900349e40010014121441c03980c03201e002c0c14940e03502038142da500c0c40c000d86d01d9a18000c80310748070004959050010402104c0408120010540c0456a8507040054600d40c0310168020b501c1d0400a685100c0036000e4010050145038488000d0184501d650240174068034160b51043c040802e03803a4010a4000445a000040c507032040051005503d805200d0030400d4080c280300d45d50381d01c0b0380c010080403604c111078082c0c0000c1d0303904103030015000d805005a0110191340d0780d1001103840c0310301d85403078825100c111141c0804116211034141d840e80151445c4940c80303800140114071034441c1d4050b69030454884011743c3e0b8964220700415004101407001d08030f80c0b4002e24885200c00d00034078800307414480180501030007200060800d44108200c610002c4007400c2d0b80e403a5a41c0f2600c0702804c6040070846445001e041c150789003070354440e12401d0100d90300f014010050800704020300036 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 377130917 1250 377129667 377129671
    0x315061005160f03050a0201051b041202180405010902130c020616020f06091609020301080604030c0c17062e0504110409020417010c110a0308060409230105070e031005 74
    0x10042e5020180b80c0200382004032421965000742c90b00c070b40d5140f64000c000d0071030b0401800940c07080601c81c07024211416500540d01903038014002c40c55040c0c454000185907084000103010244c00c0c1c40108010040190802c115861094414070004100e21044506840700e01900f031006a00110000300b00e1402c14422046400c0b044c01503c0920f025903903070300c3c14044c1c01c40d5003240d00c2e8071408981142d080c620800b00c00401020808504550602c90515100e807000b40010381006400030324181030043d40d562882c0240b80c0020760300350003441c143d0308580b030345012281d90060043c0c6000e00c440d44d000c1400740080102d910f00100c481c860919003000010115002c00010320340080c800803400410340c0c401400580186540c6111003c0c10154490a4594610004d401c110380714400230420b1a00044800c116981424400a0b5980c0c130340210b4000d0072282c2000e0503956070b005942c01c8814281590605010141d00280625a42c0d21001c1e50715030000c03640207805030300c07030041d4107500c10351648215 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 377132167 1250 377130917 377130937
    0x1d0105090402070501062c0a0c0e0307030b07030b0625062004030c06260a20031005040e0a080f0d020f0409050a090f02060c0a060e07050315061005 65
    0x190a040150001c90101c0e0010728003100d5a80d900e501c10f01003080840081000d024024050882842c2801400090440d0143c11081c080c0d0703c50055040d02802540f40c0c490345807016040758415a580e00b0b100c4080d620946507240481c3ca1304441c001d05090100c101d4214281c00e1851460300032410021941e1000040400d8580b60f58034070340300c1c03140b040403001c0341e00c8051451003c1d0f17115811810300028101e00e81e40f110003880b8589000946c440603c005c3c0b0360565220a031200740a0b61f0b500542d40141000c041026038031070080340380848202c05040658061086e0a60b00415241c4802c240710171625200b0044841c1e5029141c1903001a406100428186c2d940b0b0000d207040c1004801c8085c240c1c0c2108103511145403022600f8815994207220350340c0c0c4032000e9a0288501c6161342c503002400801e00b80082d0040b4800520200410010041723600c0035588a02c082240a1506031205e850f00d12502500b48603005540220400c088135119445c01480f0060841c40c828850390b00c03e903020b034009000b203 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 377133417 1250 377132167 377132177
    0x80619030f05100e07030308010b03100e040f02090717100501050f090a05030a0b01030b09011a010309050316060e01060e06061801110601060903120807090605030903090909010902010201060b03071d01 88
    0x18103e02c440710f004285111860744000c00c019400d40c90701401090058203d201d20b5102402004207082c0c519000000700c032010007030b000380b0341c456040c0708000ea00d01d114081e400001504c1800f0351a80c0c86007046802039000510f166140c0c443d1001010011490300c9040c1c002201032042000309203000e80100104039008103201091076031000824140140c103941610308918150040041c04803c00036180c1c0241e50350002c0100380c1a40206092090f03041c03500504060b6103404820810a0070002c680c40d0780c52a54a008101101d4540303000501004482c0c00002c0d424450001010724584030400d0081600815650510007444002204403003800502c60401020b0580d81080e14003d100450103403840344d88880d511411030a214040c4000020000d0402c00b0000030085000d9004100b0700640d4224a410b0f556615054856482c601845101e1a440381d10390050200e101815400802854400c0c3c0092040940d12000d000107170104851407408242c0900000c0b841010042014002070414100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 377134667 1250 377133417 377133433
    0xa020f04060f03060501060f1112070204061805060f0d030504050d06060e0702061f05131109061b0f060402090f04050a0f121d010906031503021f080619030f05 70
    0x1c0b074031003101181d01c1a01d00a036204010301c5080d500c1060741c401c0303c4107030a042003041d155103006035481500421401c1c9942000c22040210341d034a0700604000c08171010716511100314103e07088000d001c1515503502c581d409003180c0364103080c5803c8805825415032503250030645041c0600096040480003110015550356010540d003805c2016140103908650040c240c07071602c203099020f84082401e01c2220301d080404100126900c403c86d490104e80010000b20f12108103515900b03042c082e03603014544c40305010981d1400004401201c511035103801044030001c80c00300c80480d4030380106582c040c0d000304203034000031242c920988841703420910402c100c070a500a2501c0ea0554003040d4a801c803001401d06403803800035607008103d803840045c42c880c0fa01c08000000f0000c0d081c200035101c0c0c403051584070394410005d1104c8200d01801103802404c10070458003104461500041f108226502140118010070030700c0c10301c900811103000d11064002d480fa81191a504540301c0a8203044400e0b00c80d0280c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 377135917 1250 377134667 377134679
    0x60e09091e070314030304210c02040c0c02090a06060507020607080d0c0302030a0c030608060619050d0309080d030204030c030209130f060b0f01080f012105030703051206120a020f0406 81
    0x40c00c80012001c04014000441c190300e0100108000030f54040c010b540305100703104c0816007505d80c90724001e00c99903081c401c03901001c2d0145c84064400303d000c0c1d0300a26082e80e021946400444680c0c11602c00c45015040d5940c0035a500126401d03406100300159041c0801801130803c02c0052000368041c01c03610741001c034030402840c10380d61b4440080001035004410320200070340da8020b0740d081c4940d9040502926040104442c1e4a52009002d20712440300e0019008032284511000406001d02501001d06031601c7d00300a4004046845002507d20a84101d03090b4103110b40b003980d003504c6d84255400105880c1d5020891103000141c240d40001c181c0300c40020006241d00308081c0d002d48a480c000c9200411641040388848585007400d060203070340d0003000118000411a6810741e00241d10f201e4000a0464480a5031041500001c00344d01c400a0306000345604200074012076661308121186954820083c040000f1452103507000e55032001442500601e03040c0b480d00c4c1e01c103002500001e4040c0e41c0e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 377137167 1250 377135917 377135953
    0x50d020406090f170a0605430c0506070315081f06150804060e01021207090806070c02060a030b0f1302220506270604080d0f0207060e0909 61
    0x640101c0100701e448004210074058020900000c0c0821941c0710394003007075003c625407144050b2800804690f6078800040000400707040002950710800b0b00002e0b0820300048041d4520344194800300c081c8120300c1d10429007031040d00c0e410345441d8400b002d0705141d160150140c02404955810281e120b500040c0811052820881c0b0780303a400c0008403201d0801600e40041040b6074641d0811100340d01001440c40318550400c503415000350f8003110004103c000e003c0080e0090055040858811500c413041c000c0850740542100191401c801c16604c854561400695a01e0082c540003504100227000c1c3c400402d019a211910804001d00400060784031314000440107100801000c601a80c04900d050318901c5240f0185894116601550b101c0ca0510000500c6401125070030008041c581a01c004036101c644070044004c0405000b01b42c440c0c1d141d04100c0d8072001e180c00c0740c0002804841e85000c0e01840007900c207085902c1c5440e0721072014a901d041c040c01c0000208261154070a414029041207440 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 377138417 1250 377137167 377137169
    0x6050a1110050f040b07030203010602030403080c250e010b0a0c0f14031c060e04051234200a060c0809060a050c06250c020f0a080304051c1110050d0204 67
    0x480070342252403810b171822842620001c0c0c240000c151062005101807500001194140c2c1d42204145071500884000c6610704000034030100350300206050188403100c44411140166180c4060300c480d10382c1c85401d51a424024280c01b0400a510300b82ca04021500080124012074040d55650052042c1088124a981c1c481c521001040c00b00065200b1044403074400e01020345000889031240e810503488007239444000006401c03800300005441d041810104c8251401441e03202440403000c6400701000d41c0c05403400c1c00c207440342120010510390500da07540c3c1000030990000e0442000354200003007128420440c00c01151007507003c008101c09a40c603203001c0c1c807646003a5904d5594481c0350045450610402401e0000d0f00d2140485050034590440480c0d8002101841c1c010b181c2641800018102600180030681001410001041c03454000c8028810740e90b0a6400e144584003800300b2401d2040c03000c4000d000b0300e44088012143e403400f000d46041400d5107241503400d200d1303610f10403070482e40a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 377139667 1250 377138417 377138431
    0x3030b040f1a030c01090e1602031303050c0414071d0402041206060f0f030302030703082206050a0b01050c0a0b04020d0b0f2211010e0102160902070c05030706050a111005 75
    0x45030b004695501c1d0820840300d40030000e1030a13103800c6141401d0010a07801c0036081891401c0260074061540e032081060310760003005456840130f07096072418010b4940c85007030700b964056400d14182d0044100041071550245104c0d0b9140f08030140d2a0127201e50100e200001c8d9a0300c140c003007100003403000d0300c205090302c03640c007800000402500c0c101ea44040b02d100c0b64005480500c0c07114081000c80e030040182d821721501424580c116541d041500061070b035104e120105482c1c1aa100d11041c0700c0701703a002c24440c22543c2e404102602c0080019100d83c0600001011554032024000002400380e902e11500184050903095454400f80d5407050f0601c4111041d10302c0000c3c0c80308002891028032140210301c0d409407105609000292216003510181001c1503050104078117403598543d20810840b150b00d62606400f0000d1034603130411101039407001c9415140108503041c08030b039520703000c00c0d024101c44881d224070b4500325200d04240c40f001005100e045c1d42e805400c1d4801d109076094082c0610601d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 377140917 1250 377139667 377139701
    0x806240304020f010527090a0e1002181005180402030c0406030b0d0605040803221109040c05030f0d0e03030a0507031407080a0e0103050703090b1308040b04060c0309080102030405030703030b040f 86
    0xe00c030051103c01d08008102a4040c0d00708201d5027440307080810400b42c02e40161a01607502d001858030108004c021090035504400207006446c81e4075440382c0030701001c0aa140d02c4820003e0034004100c164042966801c3d029101088100404e500903030000c40c90a002400d00c0715080001c0d1034200440b6802c44040e1b03078020340080ac00c03901e0724000380c010040b6450f40084104141503030315060103801040f03a045004a4820011809014401a001000f0300000b400c40c0c480c800c920f0f03c91030700c4000345004a000709459040c024124130f008004d96640403956980d05041c01400c0d03d003207503001603004c40c03212802c5040020314041902e1000a100c103101c0307a100e108032903c034100018211038008009108040c0303403003900030024800365682c580100b107000ba0001009014201415103220b581c0c4551b21011f8001800140076400203408135925000340c4a0850480d07035020054280d100894009285d50010800320740000e000e42c0c01035035280d001400009201c3d107400c845204848c880607102c2c40b114 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 377142167 1250 377140917 377140987
    0xa0216030309150f050306120102160309080c0136091a10170c2b05040209180c04090c0503030703022803120203150a03030806240304020f0105 63
    0x90f014080100a0b0f0261030300c14810506080d000f03103036001c00303480e81c0e11401c040004241580302c03d40545412080750301d02414007440e103180141406056200d064650f010355148544550701484944450500007882c042c011041035a809104000400c05a0001c1c0c517481c0010440c1d11262041c0408a1a8204a0b1081e98540401c0204400c20131490804008041400070340b8001f51128a9821122036145680c40c0c00f6020b00c14200710209140d04100060342d038074055809041030704180d000314002d880b000141e8650100c0c448041040c100804c005a118104200d2681400da01680103540541138002d940782c1c0b280000390456104900136001a0311012620140c101c61244d540e803800c0e6513074600002c40c40c1c25a03003d065440e50b000d400691076030100c0015200c4400002c2201d854000401e1480b546443c0d1402a09841c0e00b0303591a4011442c103460420482401900c8040f0118861400d030b081d44d03225401c100500444641d03050400000b0700041417114034811203110310b4092664a02c40f89 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 377143417 1250 377142167 377142179
    0xd1407080109140408090108061c05100b09060a060e010c14150a0204050d0b06040905010606020318060703080103080a09030b0c091207060903080721030c030c030903050f0a0216030309 81
    0x40c943c66032020540c583e200c000d0100190080c011180450400e0824040c0b03a0b94180004090f00d041103101240c20540007405020031070041030035804961707510010041024038006101c04000202c1d46650070500460041c006c041c043c030114045000b0515042d07040521950750554802c8240746126029400620000e411030001003a50354006c0101e070045091a1030030000640000f80d05401810b040041c2c4042525522150850110550050002d000c01551340074020340d81e80c8013800d1034042c4030803c13404c145140741c05400c03500100c0d0960388009113a4250340321880c0c40c0d03101d1400c92080c406906030005c0090103500e40c96119000d901000e0341c9503001181444034088210b40800d42d03a400525051000701d80040c0b44405503074100419580703400c020b04d0400f25611102014a0303031030003072078110881c040d411703040080c0c40c03a07007560284280100036009074143c0350b2422004020400600181c0f950f995400c01400d1400114030403290340001c1d03120301c406850001e400980c0013510b200014410 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 377144667 1250 377143417 377143421
    0xc03050109080711031c0e0a050307080d14040e06010509040b040c090609050402030c12070507060f060f2108030a09020a12030f05031303031a06030a09120f0806060d1407080109 78
    0x1c0c134031080d4007500540101142d602100f1901c82080e909110540e20a0440ba81752401007502511001c0c00305c4119503201d401940da81c006084001000512031003000c040c8004c0001510115a101419620281c0703c100c0151071170740215408582203540c42c40300007041d0351a80030317641e416859907c070020b0043c18050001e04018032508141d002c0c500402c00e0000403600d80d01251702030b03070700c055460381c2d140ca5080088a46206400014100d1410f120420207000c004cd80b1000407111035164843c80d41d80c0d100f40000e21090b152540700c0304407480641020200300b00000455210018984c0001c0c440ca4940c001141d80c2002d03049020141600081f802c03c05800141c6514015100e0a0260461510344c210302d002c100c1c120002810142c45541890900d400c04140b030784a83c900078402500c83c80c1c0342c50301c48000d19810100342c800d46202c1480382001402040700f03a211001d280d4600300c1c103641d11002e00c400b65100d588008a03d566401e040c0f00b4851240294502480d1b00396500c0700075514005a02013 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 377145917 1250 377144667 377144693
    0x10f1b0f2a0602010b0a141906081f350a0807020f04200d20030702071a040618030b07080f01080c010507230f03090109080304030b130c030501090807 66
    0x400c1d13a00d8298200250f0f5540024041204c12420140010f24090404240c06258840c282d400c01e140058020503800d801009243c40380f44240c04005513a845034400200c3d01203944203071040c65881800400150119144540d0107403c0d15004080c01c0500c102002d251046404007600d070481c020401c3c10851405070b0301c1013011102101c040c000c0310408180021000175014188021000018004200c0c2c40c16030441c40d80c495240308180701743c07035142945003002d034030440d03400b0014003c103103001c1140303955014400d0780d00380452001410241005000e5803103090b81042203c06054024000001408076812507202c0c034420f91703652000307003001110204425010f0b00148142d8100c85082d11072070b680403060b24841071f0041340f004280f14515601031391820400c008c000541c09018202c0c44050400002410752500c2a030b25180100d0780d03900559100e000e2800014480841c03040032410f4801c46540d200d440c1c90040c400158047e82c1c80d40d0700c50855080b07030b800700c854150214040307040c0954010104 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 377147167 1250 377145917 377145929
    0xf17060c0708091c050105010905011401080108070501122a1b1502070f0203070803091801050d0303410c0304031215031a09010506010f1b0f2a 63
    0x19003071a409650340701e20b50003181c070042d00401d0b00c0518000c104100d40d040001d015085030080001c0d503101d80260020b803209010340310a481c2003155643c410f51041c000603040b10380520141c1030060501c401140d00446881c18050025101c8a075407941854043d500030f05070030400c00000400100342c80160580e4900840c600d06070f8095800040880d0040044010760004950016a0360015180621504040c5e8801a406100744840071809103000401017a420f0b174200c50751010304501803e802ca020000340a400c0d0410201900030700003902941049204d084105001c03074800c2000800301c21310683e2040031031052100e920b8030066170000f03484031030780148402c040189189029107000c0e25540303ca81440c1c003d10740c1c4016806c02800030119220245d0762080242c0020300e080d66011540c1c0100303888144c455460840403404560041c00e03401200701d02c81d1a540c081282e02c480c00b00050402100a844e548016051500001c074440030103115842c554101004070000b1514150300454960098 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 377148417 1250 377147167 377147191
    0x50c1203071e020303010b0d09062d0608210f0c060106030c0302040b091201060f060206190b0306040b040c24110705130915020307020a050c090f1f0f1706 68
    0xb03541034aa0200c1160706440b80071800b0381d5554142181d403801070840d9880903007003034036150b030110740c120452032140c0b40140e03241111492650307290394080c21030302d091107090001d9018040381d0010403081c0c9c44200c121006918198100035640c0c003040301d942c0c0025002c1516410210061045030741500c0350b0b0740400e506203021400c203400c05451520500c10a043c0c28030a071440320741841d071801c003500444094852150503042c0542e803504040c0d13540106644e00044200060084d0040c1501d610400090010040007014552550744034650601c501920980c0c0107100404045240030030566400100b00f10b400d03101c80e40b4240450022322548000307540342d010743c021010402055581c540d00f1100340005180018440d8000e2030031041d5241880016011175001104203c596500400c110300990b0040054a00c4019a8801c1001c4040200c0d601f00d46003120714003060b0080c00450780e00f800c0c030303044820f2005a144c41e00206528040c0a80c03201d0305080501c0140742c40050140100c6070450302000d08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 377149667 1250 377148417 377148467
    0xa02040e010603090c050a08010f0f020901090302210105010b07050f1c26040605010515070206030f04031112043f0c0906090b04050702030901080610050c120307 71
    0x140d504481882008109900c0b40d00c62000d019221041500034000144541200390f5507100e8240a810182c45810100c2d240c5012441c2c0100300e4000c982885105958145c00d8509550801903040342d503203501e00f422000e030b400606085500740b04580c041e01d10090007a03210309280c902705181c041029030320309154100c10405095014105030003040100700d4201841010800348a484001c01a0302c008841d8005002c00d00c028418070740d100d10f060761005d480c03040003074481d1100b2000911030f90000940040041001850404003140c6098100e0310130300d000c0613030314254200d5a107040b111001d000b0044000140800a84204050003102c0b5400c9840346628030080c145043c038a404e001070403600c0400c400c44a0400c1090614003503020303100400c4108201503c900c2a0001001c80e081c44a0080346400003203040c25000000751034403044165034603203259541c5424800b80403510040c2a06000b01130180c0c0041304010701c0090f812802d0110410744074600440020403900340c1c206100c502000602d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 377150917 1250 377149667 377149679
    0xc040b010f350a09120c0305070f02120604060e0d26090f0d020703060b2d030f01090b093a0207030f0317060105130302041d01180b0a0204 61
    0x900b000355901e00c898242c8690550440e01003840d00b035000d2480960054081040b0746000303500c03100f12180a20542185001c0406082c3d41e0340c5020f01002d00460380a00240c00020600e400c100d11280c40070b0b00088101050100340340c03429000755000c803100c540f980e00c4400850404c0120300b444460500d003262948045103824400080800303807403490002e0610008032448802c0200d81100311040c0101c45c2c2510f02d00000a48a040e43d000482d8124100783c10607029140c5800c1555401440b0661070070302d81000c00b100c100c14100300381880e406000d40303d07500c001e40c0020b2180c208001d00802c2c0c4150103241c02c900c66030030035150030000c0c44000c60604100ba000300d0241d11600c40f0428031207030400002c1204209a1800500341c3c00200030300c40c00000c080c00c141d800381c180003074001002c080c03a803d0b44903500151801d00035100300305044088040e00300054a015007014180b40c603d5084926000d40c6490450300396280d05c41c00c003c091501c400e101041003d12000c465000f036101f6021070400c0c0c1414 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 377152167 1250 377150917 377150927
    0xc0a11090606090d0f120801030c080606060901180510110729070302250e0f0403120b041e050403020d020d022109280b04120209100902040303020c040b010f 69
    0xc40c41d40509580700400f800c104d0a44d021440f5070360841c6c2620702c2d003885010018250942400200c841a59414001941860000305140100002041a8149009038004441c11a03801003d031642a450031000502a2211581c00100d8495550340d1440c8130891841a4a0310142c5e030f02000480b81d045021a01141d0010041c140c92440121003071340d6a00d050404138582011494004001150300c602401c60f03101c00c010340030440315240151903043d0703924540c01000d102e08803406400b040c8440000010707400e940d40501903828004000240304e00400040315035680f1803030b984541c0a5526018001031640402c02145020143d1004014000d07003400c1c002d407100501c05840258807a0461076040080303042003601c050300c10151400211a403000b00358455114920311052011445c1840410900030300011030301644c4180c000f000b0340d415164284040c40d80c00070040b500000f6400030202d40c81c1c620b400103100a50003039009241c91040c0b4401c010480e28181d042c2c606000c551603200e50300c541c201d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 377153417 1250 377152167 377152177
    0x3130b0a140304081615060b180103200d1404080a0201050c04060507060f09080c0a02120c180a09050f060603010f050f06040903020c03151608040803010e0402040b060c0a11090606 79
    0xb130300b070360141545c480c0303070014200b12040c11454415007811004249403403d4000351000d902266001100715030310300b005508540101e20078204c60340c000d00324090886101c600401840240b42c000051040040641180400080d04d007100c4503e00001c00c00c0d4070310790900595401090758058540340624060018205101e10b0f4401003d01d622151100c28100071640040815070300059015a9440c0300e403003494030f500204004911800401808218101c000141c0d8140080050a0700300e03808018a0011040180244076081c03d03516580e6850010300d0912481000a00300801454141402c0041600351030107003144e0480d0714607203030412141004414020350010026a8005407446031410101c0c1131000d081800741d010b202d29001120020007581903e48103540c078541d90000c0c0c521115040722180c00548000c0d000d40e1050005011841441c0c3e00c29401a100900000f075850407440446c0c0c25400000c41c0f04a01e8014500c0d840c00d018628403001c1d0001c8048461000034075181001901600030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 377154667 1250 377153417 377153437
    0x12030a050106020c061c060308031f0e090d110f030a0c03030606030b0a05010c03030f020f0d110c03070210050408010f0b031902010f0c0311010603081b03040e01060e010203130b0a14030408 83
    0x102e0011b1802c030b44a1031348240051900608090b551385013016a07055141058a900d010801070703820f00140c1c00c000031003054020102c007000340900718840101118404030700800318550f0700854041440b003050400052a03a0f40b40f035207441c04501410b08001c6e0455016500c8003003454140800380c542e59440d80030740800d540c0c00f420240e5811195050890042068028a0b4809880050300a80284050010340303027a641c101020b02c828401100189854000e000c0c0311500d651080c0100c0c0010318099110b900c14601d6468000d0500d036172991290700f580c09502d011401c560342e40c0c01d0031030b10b81020b00031080d0081e0212a42e40d11104c0a5000902e07170380185034148100b00710742c800303203040501c40c03039440e000c2c171b184480244802c1340c9a081c604500e80c0580c81c079074148a1031500080d001880401034078110788403060119216860500305585030b507081c842030f03811800308014400324501b02610750809000724000c1c960b21643c4281014020b2044044880c0144100740208400104600c1c1100c0110031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 377155917 1250 377154667 377154697
    0x1030605060a0f152006041b060201060f050906130507030c110c15030a02070c1e1211100e091512070810020a0c0c060c0b0c0403050604061a0312030a050106020c06 72
    0x400004035817001e4049400c5400713036010311018003051044032000c601381c44107507818030000300741d85400c16400c8454034480ca50842035803c03000c00c1a441c240500c0ca50205020b8640545080f6603032102040b120125034040100360b0f00c101c9550700c10307480491a000f40c03042c0f0000382189038289001444070001030f400203090391000000100030f08119015100b42d42d500c0307201160400d4607034081c1c00081b01120301c00641400c0e80d94000907030350340481140d07410799080444100e10104103000e01024100e82071401c414054501554a001e88925015a01c01c0030000807a00c00090701100b00b0044000c0d0704404003855008600c01d1002810100e055683c50707594140060b41c4c0c001c096400d4510441703480001c0c0510200480c0085d000b50484105a0000d1095921180d02e5442c010160002c0c0900d0001800c20750016000400040040d4800d5400c00c40c007103064851400c40b40e000914052820111071121080031041c8840e4030490f002d070f5809001f140c00036080141c1e091000c10841c2c0940c125200b5109 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 377157167 1250 377155917 377155937
    0x304020d0606080708010f0e03040b0a1d210f010c0504091e050103050d0210110a05030604060e07110f0a0201020a080f040801020a050702131a040f110301030605060a0f15 75
    0x10049510100052103500251058140e0395400e1500134507e07001142d61a60802a90340540030000c4222001e6604801c042410503180c41030490300c100c1440207021622106000c2000b02da42c40c8094502e41c1460085030b42d14400d01c0c804094208060140b00b400c0036810602d030800740c150404290b0f400d890011400090100d0b00b22400c2000c0c034160200ca15182d440e010010080c02030200e02d441c50b5480a4085848402e01000b0341e20840b03a5202c0c1c04c1e12004014446c000034036126800850b00715034010004200d0300c3c3c44004c10070b02800191210303c04601340d1860f034182d050050103007a410040c5240a400c801402c0e80003c1d44400c0020401003240100150074843d42500c641650040c0003400004c64845000a101800561200000364499014484030703103117440503800340c215803000c14080c0d1203041d215601800050b000c11444c810000d602c2e030702030781c3c0011030150141d80203500680011545050900c1170100c045c040c0d400c2042c410110031030900c0445c00004008190301c80781d03c1d2070702e909 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 377158273 1106 377157167 377157173
    0x60f0c070c1503150602031305120726030a0f080108030a0e130209031506010801050901030f03050a12051006110f060103020f030322080709020304080304020d 70
    0x40c2441c0c05004402c4098011400e82009080106000034070201100b0503900740c4e040500140d0000c50340403542412151604010041951034008850044e480103448440c64043d40d04c100b4020381100041064244591400000070400e490300c9401d10b180062a000030b5629840025030f40301d00106000801108032040c1e60303240c2e1070b2140c0d005111014801c414200400c901400c50b801c0c400d02903d6141449907855501c0c20710a00404c91410300009000140c0603001540901514001400000c3c0072031074001026806082064036004170b282e04488000c403001d8250000c9007810144a109085a1201420b40b01306848040000d803c0c0c072070310360340d0b0441791050b003100e58030060040000d4100f000f00750074150304c06026030f840c02c482c00c200c00c41c0e84414031074404024180c08030104036030001880494060100800207500e9410300c1c0d21601040e0002400c080c4c46074450000d00c00070 = true := by decide +kernel

theorem cover : BRFrame.Cov 376978417 377158273 := by
  have h0 := BRFrame.cov_init 376978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 376978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 376978417 ≤ n) (h2 : n < 377158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
