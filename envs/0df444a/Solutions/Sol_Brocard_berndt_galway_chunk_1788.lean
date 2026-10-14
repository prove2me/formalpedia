-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1788
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:40:43.984728+00:00
-- url     : https://prove2.me/submissions/da6ab308-ea60-4613-92db-7eb66f81d734

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 321402877 ≤ n < 321582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 321404127 1250 321402877 321402881
    0x1050403020d050d090b07031d07081c1e0207030209060d02130f1409160609030503030f0c0405030d0e1e0d200d05010e0c0109060e150c1b1201 63
    0x55002405600300d2070542d0640c91140000d401d000b81090000301e20b07018291219826080c080d280360001a40b00c0000085003101c16844455080002e0000c024681c68444682e468480c2c502400c000300240c0301d03c00c482140f18400d00c1e26034400041d9050039110350441d0184d51002d047c40102c0c0503e001c00005007062030400d80414180750007400f048405540f01c86e4405c020600b18030702e2584c16540300707205907002017544442c1d481985640002c1140240701920b040c4c0010b83c59000c80c08004c1c0342d06c428000140c1c040140c94002d91600c0380c10389940c50781d032030b03029150050307804c11038051240e601131003c1a41d004040081c84030782071f02d500d010310304919607010f0520250b05aa94110b255607146400003250030000401682900c059034600c0d406003000101f2944400400340c441da910344101f0100140c0c1030003000e5903690b090030a246c1062400c0405400e0010328689144a02d050171402c0172180c0101c400c4170300031079400c802c0c1e4803e800e94001c2c0900300c0400761182405010842030180d40e03c0014 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 321405377 1250 321404127 321404131
    0x51e033a0c02150405030a17130603140f0720120a0818010c051e0f0304080705150609012603040f0618050f0d0809040906020306010f0306030c0611031b0a02030f0105 73
    0x900508806a0b1584608400c02807507101d09207250230411007410114100000070b03014050303682d4081003011944002da100c10901902d10740900e944e031002c5c080450340001418000c401e80d080d003200c0740f40120100700d08110f81ca02d80340c02c890000003101c8012940c4092024803403403107003001d420144180b00d4400c1c00c8540c0070700d0703560105108124030305500c00f520700c208070070388480d801c01071030809a50551005d541007aa07080350280b402150b98420002d0034001150000f8032100d40366a14603082002a42684042c4503251030110130281107080200780749003c0b20f0110b4281e084903a1180d4400003c10144d0903446214001001084501d40a40d08194074500300c1c3e200400d0b504a0044041c204000c41024080c01c8680c0d41c800c025000301e54030385001381e4101500030080103860f460600300240441816501c110205882c20310203000081d00e070300056042e28114606110018050140146103208400441031040715030b03080811320140015412003603d10170703401d81c0c07160009110340710b00742c80e01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 321406627 1250 321405377 321405379
    0x120a02060304060504051533060409270206031603090f03050a09050303030609070f12090b0a0f0203060907031d070e1605040e060409020a170106051e033a0c02150405 73
    0x11588402002d03186c0e2080c0404422072123484d54068140250000303210350701c603510613081c0f00d4030349040f60044284542d5880b04d0404650038042c00b10016400108103106c010721000781141d0102141d48154800d601004a403039114480ea51900f060781400740458101003000000680c10240100b04d900b00030044e00d0080300c0140031112140c6a00d1016a024090040c098041110745c40d070140d68514240180d41029000700000d1500781000038650040d02e1650300705518090040090020365214500c04c1a4000302c285000107525080030040411040040d00c0405540311315000804d02141e21841c8900401c01c1207801078030102c214005035620f0203607116601141030514005106420300307030040b0380080d2005240028032a120352020704c01d40b112503030b9141907039500c040030b10080c10002c001a40801341c01034407210720305001c40083d5540c84800c1d045181d2784080014803045030305158130440c490501048425003854201c0c3d0007032035001060b000342d108240d016202413191101108440640e04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 321407877 1250 321406627 321406651
    0x140703060b030a0b030a0b0a091707240b06040f0e07020114011a040e070e0a05030f0a02011803020402070311100c080f040c181508010608030405120a020603040605040515 75
    0xa0380c0d0319000d005184c000003107a0940291010800024450070703100348145810003000512400d2401c2510340720b40b02c7d0709810380c1088100400790100e50b1040d0034000d9505c0d0340070b0720740e0001483c5031800c1c0a4014089600e42102002c2400303d8112414040002035541c138030f60340b004607a00c0c1c000803400d988407088402c2098400d40b0040c480c603c0c801607071200c8180a076140d107252070740c5d54040005500b07045031a00300040c40e0060b810100d29048039445c3c0107000480c018810042c03029900c41d102c0044010090501010750030000140c2000c0c1094070045400400c1192509010309000e410740341c400c4140b841c140184070003011400018445c4446401039640d9006860380c803141003000c410b4014209854160a04500184c1e0394800c40c11005400800300c40410540120030791451111486d80200303446134100300007480058800030660302162401c6408405c284145028079051401039000a50043e50000403c07090040d25085140118455000c80f1101141c552800d501480305944e507450b040 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 321409127 1250 321407877 321407881
    0x4090b0105121f0b0f2e18030506090d03020c06060d0602090a0332030d05060616031d030604020a050609030115080c010207081903050f040810140703060b03 69
    0x2050040c0e8500c9440c40b0304085070205884420b0b010300c0c4014100005108685500b00d40001d801c0c460012142d80000b43c0d1420744407002c10190344d04c1c039088034018550580c82c01000341420391084100b40e0502d18540c1022000980300e0401903140c0b1011610440944910a04590858031a1003243c0c1010424030103041161500070030461401112081519100c4d02400078008954581c48074a004601c1085e10b100f44003915012004218a4500101d410040d4008103100c0900c0100840fa000030000c1e07000200340d944c0c28000f52440c05100d01e01c0c03007800102100e0408154000107a0034041c0802a10541c040c065181090b03541d82044034029041540c91404009a00b0500003a0840080013000880c00c050403d0386c1c0f20201d01c60780d000e40050307480080d1003143e0303580621a00015007242c8000d4800002525000381d0054907861008040100004a09003003891050603540900340030700c240c40c0d07601d04c00b400c820040c1030301c640c01440c0214080080b807a818080d00c9141c0031035040590003801c0d6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 321410377 1250 321409127 321409129
    0x70f0b070204060306020c160b0f031614070308010501020129040f021b030405130203060904080307031d033a0f0917070b072a0302070510050403050c04090b0105 71
    0x1503000350030100c0e00103441d074001000240d4640041c2440c001c04600805260443e51105902d03a8070320ba000e9148000c040105009140c0024120f951210a030700c10240c102080c0e1004039403400c03100000020f01d16000c1052010540e006d42c030b1030b048500076402800074043c1c046040c008101c0854000030000074280100055003400c0d001005c00580e40300006007850800201c010b5110038046201000340c0000909100301c7c603200140100c05966601b04509624003540403440d0306c580500b0290071000302200044141c1c1c800d4002c05484102a10007042ea200c030220350b65640e80001c021800303607400761440110b43c51002c101440c00aa510662a1f503548160204c0c10020300c00e560802c684940c542011601041c100e178604070000c0010341005940710903600f4460b002c100c0c040e041c40104070078141d10700d003086101c100d116483c1d019020000d50880d41458160318141095000580102c007104075050b442e90014050700441c1c0c0500300f5941c10040c0300040004651050000070004d185500040c051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 321411627 1250 321410377 321410399
    0x403140d050d200d0e070f0b0702120a06230601031103070c110d240204060507020108090102070506040b011d0613181b03150507140d1503060c0f02070f 67
    0xb8080105058802c07001c1c42c0f0340c0780c0815500c1084098901a100e85501e060309004100040c010403081030104841400c0007242c185502c110b81010b0310448808102581019052140c1452664003060801c1201070708002042c400030407183d913642454940d80099030035400b0380203081040102d00e00d01e91441e600c1280a540d001029281510520300496040766603445041c00c0e018801d001c0c8010b541e0625070f2018000000d0321040c010b00e0000d0040c00200022900301040e112804c0d82401c144109a607907200d01e41c028000c0c0c100240091081409200a1100c041c91590680d5800703e840504030032010013080302d8003000d64050381c0280400c00303810110350302a4040031503a800340290702405846a25402d0726500c1018000c00c61038030b52031040013009007401520f206800c0b036038820b100600e0511406042000c2d60441c01e1020b0000282c0140e900180354410304005544842e45401d0644a0030004018030508a500c0c0116190070401c90815000180032400c0300c5159052000b558185622005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 321412877 1250 321411627 321411641
    0x607030c0e040e030d2007200d0f14010204060207120302150906090c040515090c0f0d0506030705040b100c050319020d093213020f0403140d050d 64
    0x80003681c00d90150169140d000d022082c180c1c1ca0700454403441840040001c40704900040d41c160845d02118401208100381507801c0300d40c2144141500a110448481d554120603141c1c0768000d0718040c1090401440c45405911240200b030407840440b41041414202c0c801c41c090003002d42d003e0349041284031640b05c0c0004041e4031030f00c1600c8000308415500301040c1010740d403004603070300305904015a1800400074840d01c03240841c2d01b401142800300301c4003804e0000001c1c19008500030800074140d964000c00711600032480c40b400c5941c516180f910740004010079546c01d8403e01910b10000740301c4c5442d010310354400d013004080b0f61140c0b410300c00643d513411076948200c8180c0014070081e50152040c20420f0034501541d00901080107000c48001e010120540100241c0c035600c043d070b02a160b0000740b180c0c03034060340c54203005200c410340000503294a100482580c06c142c000502c01e840400e401002e04100c912071408a03d08850100585464103e9100c3d2000010814021070f2410389140d00b00407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 321414127 1250 321412877 321412901
    0x13090207020d05060414060c180d1b060e010806030c0603060607030c021005040518010612020705071a0910030612030c020f0307091d01020c0a080f0d0f0510060e03060703 75
    0x800000d90aa41d50f82c18000211030680d280368501c03042d8881e00740b091110a501040e50a0302615054000b0b003843e1038681d403c070f0424007c40c07401d04d6150820464000100c990b42096032001040d950f2808010310a481c0d910b100d40c00900d0304004100c01d8100000c0342140a103005200d81d046544400601c100c0d030700282001d80070044058008400b503225595210102030b62540c44650f501c0c10a0140403904035410040300c1180081001000802d40c864441c00096020f04805a03032880203043c00317803410381641c01480000607070090030702d80024004000c0a05a80543d441c074100b41c04c03076100350200d0b031862045120489600035180000781c485d00020801c40d20041800044c4c1070142d000c0781c500340c0542c00c60103980b6540c45003400e078030403c0301c1000385003110100294a48011091801e84030032174094010a1540041200c1941340101c00540308407240300801040800052130000e009000259000d4506400001010071107500c40c2a1400c10100c001c1c0003000e03e0b4856810880091000c19894 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 321415377 1250 321414127 321414139
    0x12050c060906180f2e1b030509060402012003070606080303041703040b06010e0a120b060301050919060e03120a09020118061e1b052a0102120a090f0810060b1309020702 74
    0xa00310020036480344080032201c82805114680000c41b0280c02c6500103002030a25a204408000041c0c0c0d0240d28080e20351600146500c0e40100e00b41f10b1450350103030100082021342090004507401000002462086004000c075290580100c0300d12031840c48141c0f0044c0c1007501020000d2901c1d4040c55002d00d145001034070018007503a45800c0c1038840c02e42c494044403030700700e1038052001a180074081c0d0b541000f500e6004e01105208107007401100c41c0040310040100d9150462441408028000d4400b40049900300185070b00c1d04040c928001c0241034422800308140c185043c84040b14401c14001756512521f82620440110b2248001500703405541c1081280ca03040c0c41201c7c40c0706920140c5120b01c540001c0000a80c042074210000b003181802d03030098411400e01d01440d0fa8001410950740c494940142d41d01c800b208005c5801d0001a005401e59150000d030004000700000b8004410064401c01001001d8507240e85480310310400d181140301e068818014440101c03a40d0007880340901c01011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 321416627 1250 321415377 321415453
    0x409180209090a06240e040f021c060f0216020112090503040603020c060c030f0f09010e0328030506030304050114160804060807020a0f12050c060906180f 68
    0x81401c01c0880d55464140c0124a5603c00c00205004034454000e140e046280f03481c0d42c01d0494a02134500c0e00c1b9901c9851050340c0440c0600c140a1035242d181ca40142440c0d00302104800103003e48100b001c01126545d01c1c00354411940d08a0340f007914050524140211030710f001c580c0046401204c810407110201e41d64075135880010b0000c03c01040240f06984001d40c8440d51401054140480181812520300d0100104003481580d40c054550000c0d411400101039128000504d0060402c0e9540301e46900c0300003041000c032030550283c800c0c03181c0d40041c00c10784140c600c80c04030305403102945c0d401e4040e0f1081c401407240350f002e01802058800f00e01109400c1c0101ca8544c0802c44280c00802e0305c02d00b800090600003298003020040c0d001c3c8250000b40b01c000b82d20b9850032601000c40e0340c058000041c3d070303014404071807040f0102d03090b90310b008089810a0401084841c1c80307060585282d6001e490210511840c1040411a4140500241c015201c2c0d01d8000c5814100c0b19403402c104600380d010101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 321417877 1250 321416627 321416629
    0x21203062d10050705030d0216050304140418050606220f0905010506150d0914030c012f2a0d05030901050f1302210322090e0304091802 60
    0x403501c8002600c00166429004403042400340d00400d055080d02000000c00400011440003c200c85c0c901218000c0180e0b50820a0001c82c07401c850814010000d000006001482200019105d4484101141c04202c80100110200341e01c00381e0120080c82da0300a00300095480ca8000c5410000d05091540c45505900c0281a40b00310b5558200c003824403a5904640c2c0e050110920030260301801c1030310000051004501442110f0081c41584502c01c1c1d2608900c0c010088101e41c0c0380c0c6054960001c4a13150905180042c2c081c1468092250072515a02825040c40390b00e8914044416110f049140ca415010448841c8490004041440300f10074101c010078840002c0100740e10b03603400395031120786030300380314400500392807001d01681782c4110f92000313104405000711200c010940c0e0468038144c01c072880c050b01c417258084411740580ca901000c13803200782c10070f11b0742420040f810805012860303150721450203004540800c1c804c1a960b920501052041c4d18aa1388500080c00c2000500cbc400d41810313034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 321419127 1250 321417877 321417919
    0x11e020c1206010906060504060801030f0206120a0207170301060507020108090a0503070312050705040f0e0709030b0907030b090303040b34051b0d05091309080703030c08150102120306 81
    0x944440c007540c0c8480700401c5a50039074800c44000c5c3c40a1b1904619043ca0507030010000178040c007014005044c1c00c00d55004641e2164100e42e5484149140342426140c50715030b081c000d4015100c2038980b0704500503445145195801200d050380d005444450a0036503a4004690b8500e00500540c4984101003c40c808603000308094a403c510a9540c3d03c0103d508910701825504041c00a00c02d001041c001808040c2d50300c1103103c00d0301c103c0701c0c01c3c011603034944d001150a2001c6905c007410040c03240051000d0b00b140030550b80b040d00c0c00f40314102c81e1034031415111079403031000300d40c060104800c0c400442c9200e02011003803040302c070308000302420030001c20902e0130b640380801c082000030075400204a5100c1c002c02e05c803001070100c018041c0810784c282420242042c1b084000c124480d42001f050418129190352004003450340124015031201000c0c600900106800c3c4080b40c045011107000445074a02028141c0383d030101a07025040350717410145c055074150000740c1340c680d0050254410010210403a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 321420377 1250 321419127 321419149
    0x16020a0308091c02010503070c08090a06090f0e0c1213054314040e0109080414060f07060203072007150513120c080d0819050105011e020c 61
    0x103401007541e555242c000300f20000320081c02d01c2c140c0c2c8200003000c81c0583c2c0c011050b41c0c0d0103511810300f640200303282e241000e03252250151a039800400c01902090840c0e0103440300c000d641b41120742c0203100303454110301e10a4180c01c440c07007401081c081155001c12020303d10b2454004403403000480c150070705070f03448600308140c80a8203801d600c0d0f42d880300d8000a401e62100720b48410600707140041d034403408404405d40c05c0107008a980394030b02d071441001c40d82c65507404030780114100c0b030080202190b60f03e090380709a441780c40b640d0781d003038007207460410755141a03001c80320741601490b0941d2401039640c0e01c400c043c0d0001003c2006106c600d44eaa140c3e4070400c00404803451180c0c0c000750040605003502240c0d20ad00f00d1842c04100329051005d07191840300e64080009403138020110025031503003468030300382421140e00080410b010b010007002c2000d805c00c07000c6000301c400340c00389003640c01d040c0f828000f290b00034418540092800945980c0480014051100003107662041e122501d01c2c5101040e0030101c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 321421627 1250 321420377 321420383
    0x40b150a1e030b0d060c1b0620030105010f0c020117010305061e221e050319030c0509040c120e101104031a090a06060f05030d020a02011416020a03 65
    0x1200403070032102100844101c100390141c00d041201c0802c100104203049500c1100605080e541c0c00b0800c541e6006840d4484540d40b1028041c49070461450000c024200c002051281e088a1780717100c591000c60f030800d0341d0580f00103940700c0398901c1c07456100300c4001c1205082681806080c01c032000c0700d440803030540da020f140940024586424070303907502109042d03403526043c8940c3d546420300c00b0700100d0420800d9000c00750f03507425142c0030036401c0125a9000c0c6a0f41c0030045694240d010007003100110140401005644010158180d2075500764203031080b0202e00d030300261082003a0752081c942903028183c802c03903501c0c00b11400f102c0071403524125005140b10101e1a44010060024141640203000982c1205502c082c241480c5030b8400002d003071060706603800e41c0f8902c40050400303e0208819610160041020f0002c0303540c071781c03400c0041005401902e0290191803841d4980d2030000611012080d03040e510305d021240142003042d915000400c0011a8130001c250a030301590b91040240c01446c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 321422877 1250 321421627 321421637
    0x14040803040f0e07031e0f0b0909010506090c0903100507050c15011a09090403030207030c0804030605041112070b0a020705041104060e0a03050307080906071e0302010507020304050f040b150a 84
    0x108012031160f41c1400100007104243c00c2c04070118100002114404840c114500b001c60f4490802240368060440d1019083c0c000c1e400c10201300f41c180054016130700450741514444e4564551004810041c071542c100103405a106905109544c031040d40400d80c040d4640c40c0903400c0c0203042c1074181c1401541008062811462030051101d0802e02400700c02c4080d00c18070441c50401460003061440900a00140600d64003241da1401e0501a150700d00e034103644452079664441d04e0b0303e13010005207800c0d24203440d6140345503198901820031180b05107003240140020002d0318a409240a0030b6400800180118040c0c220001142e031284c0c00b4a03401c0418001000d52103508014000b010044102c04241c031400240030104007207413000c411034a02c1500b0810040e561980100480d20034404c80200410507400028003031040000e45013145a01840703640280301d9504c0320b5004a070380b030180d405100d40c401e00c08800700c4000d181550003a4200c050151411161002a4401044a421501c00080420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 321424127 1250 321422877 321422879
    0x120306011b2a050a1409090a0209130b01050607021c1407060504170703020901032607060b01020607020c031504020a08010510031103011e0b031203091b1008040314040803040f 77
    0x244400001e015003800c3c1c4641c4440c40c90a140c0c155400008645103004440c0800854400039007400020740741da4014009110ad42041d41282029010142090b030708207035107000104d8079203042c00869100b25001405204001340610a0025014041c00c040340d03000e070309460760b0801c21001d1141e50010425901e410741c9481ca000d54a00c8500d140034001c20150700b042c4014001690303004809415260060020246030003054003039201124400c90700d01c441100410b6041c00c10685d034101d402c80550aa00303441d165244c000c01079980700c0c05401e05a40c150400004652000010401168450b0004200c4007003281c1d6009024212a0240da404641503160002442485044596440c800c00103400070803021032112040d100c1041c3e040392182e00c054582043c03c0c0d050350100811040294420358117030340c1c2e00740342d48001c0d50341840aa0701105c2559070a410754803842c0120750380c4040000c546503030b01d90b0b41c1c0d19501200c0089600500380c00190083c4400f20b1802d40410192024140d022119a402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 321425377 1250 321424127 321424193
    0xa0f1a090c0c070303110f031b0c150405060d14150a1502070605070807020909010c14160b0402010216030b060918100f0207060f0b1002120306011b 65
    0x240c0c00030180401c411080181d0b00010758001010030440c4e405180c0004101400c42407103081c800811410b020502c070205150311800785000c4070b00c0c03614003004101d407900c081000c00c0c0044818902c07002110890180020406428008001c2807001711815000441480c1403035103005081054902c07458501d44140d001480342404214480a091425441d44601441c81c000958401740d0303015070b03410003070082440790800861000b0380d45520b0b4010001d010703500e0602411402445010340702070000346000218400904407004403a807600d00069100c071510507d40700c40d0810180600120304522170704810240000c11040d0050141d1b01c521885440c83c09c1400801960100c098009003620609d01c84190a29030f001a83c07031000c9144000200d0341c03211540c40b500c003e0080752800382c01207041c0342079403003c44c0c4154481800c10310200c8640d40c1d04190610704a076110b014802d0359180e07030802c102040c100c4d80240220495011a400c2c8010481000d40d0350005005480e0007840e1000b100d100000a4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 321426627 1250 321425377 321425389
    0xb040806040201020f0f030d0c09080105180d0e01050910111905011d060402090603100e030408160e040305030615070305070302011d030403080715090305190302070c0302090a0f1a 79
    0x5d42c0c80101c1c020305a5000b03400b003a07a220b110b074811140344642e544926002003805228610014100680200b1251401c011094150103100030b0020450240f4003074102c601e8007904d40d003080820306075030799400d04c0c6204060003c003d586030408828040c003080404414001049200c50300201001008012111440d066080d68004c043c880740c00c120076501d40c1e005010001b031180c4d200c1d404071120032050312840007103814506281010f05500e03043c402c006403404800001031044803082811918881c104140c0010081320a008166000341c00c500842e020a1090001c1c5400c40344c020b043c3c03841c03c3d56000b403d4109600c0054110f010a10200c2c01d81c09254081c07051240252111a9140110300e42c2d84405440f0b20480c003004200c0030010488000b400307100d410f840740d0001d42840c1002068070074107002c0c042340c111010f040a0012030181c1c44411a01c00e0003a40c90080d4022001c828a0307080d5420011804002401e1080c0c8031350f2004094403000050054005c0425a92820141c079480007050060b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 321427877 1250 321426627 321426643
    0x7030906180b1207030902120d110303010323070f15030e0708031b0a050607090305101b030b041e0203011a040b030f04020102070e0c12070e22060b04080604020102 72
    0x100c803858002041001e80802c82c2218000603092141d101e25a54201d0260005c046602d006508200c8814200401243c009101d094000c015101c0c0e00d8034a00b03081400d40da92009020081843c0708001050640a016042606c01c00c0f14000a0710507840c1c5404281c2580400366000801040710071b4002c0c100a40c0602c100021211707541c010b480700604004643c2e41e6842211085019014a4120685842014020082a42d5004054440c681050f407001400072a040c04260707075030700552198000c400b40611610700801081c01645506051071201600202200d8520300e40080d1a0503c1e5146404012468800b14000c1d41c0016140c2d418000c425221800600031812814010072040c00529101000d50380d201807075001d50070460b6900e20040342416a15800080951000380c1440621484000500015002a8160038440c0d544040849101140c0029160001d0a070507d001000d09104c1c840480c2ea0b808600200d0001c0d540c80142c4001d5100368042840b0380c01c4401072000b10b42c0d0500401d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 321429127 1250 321427877 321427907
    0xc040905070518030f0d1812080d0e0a0b07080a1e05010626060d060207020303040b0c011b0e010c140f0f07060e0108010b090307050d05061005060319021e07030906 72
    0x141c01040030115680d140400181071052000c624003000141110b074074441f011300103d80001c802c4010629040d0203035000005014200b500b0240901d02808000900c84489074101c1030070f2a0a441c6c801c5c0c00d4801d4500a0140850f680e11403601c0ca0300c07070052581c40c40c43c030b110381c2c01e000615615002004102c48180c0700806d5200302500f0700301d1805009808901d400c554200c50407c1c600c038180c94410000c0c49120303170080d094000802c000501360f4681c8090010f101c0301a0090007011141c4100006c01c02003507180c080071408200e400742965102c0c08100d030b0503611076918441007c50300c4c45902c1c0f408800a1500b0005d0740500d0910280031000d0200d913000341614184403d074200b034480064400c03a414050450781d0703040411000e4280e41c0c100484070003081c0c00390440c4111185414000c0c0c58807000c603440c0c80017928407180000c6a00f402c8003100c0c40303180741c2d03103045d44010309602900703000e58030032200310f020343c4081e000e55140c000900c030042c440d0b58070030703168103c0c0b0600d0b020001d01180d1907201c180c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 321430377 1250 321429127 321429133
    0x8030c030a0e040e0601080d1d09150109090513021801051c211d0907140c1c030606020f01020301060909050606070609060b04320c04090507051803 65
    0x810192000001541e01a65207030400424900c80b180c0841c00401d82044515007034816680002001d5a020034240340303e001540d03c549182a240c28440070800030f01c58055005403103c0009240c604040d00c07140b02c5014149040d140d12941d039007c4400780e82090310281d00040290300c2050441c074003031042d00e088054100d5504041c3d0714000026401c5450a903031502e902265561000800040300200c0401610301c01c206010b06a41880c0201a41003d1007410302d0482c01f420b991100303261011015115024507580e01c00041c600300f00360710540d00020100625482040d004402da076010721403494150480361342c005006454000000e260000b0b000c080c8059134810001442010f510035900700549808a002048580741c03040800c0786441440700c041c00d654508248101084650381080301d0001003240c0074810315110300c1300300540003e80f150841380702122041d0300d4555102d0503141607002100302c035031034202a620311500c015100c3c00c44210b400034000080c030b5102040c603440c6000b954107041d002 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 321431627 1250 321430377 321430387
    0xa030509040b1207030f030512090105010515120c0f07051b03070501140a0f0e12100e0312180102041809050706050702010c03080a0219020601090b06131502010f02070302160803 78
    0x140c4c1d00c65409000150051000c201c5000a242c020b0b0111903030015130540d99402e030300d044c0c0042c0b07008003070a01440b481490076074800c0140140e54010f96482c040e90b120855919280c41140c03200700c0e801a489003455000604c441808190248000d0004014503008074441008220400d800d142482c2c0045041c0034040804031101e06500c8241c034401000342c1000801c40c02c42000954000861000c100d0740000d0802401003441804150080340c221440c000f8490240300118a5840b40900d06100040700111000100c0304141e47c81c1d0342c2401b96204000514040d121030f40c004105aa1940301800c1c0d6443c0c040d0301040100822407140107281070b241c0203080001030f80c0002c040b803450880241c100301c1910041503030074020381c2c1260f20f6440c895005c6510000410000b039114074091158052182c5000d0746020182052000c48607100700d02d480088969003401c01054000120009040842d0750b590740880c060b840902c010301601e030180c0c000f0541003c8000c00e46610b200389170481c440e580c0040c00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 321432877 1250 321431627 321431659
    0xd050109050f16050d0e0d02010e0d121505180f010803040501050a0809010e06091f05070c081c0f020705060a1505010c021c0809090a02070803010302210a030509040b 73
    0x11400f900000203090101c903101d03d40c034044645003c1c8403804603506151054581542200007039140508990303070020b000c1119810040d50722044c5e42000754011812010800d039016515500c9003507580303441d101030743e162a11172020480c0c0d052801c409134910803040c4180441c1091403c005401005820020351800c2e0410300020850300519614006108032040814a000d80c01e4004100006180e0100c907024030341080e030031346d81d5248802035414244c01d100d0010009007060242600c6003c482d1654651460959030704905680290290050060503440e602d45484a600030703203d00c01e54540015845080a043c15800d140000d03010000d40c510f064501c0703004c51030528584007260340c2420400110107850001c41c000b00f420712803084e001d0309007005102c00c000310740018100b0f43c042917440b11090781d10725007108128418980040c1064900340700410041c5800f2942c94880c012650042c805500c02401c5140f80405e15001200070403804940e2540074106442040c910b05401c541c2100208100710f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 321434127 1250 321432877 321432901
    0x10210050c093a140109030201331502070e25020a0f080a020106090207080c06010609030f170d09030e09070c02090c090f0a030c06090e010b090f010905040906020d05010905 76
    0x7040300e210f40300302d0380120001d21135065100540d10b00030100901c000c24940c90001d000b080c034030040c210b038000904525a0b03003038036040c102901d03850015022042d05040c00400309140c0c40080d18081148200c480100d0300882922003103004080d51500001c4114040c4861168403220034070341e45c1194003210070140450035031803c88a100340c0045525548940e40f905c100c0c05031100d41c010707005560001602000b00300900004100c980c540000b9102140d8032040c0481e5420114800540303c2c04403600b660740403507410083c0c142c8444411701c05900e4007031603448800c151130b030b1027205801181c4003201010715420314031081da0b802021440d1034003410710039034006105451301070402951101c000c501000349031252010600511401480c41091990364070302005002d00e40d01407980050000c080006d1500140780d0900c5c140c8012000d000e04004600d4140149c42c100015140d041069183c000071341030b181c074030803000c0a60041c4000742c2d962070300c040380900381c07001170f80f00c00702c078034a000c040040c50940302e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 321435377 1250 321434127 321434209
    0x602120c0d0c1103031204020a140d060510050d05061b0f041806030804080303010311010806010509010807020a0206040f060813081c0b06270a08060114010210050c09 73
    0x6080109500005003060024028070400f481d8042c0303c0040c1d0f02c0410b01c0a00e0300203128134401c40c0c407503101a441d00449220b44a401d0f03005d0317801c02d09280d070030340003d482c64015552100e90400109002a5a00001120020b0500c41600d503a0400f40c24050b001c4009024007829161035042a403500c908500070600500c514402c00c00101c4000c0c140b000c140b10039400520007141c02402403501d480e01c890b030b41900c940c000c0c44202c0f402008044501001d501541001e0f120b081c05031200350070319100b0001540c4a04004001100b1400741d04440c40c0182c0c0c03108042d1000c4d100b41a44480820306000010f00b80d0b00000d48001043c0c0354040000340010911801c50f41020f200c0303d080703091450640074400290110308a001d6000c0c1c004900e0540804280c001711151060342900c41001850307210178404151050700030311045401440051100b0565080c2400031641c040c0704492004289600020880b8415a06840c01c002c00285400240c42e08983d0b000720b0a103000500c0c0000000d4000d405030407900 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 321436627 1250 321435377 321435403
    0x1080a0b090a0c030f091202071203120e0f1002190207030b1f0902070f030f17010303050c032a0f0d021b0d060906060e360a02030a08040602120c 64
    0x8400e040907800e4801e41045c241690301500c1880303245000c2c9049510001e580c44040014425068005a000c0e6801c0e00030038074541548501d0011424640c03008040d100403107070440d03d0701c10855401e00115040042c1502021510030050b1a20b011700c0c0c00500710500c69840b0011544081c0d41440030401e202c1400b90095034640400c0410a031000480c1050a2140d1000381401d10220721941480862000340103224403c4d0b40349615072805203401d0b94894101944e9a80703a624450041c0b000034058002000c580d00301e03008690501c41802281510003800302a001080b01d981030b440700a02404000b1011112801406000224901d1400030360300c500100080406407401c1c2c1c1070781450303250452581105a009407090040920905082c0042e0503c2d200768080d1603038110000c1c1002c1400d842030401d1500001d20301c11803a8000703100068040c44404000100e010325810540144d0f402c020205e211072003070050340d4486240000190518041319920080a1420800c0409030300d00821880f0032101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 321437877 1250 321436627 321436631
    0x302031506040917043006052701060807050f101b08030103210e010207060e0a0b030f01141e0d0501060801020310030c050f1005030a090f0f0201080a0b090a 69
    0x3072014002000b034a0b011101400c2407840341180911144480028016a00880192107a03580b14102c5184008019414201c005403409030039000a0b03242d402c6030390000141c0b0b421114200171581140b80e00c501c41c0301c2141c0c1d1a951900304015201080c0158001000f0850340b418015540f030000c90070016856061a080010403070141903140c0c00f11240c00521500010065140c2d80c4a01e840641e0710b8000340c00000e11142c0e03141809100c1d03c608001c01c0b0068041c0e02400d07129103004d8003031303c01110f4902c200d0380c0700c0403100c0301040a01c0480c028500c210180c0071a82c5580d40742a801400450b150840540145d105100c503410b00f080800100c800c0d11400e8400300d115a4060805e00c0c0107052a03041540254000030600c40e0170040daa03e400241ea000e050b041c0040d6507240208464060018012030f00000c001c10700954041c000c0d40034603440b0794000720214044090b0f6031002042150702c4002c403801500070440d02c081d942d201e02c076240d00c144200e0081210018840014101d50001030284080036 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 321439127 1250 321437877 321437881
    0x10906050414041a100b1308160b04140a090c05130f0503030405130e3301030507050108100902030108070e010e0912090324011e060807120b061303170403020315 71
    0x140c43e813200014000d403483c1360380b182d911f4a00c011180210f032003108584c0c49416801c41043c2240b140e0170b400c0f1814504c0aa01d090314084003042c458640d4a0340c69030000c5040c0e4000b0f1480c40300e0050808800e100c3c0d44159440b8540d80230541c0e0803409401c0584040506141400946c45c00000c07078040d6003045691082004408100c1006088c05c686551854060322a10ba48060000c1e04210545011481d0b01e51891310440408070844000b4400038080340d002041c01c011650041091030b801820500070300300c50503211642c3d6001e0341d0080e0701003c203991001c82d080101c503452100c200d0241081400c40300440c00e00c0600c2560300d090010a12088600001e01e0002c556020040b5020030800383d400c1c80b118034102e0500d4451032509124a101400d043c0304042c02c02580390350f400c0e06445098503016502e45030742c03500b15207000020540b40092541d8600040d8a6520f050141c01d1000304140c18129150a42c6040002083c00d00c0f0210f83d0360401f40000c2c00103070340c042004881400c031404204066 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 321440377 1250 321439127 321439141
    0x51c0906091a07080a11162303041401031a010806060d11040915060c170f030a0515151e12070f020d08100b030a0b09010906050414041a 60
    0x7030808410080180c200210403000c0b01c2400308602d4030034480d50300c07a5001075560f1155201039503845440380502100801528074003a00c101590b01107107002e4400c0b00c1e00600e1104034103005a00c04402884d0b01e900124040241e4031074506102d00d09102843d0512503140d1251078100c3c0410301d03088040c103100c2c8100c0000c80d591541d50a80300004002041801b41c130b80d0708514001142c6c050300075044018145840009c038802c007050740c4d008072840c03070340d44040d001c84a0b1100c0440d041c451940320080340c400c201810844904c1000ba5000d2290b00000040f02e00305841c0350410080d40c01020782c040c00c108401405041c00322001d071584105401c814000c0d1200c1c003025001a8414103100b40c2c4411400f405000426500100449100c042d40e003c48007560081002540c140b80e007241c094501202c2500240a111100800365400c880c0b50140401e500c2900400601501026044080d01c50382d07a42c0e00f0000d51800f8041d03805820301c0c07030807048011300f4152140702d2107042145002040700c401e1000701d000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 321441627 1250 321440377 321440381
    0xb0f100f1a1605010f060e0604090c0e04080f0d0606080f04120302070201021507090608150604090e01020c0604030e18090606190305060103080301090c110a03030c02070b03040f0c06051c0906 84
    0x302ca41e2041c020880441a80f491100408040c0104824181e801b40021f0341801c10340b02d84800c4913000320f001c0b80d10900e030185c12420000c0c000c0c0210360840003800034440c0d60b039495004d021107a2507040045140c608000006003074410040c58886044461414440402c030b6244070025000018a000b50790740e152800103030315196907480c40d0350f07880c00100104840e80c1c1d40409010281c440d641e94012441e22850750151806d03c020b11341581c0a0310403c020042584158440ba40b8050010009810038896120030381c18000b00302c5058001c501c0c0c503a0b241c1c1e0309282002c018401d0035028288000941400c00000c1ea45850041006000d10301000483e8140c1c191400d0403002154005c04a604560b101d00d44100740740c00a10503c0b00c03041c101440000110700920820405400708030041c200d010301038600310054152060007100b9070103034071008160344103040003c40c4070320b000356000711000811740307000f40000c03440f42e200c1020030070284007032526103e1031203190502500f010b81c0414402024184180 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 321442877 1250 321441627 321441667
    0x6161b120507080d020909130c060f110d0f02010e030705070510110706110118110405150a091a0a0e01060f090b27040204050f0d08070b0f100f1a 64
    0x282981c00301e030307201001804c4e40007003420440c1600d0b420380380d84400c00d600c8103085c41c07000001c100b04000704060100b40e1140c0602c40c94100b4074030f8510303003110380389a0160501c452509440002204000d003454240e409004403941304607124011417a100307291b280d003a1035050034041c6520500e003170110781c1d651910504030040c2d40c480b584203890b5059034501025090131101d042c0141d107035007000c04080207880702c808910301540e0890300c88410a5581d008000040800620ba41d03a1000780e07003001c1c0050384411a00d10090440300800241000122248003081b01000080603ca09403201d02441601d440501490440d4041c0c184140d0699010009540e04c0030301d90080c012001000c9011070b440546011070741c02583c80300169010300600203040c041a80b046000c1d0035000580032041648508000800302401da0003195102d0821350a9551114030740c0059980001d00e003250b90902500700c014108100042c10003036100ca600c18a0580c68681c1c58100304045502c20001082184180c000010101 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 321444127 1250 321442877 321442883
    0x702030f011b02160609050f1807030b0a051009030b0c0702030a080304031205010807210b0c040509070c1e02030c09180705030f12090607060e06161b120507 69
    0x12041115200801d10340b44a03440355000140b0400c001c2c4081102c1203c03484040d12001da9480d2a03850900c2c050040c0090200c0c2019084003c0c100c5080045545904c05401401e50340d80201784186500c040040d100d080d5008035200d9030444000d00c0d034403600500604201c0390310005e1074502c0c0e501c00641c200c2070f0140c954042d405011b98050201001400b00080d44035612a0720b54007194002c41d81803e003110703400d02440074a5404070605020700d00c009800b032256444021000400601166203143c5080c4056a00002a1002160a200600c2c01411907540b041e178500d00a15490071644440b6640382c0c070880a0842c04003070000310b505548050115645840d00a0300001290030440c0210740141110b120700c8542d8000c0b02000310f902d240100c1c48007800c0707609000420100942c55420758441d40a041c0999200d4401c1191400040250040144441440b00075200307500d001c143c40241c0071201c10201c420815400495200b2011004140c2502c0340c1088122216407004e0909544070b00c6565800303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 321445377 1250 321444127 321444131
    0x10c03180e0103060f09021e0307080f06040618080a030b0f060c06060306090f0304050402030a060e01030c05010f050307081801180f1202030a120c0507020a14030c06090a09020702030f01 82
    0x1ca81c10076074480c0103040741d1040c00c0420100500368044021100003080082d4482c201c0d44004004442540c0d802c120410002c0640d40850742d40ca102c10302d40155100219465084181044107100f403c0c81810104d8000803500350442030250b440030003e10a102d402014542e80340b507d11380d1529008100b074807260020b0a41651044000704407540d40030212803183c4248105800110791100200305a06000c45182c01035042038103020811002c0d40006194068440c0d50300c034000b40444070381034524020750088460000d1203050100040030019107203c05ea0521104205000811364040c1d40140d00c1a42260241200b8859007161405090500045000c0c202d08042c12002c0c00445100304088601c0785080c844040455041030382c40307001c0c6c02c1c09200071500c00e0b00c250841150503000074820300000e10f03107a03240105075030020390342034107179013055503294245041c0c025103050410180c6200901120f1260030650201d0002e440b0103a54058646a2900400c00340215141005010400c1c4007150003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 321446627 1250 321445377 321445379
    0x140a030908030f0f0603071401030b0d060617010c0e0105040302040c0e0910091b0509100e0d03030e0610051e0d0b0f0603101a090c090406170d05090f010c0318 70
    0x160603e450741510b08040c464880800b1850a00e8001022012a40d4074041c424003941c0503001500107010260100d44c02000f43e01c2c0640015a5604c00c6030003800b01081c500e0f0034003031034071103039421608903604002c18014950f001c1d00c0359a070400d0a0f18100d03541200c000c980b509442400725890408403140c1904008510181f003004039500b030f8a007059800e01001007001034000b8201060726140c000c50000410410450850326041020300b2514591243c00c2c2003030458030f85000704262034201c44003074001a5480302c104070b025000380034154004441d800030040250405001552810141124a101d00841e0442040945801720040403103038102c00018290705c0c2070107a146045208984481c440d020b03040890040040318861001d082880484905c14103100500b8410030311030245c80b40c01211402c0c440c8401a030b50b05d00548000c2c02080c1480301c2284c00640303007640350132807a41d6030905000052007129481d8941c9403000101040174a840242c0c00d009040c1a2a03a1280090001c4103000580d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 321447877 1250 321446627 321446641
    0x20d0507051e0315121509101a0307051314011205071d0604050a09051c08070f17060a1d0603060601090e150f060c07080609030a140a03090803 63
    0x302a2802e491100404041c00e01e1045007541c00f484111060740d08203c00c2030100300141442c0e140c500d00001d0b10700c00ca810705810301407468207a040440c1e080045a02000d02101152042e00880034200400c0d000c0780d2912100e400040e440340914000d15009001c480d2100100710500c0c0c21031a08040000c0030070009503125042119100d68600c419030301c0f4840c03085e00241329110b5240031401c4400e00110410b4030b48070181008050301001e02030120b01da0b15000100d0101e00b05010716259440d420140c080c8640d1301b650094071021b0000d00c0074051101558440081d107800c500312400d090400d02c10210b80741d5403400002c2d0190415004403241e00b9002e0500003802002d011098054402142140c005507100c00045400c50040e0040a55410641d40441c164400c20603940484400007031120202410b0a40800c00c1034004a43c00f030310307640c010f203c100030440b0103000035070300149940c02071031038214410030140c00c2c4850400ca00c000c0c00c500107400360703025120341d01056003142d10032480340d5a408c1c40c40c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 321449127 1250 321447877 321447887
    0x210c080105031605061b100f09060e0105060312070c0b0c15011a0405040e1002161e0209010e040318060302190e10270e040506070314150301020d0507 66
    0x4001c036802803088040c4103480c07031950098101118070003000680380001800019445c81ca20380030240e01441550900e24802c1501d008102001081241c00901503e4905045060f14920034a0550302c2e407500040c0320254501207001021840c41640b15995400545400581070440340c0c840941d0280c08580d80b24500004950000c000d020360314091466602c0e05428807181c50807940c50814860200400c002604007034000e104402e42c1c1c007041e203002100c1d009601c1c0a91340020f107040950600000e0310400c01110300c49448101440e10345490b00780040b070740415100007044c018003081c203007018000307010184a981500c00200002c142106526900d6801801075000443c560300301d022a14250300c4e05520403c03102c00389004c0140740411191910105542c2884280d010005801c5842400440d60b1080c0c008040241520090790b819031a01e428010304240025160508143c1810709403c2c000741e81c40e04260b0842107604682c604070701c4080c006802481651010200c142c185020030a40c0ca03044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 321450377 1250 321449127 321449129
    0x3060507030207230307121205090d11150a0b13090b0604061202100f030e03040b0d180506161e080708010f030308010b070201051e09010e090412210c0801 68
    0x102542c507070807090880780310f206229101540d4200d6000344141340200d000003012107c0b440c200e050255001940303070741c0c5400b07a910440d68548281d002d030044402c29a40b101d402c8085211101c00f401100302901808040d5201c01341800c440c00d511030b00d500e213031035507021403108081401c1d61040100d1040b0b0302d04020355090480e40b0621403807030180000b13026030404a07024405503000704601c9590048000944242c04c2ca000d203042010750301c0403000080c880c1040244081c2000c501580e4a6030240c0c5e0700e100c240c9442140506105868055060020f240007c2182e04443c000e070541c03421602003402220007042526a00800d031100f502540c0c0c440d0303000b143c410301a01407940c03280d010340c0e2282c110f042c1d00c10207407000a0002d9540c0e00100800ca401501911200d84149842c1e0316203884401d10844500511200c0300303202c0800140b240c9250307044402010100c0003074400c1490303482c0030744441c03000504440704102800000e00a404920301228514028040100c80421007410382c520028070300f5a013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 321451627 1250 321450377 321450383
    0x131109040c0e060108060907030e1204031506080109051e0c1f030621021203070c06111018030f0309020301110414120a1205040906090f0b01170112020a03060507030207 74
    0x20358004901e0f65481074a0b00751181002620701013498403010801c07001402c000b2010720050040c01e072441c0c000280e000040c4021809601214401c01c032440c02d010031a20154001c60b0960300d41500c01001a41c0444d49803034000140c00c408200301d4042411038107001041e15841da00040c03240010300e58040c041d0943ea01000565010401aa00d892404c031480d021381d01180e22a040700d140c1c40c3d005282c440c1c501150508034009403424044a569640040c102c140c203c000829a80d04003640c584804003c402490f032210402400341c00c1e085003584200440d049806410000401400d100d51030280d0440400e0b5035024008004409040d00340401c160880c0c090043d007000500205801c0741b03880038100346062030150180c84000c5903665150b00e031780d075500c40e074000b88030061000103228007041c0b01d040d0080860744004105400c42e444110304035002e00c0c0c456414080490380355900aa0309a074550b042d500440202004600c0710b00003c0c95015107a44018192402c02041101c40b0b40d05401801030144 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 321452877 1250 321451627 321451649
    0x80a080d0c020a03140a0302040306090b010501170723071b0f05011403060105090118081b090403320d020a23031f03021c05070b0c06131109040c 64
    0x90701280490f1903440c0c16402500058070400341603d200700103c0104481d088508006107031035665a614400c1da094200b017a24003113800d42c0104059604a001900d940401c03d400841c585010305000d0107444d0b45035890000266442c00060002721100102c0d41710740e03080100c0208400170130f02e81c241d20740024060103080c5240314000060650241461008000f0f14034440b50845e5900c44c011203041e0460802a41041030f005040c1c0c401c01c940c101004054480c2d030010f810008146054641c0c42800c42000c607000350170041c200b1001c43d601c50700d14425520203e500407000d040028100301d070060301000045000e140040c050701500140c0d4010300d0251826151007180e056038044e00b00c00504801000303452000c04200003a03443c406d0040003042141080d40d03007070546803a500030400c3c10381542c03182001035903034421900620200704101c1c0c0040c00f01409861070200700c40c190507101c82c4040d1048117110040d03028403003082040580c0e00c0e200c030400351017500140380a04054017012001c3c4284646c401e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 321454127 1250 321452877 321452891
    0x5100509210f031b1603090b0c03071202240f06030706021c0c0f06050f060a06020a030e031213090e0307020d0b1302131e33080a080d 59
    0x46901c50040d207940c00011001c600304440034a250050b50710051506026216400310500d074071031600040c1c007040da804401d030f020807017035403038080c021020980200b0700b01e00c401c0c0135101d411403000044a02d040c0c1d02600b010100405c101c800d9141c6500405105d0759800400c81002d444101418214803806002d010101c4940f60501816200c04440c0500001600103100011820714070740308103100c44600d864410141c20a546852101740c070600c200f2980c0644590030702c400031071425032658100b501215204106890810040d5807008246402001c2c480e15900003041c5075821310015200c40c0410068a03620042c0154440b452141c6003c1c0e0201c25103080c208d0080250000151903c843e8081e299100b0748460341c07540c24400d20000c0c0030740d00c9004101821030050321200f141e01d040c1e902000000c12145582842d0042c05e41e022107031441e07aa841d018010345558134121440c0c2e030000d06070100c6286020318030000189107525400007282c82c071441030f000f000c0000c1c0720010a43c195051404010318 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 321455377 1250 321454127 321454153
    0x604091d0f0d02120405030a03051b030a082d06011101090c09090b0702011a06030c1b0c0a1e090b180403080420090412050403050a1a06240901090305100509 69
    0x40c5c000c502509406621100d00e2000007402440148204400110540040464604e07410b10b140e01c20551a00000c0b901401d000700d05c80511407104619406c0419035407101c0d000c030106414000001e2090b0304010011065105480c000c0d8044190280c014252501c40303a180d04d5154064126010300b169100040d10000d0403040c41031050820f80e003030038056030030040320420800c05541c00113400070640b0101006040f803d021140000103000c8076040150a101c4484170400480e500164003550049442105055404c1c1400c5000b20903101e1154000550140483c0440c0c01d8801f00341040c41e901410900b0720041c1a0000300031072244e48910f079803c11024141080491000d814503072580c05c14030010200380000c041c114a082c03100598603080d8289540c80c0c58151400c0d01c103000c160307844403051603011091340c041100c0c640e006106803855040410640440b2203084003080d0618a000400306070b51015a104591800003190400f044070348400d070300f4841038010102600c41e0200c42c89528030007140713 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 321456627 1250 321455377 321455413
    0x140901060206070e0f0f060d0b011d032d0d1205060619210f021312020a27050108011a03010612150b03030703090e060406050604091d0f0d02 62
    0x4030f15590f90381c8030142c840100074401148100740410394130003000648801a0f46a00000c0c000002107260040fa104007980005403002e940192841c429944500501c41c207038030300040300282d40715a28240782910f00300e108042c0001070442241c4245016001400c50300c1c44d8820710504031540000420425911502c00300b120b00d108000d450000f10560108141c2e880340140042c09902e007020b204443c0209400c0c0030282103516190381c08103441d40c0881d403118182445100700000d05040040c0000c4856260002060311f4420711a500050454500c2460b0000041d05846c03440540981e084c00a0750311a1001400b800c00d42603032055410050316200341c1ea180c140500790403520003c002d03a21900385a03c8500c5202d1816240000e001e850b025940801c0e1010401020144d000783d0312402484d013410350341010494084c00d1544a030b41440301c1030042da950b44044a084034044403000030160a9a040b8024180c040a2040c0d014003403980203821b01040031600700201d41003075007990f8000500000d41c0314 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 321457877 1250 321456627 321456631
    0x10609060801210f0605160e0405041a040525170106030c06050d24050306072d020c0a0f0f050402120a1d07090204170307030e06031906140901060206 66
    0x8000020b0949510400300711440d20b050150250381c07040380640c01c90711170800341c0394103481d130209100c0c8011a800d01154004000400d400040310280918206500e407124040710402c002003400e94204080350030040c00b0041245212580a180200103111344100110b002c1c0da40704a0048841090380c81c4401d00d4103110706019203a00c00c049008150405004403440e8104042c03240b400c0c0d60b10508400301e40310600e80c00c805451318010300704070182400141406e01101030010401d2180400c1c16011220300c0003100403c040c40c0c00300303c2415500103c003ca29160480744031940001445c1c80c041610150b20150205554a80b82d00c80b10045d0740c1d800788400ca114419550300e40550090110b84880e0b55078100c10b05240162210400701004001750038100003450780407003a03a650004003002002015814900301140b010041c500300360f00c58401911180344001c42e03c0c45014004002a0804280d1030aa07150030b9044008100654407400510701000b41c0400241c80341404900000e0010300c0003c04038 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 321459127 1250 321457877 321457889
    0x15090f090b0708060a0e010f0501030e0312011a250606080f0703060e010207020603160f09050d0f26070605090601060c14010912030c17062206120b010609060801 71
    0xa80c070366488070421aa00c48014203901d074040d1050302e000401c00ca010320300e107000c0c4c0325031300038002041c0ca801c0025007115120036030f43d030240d007062284d0785081c0e040143c039604650701c032075204802da80c080c5502e140c14800d021101c0b15110b844000ea0920b440048a2040a0f5115030782c00c110700382d25220842c0c3e4500010003084400d609c03c54060001600c81c0e00f001d40f040040a0015040040756800039003203030400c4030381661024450290303c10b101c0e13005203440401041400c14503211410100072898404010001a200c04e4a5010b20810003042c08101710f509000111a50b091001400c0c000565620008042e600f103400d003004540c041c000803826a040310083c0d01ca1842d10360321342d96440c10154444140b1110b6540c0c640700c0602182c4140e503411300c200516980014035a00b10f134006810020a20020b1082005040c104609900c1e81900c1903031203550305030b094404002481442016140640200c002c61003040d0350b400400246071042416100e0548600c1c03d140c1d21248111130781d030003d1040f4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 321460377 1250 321459127 321459143
    0x20130c20030906090a050d030f170606090402070c0305010e0c1504080c0d0c050307180c020a05030d0e0a020607060504031119030f0c14031309050405070e0c0403050115090f09 77
    0x42c00081c42c01070010145007074003408030000142e481c000111030050004056002c40c8200e030f400080756034000501405280a44030200c4641821380c04110b00780203118106028603400074031041880002e2181200a59111000f402040300701100907466031801e0000f18050441844130507e00305109003500d05135140d05005020f4621003104010448481c0c0405940304016400041882c1e00c05101c04409881c1800300b116858400f000340d1000c60b00e246400c50119003180d054900000d0b004022290040c6050700041900020009a00e0510502400c000e41c0a100018100d003081200d4011078442d900a4982c500703500d9055031120f40b950b08000307091850084840304000040c2c040d03001c82d4003011072403600c9098070703600740d44022000455090310203190713101180d031200000207445030350081e1002001c01d1100c1c4c00c20f684e4a5540da580c42c0038260080302c1000006040c08110310a0350025500440240040c580580182041000300d002d00010103003407655081a007542400b8800c003d550003515 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 321461627 1250 321460377 321460387
    0x1e07030b0408070c080f010204050a0b03070903020f0f1807080915010614040e09070504050907050906060c031603050403021f12050a020408010c02010203090d0e030a20130c2003 78
    0x10300e0b52150300070340c4225443c44588002003040c80301000030f01b040c0300101c4001647e40b81041c00300100c60805a0001d450490104104622650300814010032a43e050762004040120100050342e00040d0214044e001014007500c0030700202d206030ba10b801030385180c94440c903d8441d0300203d03484180034144144d0300504180100203251044020b04540310b14020481e007800d031206c010a58200d0155060800382d4454035091109107080d20481d80c10440e148020f01200e860040440c0046000501107442020040f4940c8100c0b00144100d41c046c0d0b240080c4000264032901e4007600540050005034020b9204480301c103400208145901514801c1c1d850301024a07424110ba00c01610004000c903140c43d400380000659003001740a507000e00891a00056205c0c034054414514044044507071004112842b031065200303440204103580cc0940001a103407c038495001c003000c2d441030000c941500240c907840010b090015942c0401c2040300c80f541c4860303c5c2c0d45200c501510440344c200c0c2c000c03a40c0d001089 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 321462877 1250 321461627 321461633
    0x3030f01080d051806070b0408090414090a080d020f0a2001020f0d0b04110a022415120109152307122c01060519030f0b0c0c0f1e07030b04 61
    0x20804e00840740102401e01c0d000c1503a0302c000070400c1c181d4046442c15008101c017441d6107418046c848074400c800f4005400303464a6014941e41703c40596018003818070018401c6107040080d0111402c10480c40001030b690201610000c114000c89842d2041010021600c4070100106000300d80e0f49948501020b410201c001030403c0050070006041c680c01a80d03074010f0348040c41900e0181040c0e04145d0054040381c4945611040361300c12010b60078403200011801c20840d01c0d51180100c000380015a0400c400340921f560746801000d45000142504041208a400300c140c04c2e0444080d9040c0400075030205a40462180c103225025620040883c4034082e11001c160b081d0340c0107800c1c3c0c400c00351401d1200d14855602c507070701180c01c3d0f00c41c3c12182d440300c4040c0994148000f481c868001c003c1c0d41d0880792803560b15405505103000358010403016460300400d103911502d105a07241c011030001070320441c00f48286080da031040e0080002030301071400404000a030401107001300440c3e401103101c400713550f9269 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 321464127 1250 321462877 321462907
    0x20a0c061407031413260606092802030103081e09010e090c0702121606140a0825170703020f0d0c050c0f060403090909080d0b0301060504020c03030f01080d05 70
    0xb1000040a02400501c9003602c43c008117100400c0545080b045042c400e40c25060341500c507080100c0564021014001183c40d5403042c0d40d4060302c0b8020184603410110702c002e00c2a441242c01c0b60080d0b00220010041c00000401040010060b1035181d10b11803841d1100f040c90700417516a076020070042d403c41d401c40d00f04040303059405000b000d011868501182d0000300e2600a0600300002039200014100344c442d281002d0002410b100e061120320502101d50482c0c4504c2500c00303000420200d40c02140c0c46880782c0104d4108540c03850344100c031a00800400800314028513001c030300800344140200303071042d0280c0700b240c0c94036654a0b002841c000c3c21540980140c080c6030380460030480b04015807041918103201c21180000c1d40300103801941000c0c01c00503c40200303a0000d0309500c0c944040e9400085045017119015402210082006014440082d0041156a019940040c0001210214541c0c0803009620400421036000380c90798031000d83e980e81d80c92880380c00020a108001e01c01e500c40c1c00c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 321465377 1250 321464127 321464147
    0x9100f0206040201030f110a08040506010801090b130c0b0a05031e070c0206090a050a030f0311010218010c020a090c0e0a1d0105190803070f030e01020d09050f03070305010c020a0c06140703 83
    0x70322000c87c081c02d860510f080702d40e000c8102400061030039018802080020b00026004120f024020f011100c2d035600c4290900300042c12a080f07903001c5030421010002c10040e850003d004c0c1c81c4019031600601e04002e00594421240421403c1035120420709192419007014084c0c2e402c0d9442784000300300f65007404426803150101c00c2d4001e1841d440019550355000d94a0302552148441030480300c000c0c54081e004507140c2d000c007020340e40107100704001240d007500d04120020092810500448542c000304100d40004e0f0412940541400a14031419800c080c461802e0001587c04143c00b9940c1c410501d0381e8180170400544403152a001086240741610f52901c2420b442000c3d00034640d51090410b01c1c51388089021601801186000c030305154000003078000c040c0007800a00141a8035080c024000070a1b8002c0c06d1142001a03000c0010b031300d0401540c0055944400200b00000f05c0c5140a5a20a030165049809134445280841c44a02c501c01c4100c8111290481c9410040170350341c00c0c0d488100c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 321466627 1250 321465377 321465401
    0x2030724090333020a020d0206070203040b0702040b011110020c0f03030103080d0b1201060305160b0310060305070c1e0b25050f0d022b0b150d0b0307080309100f020604020103 77
    0x211074005400b00705032004003c1780744260000d040300c0c420705401038108607005284034290340040c8070810810b503203103040354140c3d6170485000601c0030250006131208025a41c0c006043c0c860000415a014815801400c0c6220b0035411034802c8084000215500d20003400024080e1384244000310b40b88865400c40004500000c100d4903a02e42c20540c1c1a003151540d40c001d031200d902c00f65802c4002040305c1c0c1400098944594107a01d50f01e00703030390f558026401d188100c100701507444c0001095584103003d0203884503403185103000c800c501c0c0000c4124511020740c003610b09000080204a00d130181c06803040301d218202c4803036051840041e00c1076405400c1400130f00c040f024104100e03546c2203158801407500400c60001d144508180c81841c01d00420801d41d041e860b41d14100207202c46564060012149285c4c0c000d80d160f8815588100901031303c42058030039090301c01d1400101e0040070200142403120303c203642a4851400100c011074441c04c01b2201c94026802c1800850090f5110343c10043c1c007105 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 321467877 1250 321466627 321466703
    0x30106030203060916050913020108040305090402070b0109060602030702030703120c08030702151f0506030c0d020408060a0c0305013c06091d0906130f020307240903 73
    0x5601c0d00440c0c00d0200440300305846800c021201280050301c658031201602094030521040d14040c1d84805000c4c42c0c14002a05102c1660002001c1500c904222250803c001d40299262401d5207085110440c00303000f5880c005042c1100402c00c2c030f00c004152070401d90020001d00b5940c0c550340340d4002600c54500d002c01000202074180001ca00c601e001503000302640d40c020b144400d20b13206c60014005000e8800b148820444040e1910b4140d003020b0101070340c1e0101c440310342d20780f5840030051003413040e064800342c150b00209000a080d000412068462921814184812011900118200e42003405180d00c8000041000b40394402261001c2020344403150810000c4410a0401440c140306540840c0010700d0144051141015451030b060801d800459081c0301818024045a01e8490040c201c40c24106154071100034001c1c0d03200303c5200280c028059800d001d4441082420821302041e0019030f07002c01200f0201400d05c550541c4e81101d400501d64824080800b02100c00101e1311088203034012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 321469127 1250 321467877 321467879
    0xc0e150301090305070b090706140901021006060c1e081602060c010609050603120705070e060102030d0e030405270604020d02130e06010207061e0f0302070b0a0501030b13021e030106 80
    0x52424400c070302e480c1c2c2c001d031540c5451390510b02e0100c2d400b0034020700d201c400f03800c00402080b40301c3c0c00ca5144102c65103a01d80780c1c1c3c1c81d0304250b00101c1c42e180c070741841141198101100054150f42000d8040301e85401018848034a030300101c40281030501081e0010148207040040c0c00300b5001101d14005080d100800c8145883c08405240d07007907034465000f0b250040d41c2c1c1d600340710070b61804204003110980340c1007106040c4865601c541ea01c42083d81b150500001020000404d180c0c400d1040794800000e50400b00702d0305014a101c0340c0c0d241c00501450f406110399034130b1000e100e90510741c0510700c0c044088000481d80c2c0d844043c4000380d00810701d03100c5616000d10541039222203500c60390f805010b00c0044110300b407500c000028588000c1d980f0003000d10204907003400b90300601c000d409a040415041200500c00e4151b0300310300a00c18004041c00021a0703c043c0001c1c411680c0100f812603004441d02c144d079031038161315032800c084d040600a5006188810a0041002a01c3c803000c44100c0240005019 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 321470377 1250 321469127 321469129
    0x1a06010e0619080106020d020a02240c0304060201060b090916090914043f18120203071a04090f0b0604180c020d0c020d05011b030b010909090c0e15 65
    0xa900800050202d02da145455401d025a0024040f80105000e01c000c1841c2e60034240c0280d21601e05150207806000f44240c2c001b0f503208030440d40c500f01000c11004540e42c244441c80e00d6141e410601400d0010b50a14030700041104911064030341c00840106040d00e130351034400c0e2540c1100b55407402d443c24020b800d4000a003500302c92240b0340e0911070124104a507484c040c0303072400c00c0c031001085201181b840008117100f40d441001c2403c585117030410440c058000c601350155407a121402101404244036100812001d08409134120140c0c0700b0745c21a648140c45240300070031045150300c02484843c0612040210400b56000b58241c00980c400001d8089442004142d190b80241c200d80c9241c1e41a5103100b1019540703204a00700b12071240301a10008a4500b00100301032040c2201a10980c4041c00a109121003988800584031540d07680702090a10b075070303019002c0c0c61701100c040d0104103000f07030006280c10140542c1280b141c2c41640c8488841c1807103461400384401400040031500307401a15581 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 321471627 1250 321470377 321470389
    0x2190608160504090b150c031804060b0901110a020d140606010c05031c0608010c090e01090b0108042d050606030106090e1207080408031210060f0e130e0304030b090d05071a06010e 79
    0xc7c02541e014566030303d07042d29441c400d00d2125840c0c501407440c040040009440010a0750b00042c03003460954030307001d510f02c180d5240501821004e94445415003080d0100120210361490320f02c3c081041d2070302c65460784010744001c7c50101c40904030f03400c1009894258003501c000c1030307903d2440d0341001440e1364132001e00d2803c40341c4808101f4086a10200c0c2803044101030100d090041961000502c10703010ba080009081c07050152008150242d2000100f04001c11a80d03610302c1008a040460655503a500b070035543d422080d5400d60180d40f0740b040124091359a80190030100e20148001c046e10315a5040104940c0e00c4000d0540c0c0b800410300c8082554401440105460941514059220304080000c4580c0c0e003038039401074007170190340e8981c01c1c0041d42100c83c0042e49002114404444601c0e003440e400600401440300d25107010005001c001c000b0302103c0c02e4001d41c034070b004450305a5480b20301038610b4440d142c005007240d088103284c0c1002503c240d0701554080018505005d28001a5000c00c003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 321472877 1250 321471627 321471637
    0x5040209010603200315030613030507030302130e25020d2a1a151017040606090f0e100c050d111303050c030f03040506040306020304060902190608160504090b15 71
    0x1b1201d0165030450524030b4100074180c1c100101542c4408403291541d0b000e030451152400080c2031540104502e0078618418482b00700406903040300507400e280180d000c00c1010a10009002481e8509902034a511700c00103070aa641d001a45a00e1407031303c2404400c951540000004015203000d00400034001010301c1e064507080031881340c0420141c244030700c08280c1034409041d00ea00440c82ca15205400c0350307101a0410f6154441c000d40c060341e4407241030510192000d9000801040d04041036212110107a600c10071350b041c94481559140042c645030311099429030b11608001810a0022025012195100708a0b01d00107080140c500341003040740e400e0615003544180d40c01c0c0c00009050302603040602140c0100e900740005545440c3c01c10002a082d8003c80c040500380a40c040002420000e0030f60000366015001007001400c0c22400d035080b8500d0741a0b00811001850180100304c11024020100d001c55481c0e0f1109410142000c0c81d10303004000b02520075074801413030159082180c0e01040141 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 321474127 1250 321472877 321472891
    0x20d0207030903051c050f030702010b1f120c020d0f03020409110406030c0e031b0a03020315090f06161d0a06050c1501050a0b0a0513120c0504050402090106032003 72
    0x6001c0529504140e41010081500c5e520116504484031a056500000b1500ca802c59444004e0722902d0b2003604900500140191541004d261410407130b901004180d844100b041c1d0340ea0300c4143d005405243c0e810758101d0032550015900030b13071aa00025000d000c400010010900d001400c2690344e40446058800b2644503003001e030b2000030b081c8045681401208158607040c2840340c0f00c0c852020101b6500c50500b140c0c00c0514003d441c42841075610400c20200943c2c00504440c0c16a11901d800403000c0380c2550300400c94070584801c1001002c0100d0b0b070510621050543c1060343c0301c00c4d5030540d40c1c422403150440820300055640c1d42d49940d8080300d00054413299480a4841c0da4580c070751854560140c070340c0e0120100d45001080556640110358082d04c0500620a8481d0603041080c2e0301e0740a01400a1203115140328041404541a40800e1010b130054000200180c0c1da0018002200c00550f000b9402c413240800500c0020b000740c001c800f02109510b00018203c0c2040f81e5007103940c100742c0d010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 321475377 1250 321474127 321474137
    0xb1f090603060b03010b0a260105090616080103030203090402071e0f0b061e101e02100507080402062d160b1b07060f0902121c050301050a05060d020d020703 69
    0x28000d20441e031086410f400f00540007044252a6000080c0c21300c017003403203110039500240030300311032000c3e41340c01444441c03800c80b0081c0201e007060001640c941d0400c599400342c2c0341c81080c10f0204a41b040f0580c60480780c240e00903500c2e0208240030321029600294054800c6080084d00c2c40050044c40b0704408090b004000504d056101c629007030940c9507020344100e108400c040a210356114000d0601010280b045a00c0b4500e118640010740e40b00c110a8080c088120580209541c11038020500c62164015403404015503900c0e10010746200c1002e8a0213500840b0501c00c05480046c0c0610020780ea0390000608160000d142a889035550311007018000007080f071414031800c00c501440d445810039901c031080140082c0140c4000c000d8016188040d00d072903240c1d800e0b00c0ca005c180e507000110b00d0341c000c1e0a410300d201401142c1644d400070b8112807401074920710345500322075101e0300640f41601c000030038402030141741c503080101c50b810200c3c269010590800200741c1a580b24801802d00074426216 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 321476627 1250 321475377 321475379
    0x5070b01091d06100608060409170304060624051305030d230702011b0f02030a03091403010c050406030207020310091101090e10090e030c0703050309040e0a020d0b1f0906 75
    0x40403100000c0d20340b600000d81c0900180700e510301d6200c1c034403001d07a042c030b00d4111b410350786d401d0020f000f0300910000a00400c07000300032078000c000040011741c4154000d8105011032a6070729905241608140c24400d082c0003080a680c04043c80f40000740842c00e600340c80361313402e10f03140c0c40000c0c1403500c90311070080850840c3d440c0c40d420000500c060b401c000c5100361000e0a116254002030440001100c68a080394500300c2c4a9082103040e246980055401404641042116180280000070a80501c8042c2e200d00d02c91845645014000d031440c20500343d40703071400d262805400340e0280d049064200d900d40030705420391600c8a5548a0190124018601b01144c01c0d202400900f8000f4680c11400c40c040006042204507490003080310103c1d40254000110100d10034101810b40c05100c04914141c00313040000001d00c0000406000c103100700311000c0104140440d40d8a075510b404d82c900075040b003a5807243c04045981c0500c60743d0321203000d81c02d403d984c000154003508481c402d9080808071607030b5000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 321477877 1250 321476627 321476651
    0x19060e060d14280902101107030b04030f08010806070c06020c010f020c010606080106090f050d0804090507080406241e0b1207180e0a090510092006030f010902070305070b0109 77
    0x4004800828041001144145d802040c492862020141d00348a03001e6024452a4400c2020100454100d1011106410540380003005120300441850000300d4100c0045080d43d000310314503018a0f10781e203a4000e00c0c04941c0d50080039401040307116800c2d540c0c550041000141d035000900d444d0081200019104d814130001410400341a0414003c07c581401c0900406060742001c6081c2c8608861100c1681e050385880029481141c1010700041c3c14070060110f2140c00500440c001c3d072184005001c41c94070040400080068900d5a5040390313054001006600d02035001e80c054800580d040c6952280c6405200520794444490003c0e4070020008004105074416040a90041c100d07020a4040c1c0c80d06100301c41340840a0040c241c2c0c2c941c0c5a0484040040030010b80580603c2200300b480203200301d0030300c1c000d100d41e02c5070b00d0358494080d0f403020369140c0360090441c1c0c0701c0c4585814582d441c4c1d0030700300c55100940098804409101040024002041840700014000c10034140045001007840d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 321479127 1250 321477877 321477931
    0x9071d01080d0305010b0f070813090504150c0c0b060a121b080706120b032a04050604020307080f0907030b040b091c020705060a120f050619060e060d14 67
    0x42140c2c1c0800d45804010302c04080703074a0031a003a80149a84042d1a042d640c105101188035614401c00c5e50b10680800080707800c41c541205108502035002c1420700200210100251030410b840b11002410300c0012000103002c806009802103400351000420680741c1c101c40c1c4c1e401503400c1c4151a042410740580754030800403c0342c50082d003202809880124a0007001410030168908481d401c561203282c000c401c0e031030400c10ba00294110443e000400000780300700604881a48001901607800e1000007805410a0300031030380500388659079807105036100c0c0d0003141168000750070450709000e1241d00101080a8491041c0918054107600e501410004c0c00301c0d2a05101840321031001100001241078030f5008640c000480300300380c41040c5d8411a04500300c980460702c8246080c1d20345001002542d0000782da2000b0b00c5400c054540240c456500004941724100c64410140000c40415864420b4184030018100412074144040360410740c801c400c15034600103d600c080e9030003580e421000501305407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 321480377 1250 321479127 321479143
    0x50c090711030a0f032a09120f0803060a0801050c030f01140d080d021e0703030605010c051c1101090b2d0f130c1401030f111209071d0108 61
    0xe400c18400180c019840d0070380724001d005a18092101084010451324045d800851416911074180d403c1055050240340c001e103450b149680014602d0036000c01e050000a00c10f400a40d003042d150f1303204154a50765a0310741e80c0014211a0044030154000542c03075000d000e03140c0284079001d101c54503441c0c426000c03162000c1c160300083c03498500c0817810b28261241c49402103c583c0220006030b03145c881410780300c080e208414980d540303000489100e40d0020415805000a103201359420700915981e80011210b880d8008406401a005049070050501080c0e01c0089251114201000807000b0310b10107900712961944c0030740d0f94900b1182001003149950f00e842c40c0c180401c01c050070710341c40c170480164a4a0001011818001c1c500310110340ca010071501c403000300b0380d8004410404a0f49a1140b1280d1a1540e2100b07408a424460b01d480e4220540c010103205021060784ca80c103041440c82e11034180440944500c102c1d00a0074004078401c0035880c0744450812011130800350f294984000c00f8900400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 321481627 1250 321480377 321480391
    0x1d060304140129040b181501031e05161e080901060506030c0a02011b050a0c0c0306020f0d051b03060d1b08010608100207020a05090712020a0e0111120307030906090609050c09 77
    0x746c01c010201040358008240d08a460304000090003800c010041e0018520f803105070b4021003900303105407070b05503940e0001445100d003041c24403590302c2400f0017500c405145907000c0034002200d4041390781c0d0501c1500034660103100340d0000300320300780c0d42c0010a041d9031094400c04404600050102e5419409000741c1c20fa841020f541ca40b0040c8000d01c0040250241595035000c100c05071104106029002c0c903140b01039900040308568550201502e441103030700805123100400d080c44001032940807003128542004030658012481c0da60384e1010041080116a41201c400c07851004100075a0a071200d40c2c0007600c0080000920700d8100aa443e1610b0442d00706003d0b20344c0100048001030700c42c0400c0c0d008685050b180894980ca4a040c140e07451f001c640142c0c9030a07440480d40b08200d90340303d601c003078000c0002c0c2c843d0002d5101c002482c540f06c820386d0750840c0c00c042d01080401c0d00c00d84203502c402403031030103500c002441d1140e6079544c0c030544449120a9441d5400284085141e03d04060400e4000e40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 321482877 1250 321481627 321481639
    0x403120c090e1b03060d02010509040e0616090605120c0706090606091503050a06020a120f270b011401020f0f070f0e010f0e0612010e06071d060304140129040b 70
    0x84114580f00307481c44003c1c46075000d804a44298011039020300c040c0d07003950100500038070580c200d401d41c0719a134000445e0b101d81c02c2070320400c04031038480c06020000140c4a6582e141c1d49400d20031084110758220240070031404900400003600071078068450001100d10403140421081d01d0807904800392142d0ba0b001c080601164941003002507000202d00d00c1e10303513001c0030145e02c440d51003d05441504018403004e9840741040a45860001c855009064081021180d4508002c4130000085e0080d50140c0c000c0c101000d403801030014071042c44d4500303005001403045550b000c2101c0c038403500304452440e41c0031580d40008020301215582c000d42da0041c214150310f160096260614064000005100b0248407500c0c840100300941c468003820008490850024800c503103200101561b04c0f10111440c90028440a1406803a80d00041c03245461100080500303095482d507032562481c5007600e14a00c9015980e46078a48003407942603079004030380108000c15004103d030800c188026075018420b0320744030705 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 321484127 1250 321482877 321482911
    0x20f0d030f140423060f03010f0609060f05070327090f060501031413020409060516080a0e0d05030c0c0d050a03060b1606020702030a02030609030703030b0307030b0c030403120c090e 80
    0x1d250112000520f004c0d000380aa0784181d080d0204083d071194100f481e451020000c000315441021080304000c481c1550766141904d5035070380f41100e010b600d11041c400012000c0280c4c8011a11401d581e08e080c1c0d070780890440301124004c1409280400e158008100d094690054442e200b0b040c1c440e0a0051a00382400e0012002040102c550120002d00120319118441c200d1425522664020705105502c040204083e0a1601c40d466105c540e8407002d000141500c0000b030900031b414003580814000103001041c2103c400d108c1540c0d146c1004002c0e1840c000240451182c10904028100002e480c3d61505a92107140540c0203054425070f4112290b00c00d4100f19001e4014841d41540c0780041d00024011789510a900c00a405d044a071040a503043c49010140445181c01100910006100352420094010f660042c55100c1743c051101905001140c0d0015401d513130f402d0700455019210b4581901d454224a03486411200c00740440360020324104000c0c0511080000156005105545050704035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 321485377 1250 321484127 321484139
    0x509060103210c0204020706052403120f0d02040611120c03030106030905010f0e031b0a0203060609040c0e150a0602010509060412020a080d1a060f090d020f0d030f1404 74
    0x41520792242a09400085411030a8843c030a00030030640e00500035551100d030b604040c03001e01000d0b50b03200c80c0000501802090108804601d500022001e0003034407404d00c0038080f4443c15000a400044805c030104040c511401c0a031000b0030143c4029224951415540003400d1300c1c100701c0142e0208441020000b04901141c00800d0380d04440702840c0200700c2201500c0c005000d0b01e510303d03d0042c02c0382004142035403a0004005071200149003214143c440ca2030301030b0341d5600e652140d0b000e0f4164100102242c81030a10101c0168440c1c007444400720125a15500e02640600c00c440c00100b10f0400414051035240c8000c0d03030b40040505200134885410b0a0300142d48071031015200030b00d09441d861042442d0f03030007400640e05850b04103868075100c0c80902040d00c054541039500800b0592044101e20b014603003441640e0000e564445140c0c2414007082c00d0041c0246c0009003641c0c044420a540e181c0d681d1686855409540700f999091f41104001c07002425000081c0c501e030301c184600340018404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 321486627 1250 321485377 321485393
    0x6030a02070b1b0720030d0305090105090a0305070b04110901030f11181801110a1805060408120306030715030b0a060906020a0303020d0608060103050a05070501030605011d0f120c040509060103 85
    0x304c16008480c40c01d09449400208020b11208210a505030082c4440c3c03290306034059004d03d00c60000207000b800207944034410702d51206e140c850001c010400a201210100341c454500d00d6000e44100c610700079940103840000c40c804400d901c11101d0355a102d28039404c100c21944640304522081d80c011307440405405181c4a03085006010a0714516044091840800e0940254192a84001e0813a40e1108080c9000300404107030068881d800c0e041e140300140c1814220100d0b400c8070b04160140c649185802c00d0303101c0503800541215070602c9084070201c0c810b40346886000003010b0980303000582008840612002411942c451801e1000c0400f04100843d0007181610031076130f00d8600140ea0380b0b28400008010442d5803c008298400d8000102c01c100380065480c2d801405002103610861380e501c011001e0302c505001c0c2038001802101c9641d0f0307240010111100c0c00300010400c2d5404003800e408110340035154220285142d02400c48202503041030310a042c1c103c401da1001d80703210f60440c1c4035042 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 321487877 1250 321486627 321486637
    0x31403210f01090509010b041b020f060c0318010b03031c1401050306130c2c010b130302120a121d030f0c010e01091a031006020f0705010e010c0206030a02070b1b 71
    0x651616013001031100c42c4203512512100e00000c10030003c4011880c0c0c09020303c40d141c8a02805813241e039801706168800024403d108591200303041d855a034801e080801200c000307009004d110741d2600d0842405550074001b5090410303c11701c00380c0207032070b41040d0326050700c1c0e840030b16141a064a00060015480c04666250301c1440f0402c2d403103070100c880c5010b40c0303021040d0340444802400305a0392080c01003582542c45444802100c04010340e6210300e200c060038401c9440911240da041e140800050900016064006e0002416103003144c0d5148c0b100c0b0210780903c50480c0025102440d040c0c150340e001d03030100146010941c000e205080c50318810950f181849518141130046481089134980c5c4103101250180180a412040c105074142c80821290810384205628038402c100200d103242c0300144081150b4a00350082c00e5441c039100054500c0b581ca840ea9a0411111500b94405038483e01e0065000702c2411000507580c201501b001103000c04054005103519641c109a40d0701010303c0001c0e01c0c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 321489127 1250 321487877 321487889
    0xa0e0405011d0a0c09051e01020105220f14191203140a02030a0209031002030a0c08061809010e1b0a05040207021e030106091404020a0f0b040b0f04031403210f01 71
    0x200804c1e000c1041d915441554000e99001700b0400e089003a0800e140b01b0062000000c0e0000c0c005030729401c01c0600d144c80a03003005001d480e803640d2094003240c00d040c00103164500030101d881d040c1080c2c041c0d2509000c5803502c0815115620280031040140751281004141760700d00c1c04000051040c9003103020040080c212003d607a4000c4049039100510f60704848220300e004040303e8808034001da16a001e50811500310440d14648030001e4480c0703008100082c801c0c4402040f201030070300743c10490101e062001d025800d00f5940e0306c00110000c00701300f010603118081d5800081e201c0c00070004121031410789401c50341c0207a0040c00319000603120034229641d4044a03c007501d802072040340120740101050703030020f00c800303040011101c06219928400390049000f81e41c410342040d142c1200c0e54118107a03104104024204010400405c41c6100c06040c2c45201031841b18170302540c0c1d4484007000c0031100000e00c6a50800203003c10201e900081c00b40710300400740c071000318510741510041c61265051140d0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 321490377 1250 321489127 321489131
    0x120f240f090e030d1803080c0403020d020d0507050a0f03050709150b161b1809020f06070611070503031609030302120c0109232e1e020a0e0405011d0a 66
    0x300d00b500000d1090742e08111182508204200a20183c5040e040d8060400c4d004a012480440d501003001011601920340291034450022410390030f10401c20904031096509001c0d840020903150b590550078402040072805110f10a811400c03c1400c142407680210312003032801c1d0713107010305030010403291003150060316200c2c0c2c84240c2030310f1070540700080003002415030030320f800704050075010034209000b601c8000300140d050907102c034414001c440f46854060350005004001d15010301d01a0001c154042c40381c10301103600d40031031132050308907000554101c17000d410100c108204485c4868000002c01c0c294036100704036a10b142c602a4490940781c4454042c807400044803101120250410315900d5400400c02850400d10034240b09220350b070b8200c0403861f008180409004458200d07a0016040c1d0a40c0b0180242c2140204440104108000b05850b60400c002002c071906881c070103080c45a01c240c4030300400c4c00c0c2c01401c000440703405801280c0e66114440d9000401c00f074141c0420380c0701800400c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 321491627 1250 321490377 321490391
    0x90b010f030204230d06050f04110103231005090c03061c0b0408030a0b10020a03180b0d0b030c06120702010b010c2111190501050c1c0507120f240f09 66
    0x701d0074413105c01c0340103403000c1e0a00080c07011120f020160300380f040b806012000b099440b540011425204544041c00c9002035152a641024142e80d00c0d00340c109409a14030610150f82d50f011454528040715100f010040c040200805d03030418442c3e02025002012043c5106060340d038840c006500c0160014003030f00c002200141a440c03c1e40d0001490507001800580c1c0c0400801c1d00a41d11048410104e0005000c0c03034071018426045290b400036100007400c03103401d103c0700c03e2440b801084442e03203072689842014290340083e1607080017840c00c00301040e44140c0301c5c9420312010b401d50f50800d0104e410003a16a9070040440d012124480c0e6903905040c070a0012b81c071800c0c0864294417409d082d500359000c0c3e0b1610803c420b030142e800ca01c03440d2090000b03110300c0e038409110035124016401d00660184070885c1c00030142540c0d6006540c00f903668105850802d2020188000322034904100001c4540c0da2041100c0d42909010649088009402504403141c104170200c128144e05104200290303032100d074 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 321492877 1250 321491627 321491629
    0x30d3312080c03130311030709050c0405010509040b0d14070b040b0a0806040e0f1b06070c15030f05040b0702011803050a0c050a050d050405120d140f0702030106090b010f03020423 79
    0xc50f985204c0f00400016000d0712800e2520742d207041010100e10038072a030040065074040e81d0044601c2070030f00d828510304080c0b0303040c01514a54428409503a00a56520509000b956581d9801c64082d024034400c44035005580060fa141c02840d4000c51540c9400740b00400506103004100c400aa45a1a000c0c201c2d49905000c10b02420103260302d03482500403101c44100e03010740007901c1c81c0c0c1040c45102005078a4918000d004091207543c0001d080d00c0340181041c40580060b180041310102039240000700c600d81303407420360201c410035123080351017000520500c04948d0317090040c91421210540312007400e840580d0050701c58440c04101c00148810040c81000344442484518229900b1001350b64040400500043c00e9a00c40d0080394495507039981c2d0000009800940c103e1403e5040c1c80e2480914a0f00d028280981c0144100d040080010030010005840030301625000b088880710200e052445100054170305001b511030841014410b000c10056602c0c0307038100c3e40d21004080c854030079000c1c1c104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 321494127 1250 321492877 321492883
    0xb040b070213020c1c0306061106011502190c1404050618090708030c03040e100608042d0308010905060f130e030f0a090f050406180c02030d3312080c 66
    0x2241c203405900174028150382040344841803441c14800b1707a0b010041c1680301c8174143d41c510a01c02100199038084c60043c030400302041001050480b0034012180d40d2200c000302c0c94a0405120000c84400c150141c04114220031100c0c1c03108044000c0358140014508540825480e540000341c1204903011200440d840080c14030450000d4107144c0306903542d07068100c0750507590758802c0c40380f0980c4403030700700005140700101141c02099400ca95561040790701d031900d1b001070500c01c80c0d007c0d01481c8082c1300c2514a0b0135103001c907182010b1203900e03104042c0d0302d060140350460704c005142e14050300d01c0f05124400d580d500300e2181c481d1503900c1000141c001915044610b503011301c40040400d0180007400e58501c4d500040c00c0402c5070b044090310340040b0f86410510040e5a820701c1101c00d030f07040c0000401c00c40300b6140c200d544020083e20450f07040030750040c1148203592404146198800050f4a410340201840902c4101c011110101d140d42ca8500309a2a405114000018100040100d941000b0300b05c24 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 321495377 1250 321494127 321494137
    0x6060702150c03040f0e13020306041119060c060c0e0303120c09040e030403060b040212010509070c0c17070b19050f040b0d0b01032307110a05010507030203010f0b040b07021302 78
    0x702c0480c0d03226503c8060490005d44103000f0010075581040001d9110030f00003034421031581d03019018140c2c0303884694072064000c0d030b1110085d43c03015a0703040c130b81c0f00004c0255074100101310aa48120340700c2c2241c2065801c60b01c407030b0f603200204022108030f0a09910008102e40b070040c040b046050301969080800c0c0101d0281407403a5a0290508880b001c242c2d00c00009802034034020803040108605c02001c1200700e1184542410104942200400c41d6213000008a50f0182242c140585100b54664822400b0381071608000c00742807012426007040042005104003502c200108145007003002c0603429405282c2001040402c400050140300c100501e000360390080034006c4105071a0001115944041e0241710b828600013864458514409031140100508246040c662540319440745e030b204507050f00c807c01c81c9400c907111750010b480000b03109108151041505d81d8005840e941400340c2c1c80c041c018950301840c4101d200744014800540d0902c21550308680c1262401100701c0b44100542c06070183e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 321496627 1250 321495377 321495397
    0x30f0c05090c091f27080d02030910080106231e180d05071406070c030503030a051302090612010e060405150106080438091b06040305031204140715080a050606070215 73
    0x20310000f041f40720703070000003400e00184c080354681e42c01040c0b08070407100141c092007440002058012801000103400b013a502011440014040c9400401e50f06000ea035001401540c003161030000711144100b4ac032800c2464043c0c000c4031245113422103030b100c0a65994080c0920960005604520812655807504440100f5844010200f043d543c900313243da1643c00884070210314a08000024202820408100c0c000b81d900034103280706030700ca01003440040044c44001841c999610510103c0b0068201f112074410391140f001000007109680310640e0482c41a0f10200602410303070180310000d06130138003141c10070841c203522120300703940d200840c400c040600c00010300700e12440044c000c1e401c4002c03c441000541d0525030000d010345650500000e4844c510010b880b41e003041c05194406802d60212035082406821150103164034070002c10b04064065000a9400301852122680b154000618a81c00040501c0802c072a14100000c2800c5100e01e00009120f06414002509103200320410703a500320407 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 321497877 1250 321496627 321496633
    0x10f0c140c0904061a090618190204080601080c010203090315070c08071506150c15020702060a05070302010506010c032007090c0905011103030709030f0c05090c091f2708 75
    0x1010f003007190082501c0030740145d000395640f041625605144c0c0385180035601c042d012565800190760103002c250ba02621089030f00000c1000041c00c010240050006001000e016140c0c42d45003c040e1403801c0c000484141c11340d00140714409007940c001c03d0880312000c04401e1010545d45104049a50304c00c030f135000400381c0502040c1c05041c41400030000040030344006080296030b07100c1c09a0441c69082910b20000a101c5d01746000006020402004003510141d202509208040d0f002036a550003100f0b4442c00600c01061020500d9424001e480e080f08081c2401950b036942034070000c08220100b01c650520b00d803c0d00b00b00e9103032a001c00c40e0344010484a101001203c202e0365009064590b5485064001070000d040b8450800c0c000c03040340c0c024286c58840c1081c1d140741d42d4400c494071031600c109840074142100002529110029058422824a00803a5440c980d40c81003020b480f0003041b150420900350381040d50060f8207c0290642c0c0b9114080c0040305102e10f500030128003451382c1180480740 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 321499127 1250 321497877 321497881
    0x203040509070e030114190b01200a0c0906080a0807030c02030d0305420d08070b06040e06040b012616081c02030a1b02090414010b010f0c140c09 64
    0x79840f054000002000310001d2001c03404255a0306880c41c0c09550804900300000c40310340030802c0b80d50145107454010705104c100c1c040c00b11440c1d10030883e10540200d058208440311020049042c0480c0b0182860090400c03609040c6000e160307a84040460040403a100022214281405628040104daa006048034029403100300004d02506040e44c038501002d01421032141260040300040c51104101006200d01654170400c0311501c00e1803500301d82d00900c58001100c003141e035400042410902950b9483d00c5420f106003400211110007490300640d42003034051100155103500b10b2811034ae07521015880325114042590101501c1c2c0c5243c564a200b120b00f0384010351007003080d500498041c24251191810002014400e42613480301c2600107820400442cac024600882c2d8665403509241041aa0254036502182c01c402d029241905e0304140716008040d071303020074000c00032648020319104550301d00c0302c50040d043d40b0341c6c010018440600c89002484a04082242100c9590010302220300b40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 321500377 1250 321499127 321499141
    0x31802060318060a09030806040b180c03091902100305040606090207051507050a091e03120522080705011d04061206050601080606030610090f06030f0b0427030203040509 75
    0x200c00aa40c0c25040c2c0c0c0100c100103040d6003524800c0fa800540c06807100a0725035590b104000041c046101c6103a03000a000101c0b00000c9120008644100b44111426959050100020345459980c5e03c2c2486064030354200c8400584684084811b140401e0070701203442d0703c481ca0300001a108540010900d207101003050003c2c0000022081000002d0340d0b44101d264886c4203040726248035101c1158003040940344200102603801c000d00c00c414902500745007015840e6554a2030312051025401c00190300404c0c01c0b0342c0e45810120118035114000900c160a9140c442020740315800362040605018007083c00c0210144000d4002c100d81a00410400c1400d4440d240c0d64071718001002d003507809501d8440020b0003540500031a0780140c20007171180342503a0752007003000700c0006c49040d0b20041004455000503010311013a04040905155240450581e404013161000c032052034000c10710550411403003c0521894070a0b9400044204000c0358904180382001e0340b9510896000e035821109000810400c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 321501627 1250 321500377 321500401
    0x50a120912091d060a05060705030903010606080601120504030f030b010905100c1a011206020c0f2d0c0a1a0f04030b06040606030c0212250609050d0503010311010318020603 76
    0x2903807040440020f1003400c46084410342e000c1114a280c2198610320148603034501280035080c2c082c4690100c911340104c981c042800e40301c0a600941c04184000f05001d40c540e00601e0f083c2e000104148100203030320300f90324010944156151154145940c0b07900d203500c07607446019a90090900603000c0030040d801c200000344901c41c0304000381c0701100c10000d482030b414480c03032006048815000e042c2e114021541c0700e140095102400000d4507200e02d80940103403c1c010700050525602038003600c84c682c1c5080c5010500c0120090800110f5001480c0b10300155464200071002c4c1c0d24100d07000c041e01504504007072220b10a0022007e18103c000c9000410442a44481b41c403500d01a1014044155580429010340d1007210105015821007880c0012040304c40018000c1d0012810f455203008540443c4900300c0c00400d041964000d440e591142d06103d0204280070030a1403924000303246600d55202c5840d4800701300515030403d40c503420030303296401c0252800c00303005400030000c1c2c1d0703203080c20030b41050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 321502877 1250 321501627 321501629
    0x1802040204180b0102030a050f161b08010510081b19121a070e0f0f040c0203070c0f030203060f07091a1b1204290f0a02011b050a12091209 61
    0x2040d600f0500012800c0d48003100b910040e80031912940e04100a41071400403d40207401120180d0003403007541008500b801d0110b83c03060840241000c401804c00c9a49400c1d07540041207807940000c010410020301c02c00141494040c0c85840b00e0710511030418001070215032140c207058401030600070002c00d04409150b00300c121188510300840014404014140704520104c0c1c254000c98403600964019081c056500d0b001e0f50300042c100350213181580d0010341295a204c6548005038808141c200400c202002120090061508031500c003d20315400607a845000502800c0407000308008284064080c008075000750400c0406480b030b41002d042201a0340c2c00200c1c2040103000c00049920a015021450080c3ca4403014000c81c5000c0c03c1220000303007a8001c60251030001015208801a01141c1015003094100c4906551361280855402400d40e0490140300da4448400710302e00200980000407915250083d04000d00300e40d4401a25000414900c5800703080c54240d40c403c41d40f07459205034410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 321504127 1250 321502877 321502919
    0x121815050612330f1e010b030703020309010f0606020a03090b16080d0609051303120e070510020c03060708010326070303091a1602010f021905030405120c100507080f0a1802040204 79
    0x10240005da00c01c1080c0440038031942c0c540b10000c001040103140303c1d4004503070001c01040003245440c059208203040301c1d940d44c070200040c0c00405808041650110921005180c1141c0031810a140002e202681410844009242c010001039888000240750440c2d4012b0524100801451a11415a8098550b00d040840025000c03404003180300072584100c5221100b40d200400c001400d0000744a000c800030040c00041d40708078032165203165400c0160921400080da600c1e03459500d1443c1250012949110882c0c01411100c00240160384400982d04115003501e40480c0e10040c50234a03070b2142480c240b003803c01d0f541c00000c2003000e02d49501420320700101035000704103850b0f07001b4150301240240d4043d030481041006102c2e0440e8032a034041d40d003150040c1c040e01c000e65500002100c10b075000c00020b2501e40c105425000d0b075180203114081c0e0100032400c200400d403400000d5035098000003014032445550340e083c507844203101c24103804040c90340034204554803500c4580b40580e00105540c10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 321505377 1250 321504127 321504151
    0x60801020405040b030303280e1c030605010804080a0507020609060304030e03061003020f12030c0706030e0d0f0c06051512030301080105010b120106121815050612330f 74
    0x15801504000041b40d00c200311240d0398166810782c030b100802d00c121051100c009000d0705c2700800700449009018111018061a84000c50001143d00c05029148541d2009048c4204682084086402002200c00c001150714040380d03070303005900c00038199000d5469030f190802e2010007007100b05908040f9051801e0f008500715000307aa1503609000514506010003500b2261418801c0f8841c00d061a0200c0090803990550303040065500786c00786440d40c250b02c08130020f6243e0072080c00031a41400b6039818080c0d9441c6c41c101140991501401119030140010041980c4200250307800d90b40c0148042c0b5400c00805900b00300403918102c82e038076003080c00340d840b0715468580009041c24121048610044010a0000030750b0300e48001622007558021011140c3c503162100d502422030900031110303110f031040b0311030582c0f02e4107190008100c07940200481c0c0a0441450030241a160005103e007d0700040720503969144040c00304000c100d514018060218540e5400340304510303000f2007000d48601914049 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 321506627 1250 321505377 321505391
    0x40f02040b04060b3004050a150c05030c0c0f070f03140304031e03020111030f04140607050427140702060f041e0f050a050606030d210506011206080102040504 70
    0x2084103c806a11503201180d0040010b1028500e03c0b04110310511041001e0451441040200d2503070084126000c54182d0040142081040304201c0c2606140c60344190400c180c042d6110007900922000d080504000700101d402003100310100000400184400240c3d002c8655400003041c00c4100e1b40401c03919070801102d0141e110400100f9903040700d82081038600c50340030150194a14003403800003a4115500d50f014003841003600310066004c0d91100030141c50034a0581007900100c01813101c40c6c46503410007014406c7c200d5219007924140c40c01c0101000f50b01001d40c2048003140200032103c4605420f188000c280ea920207603105100c2d031226002c0e5007555a5103045021604400c41e0010541c401e070401460001290381c5c600c0c1e00c5644145118440c00d41c1c544c0340c0d10300d441e612003000c407541d03072086041100354101408583c0818001d0b0814450608649000d403030300100350301010290660340c2000550b66032141200071440b8031035107420072030151940351075800b070741c0a4081c0d00d01850030469 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 321507877 1250 321506627 321506629
    0xc0e0607050705010c020303040f08100c020c01080601141b010603060e03070b04080a0302040b030f01051c020a0e28060f0509091506190f051305041208061305040f02040b 75
    0x4035008598024007500c082030410005640070003800b0026a05440140000320f00e0300241c0c100035000d40b1155004044118204c03a00105842c14000c1150442d00700c2154080540d0b081030704160003603000d0800d00305140d1030f07980c0c6a0803401460050034001c02113404c1380d40140d03c107521404c02d40f400381d2801d00c51035100c1e040d091360300c0c4901d030790050000203030a00180100e401c0c980507090f180d5042c50013500c0c1540c1d4de1310390f5040d600203461b400e040c0c030382c1c40004016030700d0401d050504007203140c0e000081e203455680001d0840040b40c41095107005440f40000e5030301c954100d400c100305545480401c48a4492a200c0d00140b005009420315403c000340c000c20f007864138020881c0f01d80c60600041814011220355201c1c00030000d410f1780d4114400da40381075601184c00500704090945140b8100f0000e18190800a0404031940b01000062511080c00b020a003d050751804802c84e508104d0115121175000c80d414079604c0640c880d4161a2806000c10016083c0c00002d880d03008950500407004024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 321509127 1250 321507877 321507889
    0x607020105010b160503040b0f090406050301110d02070204060e090a050105010608161805061b0118030e010f0e030a060608010509070f2102090703051902031005060d0207060f0c0e 79
    0xc040e080326000c00b071203c1c2041d5032548096600da54805e8050301e0070300b42d48001154030f80e04040c01004045401044000741030601c1d03c10a4010001100248050f83d01d04d111442d1900c82d09280d600e2403030300058444150b4070345030094001401c4410000185240c188045520345e644464220386039424800005500d5108400041c0909500c0c110303100c1c442115541565403461131140c0419022030114000380781e60310900985040320078070ba802c54045445007900c41c00c5a815008406882c442e42c0310b0300f0082079204040542600080c00c0c41035800c64400d406440040550903020303454417481040710200516074102c03c0482d08154024030031515090521610707121203010f403e01c188a03a41c402c100000d49000354a150f104594201d03200340d240f64000c520305000c11070f203403004240c483e003c1c0040c16041910354114400c14460441c2142020300800c2004c40d681d21035544a000f020071020036090a0794112040b91b44d10240400801e901c5c40c5000c0c01a211021541000c02d54030103140c80e06080072 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 321510377 1250 321509127 321509129
    0x20d1d0c1c02030607121d01020a110601030c03020d14030307020703170c0607080a270201090605040803070201051c1401030c06050a0207230303043002010c060b24040503060702010501 81
    0x40207418290384030314049540d001030b0088000403546516100d04487c011600c008071121203c2c001584c1da407030503217005e0302682e1403e40b41c40c0150300c6100100b01140c400702101040e2075045921850300413a41c00c0c5a00202000c08511480e0301000041c42070f515000a07102c0c048901c20722070f849130303800040e45261a038029403405021503080240010003091050b40c003a40c1c01015102d000405580c1d480a0800401508c1e030040c1e0320058100707042003590f0300007a6010003405186400c074a480d08040b6180d40301d0040070b40081c14490042450340300e484a508071450b00e040602c0003040600c1c049044042e01110a200603070707004614450100d1100d2099089a0700f84c5400d0300240701d203501c7e0101074966992410f40c18800c41984070204007060b074044c0020001000104c050710111203049030840609608503820a07248017042d40c4110060740c000300400c96040c0c000d4400913092610b10f0106a85d880d8421410241c0b00e00201c610000703020070409070007929001e0302164450760700c3c41400d908a13802 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 321511627 1250 321510377 321510379
    0x50c03060d0201030b12070b0d05060909030a030e03090913060b01110d0e06070c061107150e1012050109091104140c0706060306020a0c110907050d020d1d0c1c02 71
    0x1c1c4203889000b55000360840c107403040700a03010002e9501c5c0b0502150601080b90842c02d40b40200007195658940b041c09016004082110203c182e81405801642d0760f20411120707500741a180e022030291040300f4415103a8502d009030030005c151529004414540c01c0c041021500e00b8a820541c0a00d13505c54070000c50400700c00300013804000c41d2403105441c500c10b0303001820b502010030040000022440b40503036000300303902d841308108070344004950703820701400e6005960340ea0080781e0f07900da0007613108003000300d004801d8030840380c0750000200c1180d0403180d04021010141c04d100000620400c550300802400e4080c0c3c20440c407009103c001c000070781d144058240d4801501c1070208041c40c4140c0000c003002846500006030701035803a9641c03400c0e0b80060a9610204507010401028484c500d202403c95042c100c5102000b0301c1c1008000d8510302440d000d0401142c0c0c0481c0303150200b0000d510003d05030031079410340d44d10328140c82502951506101032641c0118001034038030590300022a040380f00168 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 321512877 1250 321511627 321511639
    0xa1413021e06091017090c0a030b06010522050109060905061b03071a01050109150906200a060c0908061902090126010e0c0c190219090e01050c0306 65
    0x1001d5620305040505018680c1c800800c01c5903400a6540c1c0c00509203203c15500e903503056501d80c4140c00c0200c032008000d0aa9504814a06112a504e80c882102643d91002a50a07142c07142c10041b50f50f80102c42c00d0301e049956200c0c034020704208244100086405c00d0340c440560701e85401c411102d041040c0f240580000d001c3c40322450491490311002d0130a010072044074200242501c40f500d02c0e103100c02c8813a20494540c4014405540d0003800c1601403c40c4800107400003e403460000c04c08041441230204100c84ea80303000300c40c501c03101c0000c00c804240c141148c064010f04d00702000180f130381c00c064502040c6072440009040704c0201d0f41c180300c0c110b0300896860704080d00030340c000a5070269150504000e0301d0807503884502409207204800044015805000d0b40c14101003205c1400c0140030429071720414030070407181c408000740b160002c000701411840a40034510108850480f20850790172000090500030510f2f01007540010704200c483d00c0240255101c2441070982884191900c6030064 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 321514127 1250 321512877 321512899
    0xa0b120a08031f0b031e0f060f030708011a040c0c050601271d161406070503070503040b0310090204050f22021908060a1212020c0301050a141302 64
    0x140030305014580c030854924840008042c0080381c042141c10f550850a403409010040c003408400c8504a1505880c40518003000c0c0c0c18104600e5100c0000249840d12500c0e1910100d05191024400d19000b08103040090020355079011b01d48849540707800782140240c0c940704803000418424058240950703006000b601040c0d08080e0710402c0b02c8a06020b0346c40a010900d03017005114458400c824010f01d1081909280c400300c001e1079802c161a8110011a00d500303e031040c855050101c00030075041c00126642c2c2c0d515030151401034158020242c0280c0903000200d00080c0d829446402180324001031145240c0c2c1c40e85600f003500c224081d40c09143c0c1c200710280340d0b650450a061201f40483c241e409540300d1555550b00603401683c0c01400349140002034840b0098482d50065105500400100e4004030190b0500c0c0d1101c044003403010004c0e041c6801f03100b801111500900440071186805402031125141003c00c000103404444550020354084c2400540ac2d04043e0310413900d038070f5000f4010002d0b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 321515377 1250 321514127 321514133
    0x705030a02072003010506040b060405010e0316120c0906080c0904031205010303021e01060e04171204030c0b0a1503080a05040e10030212071a03040606120302060a0b120a 75
    0x5500010300515009500304000c0010480a20140040031400c249003480400c9440a00d802d41e02d000c0c249600035420800c0280c0d09503140380586080d83e0b820310700301c2034081e1a0400285001d000c01a581da800100400105802d0360018601f0700e0303a8021106515190b580c0e40640c0212500e601c50030b41c160b0040060b10001d1300d09004c1c0d007904140640344c600c2c03206002a031284200c1d0820307803045000d40d0264450704034950010140b00e0915240c400200602392414800c1c02c041c20008100602e0012440044180d102c1148140c41d094803040548139190724003442c01034010566484262100941030b030006100f84000d01807100c0820076100b1103000203245a45690712500007800d40130500006000100d80303601c041081c2c921070760f0f54035000d10a90340395005100c42100c5141c929070054121000030b002055000401c0c50495400070381c0195030741d5032402c25000401c8035030000419046420045414194005455409010321003070401c049100e030f208128003019400443d1040d07401144541000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 321516627 1250 321515377 321515387
    0xc0c0a060b0121050f0907030f150608060903071b03050d08072a0c0605040f0b09031203160e030f0a08071704030c0e0702120414130c03021b0d0807 65
    0x140c010704200010312624107042c141c3c0040100e034001d00c1c0c0c0e603072000c00ca03c0d080340245090300402d404016200e42400d5442e11074201090351809040700c0c40e40b20003a1070400156215900405840b000c2e5603050507c581501e840380d00c407020503a84070000900a286c0d8040b441100401c580d400ba0090004414001060703c516000600d1074041c000d266000c149c101c100c1515000d00c1440500a0840d0940b080ca803510040e1b2041c0c2250b400c001041c80144010ae642703100341001c1c0d9915a2036640c0f918203442c000b91400c5462101c924401324040240100080c904030350200d10301e0240c0782c1440302c2d2510010305540d01a88500b1402da5071000d031440c8041006d41000b008001d006101c07003d009448619210780d194065403084996403d41d01d02040260381440c0076a400462034070140c2818900b5041d80e82c0c440c045d601031103035501c402c4001c4034442c0d568000140001d486100e024464a840e001016000350410b940011002600c13610141042c02c1c0400d10081d01ea5050701c544206488907402221 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 321517877 1250 321516627 321516641
    0x9010e0d060c020c15040b0306130e071d0a0e0c122d06100f140d02101e0c05060c031e040f060605040218060a0504050d0506010e0c0c0a06 61
    0x80c202126800c014003148481c09110701c4189250024412002c011050114040c001c032004c24211005120602c08901c20000301e80e0001401c03115202c47c0c2c0312100e16000107200241040c03205d0b220710780c1d0005900c10015a804481d00300150303040019079a11941d04c040c3c60007800324401c00d80214004a41e207141507a0400210031610003245c80440c0094000a407c204208548800b40d60030305e580020448100a00740c3e20508181d451030803a485c00070446c047ca0914016080e20038103107a14a45281c60720041d280c0c0140c1c0040c902825440c07080000782048440701d1180d00340c0140c0b4403000030301074015007154500e907074400c0080c00259038407d2080366030b80010b40700004220301c882270001b10352103840e0304500070b5024203e1011a001c00d440d02c0001c6030095840980600e00601403441c40a03420f602c8051440000c0d00c1041e624513150104071003d100307a80201d42d11880074128030040c00320000301c0c5416900b40c80f543c0ca0b180c4d101c2c1540c0140768020349140203078641c00903250310006542c03500000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 321519127 1250 321517877 321517879
    0x20c121b0102030a2a08061c0605070e0102010e01290a050307091e1817040503010f06031403041206110412060516210b0a080d05070c050405010b09010e 67
    0x10503000c18000742664800c4d0f810901d00b03515000f4401800019071008040703500c501140754118242e00c84007030b100344c0e0004c0c04544545581503c1040c1d0414200d1448201984078008200b0317403500202c0a031045004004a81c0150b1030401d0502c980601403080d625400040003501000c207030814840d244103141800040d030020305010001440e03450405c00c0d1000340082035400300d200c05a00120b000031102c11200c1840c010b00341076440e0f00d00144207030b82450b4a50802109100400d9001041c2000d10560780200d8040d840d01d0400c0721045030b03990084090703030700c500500c6104030001c000c4a56640a1800340e0f0100100500407440001c8640c1d00909541700c9103146c0da800c0c00d075941d45614070822018415682c240e110350401456141129494041c1078042c2130120070341e803007081c1100707102c1e40543c030340e54030165118040701c401e5940e4419840205110303022101780040000c0014656000000111082c80c485280818285024010030341a074600c0845036041c4862000110b81c0859600009 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 321520377 1250 321519127 321519157
    0x60406080f06180309130f0e0f0f160501051c0b060d0e061e070c050106030206030405031207030204080d0e04151509050105030903040e070207080d0906080901020c12 73
    0x1502503003031088118010010028044a1038404a0740e5503800040c04041d480341c0003080481895922102d0019461b20310050001c3c54016a02e1000014030b00c00c2900c040e03510904001e01c054982c0004c14054400c03101c0c0c15200c440c0300c502e41d03c1d01810114000c20f0b02180050145803162080c0d021300e006840c10703e850200f4004c10650203c0c40e940d100c000070308c90036511081c01031104802040615003200c44910340b01003620628240706100d040c0644002c04000c281c00c42d0505104003504403030080c580040541c1e999003414a0550368a5102405443d0742c044e101d00040c0c0c1e614064420740b0212603202015040309008600101c0741d10b07850003421903010341d40345107240e21100400c1c0082c0c00b4080c02210192003d0202c3d03409805505540d12103030412000300104042c441011066804403560401c068803241c481490a0381030520f150803410103441119135120009a001801c601190b00c0c684440005880e04400c19090740304150082025611000210840d844400001c0404110b18421 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 321521627 1250 321520377 321520379
    0xf02070b0307080411010c030c06110c1002090a050a06080a02030c16060e19020a030f0f080a02060402040b090105060712050d090f050c120d120f02070311062409060406 74
    0x2040e1503600706a510000203030350001004100320740a42049100202420004a65107280e41c0050040e01d01c81070040c140c0d42c46a002003500b1240c4010748580128103004d5441d050291110030000f5048516864400c056200300003810342011000141620102e0352041d203035a44003180140070b9880a400b940712075004101282d1031403c04041c0c0c88100c1c0c81a071000c01e041040b0340d0303801c0c03402040300c0c0200d0512150070310210059503070076202d0b001c40c0da10408200383e159080c103200d84842d4810350068618070001680c6100c199000c03807030600c680e01c00c45003000072402250034804003080c02d008450b080702e0100300107000b060105241c40d001c25550f1400360700d0000d9805d040740580d40c80c400100e0b540f44400e2180c01c10801c09000c0004040400c1e5010320010310201c100560361a10180c41348240071020510800660b425042100c0900c0f41560940d52a01207280003001c4d040701030a10344e0a0300503403003c200412543c42c010b13070480f21415001c008401041007080443c0c14042c1110342c2c41640c4400c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 321522877 1250 321521627 321521639
    0x2030a05070c0f0b07021503070c0f050708030417161401050306030a0819110105060d020105130b040f03231e1c050301080d05130e0a0914060601030c03090c03030f0207 74
    0x9944084c0a20f07041440d140d5202e031050203444951964003040e02d000600c208044290301118090f20300c0c2d00300e03c5000500e48035003007090500e00240c00002450000050214240d800150707588142d0030810100d03050124a0a2404102d0615016a078143c1c6800465206198452170140d03400010040c1981c840302840d6a540d00564050402142440c1d0b8010746050219000001c02c0010a2000d00074030082c031b0507500283da0107003441002030510801042c032150181c5203072142c4024001000203550307503079241ea0140600c040d60344011268980c10840c2d448400c200300f41100c42441d14100100f0b022041810042c05144140d0460741691044444403440b400764800c41101c4207141d600e43c01d90325410016481d00f00075100c440d150500404003c049000025001d0102c11501c440183c1040c0f601e804003d030001d8800c20320007401405c9242003403098141c001c103800303005030401d0b00d080041c40822030f01501a640c050a01400700c0c60907010401c046402080c0205d0b8401003881560121070b2510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 321524127 1250 321522877 321522899
    0x160c082e2a0201060503060f0406021b0f07030c150905060c01140a1d0f0a12141206190305070302060d0209190e0703020408030a27091e0c02030a05070c 67
    0x910612041c40000c407840e24903020301c00c02c005070100b58050446440d20444840241a015000034039241c3d00040e004003079a03400c86145200404801a1012030301040c0c0c0c4180e540311603000c255039028918400040c242c0d80302d1602d003180c904da6200c0721a454688030821410340c10200c01105155240c1e2516516060b0344200244510503d03c00043d4003c2c2e0381c2c90310403040d403407803202c40c540c0d51040c078810041042c0007880c2800c82c1d61040c020b81540c040c40004860720540b84d90001c02d0580041046001c50f80b454014910034101a107010428800034040420400c0841c8406007180c0c05ca0320050015007000e100500500840705000b500e00702110000c2141601c00e010420041d100b0654103010854071a680507806c10b0140c80c081d410241007810550703c03440303030b10314030310a0010003c5264005109a1a00c1441c42d0002e400008040d941d020102c02400c3d802c0c1500d070b81c030b101e40c00e00d200815545120302545d40009a0056040c1a031400b07040c0c40710340c084042500e0301030710301c8000a5420060 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 321525377 1250 321524127 321524171
    0x81b031c030e060109060302010215061912030f02011b0305060a0509090601090b040b011b020a0504050a02040509010b0a050901051303021c15050f1b0c03160c082e 72
    0x281d40c000500b0880d01c6034031420001d06030020301210313007001010009030ba4001681500c1100f00303e800e080b10740f9108000307003905a054070a88a048040500090f0f02a800c1c4401d1010038007944a465000c51100300417400c032070f504003071124046c0440724800e0349148240d119070740c0554064501c0c2a141d4803080040c1e5541d0b800c0b90101200d910100042c00340c003038140246180100140d0f03061052a4810300060302c08407402420800040e06504010309540d5010350110040101038020032860414020050107580903008039800349041500006000d54014100c410384807460381c41c5030515100c800115020742c090101183c0561304c024000c00581d490b0712031400600c44c1c046600010740684e1a0040080314580c0540d444286003604000241d400f161506600852001d0f416a1155454901000c1c502500100b41c50314440072031101c440c0b00a068684000f180200d5200c0807842d9960341c225658071414a105039440d40100f000140000e001c214000d007012800d03800b180340c9407a400d00d00c860702c500b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 321526627 1250 321525377 321525433
    0x1802040b070c0f081f020a03140a0b040b0604051003020309030c0d02070e01061106070809010e010510240e0103020901090b0a030501140d050a0803091c0f02010510081b03 75
    0x880c82c100100d036030b00900c0c0c1c030040181c18042c1001c07440440c440303003240803844d40d1070b0314050300015070b508030758403030f50092100d801c3c40030003000b042c100380121b8001442c882c100c950041c2d151075040049868032405a030101e0350700420041c07200c0c00d5400704402941016120100d144030903c40100904000d0002c40c10011031070740140f0000346841040301103100706034000c60030b1100c03480175500c07a4030001c41d80316030202090501944603215800e10a004007034500e248032455107010b09221240601000304000c0f21500c06a4120001c07804100f240081661404400443c4250000c10544d500075009020391803030504041105585e00e00d4528419405000d02000007656500144003a98010034024100c20003510b40c000001095030b5859520496480b01070428403010000a0200c80d00b002140c1b090b0f1420f80030248500b50704400a0a0f6240d4402c17261301550038080040c0040c10359030702120440789014014015a008010b6682410707450071210f5815000380c402180c2d00041c005031403c1c403020 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 321527877 1250 321526627 321526643
    0x7060b1503100e01080309011823030f011116020303070204050f0604050903040501090605280804050c0904020a030b1003050d020c040e060c070803130f12081b041802040b07 76
    0xd8602954901103182d03401075401c061001c4014040c0389000825581030310420f0030403a02c2c0c001040f2964842da651640414040c1c0b20b08000d03c0710705d41c0c121000018480e0160112217031420710303002031426074101c0004520300366000c2c054401d000c092004606860340c009403e4078035001454011078140d480c00c40e49850101000018414181094415261f0050081002d542410b083c00002401c900316481840300304000490203450114000c1c092034006410010080508003204601030103982c82110180c030345008100c401c08582c01c0003032030184201c0e401409002c107035080d0765070301a034032102411a006400720100044000b610070000f14900340782c2a0014044421454208015241d03600004010350700540c0a006440800074241d030451503110110540f2990351914520f50000e03885806844900c41036918003c0c840b01740140d00031700d401035440907003941d19042e0007082c14004100c0200b480400304410013440d100d5000210007050050009482d1990302c6040d51318640120360282c40020b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 321529127 1250 321527877 321527881
    0x40201020c09060303220909030c02011209020a180f0e0c030d1107050d02120307080426070608060604120b010524030112020a15110f010b1507060b1503 67
    0x140c0c0410858251660403181c0d00510f28048010035100e000342d60a003602d0300103003840390611000e07140c4010094001c41904001038045810004c2c05600680400d0b0b010986e0406410440c1d1814010f19200ca03801501515440386803a80c082c0720301c092041e140106c00c2c2ea8451100098038540280004007181e000204010090842010305280806490805101a4200300313180260041121030454504840300428000381d40041003420105603440c1c241342c0800503080d42000701403405481070304c40ba4050750070500003d03502c3d01e003003080420344080700380d0000b0320802c0b00502c14490036520200180c045ca062540c0c0702000c4000c10802c1c0300442c2c00181d03c070f0052005003450643e855a00c0740c0704802c0b0344286280319089000c0d20040c05040105400902d922095446404410009000b125900030480c114604020509911109a030350705005410782d00000180501805d048014010400c102420701082c20070096485100201c60f2103444110030751095840e55664000e21048601190b03a034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 321530377 1250 321529127 321529129
    0xa0c0b1e0a0e270604020a0801030b04030207051f081b03060409020111010c05180604230a150201050907060809190219120620030103060504170c0d0201061d0c130317030402 76
    0x2243d402004c3c14003d40c0306118820307082e640682e541741125000901d440007a00c460904905140043c1c020075080704d0195100f00703940c83d40d01d91103580c4a903203984460268131070100607514a040441030b9140200180045400f91405500120100344141082a0b8850038400d1827401e5a542110441c0480c801142c0c17461000701c1083c4d01c1290300d104648040c0360504184400e1038003d035100721550481742c03001d2844196220544294007804251000302441214104028042c01007180c4c00c080038044e0140025802d40600d04060144032200007410514482c0b000b003a1103002e14002c1a6030003500c4d00001c0a80310070317450744080178182c0040c0e10501d00324142040c5023640c0942140d480e840307600420307010015501c08203890560b0390100c4082a9a01c407030034102d940d030040040034048101d0014800303c06000020b0b404051000036002031042e1a91004403101004041c074045245d64418000508098007080051400f140c10440e00c400e03182d2079407158070102902d407542c03442d040030000c248015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 321531627 1250 321530377 321530449
    0x1403010609020306030601031217240102010507050d0c02151303110c06090103091104060e18010605030a02010c020a0b0a081b190f0207030f050a0c0b1e0a0e 69
    0x5801030386002d41c0f444c2095000300e5a03400e414031015029402e50130b411500c00f0301c204408000391807071501050300e6052080c4102100c1c42411810b5414100c01c400c401a154010b0003128803c15a40d00d841c1c5c20800100746050180ca00440c0c2d060440c00307102092581b402401350214041d40e106020081c2d1203000c2e10300038103408900c0c0c1280c84942d001055840b03059175550101c1d04101d50a10703000c00d000c00301e4502400020303040002107a0150070308801161440d203c03095144161250070380d2442c0319030601410307400c0390454042e554042c1c00400d40400954000c100008002e44003600f5491042c0c0e65201021803904482452800643d0301401e012018000140302407060a0804006140001c01d44d0b4000d44880001c40300010300c039105400010640c0207104a500031a040080c0078103101d07071458225103420002000b00d400c50900b0344c000c15880703000f0007503421128842070b00c145802c40700000c4030165000100050708001e1070110a4000d80c90761151000c0c0010505040c1c1e0810310907260140e0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 321532877 1250 321531627 321531629
    0x60503010b0a030c06031a100e01030c0c170708130801090204060b040605120a1806020c0f0c060d02070528050606090c0702040207050a0204090b090d0207030f080309010e0714030106 80
    0x12207034200c00003c0c00421800d004c51011a002800c0000b10710002c00c1a8080b80310240301d030141d0100d000c01d909040640c02c800c5845182c64242e03010448080c13150404e580c51070035604041c00150f034040d840c2454800a8000701101e5009180450522005496a0b0b02e0b504890700605220b9440b0845182142400c0c0180e90291080001842c105030030040020054001e5114a020400c8803201080d410080307070f40a800d40d100200d60701e10b401c0882e8101100030354403401840d0481d106400701c408840b000130034036108000d00202813520302071400b101a000303500b00c03034000c3d06c1501035403104a089400c42807850215014040c1c0001824030b66050860a0100060519001d110f420301000040941d40707045800c150350450b40117881d617500b81001c0d403805199513030003900300d4a046680024000d00300d807103500c01c7c0700000840c0c2030307240da882c0100e8645946210051006156004d5200015030380d4029561111b0088000a40200302d240124034204a55000c08882d0303880380e41d006500d0400780100c0c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 321534127 1250 321532877 321532879
    0x191d10020f0601060c2409080408010c1202030601090b0706060509070c0203010c0e0906131503230a0503091e1504090c08040c1203021203010b0a081608010603050606040810060503010b 81
    0x1505c008440c0c2c46480000302c00070310559880c2c92002d803910b00320700c242e841001c00d5030300181c4d6280c685031200317121402042c4481c185008034401c0311464102605a0085a110303ea042e903403000000e141c88000d004540005908807940c5880d100c02240710b440c0d54010070305c02c094507581d075407a04000340141421201000710040400408130800901500d4070301c0d00359003000c8103071066500000c0000c0040014194050088503202c0c0c2001c000007445050252104070002420348480540c9100032032035a61030800c800209580c10500a0011038039091800e0142483e40a159160112a203000282210111004c0c0004c0f40d101041c14881e00c1e00c1403196640510140c00e040c886402c0a82f905070340201244213252103c015024142d040500c00e000c004449084c01000d40c0d280d5840b21507410f440d40106609400051140000034101e000001c40240404031a841e688500d0f42800011800740c80b00030415034101c403082000149002c020002000100400000081c42d142040201800d40d10421000c0d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 321535377 1250 321534127 321534137
    0x405040213020703050d0c030b010e011b051504020a06020a110607420605060d020a031407050909070c0f020d0c051e04110405010909020a020a06061811191d10020f060106 75
    0x48007540d8100c8020340c4144bc1c2404d1050f01e2040c02000d0110325500750400074168016800b919451084064040d030042d0310889261905640390101244d42e030110203005444d520004204950500f03041c3c005001c041c0c0240e2240c1100d001c450816503ca1801010a0b0b000f694003a042200e6500600100220004505000d10446240c03c00050450040100003071840341e000892a00c2c850195000106401100709549041e1030a440003401c140c000d070b490603005818400c002403c0c54031640008600d40c0d032000d60540300010580900183c002502821038994103c000042441c0d5501c2000365900029000e003421300d40d400c4810b0000b074071281200c1c0c84c80200d00740402d00c0fa580e0000d00440c181d5040000c0140c0310030704900100e281034804c8a010306243d00d05603002c58481034040040d140c4a01120b400e0002c90303480842c410003442004400014121042c015030b03507092180c0c083c1020081005071112a2800100024441e0b5020500780005644541c1110034082c0d41408010b0041c0224240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 321536627 1250 321535377 321535391
    0xb071d01050406080604150e0f0108033108010f020d0f060b12040c350a030906211401030b010e04030804030809100c1101150506090405040213020703050d0c03 70
    0x81c0c01409240103800c2880100f200140303640e00e60750310880b07001d0303482c41010003007507a902044061f00070166101c000219000e800420b22807400030440d0041d140013400a0b1a050034120303c00348031030180c00740480035241050000307498502405588480502c1590059540001c0d03001c0f24100d611407140d6103640b5080500401c085280823003500d040742c0480c400340030f140d1390740e141144070040590483d134038401d001081d021500e0000fa44c000a00007c148518160520403040c0a60700d0ba03c0d0100100043c07040101030000621407c03900212860391030b01711903452001d4081c0019160358800074118103c0c00340c010070900003c807811500400c2c19075046181c80c1081e46008006800043c80a408e00c20020049078017030301c00304103440060358030800411014802d06401410b0302011000601c4a6007801c0060001e1040c2400c1c074000c540004041c00e107012030903000c1c0f00140a00410a99200c2c80607410b4508141090000f480f18500c2540c0d51b50307444100d1841c0004594a01000404051400c11 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 321537877 1250 321536627 321536629
    0xb0a02010605180112050f0a0f0303140f0417040905010803071110080c090105041e0602010c050a020622021507020901090608030a0e031002070302010501030c1d07140d02070b071d 79
    0x100d03c5040d81c001d00d0076000302e0512814450714026802201c0d006130f1007801080c100344040345c0003413115140320f43c1d41403002e410b80c0410182200d8041c0d0b4941c85121800c4003050000c0c0001c00c110b0540d41c2e9407d040c40c1001d54032100041164003d91001803a038200280302c1c2d080051460354010400412544092011281c001c0102000c40c0100094400c601c00600b003003203070b8000e4055600400b60901d2200d080c10380b01840040200d00d6100c1d0b07a002d5801c0c5a11044801d0041050b50b000190320360040444d555416488000e500302084a80704400220b580580941c8900d62108403003806500d080ea610810b91041c800315100581c880042c942c5800414080c5401c00310440d10b071203405241451900f54864006424502044203c424807840060304c4010981c0642280b41203d025040241da055540c654000c44200b0850240b8007010003a00091031840c05040c503085005c0480e80b25a050282650450049078840c4009a8084c120713481042102a4007040030990040e040c0ea025500700103080c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 321539127 1250 321537877 321537919
    0x10615080a0c1119080403020402031519061b020a0b0a170907031a150a091505030d23070c0314060a0903050d020715060e070f081303050a0210060b0a02010605 70
    0x200e140703407103138141202c1501444058001d40f0040e40d001441113590703044c92214100d046c00342e061420700490f00c0d13600300f000620007241030f4001c40f5501e495101c0001c43d42664001d59010b002c0049030320040d801030214091f50b814000c0e04400b80507032985a0b1554940c0015059080000d00c040e5990b40030032014000581030825504942d019486d4200054a1380820007c1408a0320066900420118400030700300826800c44041c103070000c4641e0070403e48a01c03d00d5251212164098042040f4115000920500c2c51000d070111000552240c1412107541d241d0856601d160b00945010115007500302c2402014840d443d0044610b03071080040c1d080958014010307008a50200720899030101d100340c01d000c68103440303038800d440b54503082101c48d49522404504030f0741030320104006100700340c80c844c010740100c10803401507102e040c0300481203c0c42c1d03404a0f0789500c2025000d045000303000300042c08000740e014480181003198140c68640d11034000083c02c40d41140c0c02284151280c241c0d841e1442d142c0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 321540377 1250 321539127 321539143
    0x6040c0501050f0904090606140d0206160309080a0b04030f0f080106030c0c060906020307140c0c1507080c0d0e040911040509030705060403050a120b1c05010615080a0c11 75
    0x20300b402a2240004046011140905280d40780c00909007002403040181c00d0f032012003925210501e40b64100c40b4613042c0071701180e5180009400c484c0800030046004280107034241000c3c42842c00c15036860301c40031050b092000c866411100200d4030014082010340000610a001c02d040c40e080d0f14400c0d141200500113a4184030722401c0c140e070784d2a600d010320301c210516480590030100c2803100240b6494464000c4d8000c807000030006c1c00703100c0300941c400108021208503c1c1148028980c14090104020780406141440d940c044800c220000001d810070300070700341d107482001c00b803d500e460400f0041c03c0b6001c0d03141c6192089240040c801e001415154040e6101c0406541c0041e507641c685410500e54802c040c1c020342688904000c00c0708040d444001056510309903a500440c0c4161003c400c8151958411000d52044080b0b1718440000c00000c00c00c1c03c1e040c012000411542da41d0b242201210866450348000202d4039800c00410081c0760140b1034000915291001000d203080c124031744c9803210 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 321541627 1250 321540377 321540379
    0x1118040f0b2809020c030a12150602030d0506030105010807140d0f1209090506100e0f04090c06021b10050a1403010602010c0e300709020a03020403050f0a030504091d01230906040c05 80
    0x8000c2d0708500d0344900754003a003001d540d14003270000c82c6900d898010396260802d2021100c403a040000003041c5081c10b02609040310b11600081600504282c10203203072104003044d040e04500307500001c801081c04031403504c0046004103492104001a11001001c3c442c103500f08100703090921040c8038142d1603481d48104003880500c1c001340580107070702c0051007508001c49601c2d402400c00741441c051002d00021300080300c1e02e5400300d5100d80b1094141000f11181c2c00b0009511200d1043c0c1d009040d40100300600c1c0000c018a411940980814450b40494101b84c01000050307540d503a8004680303400240c40c00c8030880441710001116407480411010a15401001c00071000050088054500c10001040940b2004106540303030900d03250001d0094000340310599a40c03142159450304004e0115140540b0b030340586e00c092800c1e0034000420b0150503003401d0313080300090000d01000080000c0c8170b000e24801040340d140c50020304c1a03001900e101c0c8080c1281001d03030414805c0c03000044c80700c1450300072280 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 321542877 1250 321541627 321541637
    0x11010f1a181510050706020c0114010e010b03070f02100608011e020313110d060c030504030807170c0912010906050114150306040c0509041e1118040f0b2809020c030a 73
    0x810007030216000c1c01000c0004040354000300302c041824106401c100100c5445a2000700742c1c0c2ccc0e90b031110041d0980c0038850020018010408a007005214a41c03000c802c41c0a070049a0f80b81e1001c803040c60407100d07198020755090759181328120030800c80142c1c2840245116100f0360840c200f20307294075030050080c0d0340240b107a2542107a940498851f90740d1520b21036040036007000a10702003140035000d88012a412000a03c5080c001440b07a8000c2c0a02d80d5034110500641c02969030344424440550b03c68400241d02401c040d14004c2c10324024020b42c20601e00c034030800b00351035141140c0c58800a0120808511807550a80c1c602504a900810381380d100b0720480f400f20b04908015002d4400784a00303015260000d0034100e4a41a030102074403042a2014244000c00604842020407001401a01100c0354030070781040e00c2d000d6a1500f50801c0d1005400d45000045992001d00003400c2540141c8034080450501100300181d141c205a005004040882040d481c0c900760b1500c45442e4030400354a41c003484 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 321544127 1250 321542877 321542899
    0xb010603090312090201090f0e092b03050903090d030504231c0f020a26010527030d150303120207020105030403080a0b090705090a050a03080403020111010f1a1815 72
    0x280c440e5803810010405002d103c1400b13902d4110744030109c0b8044402e03102c1446500381444190807818103e09006858120858818040c007408a010b0000034dc59110148028021514280d69540c0384115841c8681c48055030b41c1e1611343c13109000c1004600038403200d040380030b0610301074075040303c814194007140c01c0c1090b1001135032600030844100c54034040e400c0400c149012900c070048001c00040d4002d800c0d0710480031006001d10314203030380e0f00300c801d04003111141c0d00040f02c0500641c280100302c035030b40c01a2400e1a0000c2009011241c0c41c8251010481300006e01b002450b401481c1c05020308003d40040d460f0280e15000031300b41d0711004d0002070421041d24000341d08040e07158404010707510020321880850404c010300070f002c3d400c43d1041034450012030300002050b180c0040c403003048a0340102624206031864005548c44840420b00f015035540780c000c0302c510b480e524840c0014164403000740c000c10761380b05010320480003109130a50003054000f40901c81c5000c040402e0349082e550440e8401922 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 321545377 1250 321544127 321544129
    0x30608030717030910020d050a1401230d0515070f08250203070b0a0204050f1818030c120d0606360b1204140d14031e040605040b0106030903120902 65
    0x7244021700d40000301e2000c00c040c0004c035400d40005003c3c4e01039407810700c08a0300640c202507038018281b240a0410315041060840c040310346801400c00800182040d80f07110143d01c03601c0c207004400440303105020000c010401a1508002a600e4100c0e55140900d503510b03200c0c00321072240c030585145030a251b84600c010528a482002224540d5510001d1a00700e420151980340c042e4102d80603440c440d9084100450060911807a0400f00481c00e104001807911602c1c5030300c503060801240d02000e0b02080000503800c0b8401c225034031740749810381d1044d9550f0403282c0902c0c04451254010108100340321280c1c42c250280070703c0c441c104600d07203c0c1880c0400789603449220144216030010400b0f18011034485200000070007910302c1a406161000f8004c201b44c01031540b58030748061210003107503602e901450b0894041014590000081c103800c030b0a94000e07a01c01402060440c1c0450350b04d500c450400080094074070074140100000c0c101848402c826940180103901110b1500c20440d039510065815 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 321546627 1250 321545377 321545383
    0x114070c0509190e07150c0c0e06010302070f030e03011404020d02090711070b0318070302180a1103010909030306050f0112090c05060a0519180b07030c061b0306080307170309 77
    0xc00f12101e0010090a180c0c495000d4031001d9034450802503810045014215900940c1c58410041e40003821058407401c00910790004031000d4042c6040660030320120380080d00c86504505043e01a07241c0c0c400a440050405007074442100b524003009080ca4180401078440d074214110b42c950446180b4000c0c3e0310381e013049074000c07041c04151b01341c0d12890400040018661004500903201c1c50307020724141210030702040e550740b07161000075002034040a60030040405002e1081d0441e505d400d010030050000150103400381c000382c1081e1a0156540c005a04250b0503200f40c2c00148800c1e034480012510080000e0403a030902e04e489555140c84610907420402400d614401611008000c13586900320305800401075009139000304040700000c0c1c0c1e07407804c0d0380c040c04e002c041d22034086103c1c000e100c0c101010408143c014070811800d00804542d21700c00100c55005058034a0210182c641012a1140e00101520202c0d4441c201e55001048503101042c020b0040010003501c9010155072921030100c202d02d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 321547877 1250 321546627 321546661
    0x90a090b010f03020a08030703050912030f0a050901030e0c01090621090506060915093408060330030414240f090c090901020f0705010b0114070c0509 66
    0x440000014004142d040d0a800b811042e64002d40325644056100c1c4205035407031081d2040a00896800d01c416a000c0c0b0380108540400c4900308107480c2060000c4144580d507800032000c00001c10004900c566071035070705218042441d2048001421942c0340b82001070300005d0b641c01841c0c1005200e85e240c107207410142da031189101b1542d42c0100022001030400300d440340c3c0280e50262207004c44401158102e000c50080d040b074004020144255515140000c085107111a03080200c100b41103c031524001d054541020131000b49611202451700d04101058281442d16440c0c000d001006400204402002c0b64003900340582004172958a0305c450500c08074074079407140300d101544244a54208500101005c401c0b0b0100c0d0000b613659152280340d08000c1c0c41008454990352030748011130000e11460201030036500a005031000603d2300e41d91107114511540703c48410b441c6a91620711550055a10140d4100000c1a10288905110040d520305024003441d00c2580d21800143d00462404c20640090f01 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 321549127 1250 321547877 321547883
    0x50703060803040b0a0f09210c0b0c0c04060f0e0103080903070806070c0303050112020612040c08030c010e060901050f010e09010b060714010516170a0608070303080a110f0405090a09 80
    0x60b80f40c56848008540c1580200c070044001082002030303c00700c42c0aa0480001ea03509032007180c640e421001c90b0401d402503140d000341c621405250780052183c0040008000381e05d4410054400c0c100d5110512080e11050b600000e40f02150031400c0250560303044145064030b901925480d03449008c00d000a18104664000102c54041c3ca024402072540241c048640036109890901c260b03a41c0d4101004070000c45030001c0d4001c039041050300101c40f8030981890344180704050004420b6103030b580003441c40c0c21030701420415070354480800c1c41585040008540c8884030100a000e14605801c4005030500180301e0b01c2c0c1242482008901804d0003074000031040540944080d071514440d0a280720a5100a0741c00c04c00f40d440c20b0081441003050b0804040c42c1591a01c5651510360f4103c01840b5221008010490340f554400e00414a400309100160041d8002e54604813a400c0900b8401d003200c03884803c91056a1040000c603030403501e40c4007910b00320342c800c85000c0901e50f6401c0d88100030b040001c9000b = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 321550377 1250 321549127 321549133
    0x91603180b1003110d022b0507151701060906050708041d0103060f0c050a0e0a0512010c080705070c0e0603100501032409050c0d0201050c01020f0a0e0618040507030608 74
    0x102100c12a24510704490041e400700c0381044c03261091040c0c610b44544e0181d084a201548217540000c0c03038460260001000c1880e602c0726500e03071261401d200e5203410014542e000c003100e0b400703100e03800b00c1007059031652083c0c0082154985030002e40010107a00c2507400780000414a98240300c5c0c0304080d940206046844050510510500c8048a003000d02007241c050b0b103001e000182c1952284221150691a03460f0b0519100d010342d0192000b0b00505941da40c8080c8000010480f078503040e008201d2461841c0001c00d1000900b903000e010301c01c004100004101c2c0600a07000400c015040d17110440707005240b60b45240d240c21001c41d0501301c00300244500c0ba03007400000410401404901071043c001c200c80304404c01188032940060314109000a40582d1022010700641d03d050545e0300b02c0329105042840c6007500814000b0b080e40c1289140c03540c442000b00794242c2c5a40c000c0d803000d4045504440d4589401184406001045106045075000c2c541c3c030400100744030702079804000540002021 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 321551627 1250 321550377 321550381
    0x806010e0c1309060303031a0109030204050a090611090406051002070b03040c2301030506030a0c090f1b0f02011b0804060e0c0d05010609060b0310060e0315040501050411091603180b 80
    0xd10f0f00645003910080f0000307840c00410f010140180e24900917070480c140e6035401c18520310b808000242c5400b80400c9000c40c1d5507400310300001c90a202d0481c00a030301108003038668613040104800c0f1021503101c14091b02e0101000d00486034003081e043d05880140c001c02e07032a5221410034564000ba5a0000018030801c204142d021005800280b01114002daa0521090343d4840c103040e2141200382d0000d0054a10749000d210002c2c0b44d410607101880384c100001031805092000e0030984c00d10341004030110380c02c00e03003030348440c0e50a01a013512200d6401c1210205250404001c22800009001620680d654080f41022203024400d0300b00840c0003e001144c0c2c21034a040280c02400d0307610500c04040d281540028040c420441900d106102c2c40c201884180d00d80003050f40c1c40280700c0340107a8580515180c15100c502c40344007950049020340000907840c42d00e45841100c00e190008543d100b110810104014402031003100074810240b032034003140100680c3c03d01c681180240c0310081854480c101 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 321552877 1250 321551627 321551639
    0x7030c060e0c130e0d03240e0a1b05090f01090302062b05010510050c12030109020c0f010b130e21090910030c05060708160309140102070806010e0c13 66
    0x8002c078140d002112408010304400114400700d843d698022007484d0080220780a02c280130ba4080111012035422985082c0e801015200c43d5580030b4000010300480c0700e09002c0f040d5070b14410001600750b03044100c5c45103400100301030402d00403007401500c0303402410007100b0b883c1d2040018000035903002d028681ca1f1b4007624401480000e024101080c112182498200300123014000c880c1250305c05040c0034011443d0080c115265031140a40000c0d83c85402000300104540c0002180240303c040f10042c2c6410703ca02e0401d0601c00904440d5a441c1e0524103191000c3d5510075400300c02c007440c0c4100082e440c151641c0f072410a680f001c03c1c10282c564140310711307132860601320050100c0c1104440c2d80c1c1150340c4601c50203880c030145001c068000445402d042c001414203c004004d880d02a2a09500b021071480c5100a2210442011000650558010810804c00820720f4500c04070900151200d6030901d02c07143d5031540c0c140b00e02c40603244280003184e10303410544200e900700024240180e550940380c030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 321554127 1250 321552877 321552883
    0x90b0d02031f0b1e09090322030212030a090504020903010f0f06060f08070504090b01030f0e07050901060306030b0f0c0c0706020607080a0207050d120b04060315110a050d0207030c060e 81
    0x102c09400080c14404400c809242001800007960001940c0900390601001030003c0c0b040300501d0098035110421001009114140c43c403c40207491400714484d045c00d52040c000303444040e503501f041640c424040390600940105152702603e000352401078803001d503140068054050320704c80488c840c0c81d00102d800fa821640d040801130740c1c500d8490016802914004444043c1c0440d02200000c9081c4002e214440854000e50340200c0c05140209843d0f583c01151000c4030100352296070703103501c640030030050b070f040414582c3d004010500f0200700c400c2c07545e101e0101c201001080700c1440f20420000a02c40007044044e01c2400c01600704940c40e040d2920030207556100251907500101d0581000591004454022510100c1d0300c40094140d04403030306000d4401c4204001d10424a03a01d80808500581b103510525005500078040540e240a80c00c081c80c085486e4404060601da804000c920121504031044039001d0138052001a900e81c090705044900314103820340103004908222141164440c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 321555377 1250 321554127 321554173
    0x60703030221010501020319090e01091a0105031b0f120c04060305012715270e0a0b0c07080c070f140a03020a051c1a090d02030c07090b0d0203 63
    0x507025146450042c00070540d1030300b02c24031601c1e006034410015141e02052180c0070440e504074904102e030211791102e9041c90200000d8110300304181c4e4580360350300f1701034420055081e088400c1c01c02502d10b0410540002540300482c004282c0100001040c0c08030b8008002240d100d2a90b00900c110b282c00e068000381420352040c81000c0c0024144400880e00b2034001c002c61101010400184485001c100e00030390241801c41b9a410789481c9c2514006410f012089083e4140700182e01e00555402d40959014202e50310b02c40c9011050380300c0340009000541d84410355070424100c0d000d05844001501e0200d90a01c2107070450f02c0c440c042c05100245104621310310744180c03105040e03500e1268020300f0600c00d0705015440301030740c4800c0c000020005410490344aa03401c3e248a2520b01445140303881d50a03110f204810284c00d84000e1b41c040214a810a0002c005008814800366142002a000e0550744280d140207100f0130564800281c80c1c00c1e41c81420b82071420b60302078103480d5050030200c01c01c40b2060007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 321556627 1250 321555377 321555397
    0x7120203070b030f0f060d0b0c03011a0c070b0f0d021602011418040f0e0703050d140315040b040204081614060408060109050a0209091006030f05090a020d0503090607030302 76
    0x1c00102003448103510098a01c2240300d408241d01550fa22464001404400341c0100e400c505007807004004240d4805040c0c0c0b2074880e86903407541d48e51403d400740c1d80b50b103502c02d225440c01d0418450b0001884000c503444044680d40a510790f00c4015140d105d002e070788180308040101c44e02c00a925100e030564000f000c4c9501c0d000745c8801701000c4817000030411501c52194047d5621040305c02039415441c16520051444100311400561540703c00460345c50003c150308141c0d01d6030f1200800c0000301c4c2d0b00419003c0c030390750009601400e60426240200740302c400d0b20030a40c032550f10342184c020562148e9050b43c00070f00c020b104544034090b004e007a907204c50016001c0c0c0740241c406c0407286485070401002b00c2302104c0368040203117110380c83c0105e104010003002d03002c0d070f2660b03408010f242d606965103a5068000d01081905001c1d9a06c4c004010f402c40d034089d0044030113070341404100920720304007180e03000c076284d0140c0302000d4500552915070304500c680c03001e569004501140d44018035605601030450300702c1c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 321557877 1250 321556627 321556633
    0x203010b0307030c061808190c1a030603120f040918080a050c010f061211040603050d051206031c0513090501060306032021030910030f0f09030f050c0c0307120203 72
    0x20050121144080050041d042076600500707000c0c2c031180000008801007801804107080f49030711034141d80c4000d911490ac02c85616004803c4c40204c0c42c0a101c040d0880f03645d9401c89240402380d0100c900640100c0c030a00b0070135540d412000d06402d00d44003140086990281c21a40c0e100c0000d075000d080c5070000c600e0703c10301e50b1a0031020003595105104241c280c800b10f54a000048075147d4801589410b514000c5400a49640c4000300040c0108000201d5800e0341e16801d0700c03148030107001200c0c528001d14242c841e907c040300d0741541003000c58141070120340c1407400c29034803005070715680069091503010b410f40b10715010000403c00d6256121005a0703200f40034510f1101c0460811b2080c0400740711200b544114030341d1000c81d40c0c5c94030f00340100511801605490406040c0030015003241d414031490350100707807580c6a0500701500b62040e150010341c442010800e09076182c4004150204104049042c440001800d4800541c10040140c03d404c1c020101c41c04103440c0d0070701c018841080302049020f44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 321559127 1250 321557877 321557897
    0x3160f02061b181203070201020d03140412030b090702160623090a090c050702040e011e050c0c011d0105070203030114010e06070203190b090a030512040203010b0307030c06 76
    0x180c8003045040c0501c882d2202c0d1070086142640061803a0301c681c24044000c03d0402002c10070b9220301d085120000f203400003941c0c0f00e066074000682030007000c2045100b01440c000d00c44000b44081440682c006400060001c1c03000b40e034000c02e42c0180241c0183d9030744282840200321085a000484018200400c41c3c82c1810550360b041c00e44680a045e000d044801d81040901d40051031460301500070128000c06c0d6098569070350850400700e4400d1030b88400000c50019000302941018090501c030300403214000c00290501d80340130034407100903480e000009a1200b000c03c80c0308007460b003600d20340700541c8000c019103031000b0840720203c085d034811906030307500b414000b906090000c02941e040781c11340c1440d00d81c800e00400045030360310145251198080820300000b40940c80c00c1007884100074107032441841c11305444c28110f02c107000003441a844c580c014010100040e600005503816060341006e034034503e8070380340300180c09080c41440305034141c8140d04000080c4440c0009420446200b9103aa49001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 321560377 1250 321559127 321559157
    0x5040303091a160f0504030b3303010501121104051503010e03180906100f03110301151403060d0204150306090f03120621060f020406120e0a030c0b040c0b0316 70
    0x1620741c0d41305010440500040020070b1b040e551103588094910000c400402c121105030529210350820302003404c064041100c401d040c06d1052030b003d02206c1484c038000040c240e86d644005c0d402c60001c18020b03500d40300850300d182c2956108554102d0300900900260780500d00752652a009070400c40012104d15074914600d08021110700d0103984041e125074805610301c402074683c040d9460f007280800d5500c40107448402c600da8080c502a104002031515040001c99000b001001e400340d50400f544070400610006035580701002a00c1c50f81500c004c500708105018202603031b02d403680701509040c1441c2c00201040360000810050610030780700d864400c0c455880f464101d40d05401030b01c01c582e0f105240c2c45500403502600f4844c240c46048041201e544c0c0700141d00c01c0ea0860343c07048000c5454007455085200e0140168400012000010504411242c800030014069514050118868030003c1403c1c40b4104005030064418003154640c0d03414803c0704034844c1e841314461a00050317140c900b19004 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 321561627 1250 321560377 321560387
    0x40203060904080c0a08070c05030d020d0e1513030303140c0306150c030d111c1b051b010606182102210f03040801060b0a0203040905040303091a16 65
    0x5400e02400c040c549503100c0e990510583e00000b551601c80c07207a60790150019040d10000d100070f0f03110700072410003d0b1031305080c107141c1549a10a0301c103540110b05081d02c0c02e9804502820040c20490b07040140141010407001103100341c4440f9018040b4104012051540503080140d50207100744009110341e03200c503e422401d0100f60b61251b40050122130000303003140c005c00602580000082a0385ca031141d0551920201c48440c420b4a640b0f9401145060150380b14420901d41300c1d0768a1820300400c200c0d03815207101c0101c1000341c4014888080b84681020004c107d00c02100341403807000b0068603407034000141130080b46c20210880d0641600c801b14400140d4001c2d441444c41d41248802001559400c2240c1124441340c00144007441820144221804100b513143d103480e54406140e507542014905030a4490341c0d004030107a204104100c500c0d0950010844048900a45000072541c88525044028050042c4081e10075141c101071454603010403165107028998903c042e52001003c001c05441c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 321562877 1250 321561627 321561631
    0xc0b0a02131a07020d06110a030e0d0216050d0f05060a06140402090607110609180f0906040203060109020a050f280f05070602030603030c01020703020f161203050d0f0e01140105040203 81
    0x19440d00c080c44120b0050030805d5400c800d42d40b00fa00c0200c1c00f441940c84044050300007500240002e03071500090340d4890030a220700f4010070482e01c05045c17a00016880d0050000c22441501d028a4490010301f05002c0740c1c42d0510f00940d80301040c4e40781400d00c27030461000741c0303154016a0020090040114044e14042c4211044c1880150026007031001540702d180400426445045e0000c0c1c0400c405411603444003042c0700116410a40100e0604007100c040d940203800420781880d5510140612001d680c00084079811200046c0001d80c1d598180c21003143e0601960341400001d030004035500c040900031f41c04541d005040404113420b120441d0100f122881c921136001c601040c4104480000f0a8007500115805500034048900c0d115402c03080900b240e109800640041c0c00c0312031500c00c071000611500d10481540d000c81e00c0c165040c81500d280507842444020144900041d000b27401c0000750704046040483c07104100700d4040d0710b5007554003034a50050481c0300082e8480001c203c91500380f00307480c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 321564127 1250 321562877 321562919
    0x50606010f080c13030c0b130801020a08011502150103030f11070509060f06040b0406050c100c1b0f0506010b03150102030319200304051605010e0904120c0b0a0213 72
    0x1888036203c2c5002610698448041000c15200f00640440419040b0300403400030400c07d14100d560b40403090240e01d14400035040015182d0040002c00c2656901004c001d0640d058000d40303e2103680d04030002d0f0700c0c200e140c401c4580c08045500c000014541c020800651980940d00c41c03000250100d0a526100c040e14083c040d072144241e00407400300e0070100d0021000c4070300600554a82912690b009083e07401030b52103000007540004103000066424401380c0821038022000307020490b441d49019098944204440c40300f8401c03400e031207007030040c0300015601a58210054074565615009107140d2030b03200300e45402c120b2000040b981215440001124030407480c260b8000c00f0150880e154030094903030080003c519502501c40c80f644102020029401203100e0401008003040382000c8141003c0160701441c1404110078210b08541c41e2070181680c400e600c8070540c1c3c10b039142004103941104140c00b018100c1e01600040244035071540e17008000240c8400800c0f40c6482d070360a03d03104001d5481541d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 321565377 1250 321564127 321564137
    0xb03060f04080309030f340b0105060304022e030c020a0519030203040f0621060308090d05070902070602030f06030c0a06080a02070f030824150304050f0106030f050606010f 76
    0x5800302c0e8481001e0b60304a422801075a160141d040d05100d6940c1090712200c1c44001000340300d54080b1038050786031811441c00c51498200004940783d0740e00b103070414070070a170260100000143c01c65a98203100c00e10030350b81c1048a01400030001640390401c5801903032002003440e126401d0992400081d18000032f0394081d00a100c240b03100c01040e001c0c209400c1d0200c0541c0300900000c180c41c0009981e0703202901d035a903224813418565032126511a84c800f111040e0786481c1c2300d01440400c01c0c4e40210703040e80c0410713200100003070841d2620520b0320fa240d81c8241d9070b8510105102040043e5a0011070150244140781c0c0030300e40701c500405807640000002180d001903411000c100c854040e00d2200e0b405a8882d03030041c20039482d03885405040000e41d90031030000305000b040040030024401e0b10b5500140c003141c0c061361200340c40c1c0450a0a011000d403440510340c00302c0000d0070404100941c0307d681a52000030701c4000d50303c0c0b0b01400016101c9404541d680520800076003603511074500380007009950740c1c078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 321566627 1250 321565377 321565381
    0xf032007050d0f02091e0106050f180d08160b06090906041211070f06080906010b1806070212010b0a06020309010903200301050c0a020714060d05060604150c060b03060f 74
    0x1c2210782c0d600030004a481c114102c03100c401503030351003039103e06c650020044902c2094214180c41042c00c0140c12200510109000024034528000103907024070014002d130a00c640f00d5207000891107145494014618200000d040b00400b040120b01c0750b11078861000350800791641000c004210300c0441c0d41140541c0900001404100c0d8050400100242d0b41052075450032074500c8a818202d02d0b4002c541207042c62482040301c0d540c015400ba0744004c1e404007038800c42d41400384661f164810311740020400c0c03400408403c690794400e005c46104a0b40200103201030180d0b010401d002c0c1400074080c600c6994061000640c080c008422146080300594524000b00d05642e07071003512403e1721180c10200c42103041030092a0710309205150040680044a0f0740b00c4000c860002e00c0c4c07407031a80000341d101c601413100031544e442e1070040c0c8214075014403011032166500380110307043d07000307a600000e00422442c0d94240c0458110940d003401c580603030400e0019041c018185a80c075030b01640e8a074211175500c00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 321567877 1250 321566627 321566629
    0x60c0f010213081903260f16030915021b060108010b1f05120a0f051302100905180c070c09020a030606030207020f090a020d1401080607030e12030a02040b04030f03200705 75
    0x9806c3d280c507524001c01140c180343e0341c542c101c4801c0f03070a040c860340d20700107215180025507071180b01d011032441c0500500e00180c0d1b903223450300040070340d900b04944c020421801c828030744120300c01c50f00704000458145603544d2950314080d108007510580101501b084c01c0380119004803024001c2c0c105522003626002c8c0603c010110440000c10007401c1c1507842d0403400c595805170140c680981c0c80e06c49140c0040c403040c010802003080b840c0400c414803281500811850b22040c0c1d40050554081c00c5e6001207503520541d2950512500270001c006003201c8002044204540d40644541181c6640c10482a902c03510300307400702c0c440c024000e58001d404010780703105450031704125507200c6080040542820402c00d0220306903440007407001c800c424000c00612503050100280303a481a404d203018842e880d01c04107034a803280e1417000060580c2e400040000e64850050f0121001000d0041c10190790319501d00780030101070311000f030031400501d680d40c0324820b008000720807504404082d8050025145080 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 321569127 1250 321567877 321567887
    0x7081207060b0a03060203040c0608090a080702150a0801031b0b0d0f0609020f04030201020f01050f01030f0f170406030507030902030d0c0f0804030b070210090302060105010e060c0f010213081903 86
    0x80d02214500c0e01c0301c11200c03980c0c54841c52032000350311801c409030312400e091a0061481030aa0480f20400242c4c2080081c10032000030340149158114036031700c0d5079211500119100519040703520300e044400080c0d111165501c0010701d81224003c88103e04804403551885541c00014440c418085e001032001101c086910703800911403010309000050301030b54840c941010303a040001c040c00a40741c04a03080040d543c05221518250600900801142c075010500300344000041c00701070b003c0c090307010000c030070803002d14003444c1e00c1600f003500b840c1e810014060716102ca0b1700500460f400a414031300071400f07035406402400d030401c3d03008015204030403403828100c1d00e04217440c1042e0707545080b607902d403400b00d078903000200059070140c1850f400516080324043d00c2c01c900c12502100d81840c00d82900d0200760b001c07590b641075610919080c0c503003003481000220b8901900500e413003c1d010740d464510301e8100550040207106070341e0032061800e6585401c40b603150179004803000140c0303086a0000700042d10030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 321570377 1250 321569127 321569137
    0xb0c0f070803120a0e101a150409090305070b09030a0905030c030d03180f0c030218010b0d02091f0903170a08130503070c061706060304030c0b04020102030d1401050a08070812 77
    0x440c00028031740b6610148146004660100218003541e250881c0c43c03290000300b1589102c08040e0348441c01d59418401c06861803041c2d100f501161a51141d07101c0070944590100c9840b03640046000c1000d00300b1000880d00ca5124406c03a40c0070402e02040021203084c00b144010060400401902c00c107181c0c42d400381e0240c0001640c5a0151045040c0140000c030401e80389140d13140075511116540e804c61060010480003580c51520000300c4030010015000003608898140080203000740c1c840c0007030400304600c20b45011200200311003019940c5221680010390304103d0703004140b0208171040388032031201144501803441d400078000000048a811003080d2103000d191003a41200d1500b205515142d00e0070b00c56400c0240050142c9440c5101d541080d5450350304000c2c215480c42c5036080540d40a403200881601c02480485000000380c15a8001c0c4203842441c0f440080c02d21502c04041c08010259800340100361055a100d000030889010016410f000e458800c1c00414004d040320144403215040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 321571627 1250 321570377 321570391
    0x218013b07180b07050a0507050307052d060c100c081e0405030c0a08130812030f060f1f030509060603120d0204091803020c0405040c051e03070b0c0f07080312 70
    0x841d402c000b543c402100003d040c0e0b01e000b0f0b005042155417130b141903410a80523a1240e03121f50f01c00c4206010760303554a0f00c86050100d28080c5003801c0c0fa0700140249040794183c2e4002d500042c04a8103104401c0017017035244403044170075010030001c1104041503c030b080055908443c1d900003445218a010086440c16422034040ca0440342081e2410508a180c425140411194130401281881001e6222490f1102400050010b04660110350108a1642c0001880302c0c640d0018907001c60040d0301c1c4d01d07210f0441048042c0c203100c3c05130075018030140510414481980001e1520000603846a004900c50340903001c010301420601c3c011a890031050740000c852583c0c81c50b420000001c40a50622482560780407a42c060142c103401c034200070f41080408000d050155003003c04000000700c4c80c40500d803d07900b00704c910045441002c0700482030340c4101110103130144a120008540144044041c10607001c1c032900300d0700403050055a0700d884032401c0c030903c92940d00c140541c00d504402d040030f081d40980 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 321572877 1250 321571627 321571667
    0x301090e03070204021303050f0303060d1101030e07090501080d1e030519060602010617060f010b0c07051302180618010c0f0209040f021009210218013b07 68
    0xd00b40d00010100c0c1d0003040d0303102e1b400100b60b40030030400105000000c4000e080901540c11072410f03401041c20403008002c010042c0c86c0652a040c1241e00070f0303120a02c802d014508450b020b640798640c40006060a024125551083c054000390310b601c2010203403841d414040714601c01c100000402e4000d0400688034450444903807498502c0b86060348160402080c42e580046801d038944030000c00826650a05040260446010030075695007030340c505811101043c888907030b50a142d071002d9081c070308144c009684c048100c241d10034002c3c09540181000c03a0810009541d1007100c03100304404c1c4d1141c03020b54190b441c280d84400100358058004544003a0150218030394a26480d400114a000220340884451103401d26075800d40c1004508501241a5800c04000c1c8605081101703c845084003402e507003e881c4110541b04544650702c1841003000384600c1d00c611961900340a906440b15140e9910705913101501b5041c1140410012038600c0801c0f203004641521240c02c1211b05010ba0b03403248503440 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 321574127 1250 321572877 321572887
    0x12041d040804121a06090c07031808010207080414060c0607180314030d11040609051c050105160f0509090408130b0d02090102060a050603070e100f0303030b04050a050c0301090e03 79
    0xca40f5003004034061260350440941180b10350344080c1c905025265070f0207504400100412034050000f01d821194150501c111000210301c00d15100c10300d1030300001e8195001048010800c48000090b0066940d00741c4d0745510541e01c1018800c55004203200141250300100218030b44da40540e05a201110101d180d06003481e480361110b43d41102d05000065403540700003541c0742c14200500c208806241c01061040c5003a142401c001d181030b5042c041d20348240f102c400301284600e01210340002c081c0c1d0000c001d1000c5d1500300d42500c04440703843ca0075400b20303102010716210171b8411070455028030f200900b201400d0300c031620788807480e80080f07230005104400814081203940400340035001c0d08044080250740c4242d03030000241444006000746a00c142048240146650007140c0031081c5c80c00b00141d03030496911080100549105a481136019280082d004024941d0540054401e40400d5030b040c0195110001d80100b02c403402c03a2050440c040900041c040d81c000c07a000514900901c0045a00744 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 321575377 1250 321574127 321574139
    0x30903140c041802040b0114091302160606050901080601030503030a02070204150b030105180c03070e010c060c1808030c06041e0506010b12060108071220031812041d040804 76
    0x120343d1592a90360a07007151502c0000c610f45070042032824802860505e01da091070070780c0c925840c011480c04520a140311813a844101c03000354152a050b100f05105656640039a050940c02800c05010342d0780640501800421042d5000032454101d9078440c0080d45551344421101000350400c82080b81d00c00c0d1101e0314280c00d44400e501100c00303452000409035681d40f400c0c0422404080d0032001480c03500c0c0a004110172103900b0400c4e80d50101850a1010341c9522050048410543e00c100041100b4680b4056100c4141c0c0041c0c68401c585106103031050064481007a40ea880c061589415050303886000068000f55030303000300b2108036480ba84400001482581c3c0c40c3d040070400d030060b581002010561034261001100b0660300080213003410502e0f07060030300000709020603c10428580d035031110700c40900342c02e0391800c404040708801c441a403242001d0482c05c00008042400d12814465031020810b081007a03400c88084a14407124403941101c81c4000c544d1440e001001511040c6003440b00140c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 321576627 1250 321575377 321575381
    0x911160609030e1f0906020a0506130f02031504060c09140d03030f0e0f1c02120f160803060306010906060c06050a150f0303020d051804090f02030d02071a0304030903140c04 76
    0x44d5248a801c28032850b80340c880c0041c080c4e10240d00c04c1d000c40d0b0001070707400d0103d0008140c0b50380210210807103035039008440c100684c10230190000203400d4072031140741075160a10f4a0190740a244115010700070a011424201d40000407802200d40207568403810609514218402c04451446030401003040344400355550121820b04110300035a4001903601c030078014080c0620a4204d4103155580141c825500d0020741d14010100400310b6200c00103410312841c6007000030b4896100000075401401d401d50b20300081c40e03400075602c441c0240310390b20003c510302a0340d010f0384041e030307000b40d64880c040c001d030f80c69500c0a08005085180c4840d6901c1804d01030016a1600f8400341c45001e42c03022402d4590f00c0c0c000c1c54683c8081ea40c100f008014450140c4110800c1d0f041c0241004c110b801083d112014200610001c0c1d120300029854400ca8502e030a4554000c01c070701c0216045950003030101101252826081e2000319130050015184040074800108205a038800303540c002c404480f0000048004030702 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 321577877 1250 321576627 321576649
    0x8090d1b0f030c0f0b0405090a1b050d140402060d0b0109170d0809030414120c03010f050a0c0206061008040f2901050402131505090405010f0911160609030e 69
    0x4a8514058018401c0c00882c3c0d11800041980b5210005210324001210130b8030701071402000d1141c00404041090340e1029004629642c016465001d07a010f034590b000740482d8803150720b21504504160003210184c00030b0700001c0c480c0341c0140443e031404458158600040490150700c03414081000004100c2060000512150702030a9004109240c50403038007a02e2400d000b40702d455075502c104424000042c1b03032009131038034040c10f90f130620381c404005260604013003054109603055031074000e1a40f003401c2a508003600a801c4403204014100e000c440c101d0311400f0849403241c1000e50401056651403240b01c43ca80d2040c055600b48820f07600d07d40d00c50711000c1d06c3c81c2c040e04a0404803131310064110030904140c2c0c0100b1084800310b20380807280b481424681403620440502c1501440c006a000d8001c00840e88802070081040100e5a1501c40f40c6800c1500b601131841503d00d81001e40710102c01803011250344400906a42030000c005941c1d590207003100a10032400c002405420741c2e4035032107900901c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 321579127 1250 321577877 321577889
    0x10c0905010827060f0609090c0904020d150f0614180a060b1803060601110606010f1407060608070f06230904020d0c0206072309040b150a0f08010308090d1b 69
    0x140703070802c4290b940400300c01603d041c7c4100380784810700560780c4001070001100c0b4816102d014071503a46000040b6000303400f10300540040c00504030030101894640c04021482d004900800030180c84118280c510000c601d042038100014014070400d4900b0421440d80c0400103100c040b0700f054841d2001c6019401c5590020142d4a584008503c0c1e464103200302c41d4020380c2807800c43d1030044806a9143d5501c0041c1c000c0c0d041c85100a8242c1c1820b00c0b80d203d0422586000250540e50314242c580074004000620804446010f00c2e9000300300c006035035141004990460352400364445035921800501514a1034070308522000f0002102c4c1074540d8009401c0560055034009442200c120002c0c0c20b0207030041190003002040e005181c504d13070b02c469038107041c2488200f20070740b60300b030040120f0002c1001c440d540f54040349041c0d4a1080400d050000c02581c4107560310800d40301d40300c11090b5841300082c04020480382c4180a820f001c0d09018960a40c1c0501038004641e080000d42051002445190004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 321580377 1250 321579127 321579133
    0x60e030c07030312020a0801170f0609070e01090e0c150706060e06030c010305041205090a050315090d020a1505090c0d05160b0f0406080c07060e01050f09010c0905010827 75
    0x200b040c1a0400d00425140500c0d40003545018409000140800b030705009482015500041c140b030300036803c0000e40d4514000004440080c1400100c1c2e995803441807040c060100200e41c00451400c05a02a40f510341030320f8070003800b20b55030f001e0401455032464901d80514040070310000000c50407601415000340300c401c040079840d040c0b1409150900c8440461281814145401d000006080d129203041003011881d142d40c8400003600024011442c641c4059814485c105200810460a40781d203400746507660100c4021000448040e80c960015081c040c0044a00b43d1241c5c100d0500d80c1c120681c0b2124100540b4403441d42d51000690007000718109840c5980032052581011f400c80d28100041d121200fa40e50401d00c40b61650005407003140292800c00800c000460141d003c2071041e500e080d0362042050102c1c504d40f0460720700a0508a0303951030007544940201d50503080621031140c802d00c0c2a40c0b4500b0542c100070040d5502e00016060002c0b04250b40b007815013a01c010a49881180554006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 321581627 1250 321580377 321580379
    0x8250305040201033e1204051014100b0d0b061903150e04060b030304080a120801050607051b06040512070305011416030905010f0c0216060513060c060e030c07 70
    0x1422035122103101c0e240c11801c010030b042d403540865203000c0d117180c03044109803105c3c5c04800303600c04602551800c0c1c1201860f03503083c4010043d01141c24a40c200014508200c00d9210620a140c410f40071365504d0390001464105118000d1900c0040c2510888104080b444007201d8011588030740c45200c40003089a40100c21600050f4035005115407243e001078020840760415200c0d44094401800050042d55190340201c4030740c0f01070050714002c11710036050b5966a82c0c0c03400c003048890b1170b44441d1030005501100106842c9071081c2070b00c0301560003400400212441005180c1d00d521000c1e900c81d44800c0911000620390b131031401d2900145140340190100900c0c600c3c0c198203507041c0e801d800891014030b0003000241c0d10001030010840d012498082800405407c140b401880324000032648241404090348a01e80c0004160606a103000c0442c000c1e550707a003008840d00e0203210751140012003505410818039128211149481d0700070318001501007007030b680b90752451348030740054405a008818 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 321582733 1106 321581627 321581629
    0x12110d0302160f030503091c1704020301060302130e0f010b01020a08030a24030506070309120c030e0405041406010b040e040204020f0d0f1b0509030a03082503050402 73
    0x3450f45110183c0c140103140b07074001c42c1d5100040c807c5c02c421031113805104080b803030070700314680d281044402584a20380342c0e036170007500070799140d900ca000100c05a641c010702c030741c280e040444001801c00d016801203414001e44040c00b6007a80d1401c0f030740b180203907004100600440d5014090030351740e0307403a0410074005140009500fa07000d40b48880500c070121951031901c090b02d02480c1121034036942c10108500341d8050140040103440c00025000c8041c2c0031300908402c0a1090401c000040769200100c0c0454100310b17010b44695050542101441e20f09021250150203071076011840c2506000c40c0031403007140544005e00031075000501541c8001d1010660710555016003051141410340c24000b8003030000102c0301c24801940c4c3c40c00c4814240100101d80c14554090041d11700131f001903c09440c6004001d080403070308085142e5049120304840e042d00648100341d1000190340c14940 = true := by decide +kernel

theorem cover : BRFrame.Cov 321402877 321582733 := by
  have h0 := BRFrame.cov_init 321402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 321402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 321402877 ≤ n) (h2 : n < 321582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
