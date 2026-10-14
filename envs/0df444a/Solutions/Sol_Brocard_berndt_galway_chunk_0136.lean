-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0136
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:03:09.28231+00:00
-- url     : https://prove2.me/submissions/5ac46327-2098-4ccf-84c1-2e98ff096c8d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 24280581 ≤ n < 24460437 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 24281831 1250 24280581 24280583
    0x916080304120c050607080307030b0909060703090c0503030a03140106020102030106050f03040201050f0705010c0806010e10120b0315070207090203011206020c160602010b0a0506040e06090a0b030102040303030b0f0904 96
    0xe00140800e00c560022402901110b5029031030340340b1021303660b4001c40c42c1d561090b10300366402c4e00000100142603415015038000c4c000107807180d107664034202034182d40f51600648140101a128103040741808100e40418001c0d101c002c0c20b0366501e4102d0000900109005490072481900f8540000380450061007580e04a80840d00e4480c40e05000300018845580003d0040f0305000c006c0c08020341c40c0400ca1b000d4003016114800010322400f54800142c141c030300c02850300e4104092591480c00b1780d00ca5903c00104000c103800c00080c02e00c275a0340800050801d1000c015010305c0f036940c061800c060180106c6004a010350255000d00352542c000d41c040c1e12090117403000940c10303240d055000031070a074002d01080320058159840e1148000201032035a80d60391017640180e44031000110546058010b01004103c01c89040b45458901940e14114410060800d403145454030006926004e45410030303603400c5001402155116102e01d8050b0040c25496444c60050700071902060b00d0382011440e840c096 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 24283081 1250 24281831 24281833
    0x1b06020303010510030f0504080405031c0f0509040929071407080307030207061a030c0910050913060608070906080a0b041205090303040e0103110604061d0105041706091608 76
    0x1d40c0c2400180110441c07044c440c0c07410165203191508800e0450700c034082c0920704c0b4108142e59240340c20205494101d5801d81c08800018215400c1005074204050300024045401c005440d0100c80c40044c0041030000e02c0548801c1d450440200742003a1984540014400d04c0a024542c0c2c5510a048034801000c1140e008641d034100603070303408180c0c0d150155511809514000d4500300f03c0303a03207800944540c1d01c1c803002080c98035402d10388646403e2100c445050b00c10380e04681c0500e4203c4000c0f41d81c880520400340a15550f00c04104ca18000d0884244000c1c0c02c900140b0a072a540c1a20f10768072031305445407040d810b2070500085078806000c1108103049030170038a07408864071241c80c0d1207080b40c4081c40410a220003000040c90944041c000361005101540c4005165859810000362940f03016901500c901000c020030300c842a00100c80160380c05d030030140e409148400c2c00041e201440396030420707001501c5043c0300b00032041e00001d1540c42120850150f0300c03401503000b10f01a030042039014031106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 24284331 1250 24283081 24283087
    0x7020a020105030406020903030703030e0c0607020906040b0103020c0d0903030906140a030e10140a110309060403140f04030b0415150504021c06030c0e0f060607030f02010605100c1b060203 83
    0x5580b081e03000d0354206010710303c01858481c0641c0004c3c5140d0101a040b03001c2501c40c440101c004406103c0901c00e54002d403100c03131414465500151912400824a0348156610751140000b0392203681030b40c1c2c03045617107070031118500740c0c07c6030190038180c031880201c000400112010810700c1c496908090043d031180c0001e03040000100c025030141a02540c0c9525504c140300500d44045118011000615001c104082d0710341803c43c3c44078140c0700820031585035140b081040c0164008000303040c5034465018a0400c1c500f0601881c07082c40c40c4200c40c1188111800450701005000c001100d07103000d07510543c0313064a5515500344004c103540008000a0400c1c030008410400c505094005040003169140c10b04c14002d4510a04000c40e2031726041a102010021030a004a0005480e41a04405041c00f50140e134908400085d000f40b107085401410081d04080c83e0384210300075007296024080c010481c7c00742140c0350200528100c103501c41901d0003c4001560881001c0c1800341e14140c420941c040d5203 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 24285581 1250 24284331 24284333
    0xe0903070b0c07020f031f05010807030206040510170406050108010e0a020603130804030c0305010e0f0106120f02010315270b030607050c030403050102030703090c05010201150501030b130509061e07020a 89
    0x86240c000d20002d0745c00c0400000f080340c482d5800e0248642d04a41944210100740c0c61440400440d54160003031440d56001c00d0302840582ea50900f91811100304403040f04c075181e4000d104642081e40e0600307010407490000180410401280c001906941c980c0c80208040b060403034550b641d0f10070406c0042e4101404201003400e0301d0030050001e10304bd0003072800500c0c0c25600d5840d2101ca5481d80e10644450b59900150300340100103001503015043c4420081c032080f0306151558441310002c50307004101c1da100e03584a0302164044d42003c10b40032100d40f0b4892000783c2d41c400c04458152104c55044c40701000b6003000c003148150f07101d100000c02e0003070010801e517a10450246e5a690040d1290701f0706200a00c0b001000600074002144685c40ca41d40201d0340559510307226164000c0d5400c101d05590426003c841e48815501c40304003281c03400d02c2c0114040e04007102003488401c488520520031802d240400c918003d00041841c0140074460441c0341c0000c480b0000c64045a042d980580180c01481c1940 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 24286831 1250 24285581 24285601
    0x20114041401060302180604050c07050303161101021206010801090e0c09070c051c0806010f230f040306020414060f0f0a0203131206051014010302070c0806010f0e0903070b 76
    0x1440c4808000281d03903600e81e00011407605040c401b10610074042c10402040341010302405400c4111490394030f05005141d0350780c41c5c41e07000c000d01c07004a0004440014015038440c100c64441030341110b0003155965040d0301090449542125040e01081c0f84900009020300c482c420300c0000003149000e072120070040f50400800340c0018054008005040c200c62000c0b03401032261200c9030f40000b044401d8800c1d498000341580100502c500d06110b540c15035808982c0e009014900309058840c0c400c080030b80c02e483c40d010035000312014200d44035404940841040107981c010001e48003106c45c0e07040e100007074100308215413107002c1c0000300c48007040c031030001345014050180600c20400e0042d02d041400314440d400c550761180d40001445c0040d030060030248680c610a00d038000704140a03982616040c10040c000a0a00560082c1050343c0040c0e1501840300110004024008080c1622419692245009586203076400b40c3c4500e40e061030003044c0403c000004070781034103500031280c107800d07503e140c215 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 24288081 1250 24286831 24286853
    0x270909020303040f08030a02060f061e030a060f020405011404060e0603070e0612060907080723070b01060201050402120313031401020904060e09010b180a0e0708070305010b0f0102011404 82
    0x100e8051000b0f00000c0b80c80c003020b025000140c60714030300a40d260f83c0c0c803010080c6800c40280a0403100c500c900184905602c80740e00e80020b10021408d0740b04001d601401180c40c100301d0035000342042d46030441e2844001102e030001c204441091341c41145010610001d0116440345100340c00121700295101041c1e42404c03c0610791207813150614044820f81400802c0701c983c4045242045091100104120b915015054035000011342c640034440d0716002c0c1d0301610200450414103603840c50040c200c4900c0314503400704c0ba1400d81c020728110603560340b0003029019140c15242248a01c100010006080200205491050300681900c14045d895a03e4081b4144003039840c0d203005540801c1a22001e440d02e02481000b00b10301082007500d454003890301401c603000d0b41046d078801c078405000d00f200c01041c9947c0c950443c0e0884000a0103094800380c1c140303040c0e0075511401c16406004400818420107600424000c1c100342d03211101c8801c204012800c031808014204030462042c00414045200d1a0b08 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 24289331 1250 24288081 24288083
    0x30906140c06150307090608030904060b070203070b090301021b06090c0102030307080f04060b1c0209010504110304060b06070506010b0a030606050a0f030c020f1902040615050706020706090803010303050a270909 93
    0x41d20052070311212a06c09482d0b040d00300c8400c40d800041c1d1100182040d218240081030041c1c100340c03e028032070740084c3d07c5034440d00c035410141e80082032020481d9402e50480300340c0d091401190044920240005840310008c4603484402d020b4160b11034615400442141e10070411641d070310849540d9404031700d56513400a002a69070a640b92580740c415103070100c80062004221090078902601d510421007210016049a801541050141001d03070302e0480980e5040b45e07001030042265421180401c0d00d5000c0c01c2e034003a041e4440c0400004110341000d0041014903104c0e40c00380145601c4040642d540e12840d203069000888100160308964803d030300a11a100c0c85205803222041080560b5142c800480c522040800740c2e401844110b14003480b64100414540030541e01c100300c0303000013810714001c118002d013155030001a10000c00403507034130151826511070791a83e141e58690030010400e400214a0030041012038003003140141140001e034806440140f441c0c0301c017600340302d860000b42c046490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 24290581 1250 24289331 24289333
    0xf061202030604060c120204080303061908190f0507030b090105100e01060c0c0308031f0f050109060503041103010207060b01080912040504020f0906070302011b0806130c0509030a030906140c061503 87
    0x440000f801b10500082001b0092a801075449041038010022030362103200300d1030b12894054408000c10720380810002c20500c10605a4100310526040a000740380001e44020014003440c0004010459911070450040003201c008106950302d0b090f510a05801c18012940c41c8003d0200402809209401d1051002c0c4500143c0c050903589550710b40158006941044800001000044191401c07440340307002040d4444100350014034100020380075010302c0c040e86040201c0080090103100750f80c9410485040060001c564410450070f000c0c00500c2100041030002c0c0c1c20201048448000103603240b03029402e08000ca291524241c108002541700326524103141906103d0700100356295809404102e0080c0c0010500c02c044124803400070040014076002e00005005204161720380002040c130607409100005020029100c06940900a940740c00f81e06210b200649410540d00803480d0742140c1d0103454240c44403901400d4074009019046084e4155800b84000030005454030b00760024401001e0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 24291831 1250 24290581 24290597
    0x4051c0201090b150f0a0b09060c03040f0308070b1317030612071203030e0d0c030c03050418060305010506010c0b043903052107020d0213020d0f061202030604060c 72
    0x70f91181d21500c800c5800748001e41d152000703003405003130412104400740c8044078603000490601c805a81c003406001ca40c80d0142c1c13008602c8038810642001100c1c040d01004500c03e400e55940d00e0f1620f0030761b0003140100e030910807071004601c401d4080f55800c1c0440340d0003609012140c6118405056940008000c1e6500400460144460300414041c2c4006003460800b107a0042d0305a06000e4140c5446232689c82c41680041d030800c40c503d078028044d1501551514150402d5105401e0071a014002c0d42c0214500b44118a8501d007625802d910200807070b48030320000d020690314500190f6081940d5440900383c0044600000c002400524010b0030111a1640d0300000d030f10348030112140d40e4600d03110403840c098094424000c1c0b001c2041914504038051081c0171412202041c0000d6034090031b807000303020f202e0460440301150b581d0340d07040c0710743d44c0c3c4140115201d40c052030044019068000706003032410b241200c042055003003141e1014640360041d0040645032580d42d9400c00403c200c1d00701c041009100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 24293081 1250 24291831 24291833
    0x330a0b0a14090601020a021f020102040e0a0b0a0503010612030e0a0305030301060f080108010c0905040504150e0304030308060405010b0405060d060506030406020705060601230c0109020a120c0e04051c020109 91
    0x1000400140c104007400c0a1500c49a000307016041c8000360a441c195400030340304c040141c5d5824040900c0710500e610303102c008140100c09030b000e030150382c100000503a03d0f4410481d5180e0350b44e0000420500848121640c02d80e0f6105040c22104180110090401a4040d820100c5e00580440d007480202400b8150880c0c0e41c1c2c0c90345801d5030421303041100041c06004108034010f900c240000d01518203080200034810b0074080182c0b03080030302c1c0b040d41c0c06643c84000140600c1618415400454142c00c0c040c02030707080708007445450f940280012000300303003a00042000d9040901c9041d05880146c7c04040c6081e041800b0402203801240c3c4070051981c48003008141500c800300610701891040e4401f45c0c0b2032046103081030a052000b016141040441d01c2e52940040000d04581507030304c00480d00710b503a8104901c0301e07400340c4260742019400504000c80000e817041503110b000c545500038a8142e04450b240c4609501e900300c00d0780c0c003400650150b003c82c2446c07080c403c14129051014000090f003039191f = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 24294331 1250 24293081 24293089
    0x607060908120a0c1e03090f0b06010f03050c0f09060f0f0409060b180f0a08160806090307080a080621011b020123070c02060c01020408330a0b 63
    0x400400c59107140d0114141c40c40300900450240c110010000034403c1400d01e520041100001c4060013844108446034141c01c98001e44c00503900907000340010a603150a0b003041d1421140c165456400901001c0090304020710a10030715020fa41c4883c1c83c0c2d03144c10307240040d0480c01c0e0040042544d12842c01c1245c18102c480110050426004520044e601e8519103401c0d41e0850340309910100303030260100503020540d1408400642001d90490300d1104205400b4003140c507420307054004818a22a04628a509100686e64501214a0303802100c240d0790310641a20780300c0c01800c80040c03006006225024080c0d0049a41e6988810050590380c8034010b000b004900700d1101e2107030440682d544090000701c2001000c0010560640c40c0002d000c000c4410764580303c2084480150003440f840341c4003249680b4812480005659002802d254030740c0031241d01507000b5442441500d14511504003541102165851140e940c98500d5500102c4041c440e40c103068030090040c2220700c0b042d540c1414500ca540e03 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 24295581 1250 24294331 24294341
    0x81f0b0c0c1008090a030810050a06030e06072102030403020c2106010e19020f07080a0207080c030c010c0605060f0301020c030a020c120a1211010612020102060a050106021b060706 79
    0x14040c00034807450303000740240048030014509003020000140104080040d00107480c81480e80c0c546007950b010f82d01c004465840c0a85074002c43e070700a56540001a92940c10341202a0b104880c5003a01c405481d4080c01780c4000a0700d0380040002d505900003000050b04c03c3e4051a8468000d005403566007000d440001c5c2c90044981000e8042000d03141c01003684201049045c1c00f4100706e000e0b1008504010100b14511903c50080000310f40d00010301c8108506424266284158040d012036207a908913440a5154078050083c1c110300e1080000803541890000f412003500c00b810303103c5041c1c901700784d15805c010304001014550480d071050250925074400748010b00e81c3d500400c000e03503100d055a4400a06100030b0f0302ca007601c580020380c44001d28003804180d01c440194404992200c81207200c000342d4288010b004440102d501e08100011010000c0300c140e041207200b6400c5e51130a40e161810842124000c0c0109001a07224005480304d03000c2c00c440c040d031081c90003403029040640715031320310007075403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 24296831 1250 24295581 24295597
    0x30f060603120809100c020c060c0c0402071109090102070b04110301090506010308030a0c0306140d0c1802130608190506030c09090705040c09030b040204050a0204050913050d030606081f0b 83
    0x20f180c80c003080080b100c00d00603c0404d0f4640300081c01074464095000f5607541c0c41001841c450f01001820700d0003010200040303610084050000d5480702c1c16410140c3c4100c052210450080e1049000100b4100c8184202d50355580d000e4000b01490700c9a48440d102c0422080c0800d8056503a035807254007050007001940c0c002d40c0b00b04d142d96036920740207a8050a0750404082c003024541012000d002c14201421550011001564034080580103814911000502e5a1060540002e511603561442e08680c000f000744011994090044541c0e4880c1240e0543e401c94819968104900c2c09071900d4565400043c0c102d140103044aa10000b8240091404002903618000907840000c0401060605028020307110b096410004815881c0d601e80f914500c200400c0242709a036550002016082280c0c117840240c107006c0c004125030b29050403100740f4103c0d00310f015200c620030752b100c2210302403003801604240c405556580030540c85100300c200301e443d608802840c9040e42d142c0302050096034040030300205 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 24298081 1250 24296831 24296837
    0x30304050a06230406050702010b03010e100e070e0108070504050c09060d110f0c0a0506010503060f010e0712180b0a15030f0503090607050619021e0304020d0606080a0201080c090a030f06060312 85
    0x47e0600790300c042e08540c2c8503c090f5000e82d04003412603080800100d42050011b4100d14003140030071803114800e0401030313590000b00518650b480081404a000259003003540c41c1a0750810141d1100d080360102402070301902c0b81e00c01c4c0200f00b504140d07000e0381c004c0031382e01c011408044c5c1070028429000c45136812104078400c0c0e07076014580000500008001050040038150003610950a1000400040b0013050060002c8046d0500203d640c140c8a45aa03007030610301c00004002400b042120001c0345514018140c6144692030082810f41c00c19220341700780e160800d201c1134600c80c41c50303842c0c880b14008581c3c180d8942c0401c3c4612043c030340342c00c8014901c40b44614098541440d0400c090714004000d01404140188188400002c10711a18944020318079039a621a4499a9030320000702950650100104001c0c03c0c0b40b800a514100000d800d03403194404d0700c0e081a643d40310070413200c190003911b22a982c03041501c4000c0002c541e00300040c0c0c185a028480c0420801c4c0c42c0d0310388104101c5030507120400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 24299331 1250 24298081 24298091
    0x3030a09051c02060408070c080601030b04050d020f0c01180f090209010908030a02030d09020f030d2a02090406050c070803130204050603061018020d0609020301090b03030304050a06230406 83
    0x1006410b000801034454003a440482c82c1e018400000e40c1c0700e00040004040c000005911400e100503101e6080c010241142141c000750b840349002c4200300401e442c1160103110b5180c1c203911a5002042e86154521140000c09210030f2000c0110340c944804840c011038120745030f0001c10300d9403492101e100030301640e2801580c1c4144800005028a03034990007840c3c645c02c03d00145400541c040102c64820300b00350310205082c1c550303000046804c424601030755490300c01e201c00d00208036003048030000e003210100c5134040326406404800840e40c80040700258840c42080000e000241903a0003285c1103048446a2070070f00c2e0301a95907051b281e0080c3d4500d0700d002d50980c41c400440c0703058010550f0040043e00500b03c241490441c0384501000c60003460781c460050b520084030100c00394141c1e49900b02d801e405100256440b030020000394001c1c0942c401041c1404c1e001006c5d17003800000c032400b590340540280030580d825154000140028081403130000c2c49400c42ca0072050341240003600482c003451002803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 24300581 1250 24299331 24299333
    0x109020102160e13030e060307020d030b0f01080a020a020c03070608010905070507020306060f040b03030d06140102060103080f13030602210604050c1b01060306090c030b010602010216060e07050303030a09 90
    0x100d4180081e460b203040e14100c40c01070181c0110303020840d0300145105940001030341c40d49425202c1b9541d440702039811000c0441003111050f400903121038424140e0b09c082018002c224280840c2c00103050345280800e80840c0426502c02d00d1303a0041a1389400703031040d1151744515030006810f041181d403100e00052142401484200014480c4a030000c2d000e050a520b44012a804240c40d480020031141c4140007c00520305d1755250758010742d11811005050342e85d02d1140d80741100040290f03008a081c0c0c601140304802c080d500004101e0f0507613401a02c601d0070004054408030f040e40c0300c941d02103060f2030300c180300100041d0107001409420301e0180c010498118089094280c0580051104c0d129030706000c1480072a40101040340d84414066626002c299510b070801c5014103030340d5000514151510030200c040c05030f5107a4840c25648200c1042e202c999882100702e0907806450004401c1c1c00718204088005038480c0d00c40f521007094142590903a90b51140064259041194115039198132036100344 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 24301831 1250 24300581 24300583
    0x306060f1803191505100b0a0e040f020409050a02030405150417040b0c06090a0309090b06040806043206060d051006080c18010f0506090d05030f0909160c08031906080109020102 78
    0x70ba440c03c4d002d20030401d5103030540301c2240d0f410f041d22840042c46400120403101e07500c00c16001c2d4034450058030074044c0c0c50b030b0345822400a600c103102d60342141e481c100119050100500880340900c0d000b2000b81960f40302400400d08854000e001141c1e030604011204290b101188091710080140e1001140c90344444026103003080402418a40960014601c41c4006504281b09500f961b4984500181c500e45500203e2554070464005801d60f104c1c040811040158102c1c50041c404040301e00561a48000c000b00744001e0150340540d00b0b2600050000303039072401c0c04e107030310b400650069040310842002d007a4504101c400d950003c10880d007201c6880d412608080403a0041c498403440040e80a40c54800c201e034054009018040c4070b05000620b036182a910340d01d40c0c0ca0781c507030040180c80e40c40d03032818443c500c01d80c40300c0091401070540600040300d079119120350500000d02e40e19031000c00d42c1e0699420090b68401042000307440d040b44000304441a441c4205005800c02c2c100016002000e0300001e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 24303081 1250 24301831 24301853
    0xb0f040b0601180905090c0402040b040306060b031003060c03140403030603030207050105071a0c040b0a050405040b2d120114091203060a120303020706050c07060e01020306060f180319 81
    0x1e8140300310840351030b2607880c4000200040714200e6800103400d4403440b10950a142003030008580c05030011401080c040650300003441101d1003183e08200807a541c0c2516006804103c8104a24030881041003010414903000111140554a0000b540a01e400c650040250b01610309800003035940c54103000b05030301001208007404090801d40d090002d0741c1c0e141035912241c000002c46c400359000104034520810000d41c5d0240182c1c1480a444808148004041e03800c14860300344151706002c4000b1036414061601c4016044c468022a076003410203c81c210002e084d89031094100000c280d104003401300a100c0d1008207911040c114165090120a042c649a2404806501840c00308240300040e5540483c01e0b0858184001c40d1010f40343c1c0d407c055009002e2650b0240c0260308140420000003890310040454610031202049403009840c0307003a08030302040b41c045402001c06c12010719a0303030f101e10191401c000200761008100c091300c00460b00307081103880d040412110298245080140c0803000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 24304331 1250 24303081 24303091
    0x10c0305181905070f0303120501091e09020a0806010b0403030e030705010206060d0501060902040e010302010f0804080f090d020d0813090b010909020d020c06010f06030f06030c14010504030b0f040b 87
    0x20000c200314940701c02d48030403600b00141100e5070000440030420038144400780003044490b40400d4190340e2810050300700340342e01900c0c40d8110302d03040c0041080101407082580c0641500007a00710300c0b60758942c400040410710303c107a03030211000e44009030080c02000010302030300034489010f448500d18500648040f40003408a8400d81290300e0502990f640090029031001c400c1fa04409106a1410403d00611541d0015034603076000241c04603062441d404c206040381d00c05e80c1d5101f80608040750444140000ba40c00070700d441410030a1104065848002d4a042c1c8402000c0b030303044900c0396000818644003210212080c0c05c001c00e40d040c403810168400300050018080600c002c90036140000d0207003545008031402954003090035a0f03c54042d0b419985842c1c3c1920440704556155071603c00c50401c00d10648001a040071869260750031140501000caa6000c6101c2c08a80d00b002c000d0341c280010840b640781080024000000031614525456005000f40441c1c40b03900d040501748240c0000c00248 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 24305581 1250 24304331 24304351
    0x50f04021204020603040f05070305010c0915020705040203060303040f03050105070e0303040305030405060d0b040c0c0c08070605040b0a051908060306010f030305120a0e0d020f010f05070f0809100608010c0305 92
    0x211054901d080c48005602c65812a05556a642c9a140151040810090181143c400c0e14004804c005056000c68001d05550719039608807a5180b00da5400202508920750058020141c100610305298010f107410100080c1074906050700c4001405a05015500a540c143e444a0a11050a800400072200b44d0320613009586030604580f030f41aa244100d02c12a40034280000c0c40c201104200c0d407100c005000001c10903c00c0203031340fa2004149945281d020b03640e10990460008545500003440000c075600e43d03c50394201860044240c4558000b24014001e00408000790f0355601d0307840e40d1103c1101c0d07454541e40c1c1e16092441c1890f01e0190160808142c20464407030030700201e6045030075200c010a0602070446c440d0f9548001e034000d0a402d0000301850301c5003100400c4407036000706000c1450140a0000c00101c3c60103031181741518020f0b240c003004103081d0640120020312410045034405000c030300b01ca0559075800c1981c400c0b0341160b4820307121030b55561100807286a141c094190031640c400 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 24306831 1250 24305581 24305587
    0xb01050405031b01090e0f06190f03080f0f0406020f0c030102030105130e0f0d020c03190b0105060f04080a0809041404151a0306070c0506010b04060818010b0a0906050f0402 76
    0x21012995844100d0343c843c0084800036158140c50b84500c070000090141c0c6190b040e21410003d41e6003003a0503054680c2031142d810300240b4508890704804036801c03107860310b00c0c0b07100c400d107540c58000c09540403003c600311802c0c04000b440f081d82006d230000c00041645500505640c0c4a40b1304040c1403c2d50b80c80c195101c1e9004000401040c1d03204505007031582c1c0415400100840c0b407d40b403519143e41d0303d100215038011580b41007811500492210440c05058003503441c814040e02d10102d101c0b989050040000d400f480050185080c8440a0840e80c848282005e26080c0c498035414038003a540d031300c01c98625000044c0500e0a04150040c1a450341656101044a0a10307a680034580c21035075271803000082e628581183c481801d90740d86d07291b00102405451a034100048002c1c650440d40304c050b58648030b0302d400004c0c036180e9031003101c0c22100b00d5641c40415451380d0362642000540316800020701c0d034940740a9108c50342d8210312800100201200082c044d494001401580075101c0d171041d115500c14 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 24308081 1250 24306831 24306839
    0xf0d0305010b1e0c1f06090501080d0513090e0a020a0806100311010e0405010902040510050c0c041a03030c0a05100c14030603031309090c0e15040902010e04020a050d0b010504 77
    0xd01911400c40c00c2d640341d120400c14088200720140290100c01000d440380704a001900c0c41c114002d0405171001072001d20030152150051410ba843c207204142ca00c3d400b4688150142d481000070301100c281c0040c1c0c03446001d40e1091030400b03a42c0d55102100741030300034100200031440e00842c403030010030f01080903086526044080c02e0b8049000d1102821400000d9402c1c03d0303d038460100d01032040d038014010011561222105c8000350482e000d131502403446400004012070091064071400c03100c00000340840c1000700207110107048440a40021f0403000d10790140c00741d0301072010301010307240301004007001070355410001c4c603001446c03003e420064a40090444d22681c40041000b15240101e1115626220180403030710b1480380b40400c80505500b0b07003001c18bc9200b241c01145140e0300985503000c0454071050142c42c1d07641d0503901c0c001d02d904c0c042d5280259007001c0d0091802e40d401410b005a401500c0030200e416a03202105c210001140014424001040da12440d16624428030b0060305180c10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 24309331 1250 24308081 24308099
    0x8010c0e01020a0320031c060902040b0a030b0a170a030306050a180e030903070303050c24130f02090c0903060c070206120a110703030603020117060a05010309050102090a03050f0d030501 82
    0xc0c042001e41005600c001005c0e241e1001000200d041d1101822682e80d1003a83e04071103840d600e0a400e04e0340c4070381004000074840005000b038a098071041c41c411442c020310000160003c02c80342201076003060050000191312411f09101240701c81d95100035003080070300d0749030007011a40203402ca1481005956802c1c4110003000140708200d0304072402c0080d2440014101c41c1c60341c011840ca00394107109400010041590002c0a000300f44049412a442c1001c00c41c000c0180407061b000e040807a414240000c1c034400c0c03042c04441c1100e13004042010b00700b01c0c1600070801d40e00c0c00300d803115072901d0001600086030071f04002169211040508260800003140d000441c10300c0f80078500c1d225048610042403044401d0761050140c10000e2a80a69511241ca0064044c0482c0d1009a004c1811980c43d10101d00c00a640944540c030000d03d840801814000194018003041c3c00503245d40d0350a0003406025250410480c2c0074500030350060541155003240d007454000303009544170401d810320303004000c0190 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 24310581 1250 24309331 24309343
    0x610090603020c070e090f06070e0d0609020d050d05040f09050412030e150703060e0a050712051509010806040606080a030f0e010512040b070207140303070807140a08030108010c0e0102 81
    0x18081c6005a925030140c41060315107080d41c1c1011207003010600c00d01c1140f0b400054211000a190f0b0103580b0070b5552150243c421b1030b51220030640200c05003600000148003a0f1280022620003860801050004d0702c0d1145095685001c00d40802c5000400340141e01844c9007803001448507407400c0c44149029600c4400341c0d144048518103041e2140700303503c1020030511500d480380c041c0d0005000640f42410004010700242d10400150206d07500220f40480400d00806116032000d4450048401001c1207103402080d0081500c0f00b031080d0001c50540503564603500f103000f0480c500090420f401e0a00b000b8003110f40e0381e07000182e164058400c0100281d080100420807507454242043d1004c02d510050340d1303612502e8259201c6051010800040020451000c0d0043c0201d60072a4a00c0da203c90072101e051810708081c55055001b0f0103403000244000f0300505000d80b1030003c112200200c60b03c032031318140c001481101d11283c0840180041e034400d20400541c1006461700200c18048070380003030b440d64 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 24311831 1250 24310581 24310589
    0x5070804020a0f061d0414040605041a01080a020d030201060503030a0905030105070e1e01120f0504060b1504030602031807080a050c01080f0f13020910060212040605120406090503031302010305061009 88
    0x1c442039640e041325906da9004201c4044106240002480c0c1442c0203001042c0071602101c00d50440d1101c10b81018400e0201416940940018400a12507800b0043c80c2c1c002858110b08542d00e40c200403c40d0b0301c0074400f4042002c82a1505014582400105820764000501e10070030031211203200760306980c0720040311056620b40c2100614181d02d00300100c400306001c01c2d100b40c043e410301c203513410040072030f50103903221b540103510410040307216400304462070191032141414540300740410b002290180d401950000006000c0c607921150540700e030b40c2070030001ea0002107545c108021240510801740106c0507486401d20340150b143c5044940c5018004014003080390400741040001e00c010440d0715210040e540040982c00030385030041003142c1c0c1c00080d01405005000b0b0812550701c040d004419101a81c8444d1103960400d50b40c10156244604000c1007034549544441d040808240f01780025405840450a030f0102c00d0641e00001d410348001900c01406502d0740a001520316610107120401d1b9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 24313081 1250 24311831 24311867
    0x2a080f010b0609060a0203090a12120c12031802030d02030a020f01020307050409090609060617010b0d0b0a0506010c0c06020c01110d080103171b0105010303030e03130605031905070804020a0f06 85
    0x1726403510049242d40160301d03140b500031510140110309144000c0d91610011710404000280307001c09030040390019500308004080d13030360094a1007104c600a801000c1840201c1c2c07103040d0008035a400007032030009c5907030f00c1c5c0380560400540101d1042e818000004600003086c020351640c14480300040c12440307184100c2000c0da58070078001003048146d400c2400c195030002c60503c070f40c588444104900c1c003c401a0300544d58a8400200702a09017038038040c00b1540c01008811243c2c0d201e10311031000c0c2c000202481d0421060641000008140100724005041541c0c000c02e5010881c0002505c0c0d1400f01c0d070315601661000c1810829141e2054071103055941c0085444100310100c4031880c00c1d0301840758900c00c07140c1103101d2415021415400300307048074080d0350144584441d1081440c3c89129005010b010486100307410300a013400385008540168640d00c03003180404940c0d14002c200e5506948000003d410b0f07005020070341c94142c445c2c00250540342c1d40c5444480c030700640039148142209048102c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 24314331 1250 24313081 24313087
    0x304060c09170c0109090b09060409060b10050301060807090b19020316050f0c0402070f141002030702010b0a080d0504120221071a0a050909042a080f010b060906 71
    0x8961050700490010b000c60b01c000e000c015003181c0700503101e000b0000582d001406491000850100760b00a075910100d01606900707143c3c50711414007019004405003034400a8980098501e40c0c0c49103448610010204d654140c0c50354140701000f4901c06001c1d20781c1080140301c81c0d00f4441c5070340300c404448880c40e268807440002d0f0302a24040c0e003107001e20400c0328440805803403000300b404004180302100030b422005660403000307000d040100300d0144d61030261024075002030840000301c1200e03103401440520000c8988407580001c50b1420381c1c4c0111031000051751280f42103000d80c1030112201b000b80c002540901030200000000070f180340500d209128200f41c0c105035031401c2d0340358400c130030307a1424441e5004401e0f00902d559403640c41c5200e10079000c0d0030403413036136003c2c5850010084d22254001555810321304550b6000f040200c1c10702520981d80342052540d2132200381e0b86852440d07085001c40c0e012041ca0751401c040a0708001c50318001e030026904049140c030b140d55a0b00f08a9100040460305071362 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 24315581 1250 24314331 24314351
    0x302070b0606090406080d090f05030604050a080c0c04320402060a201006080d090503150a0e010f0b01030c020102030f130c080609030301050f0d0308010501140c03070803040c0503070b030406 84
    0x50174143e4481c50300350040301c441ca804950701114002c2030358a034003208102c055039072042c10303030b07403603003100d014020ba08500c8010001030f422000900503460700c171003155007106c81e01000400b01c6035048040c03100c03070f9203c05a400c401e01a820039082c15041200c2260003528142d001310350300b4400d030901c2070204030403042e03944100c0354907030070480060380390508962651031224440f40044c4014080c80c0a130b48103800000020306c0c454001901074560180140500511422003120700343c0001c0c0401c00c40c242c9030000d14103200d03001d201d801550b0460780b0000c148010900d00140c11104400340c0ca104690040080002140075001c0e0300b600700c980c21b8441640d40c6058280421039112a40108241d0300600b0140400c2e031900102541c1603c02c12203145c210010207800700322404544420041c08100c207480100695806003116220b10b4100307145162030b01030b28255890965010140440d068071000c0103000c14004e00f54031040141c90181d001344002c0d0b09119105a450000074001000c0c00d8503980c1c486 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 24316831 1250 24315581 24315589
    0x6030114040204020c031e0a0e090702030a031d01020d1b05090f0d0203010b06040f0501171e07030b0a080a0b090109050601030b1005090106050a020607020721021804140d0302070b060609 82
    0x1010010480c0c4928a001c7d241054842a80e10140030360000501204e0070000b18a84001003034059100c503001140380c943e840750300b50702900b140003880c03141000061503078900711420300003401c141e120010000340c00844198072800d0415500042c8003040014495070304030b40c8614001c010180d5003103030341c10740e000a1031000a0241c0040594250851808035000034010000d00f124010342e00242c0340c403981010001d0300c6124141007180c0c0245034401003e02c154040b205100c0b55500075200e03150100740240030101041b0f071007007258043c40d604e13444980d050080c8128940c0864000d041103009100003151034903075a80d122810300000c0d198164000201d00c2c10110404100010b00e401b803d00c49240da03440d980905585c20040c00000035004200000e06240d2000c01d10340142d070031805480302c0b241c84d040a030300403480c400304049810501c805500700d230000240d1040c62041d803048060b8000d0240da10030740c40c144030a8401c03c2003414010f03c481800550044003081e80510150307046071300c2c0d03001c0320006 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 24318081 1250 24316831 24316837
    0x507060902040204030b0f070c020105070f02010c060614040608010b030a02060d020c01050f09010507030c08150111100b030706030204030b070e0f0d080903010c0207050604060315081b010806030114040204020c03 93
    0x81d805480064008200032603101000c0c4155010503241c6d00641d623070042901c45c490014402800500200f242000050707443c001803000f1030043c5401220440b007682c0e2034040350013070740101c04c1c0200c4161a00f4590328040c0140e070050301c0514001c0c0100c010100101e603558001001c000d20400c00400c0400706001d507a03064035400c100442c024030480c10039481c81650b0a800307462580e059400c0c80001000d5500900804160f00c81c1755903412282e5580705600300b04001c041c00450b0421103400301d12900341000704094908851002e400062502d081030825281c01a2907200805042c0148002c0021546a001455000116003420100f000700d00f400141c02c200c1010159500c00305403800c0d001804480406064a44000d134001c1100380428070003a80e80369828441c00d0b920080401003481507612a801c400c070b2505218100016a40c1c541141c2e07030a1518115030780d480402d009000909039a03012000641019056000300003488205a00c003920b04070040002c0d014035000200a036070f080c820070031 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 24319331 1250 24318081 24318083
    0x405210a140a06020a0816030209180712020c0f06130c0e0601030204170601050a140312070c030b09030c01050114060a0c0215040b030f060406050105121003170d060b0306030d05070609 81
    0x710f6a90305d8014000e082154242c504071540c01c04001f405014078000d100711120308100400b000e1008600750b030000e144034802010481000080c044014107048280064540820b451019110f20846001440e2034034200500100c803032a01c0c071490308049489080150155821001d0b80c209581c0d41c100168064816584203100340b00e06001144039090010841d141a00d0302110042003030b940c0d480d800542c0e40304166007258140c02041c41500401e88810082138540c0c840c5407200811540e980303640c190040101c841032896040000c40e2100c54400380300b0180509540d5941010340079004000c15000d01030a8010300510107680c020005540c1c40c2c820002022507007041e07080d91242c8424003500160400d44411945180c082c011880c13916181c0140c0c0140c43e010b950b602d0800d43c1c00c0444000a0001900c1c240380d9460a200100100c0d00c18600814045000c03202c40d981c450512510004542841d0710590009000f4402d2011640c0d001c075084400800c1e529002e41c44401074107280005000c01c00c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 24320581 1250 24319331 24319343
    0x11030c12010c02060a0c05040e04020d0203060408030a111602012706030e01110c0613060e0102340209071119050c09070507030804021011120405210a140a 68
    0x880000c602005400003480541c182d4242d0304542c884091120950340042407840c042102400b051210b0500421210360050000f080a519120b458021900342103040d28141c030205000001c210000440d40100d064034002c1c42102c1d8507200800340760300d80b100c40323180009040010719214003d030b03483c1941041855031300c5110103102c001d41c1e95001030000d04000380c00131031035404e001e06021015130100594803006040c10290140b580e48070501d00518540e0881150013644c0c400710081444000d00c0034000444a072803c01d900b04128a10300c0c0840382d80d480c0c1d0f030114403450510072401601c942540701c1c0c0100e010704110002c407000461803403c00c100d03018464160044c0364800d00a0280000703e0410a4009850400c9291680c2c01d0442d05c80c8507440000e03002c10340300b002080040c10290100c0c0c1402039645006a510103030500102d01f41a00008614086400401d082c4114600f17280800030f102d00c2c01c062401d07100707102e0a149441d0381030144040c0c00d000c40501c401d80c040100b8080202c2042c1e0281c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 24321831 1250 24320581 24320599
    0x30c0304230105090c060304080f1321140c010c02040507090302030a08071a0702030301030206090103090602030f15040b01080a0c0c0506070305040c0b031302090615070c150807050711030c 83
    0x1078026402890100d8405150b8400d03003458411609110044901840d0801002440c0205003520711059502024035103422100800d0006107004c5249812100740380800f1030300c403140c070450600c04226910035104c09015084082803842c01c4ea0408200c01c082581918003103816590b240d0706950035002944041e425001da95aa407003049007150061101a219a00c641070303d0b00c1c0007210100d100801c840c201c002da44200700500161405c00b010f800045030524001c40c07403061030b50314075041e60015207054465403543c3c000d005ca1111b4030385c82c0485110007610108441002e400000300074010203801d241210781c4c1c940501580d02c3c03040c440d01d942c80b90048115103484c10b100743c00030f005040c11501a10b4510044102096440303455080f42c7c042c4d1003140440305156045d4080004c0440e028081641c001c0341624840b4108421401410000d4003e19031003070702d1480c2c0020980140f03040038a04d03007044011020411050f42040c181d40c1902e41104803802d5850303003500880c1c0b40c461180f08180d80304401c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 24323081 1250 24321831 24321893
    0x30e0a0609080d080f010315150603050613020a020703060509070b0705030c1c090b1308010c050c010510030b010b0f04050612010618060f050903010b060a0c0b011703030c0304 77
    0x4a00900110b42011084a0380030300d200d1003c0301c15070b200760340004080b0384203401003021848a002c00700101c0410180041c4e10701c0e0303449d40b0201d0030405900407008a5260010401c891a01e02012090f54095541c150f1404c0034000000b9103400c0f450200400240d95003001c108210410030114020b40345400906507105143c4c02c0c06a0b0365004140c0d104003a00c603060030319401411000303421075961031075216030b11030368102401e10144c2d401c54040c0300c43c01c0242d4a4001101700090107242e00500304c548a040e520044204038a0a440c0b00038003074821030f5100c100410004e06c0400519044030400300140d501c031f180c446442d5015210b5540b0441c1d000d8404115400902e00340003486040f103141780c885a8009206d480740c00c00030f943c203200b0700d000310f04002251500e90740618001c018090004000182044400700000c40030f4002003400000a0080b0744450100110803603440e0141a00c5000220751a4440740e2940d40c80c0300052541c000d2040c04408642002016207100980303e00c001c1210085100d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 24324331 1250 24323081 24323087
    0xa08100c030b0310061a040e040303020f07050a111201020306060304030f050d050a0b0a06080610050307031805010608060108160302061c050406050405102306031204061116080a02010c030e0a06 85
    0x4640248031021b481d98608035820440c0400b100c0c00c5075040c203030900ca140d4854500b0350003074012250b4240c841404000050004109000d00401a8407903402c040c56454024244100b403101c0d20340e004510b0f072040045c0030899503410141c1e41d000d46d1615042e0704841d43c840d0b0841d482d000d01c220580c0402d08010034003640013a10381215011010654a50410030340c2d1b0841201d80c1c1c0c805071100c54102c41d82e590044081c43c03180008643c021220304010403042c40e034942400d00b460008805650995550300280040241808000d00520b64600241046a40506081c40500c05844024030612000451603140c8070b06011038444581e0800c004c0105203004e090103009408101d80840d243e008004440b04801101c0c4981d400b01c4240d107184140d00007403c88036050b000c0c0c001d020282d161040c2c7c64032100300b4598200a001401e62039a400048103e11741c480d070f203000c5001c051503125440a4100f0702502200003440e101d1540c0918000040c0102414180e44c440042002603800c012580408100f09070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 24325581 1250 24324331 24324341
    0x6090c0f091311040204170a1a040c09020a030b061911012f0405121605010203030106120b04150b04030302190804061115040309060206060a08100c030b0310 69
    0x4000d54480a0118054040000c040c0d000c480c07010b50010107a1a00002c68040c0300e40518020020784014500b0340c959810200c0c080070303402e4140c110340c0584802c404210015000300101c411341c149522513410b090b0380750403482c04203000d400740480d1f000c6000041c480c8130350090210110080c0c102c9640301e4001806510964080d0820004210001a0711112050501c100880b4907885050240448515881006400c2c6042034046440d04140004501582c0d29022007809548060042905c209940341c942c0b0601e841c0d5000e541950428401003040303680100e004074080608c000001602a8018001401418007915086000f200c01a0104950610400500559000b5000c48560b42e0300e004800d015a00450001011040140000c1000c9401051100d884102c080b040d100c00b0754000e8140e20f044102250b05600142d10340d1020000c2a8040c040c2a0304980e054641e11409424070408030381d15401c4039240e01c1600d41d071301d884d941d60b140f10340c1c418a0080e20040658108041c11021600501 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 24326831 1250 24325581 24325603
    0xc08040203150126070504050a0e0610030b0402090405150405070f080703021320190e0102010b030a0b090a05070308090f010c0302070b090a030501090501060608090c0901050d060e0609 81
    0x441042c81e188008182402c042d4122608480349200f8107803d00780311003100c038040e0202e40c024490f11101180c030f5504c038082d0358420340c4c0c441400140b2008006207585886000380c03104040311520002800810284105507030f00a4041c0d9040100385c8488c6040f5143c0303001404c00d1080d50030900c0901080040c0400c2c60b5044684400e85d80116984400c0745a4441e039192000960103d140c2040716011009900030b0280d203070700011200e01080300d9109488041e0301c401c4104551054003d048040b15411039080c0744680800e1008010004284012a60768854440081c0c4080ca0303001c0050003002c810410340c1c69036a80002501c1c28141c1d00c0c903103107501da0041040c4c00e00c01c07400001405c1032540300c2c1000512403605035008000191612049503026841128002d41104030f124003c008a00240905140039204000000d40c0505d88a0020030808000d40445407035041080c02c82c0700b0f81d03038034290503065910803101c00400341d005103021030003403422007103081c6103000d00400c1050080e03010500711000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 24328081 1250 24326831 24326833
    0x140604021e030601050d03020f0709060501080106030c0c0f08160506060906030f1c050409020f0d050106050309030a080c0d0507020d020c03070303120506010201090209090d090e060f0907020a060c08040203 90
    0xc01d446800d0030000d40101e20254265004900400c600d2403c442e5540c9183d000e801a41d445c0c0030800c403c40c5c10302040350080030980361280c0e4200700030750b4444010341c0144400c1c41d00b0000e0310a0984010003448030f607030300600303968682c1c0f0903542444015002c894440c0301070280c0100c864030901e0000e882c1c1c041110303483d215820000015030f131030401040024100d600071011300b0213034030001041190303a0764000008080090074440400d140e411480144a40d55140c0c4882d070300ea083d0010700c9015a84141c21402c100042442403090004000040c0c8007081020308001d500c070f80e03c060503041c80d0b014a00400640c0d40c1440c0900056540110701c170441c07908907909941d41c109503038051595541942c0300080001d440c11890243d920f00c55486640c01c20380520022070400d1950300010480740043ea80c194030b507000ba05d183c0c40f0043c0c1000382d40004011480d260000c52400a002414800203600c1d030034041d44e40480050003086c800c0c0301403104a07500c00003c0044d0100d000000f051803404a8049001e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 24329331 1250 24328081 24328099
    0x60f080f030c0303040201050304050a080d090b060409020307090b01030f060b0a11010213060c0f060c05030108161406090a0b07060603020f0d050703020f15040801050a270b04080714060402 83
    0xc14800807040702e4402031110000c6140d0784072940115010750000300107451a01824040d9000a0100030040c030801201820100c4d4484181c1050701510380007070f0690b48034500c1e1551450050702c011504d003044401c0c0d00d10000310140d0070300040c1d028041d4998603810241c43e2040214100c4400d034098005001d1070b640d000040310408170030364200e00ca02c4013414a5464414010092144113010000c00544030700d00b96014200255030744010383e0184120080810004001484000001c0103203480c003c030202e00310005140b0f44071306c844646070300d006100d004020020786804540c50303c5000c0001051035081140da1443e581c24404000c2c43c050008903c1249081c2c1400076619250b0064410a50814003030700b905807541c2e00f0041a07441400782c407500603d410455012224040c40604010000100046003900d0081c41c06002c503145074107649040030040c0c0340300311402c0740e5104c06000076501000c58801c2781c903076051500d0a8018150000c1201c04916201007000f0b801185a9004074801d41319124 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 24330581 1250 24329331 24329353
    0xe03060a141f05060d0906020c070602010b010203070c0306020306010e030706030f0506010503160c020f0604030f0506090f0d0305090304030807030302090a050f01140d06050d051615050409150801060f08 89
    0x80c0040450b000c01c1d54020454106010a1601a0040c49644030300c5100042c228215501e030020398009501c0c04009401092082001c180c081c056103005100902c042d510b8040d0760394030b002d4980d04500000d000c266002c00090303e85d9000b10b04e22140e509004044032007496556800802030100400a000e0550a2401060082d4011005c0c2e03409030071803c1e06050403213007151007203130b0300d90a131794080ea07210001c03a01c40403864448200801c0590302400c000c408040f0a0705003189492070250000700650310404000e900100c021882101428032450045a6a100c4041e4540b0318090f42c1c0020f030070000005000700c10990154014146550b0948500000c1d170b81d580e041010804655500c2808140204502280070070842d00810080220000000c1c1d40390b2180045284904052020ce0310756100010740003c4242460034036000340000b03500054050400c08004001740510703c40c136000140c07246903a0503880041d058440c05000741d1070013081440d6807914600d004d0941c0d03100c3c10819000e41c039000c02d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 24331831 1250 24330581 24330601
    0x70606080d0e10031e09020906060c060612030d051e0610120209120a0c18020c07050108060111010c0504060306080c06040302061b0a111e01080c0a0e03060a14 70
    0xd40300805540b5080b8900e4049400c1c000503801c8071800a007011364481c1c5440802c00b00c0302c2c8140c1c98603a40140004c80b00075605c1070025040c0302a00d00ca02c919070a000044400e14000313000e03503010506580004144101142030f61075402186426030300d0609050805c014072410016007078003812000c03e401c1e00d42e262101800840d44880d6507200000303610740c40214488156030010002c414000d0502c810a101c1000d005051142811045a080c80e0090081050b54803000c0700c1034083c0c400d41001c41c5015001d91002e603440030140b01e6903040c0300c1039030000b850507806010400c22480c00680284043d00c000400188107502c00d004420120f0701d071003c01708084034001000103e80d00054400c40c0b5007415502080001d40008003817991907010b40d5900c0c1d02c920028403142124600c41d90300c4041c4075a1031003c10190464044446280e9500c900500c003031683d2222002d41c00c0640602c95036990180b555040718001c0840540070307054401c407403d12881c4102588100501515080311a00d25294640e6030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 24333081 1250 24331831 24331843
    0x607080708070b070f080f06060408120306010314010e071b020d030e030f030403080315120a05100f0b010203031602010209150910030e0303071103090a0306090c0506090d030c0c0803040b07060608 86
    0x20705c002444600000300442c0c84102d5458012200904450509a5072600c9a02c0e09944903a20b0308000350100c2444243c1d40c25000304c94080030300088042c0558104a1000c03a4148010800720421140c00b1005800f034102c9401182c0458010380000d80d0420305041c040c080e0320300300100600074401c0918018200c1e030003005440c00c0d00e5000c504e8901e591503d4024040b0107400d000c4503948040315010700000140c003000742e0560240710390f014080011a9902400c116007a80c992101c1c040e0174890b883c0309980e40807044984c4a00340c110185481490000300320300a020390007400341c1002c110203496450209440251406020803100c8503414116440c0842c02e840c0c001c103104142d81c0c02440070440b03290090300ca80c0319240f090011681403038280000144540000e901c0be0798401d540b012030b80c0c10300c00702c403002e40054001981e42d00e2800303142c0000314820f01d0b4800e0001d4204403494001d001000307102c0104400a040b140100d81c0c40d241c440d80c40144030791007101e08844491814000003114480400c1c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 24334331 1250 24333081 24333107
    0x20109080c01121a03010606020d08010503010b090a0504031418040506040c0906052101180b0d050706030b0a090207080a0207060c2402130801020a090609050609040b0607080708070b07 81
    0x180010140300703e080303401a012080981d001036503142d0ba54503250303d00344602c000030040b80c1d000300001030f451240545441410381155000b40d0408902010b241c60f07211071706801c2040c9000000d810385d03480c1400c80740091401281107014a001600200c0414640e4150070386130000ca404010a41340c07142040101c1e0300600310500800c1c08440100040f80c000d00281c159402c50a01c0780c03080554161079100c114009030041a0f909524451001e03c00d1000e20507030340f090409880a1000d540282c440b6540e4680300e10541040548940221642da100c040f4400028815100c066480e84c825242c5000340340c01c040c2c8000010f210311600003c507188200c100404290700241c04c10300100c50700c2c03511340d90408280904e8146603002c10855502c82200707a030300001000650b00041e25001208801000c6039850790202e01000890b82d41030000780e441404032000e00200f02e03000516100c20001181c0c160007001030181501e50007280032018000d811004090581c0303c0c01c0d140286595800c800e480340408494 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 24335581 1250 24334331 24334337
    0x1051201050616050609150601020a03021b01020708150f060603040f02040504140607020d020d02070605030109020d0b0a06082517040314070c030c0e0405120d1512020109080c01 78
    0x1000079052180081400780d40f1441e480f06103044070349400c0e103000c40c20740f0280d0f00c0b070340300081c5660748080d0342c40269007103142440589603100ca961802940ca0070180d503000400c84a4070441c00f0f07543c0c02084000002d294140c10b59203403050031108a1190402115000d82d040b14a5002400070b24103070084922596000c04a41d181d24059024000248070003081210703a8105184e4001c504a410080c0512400c15a80100580b0105410080c1410385104048080d03604c204e40522031581c00c9070607039040d140c40c0d840040c2c6592501c52804050000d4400fa15005410440007146295000303100310311894085403404002c9141c0201003000c05011154000040c000d10320b07400340c4040000300e41d50094003920382180e520510409400030307a0f100c2e01e0202c440110304c410030000c021100c5000401000308405011507031a007a00c1e216100c001d0300010015201c070000307000d507810b1125405481c8000000c02401d42280d140d258002c8149000c0348140e000c00c4c103580c00000c0b9002d000a0403280e9110686d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 24336831 1250 24335581 24335617
    0x9030804030c02010306050901091e180b09070306020a090f060207050117040510020a0210140106020c191e060e190b07050102070501020307080105120703020607110f0406090b010e0105 81
    0x40c404441480890b1002c80c100358035040c0000d079075901d02c41050301034544403c00103882c12b092440c40500c042081c00c0008024200b00030703403070034690341c180400341903400c10300c5480e071a078682000310300b4540587c10003012144040740000e005039003c3d43c01011344450109000119440b000166a100654800c180c0021440008038640202100070680c11511800031030354540c4401c000c0c9010b03a041a03181e140164054040c034090036045020765074fc2c007903052480002550500070001e4856807640b0381320b40100800400045617512650001000f484503100541d0001d61201c03000e14040c19500c41d82d00018504000704000f40350112010503080300c941d10011109180040f904c00d1078100ca038060310603546c24815079005c03407420300003103100f4102c5955200d110743c100801c002000b049078240d2841c59103e44411310045e01d680c400c6420550300004400c1500c2100c8000903d04010351103803c0d003060401c4400600219507030040b28004c80240c80c1c180160281c2d80044866000f848001d0000c0000c2d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 24338081 1250 24336831 24336833
    0xf020102072013060306020d060e0603151905070503040b1f090c020f10020712050c12090d150606020105070201020f040302040b0a050901120b060d0206030703050c04090c03050f0a09030804 83
    0xa58000402e841019014003507401500d902c00045900c50351054800540000341484016214810b602c02381c1400c860b48030040c01d00002090790381e000b102c83d44243d1391a140c082445d440e10395510040580200718144054640820000c0081e0401e0350102d8110142c0320100d10000902c403640c0020031200303508a070b00707140740003c40c0d00500808005132055000c1d505605044001c14080c1c1c056244c8294409640c036041840c2504a484160404004100301400f40030800c10380451081d4480700701e50708180d1a554808002a04140d081034010280d070410400da0b0f03161180c0b03402030000caa1064008210960354900180d00740d06c00d13111070314090481003101380014500342d03114071400321000d0140c00c1070540b03880c04110100e50a8100c02041d04680345888100b1030440d80650f03102c101680c882c8900c440c01e038041001404060484028142c90700f00240315042201e050768004d2986200500480020701d0f0301030002c20301641c440070700301c400d00006100700d81c107800340c00d42659155807400c440d9034603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 24339331 1250 24338081 24338123
    0x14040f0b0a020f0c061906030510020903010605040c120e06060f1201020d09050f0d020102090d0b040f0206030c07031e02070e0a02040f0608060301050703090b06060904021c05070f02010207 83
    0x74102208540e090145100990102000e810560f042200415081c1401c10003404500340c000600d10603207092a03000e00014034040380c028001001e085002d07032190080000039001d404c59401140d005483c0c036054008240e4000c29040385103600a02c10490011014011a201c0500715421500804415a284042e00b0702c1003031308500d0545140018281300300d5003602000d07110012003d8929500c400c0620304025000d10a56070b05034581d0000310319103400c07000402c2441d208200003074000001500020240640c4060540102d60700510441d52031a0100c1110f00036040b506065000419a071140381c0c0c0812050802140740c0c032540c0003814400e151004610381040000d0a600e451070702884001150000b8003240b0700540401c2e00c0c3c180b441d1414009040c21210700912450400d4203110354600400c041200c256080b04064600710b960391240c101040180c42500740040400c03582c103454070741031070090f8040b0f03019420780c3d510201c021740c1a100807400d074054000060001300044010b0612001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 24340581 1250 24339331 24339353
    0x706050d021204050a0209010608090606010e120601180605090c03180a050d08070813020a060509030a081902010b0306071706010905040212010801060b120f04080405060304050304030614040f 84
    0xa03824001620b440410a040b100104094034201d90340e600200200085140c5030074000c1c00740c076642c40c00040070302d0011116580c4d100050541c0f0b041c04a04242c20902e5180c064903d036241c894a41122003950b920405040c09404c0040e074004298544200894030345042d0354040e009280c4404001e085071034104000004010b0702c00140309610402c0305e6000043c0d4144846412500c0c540c9030031025240118000d000d01d40004d140710300c0c016810b068000180c2e254007040b001e0b80da440c9062900da4040c0e030003280c60001120340c06040e00b440820040102030413030702c0500c00d4000c20f60003070007500801810f15503240401d40c1c0f4000410491240d1070301107401d0f114445e40c0481c0514001000c2a42e0700702185c00c0303a21041e4480c0c8028071403001442442d00134001e900041812008036450001d80d66240007103000c0280142c1c00004d0444045814003003102c040d1000f074240104542da50341000c0c6022a501c1d40070740b2084801a0420f45407400d02212940203604c01c84c4c10682c01e800c2030156945241100c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 24341831 1250 24340581 24340597
    0xc060b030a051c08130305070f03032403020406050105120f0c09040c080604141e060303040317031902040f0603020306030a060e0d020f030f0906030429150d05070605 73
    0x48500c2010300d01240041100d580c00304000f100800c00c80e84140303001403000c20024490014014082800b90002c0c0d4040c0031204403907041505096a1021441e040300509a5150f8500d6100306204014102c0c4400800e503500b200d20841c1c00301b1950f540d07a0b0056980c8d014844191046114410024041d49450140e5075800308840001d0352070105142c0014048582200310400012a81410401c05040034413511441d80c1c2001c8001e422072404440313203045c4285c0183d0034142c40040602160b01a2070030800c5d94065a40400034281c48240c0d8030b0042107a400445400150a031001505030b00480e00d03100f1a03080d11580515190301d242042010ba000e540701511140d0544243e80c4490041083c5206804150348410040d001030191150000c2c44d105a01880821030707001003207200c020b108900b040303803010342d41030325056140d503145d081544080c02064035060b01e0140b03030302142c1e000310506d850451140008041843c5100307138031003d1001c1c40320074880060440d4005201400034a000d00c002c4c090503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 24343081 1250 24341831 24341833
    0x10509010c1406010b030a050f0108121605060103080a0f0e0609040b010e0909010f11030c070308040201020a05030c06190b0d0b06040b042c03160323130501020106150c060b03 77
    0x5000b03460040380c03800c42c0c26488040300716008010f0048206260048036040001040c21456550606004d10703201e1a40b680c060001d0700c00007488030920f500304041028101e0300003094914540c0c4d2408d003003000d54480240315000580541030010b56a000b400300c5241d500c000340c04203042c60061410310004145221a03d418443c00309101d840c1030341c2e481c03400c0e4070551000d0004100845031011140998080488141c5a100c0034400c00000170381e50740070340c0c0d0056050310380009103488030700040c0e08190482e800a05603010004151050a0000820500412400d840f05d20740807103400d03800089600041c01c45a11014680c00000415401d05d1200d070041d4008000081d9803a410b80040c04803010141c000c1c40030700c0070a070300000880b00d614003841091609000355244c0240780303120003d8404084c0d00103040c00304000545003001042804159000d501ea5080d6135103081281404203c003407240716140c019800c080000c6414410352025040c0f820141e154980801607039510303e00545402d031165a09 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 24344331 1250 24343081 24343103
    0x206190b060c0106030b070509090a0f060b12090c0904080712050d0606030b0306011205030d020f0f031513020c03040b0306030109020a06121506050712031b090503011406010509010c 80
    0x1190381d50401009070428240000654034038603d40400010001803100081c410113104551058840800b500e0780410300b4017001840c404038040e03543c010007035504010300200e07002c22030000740c6070f51803009030003298010101c03240d0103000001c00030b400c035007245e0003003c4c0042805644005010a036000d8940030141c03c00c10b0a090310240c1e8141211056804440040e45501e00c040d4641402e001c2c0c00c4c0503180001070b400f9181060b4440550364440c40c0341950134103500041c4860448075110030764014204607003043c0d90381e0034801c00c0d445606000719510b40c45104214010085141184220b98403c00302e030014505140c039001000e1020740000304030707030b40554942a0301d00c0169152102e00014088e0354480700003440f00140078a007210401d4007802c191a40e6007030140401d54016094a50083e44185540c4960403071400850140c18803946650715081841501c0f07980756040381901068a90640007000410582d00701c11654050940c9c410740841d4080000b0260355105a0211465500410301040 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 24345581 1250 24344331 24344351
    0x5100801141b2a0a060f050601090315090206040905060108071e031a0d0614010b0a080610170a050601020c0306010e0106050307020a1a22120503060307090603060c0201051303020619 80
    0x340b98000c681c4482481d82004c007400b0108485445405481007008038100400e00d000c070f001800c0741045000141c400f0380b07000700c3c001d0051540e4100c0a580f44d40a0041516950307504810f102901c825540c140c081400c00b000120690311420314070300d5000508092083c4d030901094280c00902400e009070756055001c0c1040700b1070b5203a01d004418458861040055009450200200141c1c4180c21138500c0100c2000000d905a50050440f1341004bc04c907a05845900030103400c2c0d8803070b0216404030141c040365004104480c941c59105510610080c3c0030ba45c000a820420035458803024018001200c052000611a45100d00059548003015004641510105843d020340b060090380710903607452182020880014807003080801040c0120480d11000c103c2c0340c0c3c802110710040d900005c02c11101100003105640c08010300ca00800841d2020444181c0b2418010041c20315901c0000140d0309143c0405e0b40c151755500000074058140c4d002e40358580781c1c4841c0c12030340104503581000c81615070305000c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 24346831 1250 24345581 24345637
    0x302060306010e031e010e0d02030a0f09080d020a030e01030207080f0c121303030e010309150e0304090606030203101401081807091b03050a0203011a1b0105100801141b 74
    0x41213034200e5221015405014440c2807e641190180e00c09a130466106440d005800105a032403100c20742c10b01e00d0341c00c09110780031244403440764480b41c204d1144c1098400100e8010941c2900a8003c0d501c82032002010f00065040e84521040244012010840300c4290034202c0050684124081c0644d02c52542011807403c1c5030304020302542814100784c0007001003503000020f400841300c086c00d00f44070b20300c2d19494030031815164004502e44291501c426080c1044240201d40103099000020400941c4a01000b8029001201e0301084803500900206103e22585e1984405501c1650303404810358400480128241000403030750000e2180c0e050224100c03005004041c25500402458004080c8607013004064460250010222510401c010b2203500001c0b04904184280e61080e2650380800120240b0441c8038000c03000115440c101c24482061124440c040c1200c4420000f805401e850354000100e10710152102210415691848401040840090300002c030804c0305001c0c2c041240e0100d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 24348081 1250 24346831 24346843
    0x50708040e0412020d0c080304060b0d17090103150302030c130f0216050d09031205070c03080a0306031203050606070209090a060e010b03010f0b090103141608031b03070201090302060306010e03 85
    0x110760904244441030380c1d03154104030007050348005142040c6c00b521030380c80b4015603100191020700407a4443c0505083e0762a040d80f4010215441524281c851545030131201b00c0c0e030001080076001070300b0040307090185008215840281c80d001030151018006181c108903801024520091080381c03100f91a40d1912510303c060013001c580810411440d2000f03185c60743c00d0001c809204028011800301c01d00c0031546121481a10f903c40781007013665486941000e000c01803180c1d000400c00701e80022310415259040d0018400c50703109890102500000480907401e0300c0040350025000107080c041000540380450750160400420380c00c0d1160445030761558000c2d10300e0600f07d000103a4480c4240b080b20300b0244101c00c5c010080360002c11214200c80b00094001c4130600c40500090440d0078484000d150038400840031081c0b420f82d02070040e640f040050340340d402c0b00403164046481e00113042c43c010004070840d080c1e00d038140e56018006056500f00007281e08090000b90402ca611000844143c40401c40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 24349331 1250 24348081 24348083
    0x60e1c050102130603021c11070209010f050f0303120f04030905040c1805040b0604050405090c210d0f08060d14010c0e040b040204030209070e0301110a03050406050604021801050708040e04 83
    0x240c0c0d83d0b5640f080c1203800c040194801030415204210103d031003031032040c0c10a140320240c900466684d65403800c0c12881c0c002d02c04040d44c0400340f00d00015100059003204411a50b05540500f20300f94008201902c2c1e0003464104204040002c00041080041020050340a446800c0882806448401180843e01045042e4000c550f10042d56040d102c2401ca0090050000322001e200b01c021140100c0c003035015620070540202c3d15400031030a0304c14244000d154042c009031040030118810200b5030390030803918112200500600012540080c070880b104c541494098850b2411622508140300da140342ea00020f46030350100425901040c5001e001c0c680100142c0d03501d16941440030300401c01141d11008045115510401c420001030701c0ba0640158086464240741c0300031411200030901505030f0021109000400260020016070158855805203008800030001a6a4032062100303c1c41030036100c4030760000c1440407a56642c0700300009d01c682032154141d40d080c5540c446e20706485036000c0e07038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 24350581 1250 24349331 24349333
    0x4020a120b0603070b040501021207020409120507120509090f130507080d020f0a03080c1806030f0406140c0d09030e030d0302070506090105010b040312050c06070203040501030605090c04060e1c05 86
    0x10a00c082ca1504010900282024250103031400d498240042d40c0d42592011050074418081000415540c4550003c1d91050700b0024402c0c1210820074014103a80c0150001c031284503c1183c5074000c140300ea0195804030b00003608032a4961a14180300c160000020b00d040d01c0c0c10050b03004103002402c2440154004d210010060100d12291003000e400d001c00001d4034103850f480b03d5094000b01c1e51000100d078200030480042541c0725160b5241005001c008240e49403c908004240401c04000c031080500c91070161104001440b0240c00d28840d0040550340f04180c000c09028680d1aa801c0e43d100e01d12a92281c20282800455030700443d0401c0c040201803400309901141013800c3c4035040c04110391107650030000300110f604042010180b07000f2030001901c918400142d200d40c284c090303000c480d295042c0200b203450500c1c107900025601d07840303070003035900103400c003500042d03107062280c111070240c0140c0744081c2c24242021411106601600035481d800a801128084001744000c502d60740309001308 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 24351831 1250 24350581 24350603
    0x9230d15021b1c1e03020c0703140304061403090a0b0a061208090910080a170706140103050c0a06020309040506030111030f090c0109050609010e0a050406080120030606070b04020a12 80
    0x844030300c1c203c903d40008820310100030014952042e100d040c010000f0b00c141030041c0c07118041c14503a0f10304400c0b030300010003045801c1c0714074500c00c0000003d07108442066403400d541d41034109100c1054041540c40c030646034000c00880000419140352903a00c40e106200c00901c8517503400201c600026528000d607842c0b50b00003011080f50a00c0c1c00e0580e441a042d0301c00701e07a038038a80240640d803110494006001004078407407001c0007955240403140003640080040c8001c0030005040c80d25628280b10403500c43c8038084102c202810801c070350394111100c64000c0d5090104450a01001e804000d2000b607155590b003850a2200f1017050285019091015003c00b007480c00c0e410007440d0032003101900b4144034103050304014550300c1c0c5040b904040300070710340141c903e01040302281c01c0100940110f0341c800d050410114030204154488180209101c421110a05481d00010380d60f100035911142c200340204024004110240074081c0c0192000e8952000c4130340e9980035081210801204440c413150710 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 24353081 1250 24351831 24351853
    0x30a0c05030c03010207021c030201020d0c020d09050301050123030109080304050604030f02060402090a09050c040501060507030e04020702010e09071e080106030c0806090a0f0902030d09230d15021b 87
    0x4000c0c842c68850b00341c00851a00b0281c1d000589007558022524440c0e515990344a41014401e4041d1100100d815006014000314440080c2d04d4003400042100042c00500c0b001480e482c0501030281214203500640381c2c10304140300c48114503510310441d83c1d003540d25050443c2c00141c003400210f100318000c5024060740d00f400e1a00a00c14060f071303070480341150f0240e8140703c0960307201c1c104190041e9001d4000034416416291a43c248a82490107646c024030704000041e1080c1c10000410380184680d40b0000842003110400c001ca01030403e02a000803070103040340b0f43c1400d020b4580b54000d01581080000d544100d88070b462510340b045030700000030300e1800040002a40500840641c41c00314200141e00340b038000085174051400819400405881d41012034040002d944039071800c03600a001d5543d251034500020344030005505c00c4483d10b14801c04040c81c440d5071280d4072200441d0003000d002401c40c00c2c0d142c107140c0c1d548202e080c40700d083d820800c05c12141c00e10412940701502000140081c4088 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 24354331 1250 24353081 24353083
    0xb0307080c030c03010509090f010903050306010207060302040806011401050c060408130503010b280302060408030a0905060301030f03030c14031e0a09020a091d03040f230f010c0809030a0c0503 85
    0x20300360707640182062007880402922541503e040d00d809580d074190030340e070343e07920f040c500b840a22034007401d5443c3c03030502c1c3c09241c1c0c048021071058200ba001c6941c10307551414100c08921581c8640d00103900198018000f402e41c560a5100e944014034215060400f80f440c90303070518800303440c100c80c44000006c101008010003d000001000120020010082000c0c086403000300b09412031020850544550f514243c6444411401b6507000780c0803540344c0f40c91328401035880e130009100318003060889a00094900d02041124140c0e94041991405984203580a030b0140c5502c4020400f40121031000003504034914016503c00c109240c45d03180c01208544076051402006041100b07030708c0c100441400503840c3c1d0054a0115107440314001515205109028680001010150076900002a00083c090f400d907030050181d40020650081c02c2c00b54030b1842c0011150040f00541010a05c00505c0b00303980141c501000142c092a0303000e291100d2100001e06040490138100c806c4613821b02e00f0310040c20 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 24355581 1250 24354331 24354347
    0x306050405071d04020c0f01020702030f0601060215311103010b0a0e0a06090c050c0c01050412031803061d100b03060105060a02100f050105030d030501030b070c020612010b0307 78
    0x1109940c01c00c00e90501200003040d0248140e0404090010952100c1007038903075034100c0da1851b50f1300003a5135000c8981c0c00070368045e5102e00420f901c070344505210000340c4070300031828a04a40c4280c008040c8041d1404401d000040000c007801c001e41d004c000c4043d981c0e503400718035941e2001d60441426000320703180b4144036091070400340b6038000d83c9004040d03842a124003644100f541d00003d43c0d0032a550311902e042016041d1a0401180306051160407240c954120018004000c1e1070002d55a00740340c0e04004580074020745c45603581a000711540103000c01d0240c46000305d811140c04049980387c0d00d0b0f4580c1800d0f00c000308141686030707401e00448840764505000b100c841c00041c81013884a08490000240e5481043c050701e0322504000031501d40c058020070464400001040c0280224041814018020f010074070030503002e03000780807004030414400e00c24641640e6202c0300039041d544520004507156010884126080b00c010004403426124082c09140200310b00322400782c3c1c030b140001380148510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 24356831 1250 24355581 24355589
    0x30509061501030f0e0d0507020909030309060403030f0e0d0203190206010807060f1803060b0f09060108040b0705040806010b0405030c1203120604060e0901050610020d08040b0c13090605010306 85
    0x5005141403012856101000041c085000d00e0041010500400180d004000b1070b00c0300c1c1c289204402c4400e24442c2c10002034541c0380d0089a074070340341395243c1c3c40203520784c8401c8481030b000341c01200000380024001d5000304c00b900102c02c40001d940c0c4005074039503d490300c10403a020241e400030648180b040380c102031b502c1c10146644060421545014811940c030b0045019810600100f00b00c0061407070b10481c87c3c6180300030981c0c0380040741e03517a0341014402080c092104a01078400c3e80e00546441c24451042d501624060351541d036690380e1a11a844140400741426041010070000052400c1c010004540a0002c0003420b507610752400c000c043c684552650014045e1542070440420803501000342d5050201c2600344d20340c141d59282c00100100347c80c1d005a03a03d052882d0900c005050150b10003445a001070710020150780b102c0c0c4059030780e65400c0714100001450000000c0001e000c2224a036001301012800b0343c285842d0300742440e50120b403608038020b1310740d440c00308110961f8103014840c000c2c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 24358081 1250 24356831 24356833
    0xc010e070611070902030a0b10120c080103021810120b0a0e0a0807060209060405060403050105040201021b061c0e01090308040c06080c0901080402030708100902010815010801060f0903021f030509 86
    0x5610b106a07156296407207104d9005502200040e030000c4943c000380700540004000da0000302d101e10019015440c01c07000c003034000340340454190140d40520903850680350010260252583c83c1e8110a94001d4000c00c0408120029480000d00c00c0d140b15845581324440e6141200624000c11203c0480308070f030f4070590540d4841140d01c0013040a01040301c540c190810b80150392280c4a40c045801413083d41d00ca079070400342c0020004144081940000d0169100768243e030001d0701440e1400b40c1440701070100e207610400800c41380160340e07000c075001c0200007a107140c0441d1924090389214211a485070054020484540030441082100b0109030040c0045042041460500411610070f038001c00700b015043c440320102040541d5402c00001d0024071501044880b5020b110410b403020b41000c40c422400301d038140002c50100b800c805550301301c2e000183d54101c1d8903860928111607140c2040408000e0000e0b0a40210243e1105040c940c0a401c01484408420661035001000c41b80010950219 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 24359331 1250 24358081 24358097
    0x60b0303040501140d0b090a240b0d020904060506040306090b01080607051207020c09152b03210c080f070e01140c0709050108061509040302060c0d020403080c010e0706 74
    0x1480e80c00c41d0458228410131140c3c10348508021500314020b00c801d241c801d52084010f410003030907010075081018021071120b0f180350000354103030b00e03006c1408246c05500d40c0080c042c01542140303401b6502038684420001c1001c01c11503503400220712a5030050f04145c1e00a0b8036190141d0521511f5800580100074040c000c1100b45010b140080c980c0c041c042e00c400182c00810082403100d0701c20442c6081c003a400a181c40d00c103007010508000324181c08504640640c80100480000d100240c0000e0f4680d074110a041c0008080e550701110000e04480004d14010159460300c200070703100f803044c1400002151203103030071401c5c0181210031821008020404121005008034500d99001e1241000c59003440c003006d84950b540316000b42004160707000b0800003440d003000064107001c005a454052003200710361580319038011301441914402120042c0c05a4408000f088182c41c81e1300007030104c80800f110050070280c90b40e454a120303501c058140b942a80d1205442e280d01d5030244032100050265040c2210 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 24360581 1250 24359331 24359339
    0x140a0303080402060906040e190501051c170c0a0507050a050a050609040914030a020114010504060803040e0402010c02060a0804111e0103150f0611010f0c0509060903100f020403060b030304 83
    0x1007240001440280150000318031148207071522000d44004e4100c60080c0f503010701d4405000c004d60142840c0c071041050505000141c80e0809915030450008108546180c10035941c46007c49420300034501900c0b11020440c00303502d08400e022181d0003511400c007901040d4640010090120140e8210702e11a035460750042185645034001c84030fa0890954000c00d46a810b4241030184070300c03400c90099503020004000b6500d640c190320070701c07090b103a181950030b5a90b02c43c42130004948040c0614075441d4410030051146e460a01400c9500501c14900703e06a40480c0c1e0100d202c0e0b4000c02030100c0400c090206000c00c01036596a8448980c009440501300c807005201645516000100d650341031643d1b03010465031b40a5144106c0c0c002c0d102100703500c0d035200c0c3c1d90301d0010a11030484442001c2c5518103441d5528080180c05204001c600c6540e605050034a03c100300404d40c2d00810200b40e01d0720650300c40800c0601d284c0201d41000441080040c0c41c1c9155007024015280d441c0c2c9a80d200c1e410802042c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 24361831 1250 24360581 24360587
    0x50c18010c02060c071802161b090f0203091e06060d030c080c0f060903040807030b07050d0614010311040b0a08310201030b0409020f1509040203090106140a0303 71
    0x94104404081025408151200180c603807641d0210040c0d081400014100406100040d0b01d100301c0300014108100c003825032202c44224021204002c0444665001711004280111207000d0780303007144e2650b55107503541c03241c500b402c1300e00030301001c400160040200b00050b68184044200031904e014140c0282803556001501c03814010a2544160031400880d0700b407601c52200c010006510017001e9650b04002e58802d41d5a041c03181a1007824490400060b180e180040141d80c101ca4641c4000d107151800e6a8686d940c80d50001c1080301003080902c810400c2003840e00442004068043c1c1c0002280c15020004060707540d04684000a0841080300f0040c6007240d6040b240b81c42050f02e40b10200d0b440d9116281500e038485003040c441c540b944030b03082c0301550113828160b0300c851013620100400c0100c441032000795000e00e04041c0d409508840c3e901c2541c00c00610401c070380c4c29a008158175018002d40007404076042034912000c030341e5441c00140700c10302c2040702e2040f00b250101c64071010b19146079801 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 24363081 1250 24361831 24361837
    0x1090303050c0102130e0405060117070603090201030b06070c030201020c04021806070f120503010e0a18030305090f0708030702100509090a1a060706050f10081506030a050312010e0109050c 83
    0x4080120004100410b240c081d03040d1041e481d0980c03000d1103a00e80e199009000c804d000d4600b03903054081e00e0000143d04103001c81c06440c482050000c0d0622600d010001e80003061043e205034141500c0d10b00108060342c6140060200300d215400c1031540c00d0450000a203403829220b003150156204101108400003860001c1e0800700c001c8800c0303681c650452400c2c510980a07420300605400f003861081c1304a5401401660690b102c2d50a2020300f540c800088400f035075840f8071924400b915a02045020031f1003034000d00e034002c83d80700443c1c146600e403131001446e0881c1c81e0302007003580e040414100110301c0e110991007134002e01032412604004c0403400281c0c1d042d1024001101403691030603580000481c410142e90403100c001c041d01d480da007050920401400045034040039041c00500017a24400c041c03600c0d10b0503940070303200611520014800c82500c4800260025505208190f01345c800100100000c0078090003818410b111945012101c240404042c3c01c81a68941840d0070040503481e10782c15 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 24364331 1250 24363081 24363083
    0x501020d0e0d15140a0509010902010801090207030c0c06050705100203150904031101020d0603060f05010810020c0304090501060e0a150f0507030e030d020c03070501050304020f040b030f060f2202010903 89
    0x5102c5480342a4600701039001c1103024002da006051025036451a0715080394588501200e1101340030075681c0d10314040c00c0b03844450009011402510060010440c242d000e0034001d44281000328804c1101d0f2214080c11805510090000714001400400c201040c0003001c40f243c0658015800c2d0b0a00c4d02103400c020440340b00031070040d1708074400075050500c101016203144107071314001c640d101c100005210107032442d400169003050031b10720540d04c04059441860f0407503401c0005010240c180b01c882c10080d6000030110284e41c44240000301d07504040d8842c1364001c00e055101d5030390090308001407042c030050b00d6002800002206541424154004950881c068010700d040c41c0c0e150064541514068184d100f060b4040c0b00f64110300304001e070002071141e40078500704c0444250540d900011070301c612084600079000303116a000004681001d8100f20581c410040c1503031001070307000300501e20740300702240c2c40f082c0c1180680074440c229080c1c0340380140d50200c3c0681c200d14a400e40d00041c040500fa480 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 24365581 1250 24364331 24364339
    0xf060915030c092a020601030b010e1603020f0919030611180105250b010501081014060d060503060703020904060506070305031f0f0806090d02031c0f060302120a0b010501020d0e 78
    0x221900032014625850b04204d00030b00a10075040314440c0e070081daa880240000c03142041700302c0005c030343d01c00700040c01d40c410805062003003100c280720142180650040d041d82d030907540d02409000000da59200010f026a460180401502851410620162404c581c0a410452410001d8800c2c1d008a480100c868907401e007421961aa4820605454000d0001124626400f48000c89041000154000e8100c540036a40c2d00c29585170403044c03603c60345682c45904c00321160503440c503103d414450068803012460000018589603102d02180c2800c03800c0303409400080c1d000170035804616061007000c024000a82c0c8080c140009950081c1081c03002402c40446c0001e1094280b00d17075290074412070017504603444109541d6550315881c59444509855110143c00b40c0c400614100344000190703002c4000c4000d4501482c034980f02510028a0300f0448000c1c51501d1b0000400980c5a40c4441010244160000e0410740c00300d042c10002c906041e0480e6045421622400340000d901c81c084010b04e5030121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 24366831 1250 24365581 24365591
    0x70306020f04050a03150b04060501020a030e04060b0f0d1103040c0504091502160201030609090803160207050d080c01181104020f09040507030501080f0a05030406110c040f060915030c09 82
    0x715640150196030700c40c5501c41510500402082100800d0542080c0c1901050192040d2007082105803015409903074016401504564007291080c0140c0c08106006080014815181c078076884256200809000140c0400203208600c2c0701e0601c20803008a41c4040000e055051682d5680c1500c2c2051058610071504c80c52090240044640c0d0041c026503840b00c21561560450050400d01143d0036040c0d010a18190000441c140540078015103d640f24004a195603588590401101c0072883c10400314400c1d800040f41645540f074031640c0355801002c116885004091042d07083d100321903400c402610450b554030303000984d182c82249084c0b20844016032601c100e01d40c0310780c0c03038042c1c03000d100d5106060600780031080c0c2d05503005d181030f51800d505036081490301d5031500e6a82c0c03e0090000701143d0040104210103842980300c072070500d00100903035002018140000d0240c40c41c182101050a81d80d0104001c41442e511a0307412260700c0150000a00b272458a0320134001d801403241c000300320b45403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 24368081 1250 24366831 24366847
    0x8010f120302010b190609081504020d0302100515120d14091311070b070507030206190b060307020723150a09050a0305070602010515060a030b061603020f07051207030602 75
    0xe400c541202100603020054240720303040c0303685c035000281c8117201c0450600c1e070010411090115143c00a034800e0001e142160f01c955080c03045401d002401601140250711120300c40f003815005150181101d01d13001c02111940b1b84c20403600c060b00684114191b4003480c0c0d102062508030754a909198645004280c5800100011035034400d10848440c403c01c1c40c00b01c41d48800f40c0300c0c81c050b051040c0948a100205d07991801c0035138075803044550150140e8842c00c0029049416048010000164038102040140046001c24260740094505202681006009101049400000507142e05030b01c890b1250409054010480031396441007401d840901c0021440c1c1c1050050340480c0c0200009088600903581d01e0400985036041800b50340019403c1101003501d440f501120503040300b40c01003644e480d000d59008203400a000242c081904800305200c3d122407510340000b0400880e0007900034004000904108070700f008129006a841082810842c1c2540030000039000203a0b58407140041e074800103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 24369331 1250 24368081 24368083
    0x20903150c190504080d020129060409090605040510061d10051005070c0506070803061905030f01020406090e0c27040c0c0519150b0103090b0112020a0608010f120302 73
    0x8503203080b0681d09001110341c5405a020004104869040054a4420302c01a404a00b81c8144201c440e001c1c800700c00daa05141e4400013030303442000301c0003098280707402e548104140648003401e030140e5400303507180100801d12100340841c210b89003109404104040c00c103c4551689062440c0110640340d018000800c02400201c0050152000600c0c2c542c405c4544c1e18000c001e644000c40484032001e11010024050600703205548001354840f00081c01c6a42e000240300c1c8a50045c0340d95962030469800004a94406024a280c1b1044103800580e40f0342c01d0080250a00742c00d58414001c0c80b0020080209410048082c0c400d03a1444c0721001202d21100102e480c2e040c0000980e89030320a1038100c807181601c0e00850040c04481c80b4106440342c0c0a03904644d90002070a0300c2000e40b10a022142c00640301c0915030151542c50814100001c100341e041c0c13074851440e007091b007080031111111039488041d031600140d0f510090646e490221070301e41c149041c40200c0d0390507100d02071018460700c0c0c2c01ca0030180 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 24370581 1250 24369331 24369337
    0x150409020306040c06090e0606090d080d05010b1b03040815040311030f0a0f0f0f1b0b01090c0206060d080a08060604080102210c0a05070807030e15040302090a020903150c 75
    0x2030010101e40e018181030404c040c0c000f15a11407540030654460001a0481254000d180305050041543d4201355045040c0f1400300da111200319035000c020081504807504910849010b0007107451010780703aa08844407074600344d00307460724184617920a11080160b1100052000d65004440780ca60038603450341d02c2d050b03502e140b04409004c12400081380c40c0e1003e051301805045150540d40e1142d403012403201d802c5e0b4080b958007d141c2d00255608030384180c0c06e8021103004500101c80b003030490080c0007544800c4081c8000307800524000d600c8210015944c4e03070400440707410690450b200c08070000345581d002558401c00090340240300a07040010040d90350642690020103d0300001d55071520584030040d5950b0204041c1c0d0745101c1004003041060031240160b8400030034985030a450300e980c688480c0044e0704098002c60030040e0300000082203885820301c441c1070318266030100340c6681c11031040003c0d1640040142035054418440b0074030f9960000750a220070a0344c0140d26941c0e032584089100248 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 24371831 1250 24370581 24370583
    0xc050d02120706030c02070501030e0606150d020c0f0f03121302031207050309040c080601020703080c0102040302180109180206090111010e03160b0606030108071707080a030504031103010c08150409 87
    0x2c01900c00000c1c006401d0741141c0c4240d040c035400d448425071214019005c6074000c043d54030269000701d0009502e41405400740c40c0701d01d82c030220542050f61082e0301d0f10982e4410001c64045411030a5015000b040820014016205c4007014504001b0180c080c1048040c0091075410840c0d0030707250540540d2400d0000b071039042c2d208409950791364101d041456403680b2a801a034016454006892800303072140507554002d420590284c070465182d911000101d4104055240d500d550801c00080141c4d1040010000e004c4480e0200500d98581008401204c01103001c2c00104d241c81c0360355a00503500c410071504405024280000c400110015680c010040c4038803507246440005620304400d44c0060440c0c03c003034810011000b1582d5400240a00360000380325840c04e580c4400e5090040d81d805d104039011500300e40d41183c464540e2103484510b082001d20054000c108009070900501c1000c2d00c00d03502c2580140e0080c02410310803040188260780050510412026540c21b04c2855541c0d60400d000325 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 24373081 1250 24371831 24371833
    0x1308070605040b01031202070b030601030b1c140d020a032a0c03060218010c05070323060109020d051501080105040b0103020c120901030510030c0302060304030306080619060906030c050d0212 84
    0x640340600d04050048030a0005844056006c010f40002510006040040d28542d001403800d42c2c0714030005402030b200c4041c4d100d41c0002110415007003e100302405010143c010340d00d0321070007015013000f2820048040710003021504004840f101007a085501e08441c118801c46003101080101c1c0030000300c8a01b014010b00551a21000100f4420b503500a441c5001d10b4040c91510090804019110b505500c640142180c018800800209003540240c60b540790070709071030000701c0c030b80d5014081c14891309801c840310b00f603804603500d40d41c00414819140c0c0810400310303c07105d02c0b04200020f040f0441c1481005e2296890710080e042591080c5c0540740c0e8490f807481200c04008080b6801d2080341c00051a0380d0019180400051441d01308038a5002180d81060404055030701355003d10280d41e100030001d48c1495101e03180000c1200c01040310a11440700601c4141800d0f0500480006032000d99201b56501e07400c158040c408607500310030343c0d02182c0c07044468103e5030070640701040400103014080c1130b20b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 24374331 1250 24373081 24373091
    0x60b0a020705030609010c170622052223010b0402070309031104020403200102031204060b031507020c01050d0e070b0a090e0403050706020901030f06060e01030f05070813080706 78
    0x18203030002040390503030b00c0840c10ba4485a80c1c20008900700c981c1e801c40d000000302c5074242c07981440c19204540e9006007000e482c0310301c130303507484180c10b11717280c03005c0084035a0590b6820404c1009003001d40914110480c15901d00340210300340d128011030314810b02c0c844c40d40b404c42c01044005d15509500c0b402096074050021740d160f801500b8060308200280c401a15022800d108000031403909208541c1640e0340449088401c2e52040710a0096409091030141584010400d101c82e140c80c2841403449140305050204454003401c0500d82020b5800c0d0140648a00080030f10145076008a1160003403034084c80c0240d26016068440005441c02c0d40091080707024821010500041c0000200201c0205480d00d040c507a07600c5d10705004e2180111405000203509201101c005222078009080a200500d000718070307109a8060300040318002d5229101295034120341c0d4071a5600360086910302d407149003040080c1c2c41c1450016120140060070f91100c00b486445404c02c00c1407000030b441d03100d2b82000c02041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 24375581 1250 24374331 24374347
    0x16020a09020a03050a05070c170708132301050a0311091206060102061501050306010e011808030a1413030807020a0b0406050318060709090b0d06020715050601110705010c06060b 78
    0x1009502050b0584006420103001410811a5028180c0900c0e01c0342d48008c0d0a904c0c82c0c40d4030441c0039021108251b5510304005a501240e122009001004c02d005800108903140a60300790300318041c03400904503542408083c016a0703801c0016503610042a05010590701d000000300d488a118807000305030320221350f000a442c040c000081040c8148002e8003107072025154a5041d5100c1d1764001c1c2d0990003c0c000304005016944240c66030070340300c1e40605200c40ca00760241c8007510f181c107060708442e4403070348040703005d440181d446948441a0711000314072600d00300f018040302400060502002d44a4440007a07640c0441d200c80703604400400001041944481d15400700429907801a00d000510411082450031130b0720011030740c5070180405440e940981e17458080300d540a441d21a0140d81d0018401c40307071001040c142d0004002c2d151154501141940160341c9070011910f003c1c283c24100403544425842c0138100140f42d0701903c409003080d815104081ca00500a802c80c0c0c0c0007000c41c20000304000d1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 24376831 1250 24375581 24375599
    0x50c1b011d03040e1b04180506010e010c230a0b09010c0e060a020c01031d0111120109060305030301060309050a020a12060c0503091f020405060f030907060201060e070516020a 77
    0x5240c81c41c1c00d601440300c0080a881950390703004a01418840320100380c0071a4100d03925040f501103100c20031404034100b503900e9480c0d03500400701002c00a0391075120800c00c4225170348600c082d40302a1090801d030140b65813980b00e420741c0b40b5501008203c450010440c0200f11502044129403a42e8821641c984502d0150141c0d40038100d0380340e90102040d132801c420a058589001602c040407025402448900140d00c0118050503000c03080c80f2403200c819404001910b401c6c0211904048a40e1b90b2568030740000b41107452410050740302d50f00c1189050070130b10001c2c4012046a0445206290210300d641c290308089050410310345000b5800206440001141b1103001c50360203141e8000c22040004640018064405202c2140ca40c0c00d243c00a00454603521a501d68001d202c2c4141c41c07006050903280c00102349154010020031910500c04403c02c01c03003842c00c01c041c401a00c001e100074072990b490429090304045001d4296010311070301003008800780c1d480ea40440c0c1c0b80342d002051a85620b80d102800 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 24378081 1250 24376831 24376841
    0xd02030c120708010b01020102090f01080403110601060e0306090c011b0c08031c05060f09011206020f0a030603170901020d030f020903010912111902010302030c1210060905030d0909050c1b01 84
    0x3c1c459401e1024001940d030040c0b09582e0001805011801c03416403150044400420040c402c400f844224000042d0301c1d242005954040e0056855201e51020380604240c54900c0c02002440c07140c2c44260900c5c0e040e6403240b001c3e5400d441c29403641d0f1075201645000d81d03040000741c000d41c035640f0000c641c1640250350021481c0c405503074000c00300015100c2a00b2310201000d910042ca400c07a410500400c030382c08003145608452405a5030050030081d217000b080c85294003104180000a0311b6140c00c1c4148005c8048494468401281d4945000e0807040080c0d01c8102400400d01407503511031142244c10710b950119051240d00030000c001c1141c0303d00d421050b581550242c0c0000503100300b0412040d040001e05821545100740c0602d001c801076030f004401035480102000d80d090000c2c00034181e0031b03451101a40c0941d800c41c411003051070421000425203030340380c4c0c04180b190744000d44102186800070320322000e03283c0c8030101142a07695511006103620900c0d150409070301804c2d262112003207046d800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 24379331 1250 24378081 24378089
    0x30e0112020a020606101107060e0409051506030d020307030e04050a020c0604050601030615030b0105060a05040e0103030c1b0b090409032102040513020a020607030b0406031e0b091603020d02030c1207 88
    0x258480ca24501b10072a4a8225500c0401070360b03012079024000c1500600348a204554018800700703c540d01a0f46040c14000d0810200350030900d60403c0c40b005280a001d507040b02101031009600b4180140c60003441e07410301890b0240140e5403100415280b02040e012145034171202002ca4001d400d0600d852555170a003444181c620302d00c1c0c5803000500d10300e0b10011508a03a00070341d00104603400d00c4108852680032035440d000b40712003084005054a00c440c607483c002c40c000d8031080c1c00000a8189000b0b003616000461140c03a50421081c0400d000607426500001c9040c5c0e00003034000341d1480d0980303015000c04410751010f00000b10307803c002c50030f0f900100203480d030a079420090114085085020b034060200c1c000e001d80c1000001400b142d1081c0d0000d43c0d05034000344041511941c80e140c0c0c8032400c0445a1410207003503c2504001031042119030b041d004090035008240041802c00b84401e038009030b002c0240b0400b482e844850030b40d5020810030000c1040100701c2d02c0e0801080c01299901c00c01441 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 24380581 1250 24379331 24379339
    0x30a020c0604150e0d02030f030d0b040203040308040f030c05010501090204050f0306060303030f280c02010507110303010501050a120606050403030f031a040209040912030b0414010b0403030e0112020a020606 91
    0x156400c2401c00d80c0c2682c085030010110520800da40d504103440d846a449041c1e500034414103a0ba50142e901009000c1243c00700c0c001840c0d43d000f0030a0040b05954050386078a000701d004006110000f5030155000b94440e401c01444010201203140c1250407450044004e8013940c20900042003082c0710380d0007402110402c40c1c60319a82040305c0e00303040c2c480100304c8103036600d60004d0002401803211054007644c4410f808403030603140701141280b0070071041000e02a85459598100443d90140c092041ca9089034203800e00640d5020007100099882c401406414100900807544030f0a060080050241304c400b40704090001588903c001050354110b417005a000882041d03280c0c02e8103000b0b100e8010011880c213119600b185c08023084c04041d41c0b240702d8090300179640702840004100031403045041c0004564000c5031003036085c02048103440c10240b10701104070059004005d588003140c00c42c3e0840ea41410000031042e810801a80e0b001d00101c0340c00d18007800002c540c0b1882d580420400e219040c122 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 24381831 1250 24380581 24380593
    0x501061205090312040203030d11040302040b04020c0601031103010f0e030a02071e140d0206030a1415060702040e070810050907060c0822050409110a05010c0f06051b070302030a02 79
    0x1011410580c1c1040c1c42d0700710107410030000c4020160001000d25400760020742202e1a042094007420100d4100407401c007025074012500784114509405644801c3d00c0840e025401e119500e07540f82d450ba1018440148420f09254004260391000c2d00000c41d1813942d00002c11804141440f260748070f038050b071021401406003490107e858142b80ea20401c0404007407110002d9a414a440103030441c10506000340e02400145803080143d031920019881400c038080c001c501080c202400e5415408081c1041e103407500b00050b094441c0c2c4405094800e2660126004110700104100305803c00c809a00321b09050b015001d84075802c1344c070907000103010b042164119010300f03036144411503030900000c400916401040220440711803805000c5d04c4144002035250b84150ba503500054100e5448603011280716000c030100304054030704440010010082800c0503d00700c0a1562151903200880d40010a9296200d011841201940048803108501105055910300c803034200a907a0743c00c03044045005102e04 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 24383081 1250 24381831 24381857
    0x30305010e06091b0d06150201020a020d0f0509010e150a020d09051e19080615030c0d031b05030708070b040b100e0c09010203070c030803010e0f0412030c050706050703050106 77
    0x84450640b084401504e802c0c15031800f42c80c1c07803080d540034503140011141c484401140310417003901148003808043e000160388459911019060031f0400c2c0701c203000d0100131140b445480750042e003185c0c0100401d1a020b94110b060100150020802844800518901040d007a1560b13800050243c180b0329151902e928260399841000b41c4020800b4070066811a144090200740c18400c504020205884007412009602e84229a1400d201206c1d4003061003486407100119040c2800307000041c036026228501c9140031a140035000501603446590302d000c19543c0740301030000038401d480351035621442d01c590310185070038200f6842c103080c0d900790780044000c808035030440c0e90040355204445410001c103c666030b820103400301e50b401140d01a030550004001d403c000460a010110165200703035a801c0d16075041210744844c041c4020001300f540e080301c100f0310010850009252000d10803a180c0811544284c95013114980548007000b848982410f00380100140c040e00054162140b0340e0b1255184a44 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 24384331 1250 24383081 24383089
    0x303020c09090f0c0907020c030a0c06170105060307230a0302040302040507030e100b030f0f010507080714070b0c040509040c0302040c030c050909100f0306050f0105040b03030901080709080a030305010e06 90
    0x390900503c0079a00150b07403016641003e4100b140e010005005413203508400307801203070030540040b00490b1000040d80080c01200e41000030859140008039031080e45604040c0898064170005d03000d9400d000e2000c40401c41c3e4071941402d8640c69880c0820943c64030118100540650800d000c100d00c00da08080000b002c5911a1081107640400c500c018044081f181e58044010128105402c0d01030190302c410f403001090402040200c038078010000201850003082c01882c80002074400000c00180840f24000c2a50a409551342542c00c2091081182c0314840303540d00d20b224651050381c01c0034004080000707000e001c4441c3c6088074000c6d60b0501070312070b20100440c2280d090b04160004140c052041495a0a2004450780d111f0400b4a00100c69501d03012000203040740d580c004c40704d00d0385900400c8009040481034900610041d901403100030601c40c0081d80f81d0041a84280c104402c03900026140c61044222100038038540040d40d000c0740720350a0007005071000f4084c002d50005400040b4440b828 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 24385581 1250 24384331 24384343
    0x8011a06030603032d04060206090c04090203060712020915070312200309030403021903060e0d0f050d0b1c02090f0c030106050a020c0a060815010216090902130203010303020c0909 79
    0x40e00070b019605e0107001c0d41c50401100c06154115003a034042100384036421038000000c002400d070b580c000307048074506074240c0c601d040480030900f4002d508010f141001600e00040d0070f030b00f12007182001e2615103007800245d8028028464440d43c03204410a1007201c0c0b007418801032003ca0702a98a1074660340308861208182d415a11941c0c100b100e0b140410560800000003840d0001c040b841074a180076541d4000814540e90301c0b080d0903582c031041030100f040010034407840940c615250b02500c64220128005409240c0c4250404240080000c24205099030f59002c210300541c01454031030741202200c065400d020003400220f00410500000c180c0b20031482079401c0c407d0f0010f00f5442d25507803c0c100100d809801810001007988180554071409607100000701002d00060b0f030314160146880780c0328246800840310b40300e065421005030a01c1c01b03146024010182d07848520003041e02407031407000c245900101c00c458035a103440031001000300355000c114000c0500c01180e801d115078541c6140780351601 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 24386831 1250 24385581 24385591
    0x60f09060105010509130c08100f0b070305030402030c030d02010f24060507030c06060b090f040504020109031e06020403050c03010c090f06030c05040e070807020d020f1b0a0f08011a0603 82
    0x361090004000c150300c54001070140c0c540251660740e80c6080d4a5000c01070b603004051160100e4681010031030804509240d60004141d0201c8482503940781c080b90070788600c18a00d0140c01c01500000040554070100320090642201404403150724141c840003d0003002d01044da41003207810a0302d01c440d070f910b040480c07414250402c9551400540b0f4076a0581d40f40d40440811410300c031001800401080d0305100b0100100340c48181c2a030344491a07410010602c6040990500c610300c3c1205210250360b000d905001a641c0c001041000440010345144501010850003041c1a0000801100300034010820006200301034000703000b100040c0405442c44040c1e070181402c2c140400c00100407091103a00155410940743c20031500c1e0503202c104681c441031080ba00308010404050610210b29030400000496640341d2001c1c180200c40036580c191142905441a10b140060f501a501c581d560010301c00000e044064040b01207550300d49407140a040d0300446900f840e40807001070540c1e0300b8400200c6e4031030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 24388081 1250 24386831 24386833
    0x30304090203071403070c0501050f01030b040605040204021e0c06091903080a0b0a03050a0302070b030c0f092106040b160f0809010f0c0e0411070f140a0c030f05060f09 74
    0x116003800c190500a4000070210800c02c001c151444501007022802103003c0c0105c1c3d41c03036491700e07401030404a007941c2c1c0c05458041140c40400c010404981080d4085070803035800b40000c142c9441c0ca0000502a0081900e911442044600e0711825180b840d001808080d0202c01a40d006544080d0615119841d0156400ca0f40f0b0491040304000380c440c803541603220403500400039080e0098030101e8424000303500119110751010002c10103054041003000c00130555004054a10b14148030008028003e400d00c2c140030b0000400c806009941c0d900f400301c41401c3c14036a070220072002140280d038034a01130300d05580c100100000324400e25260201b44100006079140c080340c0c0d0903800401c5a04010003080c0c44405c1d561100041d50280e0b0900032426550fa29035501e4010090b1002004200e40c288800c08218240411400001800a0230350204282c0c00c801060203400114480c01c0c100324090200501001c0424001b10400111040810b1404d000d01c0483da8655501454841040e00c29611040343e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 24389331 1250 24388081 24388087
    0x60e09030702060304172b050103030210090c17030301030c06020a080307110307020d060c090603021204060207031101060906060809010b09152107030302010b010c08090f040b0607030c03030b0f0303 87
    0x5070900f4002150094440c5840806400900c5007a055030b4020282260000001e17105c000e4044803003e1640c0c0c8012101c0c1d50411182d49036a030041d5403002407000041400b5214681c08040c003803c1c0403008001c00002010302d0707110900003407007038999100340811110a030201c00d002c01c20a10004404c0c80c070907802900d80d4a5503d4518080e51542c900c000c80c10040d110401040d00140c40b511010031a00d8031418010030000d03145900504944a1a01304d0420140f0500000400901c0207031082c0c0c1146d0004001681c46483c1d081c05c640451790b000c01c9020641c2001400a481c41d8982e200313a08841c00390380e42251030b0310b0706101d0342e083c0d540c1c0c1c0c1c464681c04801c40e030202e01038072052104d196a1050092a4880351070749142895408840c01442c0a050741242104009254080c003921202984c01d11308120090b046550718001070140003c45402065501c5c0740004a0f00d880c1c0c8082d031440c00c02404180c84030014900100720340d20801c400c170006401c0010540c1c03039040001d04131070700190013000b440c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 24390581 1250 24389331 24389333
    0xd08010306050a09050f010c08060d0302100c0201020705030a05040305060a0212060405060f0a0e060901080304081504150203010306020a0909020c03040b16061103070315060e0103240f09060e090307 87
    0x1d00300141140390001e07074402d54040040d2081054101b0800e4610002c115103c0c09400640f0b440d40c014051401135400c10000c100290380400ca542d001c2d8504580020540c542e8603049009020305640103080d40b00c00601c60000301d80000140c81143e10480450b00d10b0341d9605403407800c0e40510405444074107028400300c1d072f172860a0b404c6103074424406818488500c1c40c4400240460f4803e41c06140c500004005024190801c491040e0150075800015450a45041c0e01d03940c1e9036440080803a00c691614000c2003c000c0790b10481e040c960311a4105644030350310b03410701600079807100e9000404900d100b81f000074017941600960720704170300280c00380d410945041250f1042c0c1e4071000c2c5090801c105684003100203402449040800320080c043c040c2c0343d240000c2c02070704990103906548125500c541007041400d40c003400b072002c4c1020038070700410010b8040c0d5a144000e80c031081b01e1216030900000c04114100260f03402400c032201150284607140d500c1081031942441a651300312550401c01c2058 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 24391831 1250 24390581 24390593
    0xc060b010201111912050a1e0b2d04060e150a0807120303020d020c060103170414010e21060a0c030207110603040c030c0803121503070302091005060c0c01030c020d080103 75
    0x99980101da041180501303500e00c2e01801101e004499001640350703034092208505d0940c89800130100e003110800c10551074649d000540c0303001c080c090308410070068405503402880c2214841100b041c003500030712607035407114022100c14400300c035529a00e180000c0d074203200f441c108081108940204000d400914100516141d01104402080e0249a02044007a02c0d021040c0f00410300c1c406250090081541549084021018030100d1500210b030180701c06e00011112002c000108542404c0266001000d24041400c0c120340b40c00c000003c1203160441d0040312804a425480303801c6001013001001d09050080c1c00b24000c441c0c0c040c4c05069507150562981c1400c5000716006801101014101540d03580d0b00f904801058011411315040440c00c0c1000b07491046203d90040c514503a0801404241d00c04690355aa0a100180c4101007082c00700d40b40030561242d400c00391a015203450b90b40e1440c408041d40d108d2980e84000e00080c54410300701201071003c602c0c1823141219980e040100c3c1d107140c40700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 24393081 1250 24391831 24391867
    0x90c160203030c07050307050105180d02040902120c0f0102070303050d020f040f0603090b0a0903020d0309060f0c05070507080102120103060b01030b09040327080a030507060b0306070c060b01020111 87
    0x2142400844942500941d40801c090a41041201c0051000e40d0510f000e00d400e0840c1944242c1c1030100c1404030071590441c4400001100c00c081e05c05800409032400090701800b0382503406900a02c1418400000b042c2c04030320303d01821015604c001a07410044012a079640c2d6610026000031000e0104200c00c21198000748100841d8aa00c24202601e6000c81c1610610319405840425640e400315020000d800144942c03004901000300b25100850700c0c06034136070070f0744140502007542e40c041c40c00c20003143c0c1d0b01c4101d10400c0700ca420050140346220181c0542e0000d0411341d00c0f4480c1c54000030700700005000721688039240410030704203a481e582d0f1300000fa009100c4441d06050321114002003640b00d0a4000744240d0181e507546101d0018140040c4084490442000c1c1034982d40c0000c0c0407141e40017a412462541c1841d20300d5482e40300341400402001803032155236041c0155000e00c00f4107603009040013003950242c6000c202000c1700340300590880b0640c000104450609000d0044402d0500c102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 24394331 1250 24393081 24393097
    0x50f070512060a0b030903130602030a050906090d12031e090201020a0f060e031c0f05090304060c0203030409020309030309060a0501140d0519140d0e06031b0d0911040c020309090c 79
    0x2d6a0640752269810f04c10303600102c94a0030b05500c00b2820340009611100e96400401090001d10318254030358000810920451083e01e004503c009802c4d02c00340c4a145a09091941160f00940264140d8500034098180d040d03404c010a010606000c4420340c5078851110515816002422605125650760710000312400c01501c0c0c4aa6400580c201e4a5040c401080007401583c1c1d050030f00c001084a000449041c01443c1b0041468102001500b90700041124140d58190411300c40290b42d510000c1c0c51403181b500402061400801840798101001024500607901001a01e5099482c00d5405048030400d1250f000c840002c544010603609085088510b010700920655140365488a6900c120300040e041c2200e484a00c4a032420020704244915000d15a00b85054015110000006440b6000103802541201c489941059103007080108603010814601420b002036840c6062410556001c01d400c18020390420040f6000a072010040b2005000002e00708404d230f03102c0c48040b4100d5080b03844 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 24395581 1250 24394331 24394339
    0x110a14120106090303090905160e0411040e060906030a1713240201050907050306160509030a0803090c06030c03040f0201180306020c01061707030305031302090408030406050f07051206 81
    0x40411152540844038041c0a060f101c2500c058654a00102507082d540e0014003400d1415090000e55080400840d0640340f2600d400e200d800305410000b4000c005c00d0583c84a200400140085d000c01a80c0a0034801c400480384101c0c0d641d00c81040c180c07516040c1d0300c010000204c00b5207102c800350303440d4054650200c3d00e05011107203684403952079250300141603031001d5015074860401e0b00c0d02c0d4240600740c0d0100c250009840102d16180111742c0c1d420001c4c00440c43c181c00c1b581003059423031192081d285104001811510140500e081480e1076078401e5034810058040d0030f10101c50703428401c007128007038243e08420310320b1640c82e43c48103400d1311340c0c1090403810000064003240303415120340c40d03035000f03140290300040c1d0340c2a00d100d4050845060703501007107500c842c0c1d5142036502000400c2c4030040701e8150901540e02e40e16040c0310803000840290096101480360103020a00269001840c4514402c00003044107807030382049400300560494031900060400c1000c0d420580341004c069412904c050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 24396831 1250 24395581 24395587
    0x1a030a0209040e0a110a050f091e0c0307120c0503070302031005150a0305010905010308040303110c0301020a0314090604080d0c0c0506040809100806030d0302030601022a030c04110a14 81
    0x140002c0599266080c854502c0c1d00c00000d540501040c90300300500003d0484005444901c1d06021031040c00e2003c00a9100f4400300000610011812017498101009001340000314501042100700075042600c041e0002010107100044001c01c52051038019001621424290340c0c84240840c040e510040610b90841e00300c0f41c000489032544903604410340c0500030141c0e20341518480003001c44a0580c011030b00c1768181001040860b0001c0100d0b030940341c05181001e00d0403010200145010601e0b10b1310b54041d880051a01601c0764180d00c046070300c40c0740480f001402e8680c07911107580d412041c0c2d0b010f800c1003810030034030360f0100c05540480ca2480311070904100c4020581c132100d08080045400350b40500e00003900040910f49003900810850035401c11244c01c3c1071030400700b40e44122600080c824103078000045000c40c2c0c000c0101e01c400b41848001818161061581e0398400001407503039074000d1180140010440c9064001c080454041d0b8003924184203482c501281c2d00c000d090b00a0384210010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 24398081 1250 24396831 24396847
    0xb0c0c0a06020102030a0f0501030c06030203041e03080a1109010815030a1506050306090a030e040b0111060901150b250f02060408161502190302120409050a05010801061a030a02 78
    0x220004030024000340d000143c0300d203400b50b603800c2502c0c44410580304a0b460b2100503c000b0301000359407002d42c0e449281c0140c503075840389408900c0441845181025803a1000710408055211070b0780c234802c0110007801d104940c403018503030f0f02d0b5014046180d40440e0180d00085c013260032a03580007440d28001400c80300e28071000c0d00c41190200201c054a5289901c0c3c410600c0241070030000b80c1d0300702c54803100030199404140c900030082d01090f410b40d88240d03120b1044084681c443d14041e00d640490b40d007640c0141c181034038140d00030043d80b22030181c1090001d80014510801d401a1400381d0040d000191044001800e00134a0a440c110304940c130500740382225001d6103c1502603c003500e800c1d001000348403180161580074002c5c070382c404881d85204c840c06611450b400700c1d241403002c189017a90046800039250a80c208807441c02c40050741c2d64041800102030a42c2d40190307014900d00c0100b042a039890340c607030a0a841c0140940d078141c0c1440e4144d41459a241001103a000c484c50718010308044c41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 24399331 1250 24398081 24398089
    0xd0203072106060501080705041701060b04240806030d0818030301030309090501080303070c06050402010908030d02090a1e030b13021306030203010b040603230f03071a010801060308040b0c0c 84
    0x3158000700c00005050400c1004000c0c0f01d248054402400c0c40d14951424080081c96480350380200c8403440307400c20380c07144062000d400900140002d0700b441030710707251254608150300380c080380344c0c02c00903040c10854100103000c0d4005902520700500548450403800d00242d42600700a4407e1502c03d01c1900d400444481c1440a5030281d8800d40e2200c5080349008015420743d10103070002c40454100b0411f01440c140c100c01c03120075043d8000c201040d107a032507000689010040b544440d695000004003a102091180d0007032050600c111007038004103444911086282e10303107110402e0512000300c01407010070442c50440b0b40c040c030032603008120703042c4542c0410465942c01c0d805042c01d90301c3c0c0301d062007103140c203000740102e000c000c2c0c5041048900d992100141c52090f2849002160708400c00c00c511004144103c41100909034201d0f1b984075002d20340f400030101810b1040c030311280c1c02c0b400400d01c40d00c10301580c82203a4003c440141020308006c00c0707030206c2d4007186c040305031031241d4900030181d622 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 24400581 1250 24399331 24399359
    0x30203060403020604120f080a0906090f031101060803030c0a081f03030503100e1501080a11160303060608090a031404080d0201060f050319060c0504051201020703030c0c050a020d020307 82
    0x8403c0d400361000342131616105c5000a103811070842031001240c801243c13154058807056111303400f41004a245020750034111700601d414540901500c2030071454900b410b40003640003105441550003003114690742c03c90f00c0c0d12400b056172003080c0181c04100410060384034125003032704407201e402200d0fa0003096070b240b909400c0c1e1583c821008a100841000007915802e8242d100034003c80c000036240349080445008802c10090300d6506104022001ca014040958041c958000c540c942c401d6940c50010351440c2d4070402c140003200000d08100020504034071411489010f0345002c1e0080040707103131550303080da205c2c2000240300001c02e100388000101a6800c00c28101700061503000050700f541003150203501c60655800040c00380d4484803801e12034170130b160722810b80c02c1e402070340000c0c44d1100329500711094410344d80585c0c0e0003698a00000032400040d4000c044445c0b09480400061200d440b0075100807103410f501400301d80004900b0f0000d42459045078041910043c10b85044a4513015031184020b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 24401831 1250 24400581 24400583
    0xc0a0308040201030b1c030c03180801020705010e0106030807080c0118081b0f0318040204080109050706021006050a050d02040e0f01060305071a0f0c0c09010b0a170106081f0302030604 81
    0x880c0a000e000030355806110b110070b60721080d500086990039444411054030704694008003004884011201803500c1520003005286070506680503a0740d40f52080c50103500001c0c001c0d50507505c1c0a405602c414014402c1034100ca0748001e0150600e01d0b180c440b05001c1d002203000c91601d540b100805603081c40c18040240201e0b110f010303d41d444000c41100c10884005600549078154084002594044000030a96201c01c2008032110828000d0202160181c0102c2d4400d5080d90309200518082100224a0205039840d43d0b0032606000d194800c590140ca015104003034025000e000184003504141143c840707800e001500205a40d250399504515060400000040300d035500c2d40240300300201844501c00416480d16143e400e00803412040010b4032601c14141d00300e210005820002c44001d2208466000008181034115a03482d003020515030b001110310000100240d841041100411250a050390310640e5007407060ba030b07099107249506020100c454500c1d484140300100680d803c000940c861 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 24403081 1250 24401831 24401837
    0x302040212090c040902090a0c0905090a0e060c041503090609020904060b040b030c0a090e10050403030b0f040903140306120106030807031403090a0b07052106010e030c0d0b06060c0a03 81
    0x1034500080001d041c03c82c8a0500e80c031940c1806580d4001d030317546207200c90700b00080036000103981007005070550f200c501a48c040c94000110804004e00036090342e104162241148003590a1540e4580c160480341c41039000d9108400182c00c0c030210000d100b9403100c0600c62090400054100301c50300025036100c01244d08860f46503e43d1840000d9041030301509441e0701f000d5000f0450060904006038203605e00d800703050300f595503501107055485010407801000d0140d00008005a04013401c00901070f09810300c2d6240140c0c01c5000c40310703650400b0312600071a42d405d03584401013080450050055a40060300b1030f98880681a00e0004042081c45800000e6110303030509541c40080e464050110380c840403100d956410b0074001c00c05d0107000412400f50a5611210080e4542d80b400e50684e080d00900c040c0d524007508840700d48140c00365158016000702003d8030b90500402c0c403a000c1586d50b00ca0020459080803485000b103001a80348460190040c03070040c5594244001040358500d4450444826000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 24404331 1250 24403081 24403117
    0xd0203190509070504060902090904120219080703080c030105090a1d0d020321040206040b070501020d06080c0102070807081908090603040f150501060f1101060806070207030606150e1201020403020402 88
    0x3840c40d06204807402014601ca0660274840040002642a13100030006072000b80f4014425030300d035200344500455511942c202407400fa40783d0a110b045600204422004544050301190f8812007603030540b81291401014220560340380402c1030b024003180c10b003164100381e040c020605411801e01ca0007031038015640c004c41e02d810034280220800184200044500c0d8400340c00c3c000540c990340115001d0740d01c59400940e8130105490038030300903c6900785280b2040c1c1380c40360200b01c10700040b405803a0145c00742d003245e84840c0c813140e00b41e49620fa14851114143c0c0500e0500c6240800d5640342c40801307000c0c440d01d50400314804d02080d041d910441e4102c513191402e07030070360040121340c200384100380010030010400342d814018058030801c00c4c0302d0090b040c4686400420700300e0009410410103072100b44140c800d0b60a00c40006035944160740011125241040400701e20108885800c12500d01d0f01d0390361000c107200f40400e00200200394800c41c021075400f0000400540c4490000704404c000c00c02c15040303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 24405581 1250 24404331 24404339
    0x7020d140f06221b0f030c0302040b04050f01120c05031005070815010507080304060b04090b01140d110906010507051203040c080d08010905090a141606080702030d020319050907 78
    0x8140440200303e00c41851200d02041501101250904403803036100e042482440402c03032030048414603aa1200007801d445c200040f04201502112100b00d0b88251428024503a41804203c184d4004075a04040041d060b0b004111141070700c0300004c6428010010020760940f01c50100342403150200d203080840e0348400074003600740d510514459120b144260440d04031806840000c0c4140300b502400340443c000440410107000c0306501c03030040c1d003200400c10800703190146413004c100c841c00d1041501400880486400d6414004405060154401c50211000056104001509030058200380c108502031141d003000810800240303480c0c0c07030a07844480e103e1030a841c1405102c2203036001032000f82c001c65200c02c401c0b50071110850540b1a040000300d01c9039503080c1402d180c03010b2100c02500c2c2803c1b644c10a0443c02020681d00d03940c50705840c0c5081515140c401c10760310340209940c940c1c0180d0042050800080195000e503820504543c001601015041c150400f80c1d00180e0382e0416030742100300108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 24406831 1250 24405581 24405583
    0x50c0301030b060a06020a11010e0d1b05060c03030a020c0f030a030e070603020a0f0f0513060c02151215010201020d0603080a0201050906060d0f0c09050408040305060601050301031707020d140f 85
    0x10758440000c495100b04d407814000029100c244403000100b00b20b0421041242d1303680124006020200c014010400311101e07420b0050048a02c00c1e108040c0900420300456141004021a1100d50061000b14a940c4680c0e14403030095110300c0400c8294000d440b000e6075503c1051000340150841d40d9008951903840c00c540500301003007640301038245403041100340f040d6500f003109940340184d541071454806030705500c01d403183e200b616000c844400f5091404a001c0750045000c0566500036a00000718011100c40b421040c41041c4441c1070b0040110b001488400000300c4003404800f0610001d0705106a040d000000c0d5440c80d00121000c0c0004217414000c15030910620f640319070a08010709850038418082241003100b404081d0988a105280d2414455180c14003402080104020441482d26080c502c071160050b00048400b030240d180490070a6114200303032030507a40c05c8810350980da140c151080559070f00c1102c0480c0c00820800d840408982040c1480c10f40b86d1410300a0940c20111810301 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 24408081 1250 24406831 24406853
    0x1804020607170319150303180f0603020a030e010603111306080303010e0604050601020601051e180109090c08030a02070e150405040506060f0a08030f0c0f011e0509030307080c0a0507020301050c030103 88
    0x4044d482d01e80030300c0305819041500d20449815003000f8a922640d00086030f0700c168540c0001c44c01d04060100040c0305036040d0b0040001041c1c96808100d494030200c0c405007610384d50712014003120146081961240b408016004801c0c107210000500c207a81c5592560131a0402d80c400c005140522040000c6c1d820304e809155480002480039003040c1d0304140016441243c0340c98603a10780c1d40e140d0010460394407100307212039008800c00d000400340c1d81d40c1c00d802405000b03607000c100d8484240c107600107507000000094514a25040d0007030728a0f00c2c1000455039a81c4c500074100a0f8041c0d001c40d114105454621986005a00400150099103031103805d000c00c0b41d480d030603050b004920403c0704024001c03001c410341e0002084000401c0e070324038403a01c1103440c050401401d00401c0d482d2a142048074001d8160a446880c0e84810a0001d0341d54400c45d03c0d01c03800129444004a02c00c00009044a1284001420342145504015042c07200c5900880d0071200108e41d2421600300020044c0b09202ca54105 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 24409331 1250 24408081 24408121
    0x415020d090b1914070209040f0309080601032d0204150905060d050c0405040c05030f0c040c0f08070c0501110f030402030709110703050310031205070c080c18040206071703 76
    0x40c0b070030815030002d034104201c1584000402c801c000544c900310203103004440f415034009065420a040508100c2607010405500301c0114400200000d694038010035042d040b240c00c0030031048110700c0700d88004107043c0103942d0318201103488900080142d80c4c80c03213a074801140d4040140301250500c5440310403264081d2202d031240461b08104000180c00003000703034141c4015178000c42c894882c0e1511110b41101c94000c9541801424401000078000250300c5110400480d03052007402c80741d000545a60b000c409410740002c2101d400580114007a046040b642403080c000041c5041c448145c245441e0440f850051006030000184802d502e0204000740c050165010100b0a0100c180c00d84541c0c2e02c41d24000030184803000c00000d501007501c00c1c000c0010340e08000039414060509100a105074040c950845458903103c90100300000000740101c02c040c0d02407c109000001940d00501c0c03181c00030300407030303200c20100301200000b0b840b0283c511144807400a03003a1a8108559405014507501d50 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 24410581 1250 24409331 24409349
    0x11031801020c1207060f0e1b04020702010c02012f0307060f060503031c020903070303030b01020f0106080706051b030406090f1508040602071104050414010b030a020310020903030415020d09 83
    0x3202c0060004200010003a014000c0103540301c10500d4600e01600c01c44810740002c2d45403c80800803e0000708840e141c42c011b803444501c034007441500704800c0f8041d8600203400600762a1906005502403881c0d0130a041e0319900c0c680204100c0c09080005910401c00e0500c6030b00045084c0080114502642e003469441c134000740401820310020a50764010300c910440007207240340854049211030f5044507a00403024060300c104030707100d0801501400400143c24014801c00f50006046401840b0300c1d8180e07181324019210349890000103e8040d00012181d9024602030075001d070f0241800c01c01000107040a48840003254900143d04254256a038000024031071046400b54816501041c000e501c25440100140c1f100c002d410b00010b207001050986409c2841c080521080c8030300540340050910101c0024028248085e06058862003c0c071070080d0960b02240c3c04059803401c5030040c1c600500c1c00707003c0701c0c2402d42d12444c404400d9070450260b809038002075460600154401c05480103444112 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 24411831 1250 24410581 24410587
    0x200c010216030b0a0c050f0c0102071a04030c02090a0f06080c0102010c11071503060b0703030902040606090501020a021e06030708011401090b0909100b040f170f060403140403061103180102 83
    0x501d40c03100100f00101090300644e82d80c0031007000035001c3e2080c1d07141d042199040f180c0300d18090300154006d5004c0b1409690702804c04007500c4085040d0b90640b40318039803540da141300b184030136800c1c058462000f40003404c242d030711000c00300e00c282030031b201f164000d00442c0e0082605003081c0002908480407d030020b010020307449a509481000003600ba0200da814080c07606401d05102c000711f0080030a60440c2c00401c0d400200320b070500d0ba140d00b2011340b213402202c04000c074a5940006848015481c030820380941c105200010161030f0110340281c0d4410401c12500b2061468000110654411501d12002c660003070014061042a08403040c0c6560302800c080d41c016060011000b801d00034103a0042c4a001c3d8103000940c0402c02d2240c40b4014180c40999a494030780b6501c010413030001901604004140f0a00000c950354070004250101a010302c01410850b216924201e40d46500b910809506080c00c000010004042d0f100ea0b0107540e00100201ea1281041c080c1090000040c5201c007100c0c0c1e0042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 24413081 1250 24411831 24411833
    0x3060f020304030c0f050102040e0108060402010e1e01050c0a05070b2101060507020409050f0106060203040612050c041a0418020403031805010503070e0d06020a020105040b0a020424200c01021603 86
    0x307132619095044840501a07a004c0e182040c064416904400344100c1210b00001c0c1d41080080ca941c0114800d8a4291610b10944c061000484081d000751700603100401c400c8205501641c0100b07001e80200042da00c2c0404152119031500480f9840b001c03080400142c0d0407120740900300c46141d2f010b071035072482140354500140100075006401c4041d00c2150f580319000100081005004041c40340c5400034044140e6030840a51650841e1041c9008115015510060400320784035680c491981c0660301d030705041c00c104007081a1441e8060010b48000200f0012503c00c002542e2005803c04007500540c0d92421883c1c014500301c106c43d401016050780c3c1e14180260303070300301040d20303070141113171401c40c00340070b540c000080c7e0b5020035200190109100085420040340d040d0403aa1159000340e0100d0000c1e1240c844500480c840c03407241c05803480d61281015040c1030744d54010207250940b0720704282d0340450029403665102c0e1420021385554446200300c80f465070140072070084003004442c8510854a1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 24414331 1250 24413081 24413087
    0x1305060607020909011404050304051302040e041b0306020d061403031602040e0a080d05040302070509010f030602030411060c07180b03070306110c1e0606040b10030b0a050d0c03060f02030403 84
    0x74150000788910701c108001418040c0950003c402050400100c10007424607080054507030f8850700400c0d0044812031010100b400c03685c000c403030454131201156400c80da1151140f0f4004000440c501000010685001003c502c060014020300c4d4101c007400141c80d490002c441c1990035140c040c2c940690400e1007500d28000001d400e0070300140e010707500841c1c450690140c5030704125800000420040c0b0210305040074495952140e8441d610913021150307141d46400412081c0d500901c945200180d0140d8280001416034000d1a005446040c00b0845540741c6000103401c0d420148901c125a4404941001840501c042454580103401020006000388070040380e01c0e900903000240442d515154510300e203401c1c10b011622280320300320681da00344a0420110300b040343d111003000c00620843d0b0101d4200d262030310a401d20700b84000c04265111100c1324007500504401180564455041070f00001e00c2d8580700703038400c49588a40d514114050541c070306501200d0400200c526501e03c14030800c40000c3d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 24415581 1250 24414331 24414337
    0xa0801061b02030618100e0109141504120201020405060a0c0203010b06130506031803030f070f02070e0103030e01110102040801020703090b040506030c0f070507060f0e01080f060103020c0a0501051513050606 91
    0x32291408411715002046a00d0020782290341d09203645006d101e03808001066014010181c400d8059528031001984107554030031200c250301b0807090b044000720380010f19211188246040310300015080c159140006221500031624000110700100300034021880d0078802e2680044046a4450600905d055000480040c0d80100303406548004086803040001e03e401c0c401c50f00f0302004480c1e6034504114000500314007a548040800c002480e282c5d00c580c004120542035a800060f41c0980f80e180d51800c0358404c1d2000043c50500c0f21007048029181000e000504c00f40011400144c0d032046589402081c45031294000303880104c1c24002402541c0e0341d4011030742c1100c68001029103a1159400b100c1c828402c851000301a4401e00d400010320030341050440c0446106a21190519800c034001901c480904942160050b500440054600d45c0681d0140c111010490101d0385c04030010f9a40c85d08490040d100d120448d0303180103240c1c5251520641c041c0015032080014046401c090010071b100f80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 24416831 1250 24415581 24415591
    0x2033c0705010f09030b01120507090207020f010302030402043e1602010503041509060606080c090a03060c0509040608010203010504050108070e0703091e21020703170702030307080a0801061b020306 87
    0xc80407440e190700d92031042182c840519000540f4000c81d580d48c1032046600c2d48804001c4955000310240040d00c51f803140309440c50243c010789514000c03403074200110001e44c00200126409a61100ca0028603118031020044029102c031140c11180b018902d1300c41c43c00d0019041c41c080550401900d50714802c003105200541e0b90a090203503da031100d1030b00388000c81900c4210300705949003001110a025041d000a000c980003625400d01c152144d92955000e81308505480b500403418080c2040020215800101d40300b10f00e140082c20030250800050a90f9455400718030642c1d0044014400740c03415120311801040d47c1401800300516148190492082c0100700000f410390f00c2212009202580c02c0402c10340041d9100c03507402a103545000068107000d01c00344c502410b4031003580c2c840c4500008040c805e0f43e41040c00360381c004603421100503a0b94071041040340c05010074410f110009100724042c02d43c850558650b1021503041110040000c0b000c00081c0034042009280080980c9001c5171590b040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 24418081 1250 24416831 24416837
    0xc041a0409032003091003050103260409090606090e030408061503030f21060909070302120c030d0c0506070314011202010c05030406030606080903040b040e09070302033c070501 78
    0x20701841d09090b82c07506400340c260b80c040070f42e6903040781442c20f0100092a5104007101c607800841c401290407000c40740240001069101501c1c48924444114603a02c031104207181c4890340381036103954010040c1d400c2c4020849403c0e40750b440510040307a17103010300c152042c034800043d07003007a1a00f501e4a80e206c0d40900450a2105111004001e64030184200c401800440134540e40d5060000110404e4503149a40070360182c124801098140ca0b00340182400344400e00b00801c1510306680030040b9020003609441070b24407841c0c0807042075071800d1086050400c501e484003a00b070030150401e40d0524000800381d008141c0351550391030340131031000704950540d0f40b51403640001035032610041e103144e078080300090401e100104e80041c15076071541000007901d04660b078105050304d511805aa8034010b90044110400e0140b000b441010b81d0b000c80e09501c012107004540c209990394002c607080500380c1440803281c08900440e6240c0392800f0903020403441d00f04200c01440c45007921110384403000c0303000305410 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 24419331 1250 24418081 24418091
    0x20c0c04051e1e010e190903021b03030d0e01060303020f06040309060e12070b0d06050a030206070206090604030614270a1509060203090a0507050a03030e1507060203180c041a04 78
    0x30f0303d1916121050385204031040302125619010300001400f001c031000c01030028510f44030080540e460040040c4c441e81500207007095901a0707001c01824215500b403540500c002d0260303c144802c18080d00c0c0442c0124800004c0f80d03421414001d00308114410010915400013082c000000e92000c07034030044444614054000355031400000740c00740f42c042c11601c140d05c01c802d804140502e5680050120601c1c1160800c001a525420f210240034944400f0358000030500100001d810903d008101c3e04038010030613858140c8030f6588104a810070100d80bd0f580d91181c041080400e40d880c1040d1807503c040b11030212100d10040a1961041e03000801007240305180c40046006e10160440f500c4240e20510a6440e480c0c9215002d5503091550010b0343c1600c10311703900003a40c0c1015910003080d07039050f03900c50305080c1d02c007414408150b0001d8800c42c942c0c9010042800420810301c0650b020f0108036402e44c1c007004d401507115252500d900312162080d803402e030140c4241e45022103140c410f80e030180c5001c98 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 24420581 1250 24419331 24419341
    0x2070b0d05040c0e040318150503011a04121202070f1220060d1a0d030207091a0603090c0a08010b060403020103050c090a081c03060b0a0c11040f020c0c04051e 70
    0x14031451164820413100d80c0d814140810903410100b289590801e0800408403507603213030b6048181d00c4100d6130003004100d0820041c45810100790707814a600804900031071030a55240010951400c500c0010344251490440c0c20700300c6503041c8104d03001040d0403840503840c85c1c1070a01c1054016005500140301a26084454121201c844101440001c006180e43d484414046910024010925120042d03514418003c2031901d4401d412240583e01640140079290610b20710300c00410400302900fa45080b01044800b869031401c00440c801e0416801414201e0503000620036100f26030782007504d6690412500340d0f1503803030300c5d42500e040780e0302442d01080c0768640e580394000d288541c0801076007103415500d0200b0032f00c4c030008100800d075449441804058555200480440d2403500a085c00c00780e0400162003103d1065103100003079070042e5440500c0190290000c1c0440d07070199510a03050744c000c9860b461000003404003114114056501740041d142c603190020700d54079092680d91904100f440416 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 24421831 1250 24420581 24420593
    0x10050409062711031203010e0705070501021c0515010816090b160308090c150a050c060106080106030606031103060904050703080c031b010b0f04050702030d050a091202070b0d0504 79
    0x1481d9486684184100282c40b1200714881e02c00e65403d9807009903040c6459200d0a001803a5039104400014a50451342041601204000003a2103407040000a0100c03001080d42072009156200800741030020608210100c5000d44000400485c1000903590001c48182d820542031a444046a0003464460301003a04c00e0b66507040b02e80020041e4400400d00f000d034100031400b1400b180d40241c80e9543c8541d0340b251440d40d17070081420a10b4000d00c0b100100d202100845020348240b400386c3c10000d050a03d940c0003a8070780f035000d0340f0940001e03144030010440c0780c0e014803d04d00584820b02c0d09000070250350394040810720001e01351901500d4070000103000d00c00207200800c041c40d80f01c82e401e91b4410100300141c0c0d590708640005044020081c2c0d502c02d00f410148111032000c0d4021b0141300b81903445800b0040208070050000c01540810020380941c41a2441010f1240001e004d0000e90700d81142403254100b51261010000d540c4140414021652034000f91001503960680119040d92245440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 24423081 1250 24421831 24421841
    0x507022802090c070f030c1104050f011505040f050609060705030c0703020f04061d040507120804080d08010b031501030f060e0604140601051204020a03050f030c06010803031005040906 81
    0x8200340342032250654003449032860102031514021105144075459a0500700c06601c5203042c01008040c030108030f0030001c1e00911030440028050201c032000450723641d0100c1e0030754600b1211001190413180c0180403030484c42001d030744020345e6850480d04043c00c010300c4684070202401098460391001c9900012680d9480071075012907480340590b40c40d80c80c0301c02040c0c1d0b501510301007244140410441d020349030509210b50000c44031108408030407800360b022582400e100c042c0c0159154000c10314082165102400c64103d0a8440d5048598aa03c0c02c400d0301e0070007600d54500b1b010000c64800421190240c1012750340c104801000c1a0f025290540c0140c00410500124104017400d2450004d00c4215452000b481404141c4040c000c0c400c185100c035507007141c00c85842d070114206000131040031640f03450380c641c054805411004900d46989403203203000902d25102c80590320000d180b405031402400300900400c03200c0011800d6080c074001031081d002c03550080c80e006a68440200061020507005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 24424331 1250 24423081 24423103
    0x315040b03100606020f120f0301150c0b010807030b1608010303080901140a1b0306050a091e02040e160903030e011110110405011812080c0709020c0703020a060c0c030303050702 78
    0x7006050341d03035136001c0c0d01d03594094840c44080c02a0000d41e80004480400c441c00750790542c010390702d5a801c0240700d46180d000d00c0301c0c10082040d15140600000c0010044901030200e802c01041c0313161a43c9004c40b81142c0050215940c20440310642d9000c5c0c2e0410701550540750706051400d501d65035002d40c580100001c0c800f41c034400d000c42050000719506d40d80144506e090035010f551400c3e00350300c410ba090312101e124103508aa42e0355400c21401030340e0b510200e0400f400029200c02c1280e0180c046050360442d820482c0904110001d010268045500e80c0030f0407000e6042040009143d500c2c050100713a0b001025505001032100b00010a06051102686c11007080104000d490404404002d00e40c000d400751501260040b9101c09144280a80c1d8070304a80320101280c1c10380f132055445075103a4102c0019a030785403041e04e02c046400700c3d2a002504810320300ea0010800c142c9540100100b01c0c4041e0b11000902c0310752012000410340458881064a0300750030089842c0e111360f03070101d01d03007110308007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 24425581 1250 24424331 24424363
    0x306041e0c03030c0c051806040f0605060c030301050406080a0302030901030908070501090b0924040807020f031209040c03020405090a0b0109050307090203090606060a09140103140f07090603020315040b03 90
    0x700110030540c2019000407001c0c001c0d8181401281c4400a1103444c03980e0340d003560050464100080c0407883d00307030094000160b040703c01180c115a240c0115a01e60070010858205810100040c8080e0900c1d03c1240c000307181c003500802507a0300d140c40207900c910464111a04241d1035103d00800d01200303008403242654020020800c4454504141d00c0c400400d40e8a4a4680511008020240c182c1c801074201d44a09100e04805070f101ca076034541c1c40790302210003282c04c1080700d0300c1d601c00d07650240000c1d0842c0110516007a41c640e14041000100c0f036130346400e10241032052200b48215101c6001c41c550280c0000c60002d801032403280142c464200303e61003184d140c1706018010071041c00c5074020398000c3c800d0604407081d980310882000000e0042302e402000264600b681000b061619000640341c42006040028101c031b01415a240c042104540c0303003c048601406000000343e0200641e00140700b01d10b01141141090242c0d00e40260040c05001d00c929198445601d29a8092000300343c0903020034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 24426831 1250 24425581 24425603
    0x80307180308040603050417251a0106050408010b01091412010f020309030909060a08030304020603100906030807331e0e010e07060905030718090c0e160309020306041e 74
    0x184c4002c0c081d10007100c04980e41a4400d134142c058030107010641d0013a040d000a003580807942e0418144000418400941e10466002051a80b500e4502c8016000e4074141d62002d036a9030401c814035003506c0d0610161810841015400c02c2540040c0c07441220441e421200328201c10401140c09014202c3c0c41d00b1189800d03c0001404280310001004041c1103a0aa038040d010b5900c601c01c119049065110714400b03070b041000081c00601d0403c0040d0b500031083e10392141e426817a030818004444c101e40080312402c4000641006008884074041100c030140910024040102e60683c0005081c10750492006038440c01c001c07040c920354a802042c03204158000300304006030090a18041d01e940c5e0400e11042c09600004030b07400f0721414650341034940140040034001d150042e80c1115480c03000e52008955650941c05000418644d0b6000c010702040412104c2801c10400c5161103114082d142400c0c585061594030040c1c90105080380d0107600300d21fa41c00c1c0c078030f05030340301c08051510000001d08094400f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 24428081 1250 24426831 24426839
    0x201050c010e010f060803040308030403050a021504050a151506030b01210501090605030d05070803040c0506030f090c030120070503120a050a06150e0918030c010f05100308030718030804 82
    0x150b1080350040c3e085113003800203035610324050b0307100c2c8aa800042d08c4800104005070101e40120300401d9440404c1c0304440004040c05a8140c10180c152000c41d0f494000d030309100280642070441c101d042e084a0820803404250003541c00c9a20300c148142c00c241030b250100b540c2c0580c000c0b5481001d1012180400d81400e00b85610700b0000c01c001d002d0070080c2e914000c1c0129880c2000100400c006045469251600c600b61f140c800d40354200030030881d40c11703010100100c3c5589900c80a54098140d00c403080d089030500000301414900d1803040d81e4000e81c580102c990888501c15075919a15020044250744d0315507904201f0b04500c9045400721010041800740580d03c502c0b07074002440307084650010080d440e182c10701c1c0c2c40040001e0040100103007203069101514902029040e400c4240e0a000ca40304140c2102c0850444d0850364030100c051759152841411b40880b4022160710608483e502c401c282c0c119500c01c130f40c500010b4058410441c0c0001d004000541c1d00039000c02854015405685031646c0f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 24429331 1250 24428081 24428083
    0x40f05010f15050301180305040b30040507080d0504050603040c1e031709060d0203071e0c06051003030c03050c03040302041401051008041203090206091201090515011d040201050c010e 81
    0x20b10b1256502962815050403191200120045002581135035082c1c5040c0c0303489044003241e000070b4540c1090b920055110150001343d0252204080208484070207107180c6420700a0030803820703502144041e040030869025040e408003c4405442003290a142c903610350741001001814560809906070440800310021a0150204502100d1068800c2010311103510000e107150700800d4080c0e500304105200c24045560203401640d8030000c00d00e468200300004601c00416074156040c1e24000c903000111020038003807030707004150f4011001035980c03180740d241d543d004049400320b010190400c0780225080c400c148080c01241d00443d00100180820000355418000c04c00c401c0c840c05208204000800d92101d002d180742d148115001100c0c00f0034020b00141c01d9001d000e200f40c08030781c0541e08000380305107582c581c1e4840c0f203800c0d0424000507030314915103007040c0780074a501c8110031900444c900400c81c0181e5140c00103148000041520040d88403840180e40500490b4a40441942400d0002d900104 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 24430581 1250 24429331 24429371
    0x1507060c180b040b0904020705010b03100b0f010302070b16090f03031e0f0e060309010609021b0607110601090c1103030a0b010206060a030201020a0b0601180602010902150909040f05010f 82
    0x1003201a4031901c0d030b075110107036025485903105200b0700d548244148000343c50983d0181440c00e01840c008a402c00c070f600d000a0514279076420181026586a0014000b400d214074085000102800c0071442e240362a140c028440034024000032030f4403048010901010300ca8822a00104240b004425505407686805031090322243e98551140c0c080c0c680341302c2018403a0a8a18012002e80c0300d0145113800201400203641c4000c0140c1d060b5900c0d40c00001d21441d44d0710050103e0341100d007015502c400200d01c07050070320001820490800284009140000e817022400c2d034119503040078005038030850104140d5080142550801440c0408810060550201d030800c1c0c8030b00d0002d80c2515800d60301e600401251904501010340164044020b0900242e0310f8905c03140c0180c01410704500d000011896140c0c1c040c015000080180d458100c45000c502700600340c02e146a0a804040b42400c07103c4002ca0544200148003414034102010b0b00c3e424482c1c00e50041c89461030900701808251b0103a40444c2200c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 24431831 1250 24430581 24430607
    0xc0f1b01050a0507030605060304020103050a02041809020a09090b0f04170c0a0204050619030318050303040303120b010503060f0405070e0306130201020606040603030905010807030e0607030c081003030207051507060c 95
    0xd0700f008001000c203480f80c80360710282d8600034205415502c0f02c1d001100180780c01003030104544d50802c00071880b204011440120071000c000c006c100f407511031042c4040101640e1240f503100303060407d1000000d01e801c003140e03170048000b1100c0c059603a840c181102840c1c0500c9110441c03680000d689688648041494031901d402910248010703181c0c01c062120000842000f41c0034a41c641100b840000c2c81183d030900800049040c1d0321550303072101c0c0002d00356407041d40700720041246507402d040e450700c07031b4080c80074074500900703000341103260903404a07004e01131500c0000c1c0310b41d60b140b0000d0085030145d00c0707088a00303501074120b90042c0703800d005c2c1942914601c0400c1c0d015115400016401d0b14290142c02c041d40d504d41d440e00c4549180000669007410068800002c0c99152a40004080704c10010540300e444903079030224140ea0780d24400741c030400740980724841901d00d0410510102e900051248100c540070340f00040c1142c50411400150301500c40014400d905203c8448400d075400000410b030741d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 24433081 1250 24431831 24431851
    0x7031209060902100c1e06090206030c0a09090207020105090609031504150b09130618140615060a02070b030c090904120f020304061b06090b090a0c090b03060c0f1b0105 74
    0x1c07092462041c2d400c501140f000402070704014a0500c98641c00103200850203104107c007140262080d400a80ca40d0421205000721210100303400030700300d81c48400000101003902c011482c10801c1d03000280b0314850907040310b02481c80041c403003c2c0e80d10200007000101041080d40e143e1810b0620304148071030f000c105138007402810485108a140340c100c9503a4007803421412800c0315440141e541e40c0242c0103821245a107410480c2044000c5003042944190400002d0054603003450141c0111800b1048201c140e402810706001b120095600041c03e078003550b00d6640c2040e260790f2074032182941e03445218181074210320440184010000390740354a018910681d110341e41e509681c070350200da03280524400c10700014000207100c041001c0f0b0103d07400c1c0e19401a00b01281418650b180c100c0d0141d002d83d410803060f0b000102c0d40381805002841070014008109080c0160008100002d9a40034041c004c094000b10006607640b4aa06a40881e5404002c4280c0140100c1d01000c5013030090908580035452 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 24434331 1250 24433081 24433099
    0x270c0905030106140904060b1f080901141e0c090d0602030615030f0406112109060603061014061b0601030b090a0807060c02010f11070309090e030a0507031209060902 73
    0x480c0d0f40e81d8100c04c0362000c0241003094955919200c0740d01a2506956198214a500c0300b54014a0007007040d604411800d6215203040f420b0044405085500a61401e00c0c0c0003c89020310580c41052589000b498240000148241c0c4410b01d60b21403074410a00343d07540c000f201c86c01c0c03c400c0240d035801851090700104c920518030010140c40003401c0c40100c0c3e00f416076880100015001680d140d101070280041485014140524070703a00f8005d140064144100c4019400c080000c1001d040100c942d00000c140c0c043e2a00d42002800c2212080c0d160055980c003406502c40b110168481034144d4540e01d62008030a00c00131181141961201820b00056034800c8001001852906000603000d070003c0c7d01c0040c5600c1c2c01001d44410005020580d288401c554880c4000441c0394018003c0c21051490034407640d540785070500e030140c401c00035030f404814098140007510401510200c02e40d00b414019081c903035940c00c2240f80803280040c0c0c510f500b0089600c0c2540340010700203168480350155200780c3e00251 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 24435581 1250 24434331 24434339
    0x60c0a060b090601050f0a12050c0c010b0d0506010621050f01080f07030c03020105030601111b03011413030804020d080a030c0f0503040b07030e010b0a0e090106050a0b04270c0905030106 82
    0x2040c0108940844c0842c0d01003101e0030032402440c0c001c1252107101c0c50310740041003c5101003000d8a03403e8031201c54150001c03d0903072400f80e003071141d40000402150841d0b80141c0c4d595900c0e071600342c1442420103102116001e40076648807000c0a03c2c512258540070003c42c40d0100008941d00020300030340c950f9104084103420071007400152a020390b5000769060102c940341d0750044619602c014000d0f410046c20a02c00d0091000410000e0754828860306c0342d4014454000c18103003100c2840503000004003c0380d043c0640101220501d40b4201d80618041006544600201d0311440034010000c011502c000740400301706525901c050101d49441da00c2e00f42184540d90200c42c140001e83e806403008480402050843d4043c0e4441c42c1c102ca5880000b041011024000442d41c10081c5c1c80050300160710401c000e030244081c441d610142000b00ea28a03461400d25010b041d03076000350300581c404090031140c4000b1442100c40c201d400845568400d00007440500030041c0070b0b007101d00ca0f280c0650b00340f83c0041 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 24436831 1250 24435581 24435589
    0x50601062007140406030203010905010504021005040b07060c0509060a020c01020709050103050312040c080106080a020909010c080406091a010312030c0201060614131208030f0703020702060712030b060c0a060b 92
    0x500000c000002001d03038900f401d25144200c038003820859803184e078403800003005840a0040c440303190701600002503039162500502c44d017401104070a07803c10000b0002801320b034800380b041e0307240e183c0c0004000805c00b007081015903a512410552560103040882d00c4822540c3c0090a84210701703080e400d0703030011580c0d1440c903002d0716400e000007000b541051021445200b0006000356129001b0088594210340d5012050308590640d00500626000000000150706000410700e411100c032000800480d648441d000340704910150008211544607128502840120880c000c0812841a050300d440e50307491030700c084220b1400360001c010909050781182c40c14010b1003124211034003500c1d003000b00c0f8031108030343e00f255028400c010150807100c80003241510100960000c034a01c5079032141d17500d08044142ca20030240041032102050b004010f501e0058a50000341c0d81c1c456400024859074100a903002d40161070301c0c00e14a5000040860186014400040e2030b55005009850411040e20720030144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 24438081 1250 24436831 24436877
    0x40b0c0c0102120706051f0602030d1b08010e0a1b11010e06061011030705030a111905030703030e030d0e03030601031404020312030c0d0c090302090c1206060a0201020c0102030405060106 82
    0xf41d00861410b00494020401035008030354805005140002c0701400b911951510b4030b8180c024100590000c00d0b0100d00005c3d511079071038035a00c46049513981e8030480340000c0409a05000320500b145100002c1a8400340a8004010304000c040e0340d1520004075131001441603402080201b580c0d800c241c1c0ba41c540a50102d0900d000d480080c3c801017483d50030070b00a84500240079407e00c0c141c0310800424001c0b500c00e1002d050030401030340d500d55441c030306410b0301480c01511458010301100340d803552000040c0000106c4134500d50608020440190141d90139045000b12100c8600090a0480038820200003000452103014240c0342040200d01d242d83d90100e040040350700079010f030300168079641280740003000780d0b910403000b04110b8607041c0801d098405075044028a00c0204614041c144110f1403c5004540e0003410450b04908206000d0300c603680c40310015203024041d80d000500c030014a4400c1d0115000001404000d40da0b9003003500c0c00070341d82c5a00340b04d401c2c0001e80703500030200e400ae250f1540d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 24439331 1250 24438081 24438103
    0x30f0105010c1a0612030c0c0a0b04060f121e090605100f03020925050406020105150d021212130504060602030c0307080d1b0201050901110310061404030602040b0c0c0102 75
    0x41001d0001c00c00c1c0d064080740f0805003005610140b854460851454208010410010032601828566880d0030a00c40c002d01c1a80020341948010f00041c4078681e4400445144214107141c15066500a903400d4402000c03044994060707980d41905d1000031078070a4204620682c0304800030450b6503505005518203011078000c13072110070716442c401c20252400c0600240c0040d025981e10007001214032283d901000e2000412011940111301088050780a2040035441203c000f4505c80644201c0000b4502c040071249c020710446000750b0085030750788100124120048000c00d525910181840f480d001540b19200b00b44c800d134103109003c14114804400e54220600400c0294108080380da00c180319500400e169100207039551000c2c012044400c14080114500d5800004441c10324190240c03e54198003842c42800500f0400d2041c200c020000f01c008880e841c1c0b404004201d40100c144401d4030880c1d101900860000c60045100c07200b44005049001d006d004450720b512820006a0b2a0a00011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 24440581 1250 24439331 24439343
    0x40605100501030b01050a12060b04060903140712140a050601170c0604050303031803070515070314040201050f070317040302250509060f0d0204050708070318050d0f23030f0105010c 80
    0x11520307d0a60090091304845d01c2c660700c0c08111360761074031501403080e0041c3e0b00c040c0c0040c2941c0000c00a1060040c0944c12844908010b4000c3d0f5041031460007601c01c1c040001004036850b91019841c43d0403d1180d091440d9024094038502d50351070403108490140e2203a83d03806405808003400e0f0502c1c00c042124202c500c050007a508540d01c11580c48a07140b98002121501d010810003000091400d120314540f10166240c141700d9400e060350300a084804101050701081002002e1001507038010003624050780c1100c03200d503600d190302e00d002c0b580d1032030348402c0d140e6403407000c0c1c21701c0201030300400c0340c1041c40c040803032a05108080c070f0740603c80410f1a100d15500701ea407400c003013402410311002d8100348610151a082d80c1d100d10f54045400c86208455880000f0466002c0c003490692502658030340c0c0d0150002056161200d84407203440d407065000580030f02c00c03250a101c14103801003001c82a0b00b44003500686450006d54046517999104a0700324051500301400441c0d20b6006425140419030042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 24441831 1250 24440581 24440587
    0xe0d02210c0c0105090a080706050a030513030207090b12070e010509090601060804020409170d051b0703051603030608070906030c0e011d0402031f0f0516120b0d020405040605100501030b0105 84
    0x10b80152103642c0b00c4980550000400707803002c00c0d03c0e103080110000230f260780e03035406648004145000341207440c040c08030b02c0c07041c242d0f143c1c100200340c0c009646001c2e501041c50015a10b190300d4006415408804008500740c014510300103594400d014609040b104156910351391596034680c4e03107032038141c00d01a100200d04040086005802c2a510409025110740100b01c400611000d410325142c0040c10f0500416441e10104042481c001c00c00405180c036044925040c4800380d40d000d0702a0084008040400d6118508841414483e400541c020300f07002c02034400c05910350f9000c2c40071f02404d0100b650b0440b106440054001c3c8960310003412a040345080c400600c24100d2280780031071000c2c109992600c541c0202210b203000351061903800403884080000ca0800c0180c481d029903a00610b406003403039124603009421500611600e11001c517900c00042c42072528070024020344a00203019412a250004100800c1303c1e69100501502031501424190b5940b01e004600740e410810b81e40d40060014 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 24443081 1250 24441831 24441853
    0xa11030702120c07091419020a0e091504060308070605070206010311040c020f030301060309050106080303060a210501020a05041e0b04090c0309050118030f03050c041401030e0d02210c 81
    0x190000c0c00b0408915400c2e2440e0f180d48254241c02c3d1640000d0751240c8440d5130040c407d020454074112801132900784030550034002e03c0700c8082c18043e04014098082d04003032000030340ca0442c0010846091000078001c0241580ba030500c20400d0300004400c44140e0716203000314521030700005900d412203500c0b400e844004c0c3e0182d41400041e0000544140651190561006040505001850180581c0d5500042000042c01c280c7d003500e406912041c459002001031000c0c645a1000034010b0b42c90031468450002031408403081a8019200b000e00154808140e030b0000c01d46c03000c000d004071051007090003c2c4030760358827000c090a8a14410552100c0007040100160013640d04101803140342c508000424080c6500c6550944091003880c1c0030210ba110007800805422080c1718508100c1e5103000c01541c078003002c0c1c86046100e030380a1004460b00010320003070f03a0f070b203c0e412281452080e402035520310b44105501030350741c103580f80c4000c0503080c800d10400d1031001c000058a40d41442c49004080b1000f0b1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 24444331 1250 24443081 24443113
    0x1403030c04031103010f0516020d11030711010c0503040b12010602150403110f1e19050c0405040c240306150206061002070b0403051018050c090a15030305030a11030702 74
    0x243c81c4816030035540720b80c0030185402c002d20034a4030800d200300c141072018402a00003800c12800118000c18000a0805103402c08000400c0d074101d181d101e0040110040c08000585540c146007600508911001070003003010240c04002d8441c658200788101000e03600c500c42680c94104260804070040300365400038000c00d11030101c40d00001081c009403034901e4503001c0c031b880c05e11010380c1c40590031381c980045a414410003000551844101884081c001066582c5d5003500c48110700301c090300c55030701c130000314007072014505820300100380f4a03a0000f546001c11560810350308031848424082840c0c4000003d591250701c004c24020000c5601500203541c0e00ba080180c00201326000c0021880751603408681d0028040c0148013075802900100a0744040c5503144041e610b13030b003050001130f00142001c040001e0000810f441c1d2008221003000a55850b52510001032001140e01d2400844040d800410701d5044001580500388520703040c40183c407540703502c1d40148011740b4a40c00607030086140000f0401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 24445581 1250 24444331 24444353
    0x30f0708101d100504050402010219030e0406031b05010302090d0b04080f031e1509010603020c1f02040504061d010b03071806030b030c0102010606050d0207030504030606121403030c0403 82
    0xc1d420070380e0760140b629544000b048452841400e2915892103060210b00a840d0100200804003180c06115525044d80000d485402100d48031024107812103010003094001c5030051301140b00600f08000859030b0b410029412078410510280142c00410081183c0d4460700888468941c00351558440015036512540c0900000308180c94044061104548903020000114000c00300906d180e100090351005044040801404490740114090010103040c1c580407480d07411a0b90b582001070301e5500b03510015040400e03850205503882d460040b8114034290b194090410348000740d07002c00040b901c07000015001c0f80c1c01c0d40105006220035004001c0030016000455004010b46040c2036041851064890300028580158000c030391a0003610200e81030822081c5600402403000f0700046103018030290543c400c00d030030555801d800061060034035008030101d600a6500103000c00800b507564146000c1000ea001e4119032400302e001c14070f258180004240ca009002d0752844610302840e6660b401e803051 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 24446831 1250 24445581 24445591
    0x10140315010921051606020c010c1e0503030a06080c060706091707050d0f0507030c14150f01060f02030a020c132405040507020102070b0105060a0203040b040f0303020111030f0708 79
    0x903500c03201050545941540c5811083c5010203000701c44400e142c880d090110100f80e5a0130050741d04410440e180d40014600360043d03080c01d10087d1003040b410500d48103160004440051440d0100042c10081b00000030340c482c00e01c01400700000c50710b402c400e940b107082d115096903200c0b105000c0c8101084040c1d11020365607104059150400301c0b1440803100c15004000b0a82c3c8a0f08541d0040e4003545c1c0041151060255600d0300038030b0240d10f07a401401c0004510400380c507041e040c0c00d425000403010030000d40c030704082c4084900c1501e001030941c803011609005500008034000c041000c030500010a90385810101e401500c000d28800091103070705245040c0c0f480030141c0390ba031121500d400500c0c210b06404542d15807801000d090400707000581d44050502001c5a10402c10503012508103200c00b03065030400c030782003075560740d40d640228618011a0891594450002070000c0c0c1b002e00d80b40d0003070492748079030001d205042c1c0702034a22280d0f0104852114440704d0810004034518842d010340b580c06 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 24448081 1250 24446831 24446837
    0x30412020f0a0c090b04020304020d06050c0405060c01020705010b0f10030b0a0b04060c030206070e060a110102190207030b070302070b060603060d0501110405120a030c0201051602030a111014031501 87
    0x24015415540b619014460030381e000521118180a0781490303000b20324012009460661a50410354007084854195040280500e951540030a6054010304c00f19001007130700900e15600c448644203518002d501001044840398030344030b81c00c1c0c4541841c6000780480340d401806400d5608100c1c400f078021303181846408d03a00500d000c501107074400300500940081c1c0015696241940c05928000c2c0c43e081c0091700410501c0f40c22240c0070b04940d680d4040740c108800750b01e041e40b0004840c409a41c00390168034040c04c0c0340c12415180b4061240d000036014101ca0141d951a01c0c0d42e15613a009400720703c24100007030f1100144100081d9203082003401103801c8030014001074188146d41c0c0303c0d03a0844000010300002041c0000d02080b039881d0040c0b207034560380001000340c41c02c0740c2c5c159030203003441c8130342c160081c148400858540700702240890103560260300230b001d4400c0440c8900d0840c1c20b0b2810b00110b0b5100342003945204a0482c494450307090188500090680340d030315101d1030310905003052071881d410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 24449331 1250 24448081 24448093
    0x62111030604080c06060114040b07020a03080c010c0210021201170a02041d0c030f0c150c01090503190c110108090f0102040e040c080312040803060406080321010f030803041202 78
    0x200e49007080054400e6010700c84070340e141e802c0c55100c3c4d4109072010b001a4100000d4403040c4c1e5401c02c1c3d50040b201101c1c1c1d1419100c1d503c402c184045031b030040c9540e102404025010400c0c000500040d0080400f58200b039094901540c1542000e070308038040e1140381000c4058601c010f020000c10640703490004d004001c1144d0b600721700c6900040540c0d05009a041d031441e640040010030200030441001041000c401034070051080406990343caa00c100517180c45021841240b03041d680640044072071100c8000000e00c098202824015541d500529810203e055a00550911280b00d070745100310a0740d012416091000c250342c01150100e0020300740001a01070604540034102d42403000300014503403014541c00524150500c2c41e0f11860030ba02c0000203400400008048101d040380655115520600c003548030344403403010400a041c140c008407514400015250400341130011000c0d00d024854810b46200c1c3c1e203e41c40001e00781d90b14840280b103d202400400c0c00a02c40140e00c041b00803451040f07401d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 24450581 1250 24449331 24449363
    0x41211030303041115040b07060b0f1e030d030501240201110a0206040c05030303090613240510050406080c010c02040906140115030b0105040306150801020307030b0a05040621 77
    0x1c11640141c8007198403100e9420790908a0400c90080e5214005411704282081c1c5442100c040794861018001c01d140c1d44c5000d8081d9941c0c0300702c080f010116018100c010003a6001c6401d000c0789448100091081c40b03106d2142401c0c134420b0150078162650b48100c5201650890080600d8480820348441995210001e40500548001c041c1020b0030381c9500038060703801c0c1410400a035200c640c0001d402508200304000c01b56200146950300300c9081c0d01c403281c0510315814005024401150286551504a002c11524041c1d90304440c0c0a1890005010403507607a401c100300407240729100303217400d54101a000c03407020740c004c00b40c071503007940068004900c211140e81d40c507084445950480450f80001c1c001400239011652628100701480d04040180d0402c1d4800607205015611000788001d0b1507030070030100b041c81c40c0c2e19080280300c01380081d0740341e007040c150150150049030241ca020b08140340c000207191a0174081c010031140514001c400704508a40040b0140c803441c40242c501222421440c0d03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 24451831 1250 24450581 24450583
    0x30815060403151e0606090e0405060601080c0c010c11010b040902090604090204110304030f120c0815030109050601060503160206060609150c030313060f09020f09090f160812040b04121103 83
    0x40e000d144c00700c000040d814240000a440c08585401000f6001c0d09441003100060380000c8840e000002400c084110703641c0c0480c403003231510410000c0140355080c440001c003910b0700080548c402011520003403048560500c2030204403442c551010394040c40c10004076420f403c150b403001405070f0000d400402d80d000264a03080c032940c000e440c1140015200903003602c82e264450f0101081240d10032080c0126030415400030f03c1c1220141c400301626a01e00c99440040e42c0c25803060415903404815150355680d10400a060344d00116402125028201500312880344046499403007030703000600d00d90900709008148260840c80400003050f030882000412000242000a948505c08203a00d0022401562a124059a002c00340f000e011b18241240ca00c0107030f403140d0221400c90020f0350b040074265189080145001d95807100000d09018010101c003980d040c420000c2d0569090504a42c00242101e403100b210b0712540c0701e1100c000c14140014804d8003e2400da0090041c0654483c0c3d021f00c800200013 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 24453081 1250 24451831 24451871
    0x50601110109050304030203160e010501050f0702120f0609030c150403030b0a15030b0904020d14070510050309060c0c0a060e030d020a110c0603190b040905030309070303081506040315 81
    0x589581c0c4c4040b0b820011071604000c3c800791000040c4031400450b180c44003419004006000e110305000b00810342030003242060056800c0c1c1d43d001007580300c5e04144a15110749400d003040d40c110306401600005840410004121000414140001c104010342602031012003040074008500705a11012400d00903520041508042c1817041080c0401d50014180581240c0d0300090b4179006210301d504020142c3d42e000040a00b680c0c21010842c984611001c403142420650b403c1280d005040324241255030354018041c44c03141466204544c401e0721018003940441c01171500c1c0310070aa206008060000380a500884082d9804104490034140c443c9003207001e0344c1005422400103100c518040c461500204500503501600344c80040c03a6003081195007a00b44540070f16002160b45821242e070b456110360380007608880d041002d503038981c2412200360b611022144400c1d000180c41c0804201c480314403845503103046100418603458a4a199524201e04804084032182103696580c100c003403004038054 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 24454331 1250 24453081 24453083
    0x6030c04021908070f05090d0201090806010602030c100b0d17070501021b010b010906080a02160506130b0f010e070815030a0501200322020a1d01060305061f03050601110109 76
    0x9000840c42c0c100001020810700400d044208014003c5040b103058100d0210f0742c0b011419190100303980c0f864001a10201040c5e4410700941c0300b01000092050345c00300c0a0440d40d0303054015039120440403c0e0080680300c20503612503004410443c901c1c0022410b1031405805d1845001060611041d51521822030b0084099001407240106168540040c04c0c4129050204242801c007002ea045c203d00078040040181400d464550009a0300c2182405001e1031200c6a1b00400f2200580303488449070908240078a421140070340003401040306d420070007a4440c1615402c03090210030344c0d0340180c11035070000090700c03800e6a1001050920f14586091100c2c0d07200c04e000b94008541001003089010b150f1046400c641c50481c0103000340001c5036040b9000031051142181d1039542401140001109255241d0103a003030100a00c0081c0c1c042e00c1d81d011501e04840254504001e00d0f5280030a110f8055071a07000d100f0303903080200140d0074085c0694089a080401031409030009542d01c1c000d2802c5801d6007030 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 24455581 1250 24454331 24454357
    0x309010b09010522053106050606070b0705090607020d031e090b040b0c01060b070b0a050612030a03200a05030907060c0f06050601020309090429070903060506030c0402 74
    0xc460000d400d044000a00409050302c07108541c85140c5042e1900e41c0304048614440b80d02c0390702050301d54140c0051600400c0301c10f0b962912101d52000050001d08480314200e80041c1003400061007031401c0000e41d1a6580c114005810070741d41d044048401e6441081700c40e9204d0b006010900250300d4032454540b44a102c1e03215403070055815006245000e010056400800144d050244480e8901030140d5041350324170010700746c49401c4944814050031050700614100100418190305100d4010f60840c01410956000c20094070b0744028420300700c0e00760b00180704642c01001030b10484d030b10035404210880c030400b0071401c04203020004481c159020209500014002000f48075101701c082c05041c000707001c0b03030034801890000d641d01c0b04003201035040042c0c545662000024010b9000f40115801d1b05002440984289420700d41000c40103401541032070506260700000520401011300640158041d40315181020f02d0741e80e45a01914004ac2104d40500501150b04510b03211400904501d100d840c0f = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 24456831 1250 24455581 24455591
    0xf0b2b080c0607020105090f070e04021305070f18150e0d020301020c010b0a0f05010f08100b04060c060c0804030909091e03090501170105060a03051f090203150d050c040b1203030901 80
    0x440282546c40c0a0140c8140b500071450f0b14645820010314101100d036a5841c0000994986c0000340004130104c0030000018104003c004809901c00f4068401c2c90702500d600d2000301c195910102c141c040c90003242c10548200c00c2502a49010f2038414807880c80040000e90010010750110303003a40c00420281003944c0d107450100e851403034040040c2019051202009440a14007070000349680079410f07401003446503241c041030000c10080c440030003524118480c00d0350340741d45e030900030100320103a081503540c24600421520302c24402e035142c50240d50140d036110442400c1c0380d403240003400d1034241125a031600300c00345585400c40c1100010300d07078040c0e03c1c3c0310582880c2000250a5003030380072000c001d013403202005000039906d03101a074400c204240390020f102d0b500c4400b010041401110440c0c9540f045080004800002340c000310710604490380d2161501000c1d0042c0494228040b500800342c0d000b805d28810f107800c041e4899501810010403180050380703c0303c4010304641c010b50312404035944030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 24458081 1250 24456831 24456841
    0x7060e040f02070f1101091a0901080903090a030210020a05011404050c01020708060c03060f180403030f02090303041514160507050d0305070b0714120a0f0b2b080c06 73
    0x2a00c501c52481030726003015442d11010f03640b4280d200040e280001d19244220f44041920b900c2006100003800311243c072130180c8000381d80011030a4120386d50741c5000803c001b000629184002c030686200c0040030301200b690b43d0441c0c1c20000a410ba0000324021441903000740030114409001c0c8510140b039050015080e400d007420010708000383c64400038150b601c580e4041043d0741c000100e80740e00000c42c0c03500d20b4980d11140000361400c3e402645059001296103104480b03a495031013018002d0344a61020000f0330850380c07641042c2d01880c4084d41d4036810901003048003000812007060622120b2a10000c0c41086261020064003d4040c4102e203410303040601003004801c002c118081e00c800c0310a44800c55540d40c2c010121720036840024204880207010a000500400c001d4250700c6510700000e0710768003062075808081c0802c0391100790312402d148494803140e11034484e0102100d40645000340d13481c0c2c0c040342d0f0066070b00c000700c18004800c604200800800c24210151a42460300d1002c1c2c650341c18a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 24459331 1250 24458081 24458089
    0xf0c1712060316031a1509010b09090906010f050103020c0102041509060305090613080a090536071713060c12150b091c0609030207030201090608070509011101090507060e 75
    0x240b150f56100c1d04006420030b00c0414049044454680d00109898213107075104001ca55560801c3d0b0342c40ca0f0040610400440e00c0b81103040a4484440107560018190303441c007440d6680c0341c00030b11440785640c010300c605004135403203500207041609441c00098a841d580d0505400312010192204000802000d01072060f9603040c0106504030001100500e81c608182003003c0e10510101e9000340024000074002e09414001c001040c014903006181c04c00c0c2e9610754000f4000d030b403503140d0107002c1103494501085204071141c3c0c0f4540207211a07520f481401509007c04980c000c0c0103880a1910480758512000050280c05243c2801c0300c0f03030380c0d407042c0c18000700200001e84090f490703841c64180c1600e90034083c5035950303825218508000c8030304148400f80341c40c10450100d10a02c01504141c00c0900303140078985c0002d540011240b0070b80c0c8a142e02c035a10b04c0112020784e01500c044000400411625200390710805a40c561102040b00006d000c20070381c4d5030145004600d0303221a0104100100520003454 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 24460437 1106 24459331 24459343
    0xa050a0f0e0315010f0b070b060904051207061d0109150f020d0608010b0f060a020a030f0e03031306080c0f0d1505030607030207060f0603030f0c17120603 68
    0x15081400b111071001d0240c0041c14006005c00038031003d120003102c40d13468004a45440307584075a1308100501001800540e00d92198100050444c91031a008040451280700000384030302900307688030394284010311589440c1e403401c0d8020001c1480b0300c0c2000c00000b03907140000b503403c0ca0800b000340280507070840d4107012450001c0200d010380c1c05502010140404030b03030314061403d40c0b4081002070301c030340c608280050300681c001c1030000380662030192b541c02c1d40342040140c0e8003440c80840d241d0340000d803203154485c814ec40100000c980001181e030f000070317001c1c2c2298074018440e08400c04034818045421602c1d0380d1105e00b400710f505100b00b094040c000050030b03035103581042000200a504511820388900b0300e00102c15000e055075204605c211ba0b8542c4801c134924046030016541e0b450075140965010180c9034034000100e0401008240715410354001c006503040000c00e0502e41a = true := by decide +kernel

theorem cover : BRFrame.Cov 24280581 24460437 := by
  have h0 := BRFrame.cov_init 24280581
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 24280581 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 24280581 ≤ n) (h2 : n < 24460437) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
