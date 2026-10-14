-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2904
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:05:43.318268+00:00
-- url     : https://prove2.me/submissions/a977a264-d6e8-4249-b6de-5b73845af91d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 522122302 ≤ n < 522302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 522123552 1250 522122302 522122323
    0x31104050702190c030c0f03020306070804020402120408030912130b070203010605090f0a1a180403090b04061115060d0210090b07060219030e1018060903050301060818 74
    0x4540e0394001034503030392091042002c00100c0051510000e103da080c141400e003039034081905d5010240400145c0c031017204c24500e0840341c0c050060010755840305420794241100410680c4c0041c0c0130080514000800c1c220b043c8901d100d018110b480c0c3c1480306280349489201a100400344030104000220354a94034115802c940d00e03040480d50f10b0025201003070140ca00355000035000f1407040e091160151040500300c1c450040d00c0c5003000b0401d40724800440110a0b07901c0b01d0381280520580903240880c01c404141d000703000741015281283d80d982a4001c42e4050362201c0c0002d160042d00d204115801d0202d078501d45c00d0700d030301821103040c00000512090303038100c40240708405006c60601150300544100c40102030402030380e5210151800c000020354803c0c0a0400d2402044400c102590b010744180244048030f900107001c1501c0360b40032403004000450400b02030726001303000700002840f9801000300b054840d030384158480d45801c402500245000c0c0040e2090b01c1c4103079003103034030110000b40d40104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 522124802 1250 522123552 522123559
    0x30f11092202040905010f02030430030218150a02010614092e08010c03050a05190c141308070501091a03070c0203010f0e10020412200d030801050108100311 69
    0x72091480050700a12007020b0080c890350914040d20071912169010b144664021020300c901c3e040d40f81e00311455422026070300d07200e030201030b0b41344405030b2700ca68003902110203400185d5908444ca10001a54160701c820600c0b0440030006540c0380320769080c02480f00400441c0c2d030400e095843e039400aa0882c134001c1c1004905207032045048410041003440c6150742e4039040e055200181c4036011305019010302090403000c81d09007008a19908454811740c0d201e0090001c212071a0301d1024001009800c0d02c05180d010055a070040c62180c0041000800000c1803500b48444014a803d16079810704406074040344c10301604507000c00c43d4403420307105041e2400402603120f65075560403c1c151549035a00300042d40643c038240e03003190f43e049258404451111040100c842581c40c0b84107240503031040b8003800d0409440201c0d4000090851764030954001a006c42c0c140055441e8000710300160002142607000551130401007000d960401c04594002c05e11440c04813070300b0f0940c0c50382e000c45412014020301 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 522126052 1250 522124802 522124861
    0xc02123003060d0309050a030b010501020d050a0c06110904020412020907080c07080a03090b011205070927060609090b16021606180302030708030a020708010b03071806030b01030f1109 81
    0x4240c4248904000f0b401c005008074041c7e0388030308000710f07e50700c2406054058489d5000b003680850240090751100c807055074810340000f20903500c440c0500300c0c54240b0204194144a14a0140e55500140c0041c103251507030181c0c403042c0c60040005111002d40084203004140d02072120b01d562500480311a20b80202c0c0080d075840700a0400c074010031441001a000b10502e8002056046140e11f000c60314038040d104071641c1c180c5800c0440100c3d120402c8002000303803c40107c4100d030703010304031100d1440c0c0a5000083c0c4d1641e144180016255184811101d01c20420100503007a00141e075641d159024178401040c1c01c580080780c604140343c0780e014483c02d0108000b00024005800c201100182d036018007600d045035650210580d40360003003901e080250141c0d44010035050014806c0e61034000c0020700803c0914138006124200c50040059012001c0e143c41d0007001142c0e2804106d8001c0d841420201e08042060502241c81401c003a50b41e4400c5120b94188002c00d0142503110b00fa501d024a01c542 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 522127302 1250 522126052 522126079
    0x3020105030103140304050a06050324010f0f110105040501060f0e0709170f2b2c06040b0a0509041109181302181f03050601090504030c0212300306 65
    0x1031039400396500c050751010141001082074ac0c1c2c42000703180105c2014036041031902d5000c07101135910014001481c0061039007007400c501180701d0038907160f28150605001c4503110244c1489400c0d11011181950141e444040400076203c0c01004000200452888040c0da410414402440d041c1144a800308a565000081098560501c84a010100c4000841e80c586010b82c4100301402c41c1c88440d0404050441441c15842e40101034241c0744021115000a40d96000024007031080c80440c8000d8103c071050101041c40030a0350700501c074801c60703921a9a10741c0034080030070041e1144c48129502da884140000801511081034a01102200c503d400d441d590b984259031181a02c1c0420281d0b100d01150001c140f038050400302a4050b180c006074000744245508251880d81080d07200060403a0701c0000100002c1d003056004942203840713442c0c105411480303500080c031101410040c2d00c40f19017064002d50380e5808100121100000840d410007040104042e0b629000e0000801050255407040b81c4c08 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 522128552 1250 522127302 522127343
    0xc12071206050d031706010e0904150b210d0f0e01030c0513240c0308070c0201140c010b030c030c01090302090a0e0106081f06120305070c080f0f0c090103020105030103 74
    0x10300c080d1102906003a0001e005040007881284907418880e042117401011a960f944240c51100e004c80000e00750358615100c0d0b60399051084038420f024500d4a40c2c41510301c0013552a51100c184114010140307500f02e00f0000700090504072010400001e204209880e8496280c00c1203041e815002c09007000101c0c0400c0002c207941034400c074550300988540c654400325000c40100c400d20001c15a04004401080f50708005640c1c3c41100500900811324407400240b6030780c82134080c000c2c80387c070600d0156106c0c0e82c17900f01c503400c58000003070b101042e035111941071000342001c00288044020840c01400c00b240081c0018040e0441404041e0044c0d0344540040c2c60450b80d40c011001840f03183e002004001c2d91200d000782c6071404400c00200400107145455010001c50241c002610b80c906048001c0e00507503a4140c50b0b036801b000d001c480e0910219400207880c441481703480500d80e2031401900038071076481002d80c100011011068400d0a4910040c000f42c5d0707025040c0da0544c3d40c05030301c6200c07460140c01203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 522129802 1250 522128552 522128561
    0x30a0b010305070c06200307110f2409010608061005031b060a1218050307021005090f040c020c18071803080a0e12030d23060904170d0603050a02090c120712 69
    0x4079480c006d00006200541d80d01031200b1800507240c105880d20b016400a60586030911004025180e130701c48001140150640b41040c1c1d00720707100c000000f42e840e944034581e9040c40c1085039000780304007928a04004e1400c0a1044202089100c28800034481740c44000522a01503d02110204001c041d0b007052010000d9001500780c21400c8602c207100925450103da40383e121b1503003280148403a941740380c421070052094800154004000280483e03280085c00014000c152044c0d003144110701c0b500e50380d41c0b101384220340640544071144004c4e250051014104240c110308a815030503044804102080701d203401d81e4112061443d140b424642e44000040c2e862a074030b00c41480074000000c640407075602d1035120080d0061b80c1c903e0f070f2100c0110010b4101c082081244c845803c806400e00050009010720208007040d80482c005900304a150a400381c119003050300100e520758000d500a5055140c0040003e5100020314009481c04421501044c0302c0300f0040d000c18140004000d00d070005011a421 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 522131052 1250 522129802 522129851
    0x6021c080915040c090b060301060f14070605040b070e030a0510050c3a090b0411010908030706090203060c0310030f0302070b030702160f0b040501051e0c03030a0b010305070c06 78
    0x6010100d0402e824110340301000c43c0f003250740e110b2a1040c443c031b841c108801907904035841910303207902c9000c4030f81094488003007000c8400702c0c00d00d0410034240001c15610400c0d001e507006903820002032900540242c605035000e8682842988013524030710000d900096580c2c055072644101054644030a8441c0c0e40701d01500307451644c440740d100d500852110010140718154002040d116409014542444085482d4040040c104910321700014011400304598404040e0040c03401095081d40c48403503034116005041304503280c603100d01802e4154501003125541280e50214071524504150329140d40b02040e502c00107120300301c100e1902c0141802401103d0052812004443d901c0c80c0c41d03030000b9104d140d25210000d0315103004401089410580c001c0307000b91443d1040861619050000540b45174000201030350b01c503100004a040c1d542450800352400004450041d030722070503c0104e0000b80c0d001420801e040528120410606560002910090580015001030691400c070318106103041c1484 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 522132302 1250 522131052 522131083
    0x813021507060e031801090e0c18100c060b190320090708010509070212041403010204090e06041406060307050108060402070f0323090d3009050a06021c0809 69
    0x3241d80c80f09404001820481c01c0d00090842d02e28441e8019150410140203031120b00e103100d0700069040c1d820400a102e0155840f605c107095600803000a80c880009031321910001303144484100802682d07004425100c002154008e050401c02117480406900e01e02c806030502504d241341a441c82110840100c013801d001d4080c5076146010070010b04848001e101e203502808003840000c04031840030540040319040755000924151901594110809804030410742c1554208000140409903104000034410003202030402c80c5898107065040b0081c04280e03950342d070409401c02c003180e9404078004054401c2420000e199495401c0854001d000b003460040001640380c00c05800e06810074008060b020b130380e58041200f01a041d000480c2801022140c03a00007229200c1c1c00c000401c0207c88880c030949c0700759909a80c0c905003e40d1002c1140456103c400b040011030180028205840078030090244c50000707100d00345040e401e03e0306040d51085184100807212001c076101003c144551143c188004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 522133552 1250 522132302 522132311
    0xc0906011709030304200a0e0720060a0c0c0b0f0403090803131404020403020f0d050a0b1501121a0d0203030f0a0302180315010303080709180c0f081302150706 70
    0x49400d5981354400c1d101031b60001810b901000c0610030f00b2446800501010380702c0c400c0246004500c0c1102100070388403800340031400d8010071102e00b0f1039083c3c0700549180401010b00d81442c0345800212407000303d8020412450000e503030041016502c1036900020350207510075055035a82400c41c0c030900e103500201c2c0b0328040012401c0060781a04151020384042035203c0301d14840000400c0200e10132440000d4102d8802000300903940b5021150584142c080c0c1c2c1a210440780310740d00c542500004962200500d410070240d41c01c2940e1140300045a40b00d14482004100c0020510440102450a645100710003003a40102152400d0041d6004075822a80c074580b24080018041c002e900710022030344034520000030100c100d14000440915603820b9002c2c5110503400d64500700c4000b40000d010405201c40c0c19000201090101490701c1c2031000e04500050050320440010011141c0320288800c000380c4400b0f00c00c1a08d0404180c10700d4650445a0001c0c0c00c601b0307800090380380150341c005045240780 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 522134802 1250 522133552 522133561
    0x60f070b0405060604060f21020d03090635060312030709140406060903080a17010611060906010b04151403070e0a0e09030304030f11071814090c09060117 68
    0x4400000c0e004030711801c1556003954480f01400111030342442180b84004407203404109981260100c0300f050101154101d09041141e0041803060184600c110001400d0710300800005510030900c540040e5595440c000000709140114003840680346821506030f130b081d02240487e50300b00441c88503404085115030b204e01d80000064000d640610408003006010200040c4038a440d100c0d400c180d905a031030355294141181c07500303801e41d0007150645042c080c00c6030304080305550300c41d801030007007030030350303a6000003404125120b407c00f0400391001c0c035558000d4005008820b41803040d60241e82200c4090624001428070894101880940d0000009400814050034591140003680d8a00054032650442540c48440180c41c010845001707141d40c1060000c540000d110b0b0500c8500003846107003107002c0c2e54010304803500b05500d9901c41030700b8030041146d41140c5200d81c021300d40961110140382c9003070703d81001403541b1340d103061441c140300d0101c0000203422a8003542010441c0182c40c4a6510316252 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 522136052 1250 522134802 522134813
    0xb12272a040f1a06070c0311150c011b03185d02250b0a030c0206071404030602071a0c04031b12230a0602040e0f07051206060f07 57
    0x10f07805510f02803a0861502c036043ea0911404890000b5800f4441c2c42410b8650384400041c14640c0c0e00f03035030f486500103d074001c01540c098050100c0b184980d0000074070f0803081004946c04622460b80609260403c1d80280031030403050010b14600d80c2000c0104a00000d800405e2001340a803405c00d500b9199440e01c3c0c8022034038052000101c0c040c0038124840c0204980c280c2410001c10044031380c0168441c490042d55503000c2041505000c001d51054503065449411507001504665040030002c0e5498114000c40c550402040b03400c10418109901401c003049401c524501c154003002e002d10f500001c803242048440103031240b440c28602d4074824a410f0086172784166500510055510849002418a08004007101c4404035151240804058001552152003d08070f0018941c001000d04a41c990b5164050215100035803041c070005030b946041a0400d0391041c4054000448005e201301000fa4080e041811600988044104408107541d1400055018814540300310b048070b801107804804c200 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 522137302 1250 522136052 522136061
    0x1903030b030f070b03130f171201090203061e0a0504090c0911091f02211c05060f0111010603080706020301090b091902090a0b12272a040f 61
    0x310101e05070b5192004058220355611454040c10b0018141000866804119109096090b80c806c40104081e44c1281d12a00c50408140c0000d81043d080007812100705094034140c1c80c00340503a05421815410071801080714092200340c620f2a401d510140a1603598451010704020301e00100180b2030314025290001c0d8040b590320030b080d007040c180000c07072a0040e0702e0000d5920b44100070f00070311402c2d00b11503070701c480440024842606600a102514160a072481801284130b0742e01031200c7e941c0c0c1660301c541c5203403410480c80b01da19540b03804144031703140d62440c01c002803541d001d103420851046103a41c46c50040026600c020803141d400941170b0108031a5402540c1240c41c100e2003003152402c03030030178045280c0e000c07244441c041406400d01044505554054184104090000034003241c481c00500d02030f83c03050b55031850715a44607003003100384441c00703000000140c0307001c00c07448402e203182540c1550750701120340004854003142c1410b0a40744545030b0302542400300600500038450025000c00092 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 522138552 1250 522137302 522137321
    0x303020c061006170a021e0c10020c030d021b0703050105240102062d0a09060c02160312030e010906050402010207140105041a0c0703080910030902031509190303 71
    0x1e01403540025000703240c407141442100d210740c0b11220901040c08102e81c0140000b0821382c11a075003840203c002e0f03120341501003006400d43c1116540d0350840714600e858054080e940c4200ca900421007001c884001005960000c241d14001580703514407401d1a0004c0001048211110b01ca001400002e0050542041d4001c02060078402c64522184500200356001001000c0c0541e0050f03003c68060748807910903041c500d203e480ea801c003601880602e00c4903404241d41128545c0e8441c440b080910010303100e10706030404540010590f9529601a400b2205890322001d004800035100072120140a9082805412103100003080a01a94034110008010546040c3c1c0180728111000c29820b00040c690003960f40c05844850030b192030244c22681c507192900002200715400d210880c040c0c1c0081001c0d074055842590060740b200c9400301071004a2088107440810075080030905000352302c02150200d4908098081c1d070003070380c1d0307034410040c41d00d0f211006184800d82501c0448c8181035040e8820f440c0d1307 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 522139802 1250 522138552 522138577
    0x90303011e030503071101091e0306111c020c010b0409140606060306030a08281d04150504090f150b04050604230405101401150215131e030302 63
    0x20150681da801084201404001c0c1264010000000441c10403090307680c0c404c00515041503540d88882031400c402004076614211007082407401c2c41000001c1c0a4081d0803001c06026034105822001c5160402d407061008103d01c81d4001180c0d100606d003074220401ca820080e00a06c001c00c00c61828014403240c5c0c2d14030b41e1640c010040424175070304e007030b0086030300507500280142030b001020740702c9420943c00070000820a050302d00300f48103031070b0541802690810454aa5880c0f90b030421180d004800340145917903201b20b29080c41d41034410704070f02240c802c0ea581901c001590461510f004400e55826210103009544490800ca80e817180e6900b00c081c1034003041d60240003030303101e200601040d5802082200d007483c0d44c04d40c4a010000e0000e24441d803090007070040700c2050955612002c2241c680300b0f16511100040d02c014000c0700d6246000c420010103e00c0100b904172000d07980021910300140c140c1c40740e4031509641c1c03414800c00204040740504000c203800c8041190b031402800a50248481040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 522141052 1250 522139802 522139829
    0x9091b010f050f04320604090f0204030f060b010f02060702031c0e123c0a090b0a021006060216150302090a0b03040605010e0405030d050c120a090c0b18100306030b09030301 76
    0x5c00300c45c2034030069200301c409041c283c241410007021001500c2e0440c006e80043d60700780000008105042c406080c0e15000e000005900d0132850300040c00e011040000e0025940b03c003041c40041c5030700000322040741d900c142c0401100c2420b8101c10003d88202858071903240304041c0344420344c800140041080c100380601e03008248540e1600e0b22488a10041c4402e400d92240000e070070780800105c010103c1c60312602e04040d4107521100000c4a9030010000d00d001648844800b0800c0e000504c580000b901070b5000511118030009107e61038814940940010760b41e966004580c4540030750107880a00000900104403507898615030451a0001c0710b00703447c15420213000141030f407119804a40250741000245103440100c038454406020045c040d00d41401007041180c2440000c03100686c0980640c941c0840c8165103803d00b0b10b0801110307045608a803c00308411886c0110b5103050450b020416541c4040200c84408180c00403c1c0c207600c060183c885000070000c0d4614080b0096040c2c91301d041300090b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 522142302 1250 522141052 522141119
    0x91122060228080a1106010b120604050f07030b030106080d0c05010c051603081e010b0702010305070201180f020f0a03050d02060717061309170909091b010f050f04 72
    0x14414065001480004000d82400c2c001c0f90019000303045000c1a03007003803008114140703c100d10f000001d0303011031150800070422215078200140000c4e080715003150140400d0900d5034400d8807a070340140c0350105040d60b510814072141c800b074016900800c90b61007500c4480c480860082c200011001c4102c0381c039464840d611141500810549901d280384a8084c0d44400c5503075401da0340c210707000d00740254080c0241c10403105101140030140c0039013101b19445032551414800541900d001801c84025a4103103400d03418590500342c9032800035030f0024680042c040c0c042c0041150104a0340801d508008045404003e101d8009080c0c20041400da00312085a03440c2e01d01107801068181954014109400205d915071a010382d01c510146030400001510800c140d98820008119a0b00d0905081d00803400410f1894856004e80d8072030060700140200602041c0300102d0004502c8240307040c0224684502e1685210344181c541e10281102d18540d62030301c07032103100c4518244000c2c06000300301ea1510071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 522143552 1250 522142302 522142333
    0x15090a031206031e030905091006021501050f040b01090302150304120809030406110c100e010201151503020c15010e04140102180f030a02062215090911220602 70
    0x44088039000540541904c1010102d44015a0882ca0507400c00c5807900300880c4581e19440700314061844028505101840c1130000380c100b104000c2ca140001c1c0d403010040115494460400d41090412a030001e07850318810016a51404503410203500000031b00104c854170204071000314080c2c0c2c0a6101c4a1401d2040d200c1203c0040003202c5150640d0010312042000354000e6013031210440d0300f00300743d400c180c1e840000319001c003e04040c0080081c5d900221140300d541c0a205d032421921110320240101800d01131180b1000c0c0078500a81f041642c002003640a40c84188502e10f91400d10583c2c028195035140c8550700403140941c0c00340c400f0380302d1065003000c028052089950b0b00b50703410b41c59184001010304200588180092580c0c060150750300c464016601c50005000842040410050200c00b29235103621b4510260400d0210b04a410100c02d0240d82048183c8221501c1030004a03c500040c83e8101050140c1e85242c440b6285062502400211101089050701c009130300320391070222040303001d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 522144802 1250 522143552 522143561
    0x90703050a02100c081201140604050f06030901020412050312010b0c0a030f0e040f05180a0308150604090903080411030120210718050108060105090603060315090a0312 74
    0xc00a601015400006050000c0c030010040d6103420b20555001076038682c94400d42c44080b11036801c03035820380180301c1c0003a0b203800c1c40c00c0e8100a4520358281810320002c25108451891828414100400003501c801800d40485d0043c00c41d17540c0428a50345903140c9641ea07900544a0450300200c490008107000650009444181c42044028000e0720400d0f181034a21030020034100e0100300080101d0740c1d01d074030785014003941c0c0c0c084603c0c00501c900d000c0c0140380c40104284038000064126000c1000445da0005045421150300798005201444c010001400b80c803455000d480140d060526207002d040e00410f50714480c1c1c3c0280ea550b03405001d640e082508880340c46007106031514140942c80c150303403540c2025040140c084101c03000001e101540028904c4021518507001816a00d00c08078031820030007800004100030308001030141401c41c00640079005035031000d80251808800544640e504020860440c07203010721203001070806107003080d00c4540a080640109110075511079803500207119 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 522146052 1250 522144802 522144809
    0x1c05070308010816120c05210c0d0c06080a09061404031d090a0b04150e0106090f240c0b09010b0f0f0901050409020325051512060114131403060907 65
    0x600c03102900b400640c80d405c5003465000d9a042c00340d15008242910707410780b40314004c403050710f8092016451800c0707a440c04a51a01c4130740914081c000c410001138801c9010000c1d51010b041442c030340d40d1074004e100e000b4820302030b01900da0350070000803230b441088540d01d50f40100d0003039a40300585066098502d000d4540b48a009801c01c4500c40054007510483e8011004144002ccc80400c03d55081c0e94150741d088440c0e0007031070300c500683c001007189030340201c49600100000f0401038a0a40740c400000c1c03115414101d080001d00c1c9114410382c01078031400c200c020559010030000000d00780212968001e2440c501c00f1802160510f28030a01071510a0001480346002071035190140e0801007400040d120185003243c043c41102d8480c451102c901c110703040708030384156854074035a180c50704005024550808428060304104141030317000d41401300c41030f404002803c1c5958100388034851301d0910300c10f07042c10101103040c070440462904001c421050040100720110b500d541c4034115603a032100c81c1c070b10 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 522147302 1250 522146052 522146083
    0x3041b080321100905190b03120403020f011214070e04020f09190e070206040b180c150d0e031c02041d060a030209011502010509061b0c1c050703080108 67
    0x41c40c092900709803019180d80141c003007840c0c003041d982c1d9440e0036055a03c1511051800010501000ca40c00083e1187c4c00a03820100e0042c40c4005002406080511840c000a4011803203403035a4a1603900522001c0050000201c0c10020801050302d004d51509040d100c010005100403501c080c540341c18001e88070041140000b01d031404181d441040000c95010480d039800101d802d100003000c0d00042c80a40c42004c464000d401c503450305180a18031000018007481140c090100fa80c2c079024800203425000d21402d9551a400001b14061140c0300d00030580380403440c90400000490310b0340c011002e88103c00d005500c2c0035100741402c0019003a40554003034601c0003440c00d0180c1d0800803040340b00640049020307200c0c009403510303600030552590098024440c00c4151540b41d50020303a0910940341c2c0b04908001601c02805c182100c5c1c1591a036044080b554070b84080f419480c0118240180820b003070042c0140c40b9110311070364014241e80c01085003600882d03a604000100c03064046400d680c10003510 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 522148552 1250 522147302 522147337
    0x304050c040b0121020c210403120318060507140307031a18070516060207060c0816020c1009150c0507170304230d140f01140604091703041b0803 64
    0x948200a41000403861b05c0d034884c64803074100103000c0340c000a601c01d44042c2c803541c1d030754218200855074141503410a800c0500d0030050300140303084070a10000555003d1000b081d0707602d446404230303007212580da8202e41c00d400020a000030380d50154030902007450314000e039132410360f42070013081152183d490701042c1003000440001c0005100d10010b10308100030300c0050035196200d0302d070b0700100e0b00200d074102c0d08590307551640149070360040100e540c000c041d10803401d48070701c65540080d111160742a1942c098030240b5000d98405000d942003001500f003004035000da00c05161001010003030481000d882da40101103012810341540000f0781040288000114645880d10f030201d402e8884000301c0801052820101040d01e40e2a10124490913004000d070b48042034641114a007064203c0002c65400c3e854030903841d01c3d0841d9540b006074060804c0380c0000e00b140351400c0240c050642c0c2d0440c0040c200c4008100700c10880e80b080b26044080d500f8000d0089103480d03884040ea680b28191280611a0b1032 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 522149802 1250 522148552 522148607
    0x210051608040201090902040311011b02010c0b0c1b0703021207081b01110d080709050a0f0b031b270a030510110910170f0c030411030109080304050c040b01 69
    0x41c0da4040d00302c0e00c10300d0004903c540e1101400708a8002d40c00803190a250078002413843d41e4009402d00c81e00c05881c006040104003640007924041350070b072004012513007000010719000c6424098400f100c040b005142030202d1032600d69501c44006001c101d10a8030380d41c80c101d6045100042c1e5406592151005202003100e000b00f50f0484a0a10420360401c24004d1450309010305c00c0c0100c038041100d54980e8902070030301280c0a09422500c1e003280e405201040410094180c2d5402d0361390403038840142055803505d0f402e0740c0f0812758540a22503000712000146100c08000b810200303003064601d040c0f41e40034040303000082000303d801e68400075005c1c4d84100040c1310300d25041e0340100060420301c11150b1804200078085181d49000540342c40120b10b41c19500369005c0800300c031a40c0c1c41490759218015030700d80b81000c54054000501701030040001c0c0a00164151400d501890610750403a40880d01c80c6810326003d56034103e04420180102d0610148800030350045500c100f100c01e900d040c0c5c01c5036104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 522151052 1250 522149802 522149807
    0x10b04060b090603010b07170c060906010605030c0a0302130803040f09150e0408090307080d18080102040f1511010504060509010b030106150507030c120314092805031c05010602100516 81
    0x701001d0b108c2c2c41840913007156010342d820061506c52451409490149040000d036420800142d11202c1800301c10010085410b411504031040302700305060041c0c07507116902c3c1101840440e41c01002244c403001801044070580d50180344116100d1240c180121041c41040720100713070f900e110740c041e42d90421000c05e000442140241c0448100901200c420584c1c4003071040c80c5c01400300c000c00100d9922a00c101c40c8184080304a0050b211081c001e5281c06c1c03602008000700f40d118420001501c20a05408034203034880c00c60120404200744c000d00043c1400e052a100400b01683c00b61074035860003030801c0d42d60806008900c1110311400c50520900c07840d45003502d90703070700c0210200e04000b201011500000c800c0c98060620002a0386d0008410815a090403070709038029103036a02a5000440100c2d00890a0141c4130040c0105101c00e08100c980d45805451401800900209417480d9400c041005949070701c1302c1e04982d0283d00300e60450020740001c808441050f15074803200b0410100e803e85850 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 522152302 1250 522151052 522151057
    0x904020d0204091704050102012a0509030703140102130509070c020105031306090b040615081f0b030a05331f0e04060203100630020912010b04060b090603010b 70
    0x140042e10100b2a03504030398454054540203a1034415101000c102400f90f075070f09100d0020071074003039007250f035071a581d107810a44100010000501084000602c6180c00d44040c4a10f20045601241006100740c0000c01309020390810b01d1650496800701500003058600f580764035008266030b860740f814981c05c0f038004480b107903c000d044210000b034840c0220b000403003030320a401340c1c54040e0a00120302e04043c03804006039400307048251040075201600303116141c00404c01010554024959402c9883d03c8a0044054410340001c65898003903081d180040c400042001d031031408a10b91501d081042c0c0030800680c62500302e1070311a1003c2414004ac44456441030741644400c842142b80c0758150340c42c03030600366841d4110f034103c524035004000d000c0f10704018081c000c050142d6083c860700c0c01b0a80d10700304e001c0e8802c03031101400e9030794036102c0b100e95190583d0441d881804082d10700d000d02c02c20501d1082c080c100d083c01a5000c0d174a4580002113042c14007094600f072050080c82c1c58034507480d00a030852540c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 522153552 1250 522152302 522152329
    0x1a03011d04020a0b3708070f03200c0f0607120914030a1d0f01081911130806010803040303090513020906130e070201050c03011715012d0302090402 65
    0xa183c840c01092219205002d001040c504c18031881060000050b0716906010020310405001c000c2c105503030030ba41d00030305078580c0301540f07140c00c22085c16a68801c0380608116481c503000700b000500001c5440d1400001000b540981c1c4084546503108503850aa6034181210454001170902c1c1c1401e803108090b07005036061901404240c07025580c001092400c42e8840d030700301400b151102031444c13040e042100343c0d444140c100703c8134012000381810028041f400000c00a030706025282100c0031030604550f02010148252989103500c0326414071215810700b00314010205c482c4203041c00003030340c5000002100d0590fa816a80d4110151a250a02810000f542400c2c0b840381e03001d00000d405078482c10702a1031030a0076400752800c0145821b04a281d501380c06401c000c11a410041041255003a5030304803811146807629503103000b608030080e68186050740d0b41100444600300000210101100040000b075440d00c84d01c00208000d01f00110181c2d03046210080d04040940001409880c2c01e181500c1c04 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 522154802 1250 522153552 522153559
    0x80d050711070b0d11030f0103021305100b0304060e0a140106050f0f010507080d0504060f0f0507080c0a0507020316060e0904150b01030b031606030633050f04060201061a03011d0402 80
    0x5e802084035110303890381040312190020ba5030480108298940202d00080f810f02d219010040c904000740c03841410708080c0505101c8440000c0070404202d003581c01080b10540450584018a14601c0c010601200b15451019598201000410141b800e0b0004c00c1751000000c058501005460700155815000382c4e04c2618021000d2100c21405183c601503584118441c00c00050840507080300c60003120903d841d0301d18140c2c90001048001500a402c0640000c143d82d0740755100c62008404880301e01c98010000d40600078142d0121440c90890703249401c3e54003a413500d1400e000e000c2d0602c260030a0480307000c2c00822214495882e545000d6000e1001d44106140c04541800e0000110746030211228040803074565803182000059414490b60028041417082c150faaa4000f44040c402600715810380d80d80295500c481c0312044d80600110b407621341e442c00302035072219907402c00030b4003e180c1442000641d55150405145840c80c11045034144c401d0703a03034200610b60b001c07428600b101c02d00401c04ca82 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 522156052 1250 522154802 522154811
    0x70b0405071203050a0f080f061909090f02090703020a050a231918180b06090913110609060301030303090c050406080d030f0e03030c0a0e060304080d050711070b0d 72
    0x41d550015407802c6066070203500c9665981c280d81c03a00070903542545000008002c0c49500344840c109452901d65003006c01103c00a41002610035075514030030503580711113646460000d9078030030440c68840da0480c0f54000c0700d118041c4d42d1030550035000c0c1e100f2200e2900010308108200340055000d601c900780c0150303118010f05514250a80c2180d03050707000304000c0c821104c0b24040300c070909038000c0030b011003908085664010b1a1030f001c0002c00131007040060401142d101c00100f0003a445500603660040c0c00200815082e081405424803a428000c03025200d007040314011068909010084809658011b015986148e2940d101240208208201180c0e403005480c00000c0a07600c5020700c3d005040150050500070b016000c02908850032240c0020320f0b241480310821724040048145c03540004c40034003540e501d42d041002101c108403101c8070240e004002209010a20500e20040c050410401c0d0302044140c403210b00580f05800b10300200d05040e840560140405103001c0050100ca90140c1004503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 522157302 1250 522156052 522156059
    0x70f0f0512070503010f0f2f0d02120103110307080105040809150c0a060b031612030e13060e0609060f031c020a0b01080d1412010605030403050408010c08010504150605070b040507 79
    0x2402e44603443c00c1c2c1b4144e280c80340c0d2451072100d164490b408000c0882d0510140d0905e01c80d6055246610410b20744821040100d0007240d003140c0c5030101d490414035074010b42895a100e1030316561351002035031160b01038481c0203000b04022005100c3e42b8041c542048201d4140701005d4104592030350201100d4003036220074848101d8200042101d1500d00744203c4c4c02140700388200c0f0506142a030224400b507020070941404100191030b01410020f65505840c10011a05000c1c0201f504228021084c11950380341035000a440b061a00c1d8042c0100130403103103940b83d519500b040090260b00b55080690540117502180c195800007a007440414100d40150ba450190b81e45036403100202c26402804560444007211020541c0140c070030807100d01001da2142481c060105510400c0341c14042c41c2c05200c0c0000119090501480603500100b003448000c1c4400c0d000c1110040c4001000c1c8900d502942c10034400b22100301820300c074001680c42650724581040c40507110643c1070000940f064515008040022 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 522158552 1250 522157302 522157309
    0x5061b04080a260d050a0c02010605010e0603070309080f041a0306060a39021503040308072a050d0305010927060e010c050406020d0507031706030f1905070f0f05120705 74
    0x20100b007811440000380c140f40031b841c0030701a00c00d095030200869160110501c02c0743c2e044450010f901900ba60075a44907074600006030b0040581d04005083c001e0040f521039100d4403200028030a595003500d603140e10300300c4448049194002603a07d9544408188078419585109170381400481c170340480307800001c114003d8000044541c07071803200300900d055244041503017014403c2100c10780e180c000aa145140a460007000080040d0060080106010641e03c06841301c0f200841c81d5041c3c611140c0a00d801882c10036514082030744c0085c0800c2c241400000c0780a014400d80d124881c010319071407002c3d034007031918403008084004100c442940d40c1a6641c110a400d10070a044002c1e15100d0a64403418020702a1505c002c0803030010070814200200c2c00000d40c007540c4000e0101d980601d800d00c42e20384000190030113500c2001c034881ca100303c0c1c06980003c13800f41ca40f20420381c0030307406459007140c407080142240b005601540c00c3c074480700f2401b00400e041c8540104406d041c070030152960f40d525400007 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 522159802 1250 522158552 522158557
    0x306011d19060617010b040308040317210f07020d080a2c010203041e050c120319030b100822150f23040302060a020c0a050a05061b04080a26 62
    0x400e00040000c0c414010ba4210308504c3d5025181e05090b150416296989800d240d00c80c3e40001042d00202c040b1894075011309401f542d00000c00042508280c4c0001008074401d9801203850a01c0d840c4048041403001e8000300704840c0c0314103035590b844801d0342d4441c820009451528080d900c00300d032001400c01014500230900b2860090032001580d02c0c101800c1180442000000134011602e60f002d002000910000394000c410b034059400c2d12014000c403104504600a07844c043e00c801d41c5483c0010380300fa40c1030303000140c6d0100880343c0204044180c034044460030000c5070180315038110400040d415105180095103118840e00c0ca032a0600380c0e142114054500005000050b942c8850100c11880c040820400b03c20080302102e041d546010388000307545a00107010000400d0340010200064031040c007a49e625150040c0489503501c519142c445d0f07850104407042140844d81040d00a266882c80d41200d0444c2c00d0500104074505ca5500d82c403a150320107918021944500703440307048020900001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 522161052 1250 522159802 522159809
    0xb030f1f03080f040617150112060e040c050405010602010b3d093204050403050f04030b0915042102070f0801051501020d0c0303090f020d05030307020c0306011d1906 73
    0x803c19115458101701402a18001d4403075a01070340c00004025a00c3e205103a80c100004007481e02041443c10426a00f0041c04103420041040311210308000078081e007c03030705408680c1c0c04d0b40c040000f6a6910f001b01d003201d00181009902c0580380d40c244000041078010382100c129803400c44c08103c00c01c3d10003003e48039603c205903400300301c02c2d6a0800c580b00c00010108181c6950400c10313051a259801c690000c41082d41010344616130301c40220302458800e4083d60f4900b040940d015584580724180548044000c584040d10f51188000100345286015441806280d02910b0f03031800408000b02c408400103000003000031885900340001e40091043c00c0d210007841e459000058a060980c0000320140308250050f0540d40480c0c0020002680604e00c1002c040c0c140c5000186046036140c100c240507980e050103944055040e24a20074000044002c50151006808030f81101c500d07401415107883c400d108820702040400d030556600e14100503440c0d80000100e1604940c1011404403c003280c034280c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 522162302 1250 522161052 522161077
    0x80408150a1b09031b03050d050d3c020906130611010c270503030a020d081303020c120f1507030c1d010c080c10050a05010b030f1f0308 60
    0x1010300030484218440c8a812280e241480b409030256401d02901c90b01e07a5100042c41003100c402030b016a8402c4c6005440076550000543d04c81c1c01c202c850040c220b400c50039041650324940303201d01c44e40a114901d064240c98100e820001044444003030300107102c03410342e001702c1800d070208020000e60380c07030400400b20344191103528000780341848401000c540c80d42e01c030703c500e0f68944075406200302c0c1c101d02a0704900d090b450500d000142080c0c042d00180c020740d40500d03014800481c8040c121a000b1543c035003108a240e4401d203142d502d0342c3e212a055400c3300301c05001b5800c14541c410060a1031f0844d8000c020a030001c03181803000c1b00d0351543c47c0155040346c44500c6201c0d03100788851a9030501038100c040c03401d450054140c0460640c01252039400545560600000c60243c2c0d040107181020758030304180820950704100e0b01c5407403080140c08200ca101d9541898030002081484c00c02c0c00340c0380624400c40401800703645042d030414034042d0307010b4035000c640c040102c000300258103100241041c102c0c06 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 522163552 1250 522162302 522162343
    0xd03030e15131e03080105040c0507060e150907030c0e0c0714010501061808060c0706200702100c0305030a0b030304080a0f1112030f030a110c0c10051c09080408 71
    0x1420900c005030074145000040d0302454043c40080707548811000d055501c2190002070701d44050605807400d104088008102c241484100b1242d41404150984200741e8400402055521b8160181c4c0307400250200410003108010103000b03c12110340c625034884c240d4040c651605000b904d4a000e1000484002410746c0e4480c03005002d04c0c0d9115107280c941300b80c0d2210109840341031019a0f0785070b440040c040e030701d100800300d281024002e164100c0614456628030300301101ca6502041c03440c40e844441d05900503c068091011803510860006103101c1c5c141d65035030b045407280042c0801415900795901c0d403610040c440807803031100511101003901e200b00c0101d00c880e03909251540c884607001c140e040c41040b902e9001e40171080d0220031200c4814651303815941d0390707840d01c451b030300105000d8000390800000030825180046002074286206107080705d0083c080014120f0880f1940309080341134515034504e80000c4003042d4180c00c0380100798840c80e407440c04e1640304c2d40582d2426004001146109010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 522164802 1250 522163552 522163591
    0xf380d060f110c0a0c0902130302040f1d06040c0506030f01050907030b0901080a02040b0a0503060f040c15090e0a110d0b010e1305040c0801060320040e1002030a0b010801050d03030e15 81
    0xb0300f00344001021141b10543c1880200340e28440340724503d100c040c0c0500d13158040c100c6e10001035030180c40308600d2848900220760040c1d12403581c42c04200c80403600031000c10380c04916854094181d80c8294068006140b46a01b09018003c0e0031801038244014151500e81c0900340d640c40280090182c42164001c04075490303d40100400c3e6044900303c24000c2d0042a001c0c403d0303071000704480c1c0d4000c4211075502c540c1e407101d2504160081942c2d124044005001602440752030b40081c420007100c4020455000c00d0300c407050000102e07a150381900e48003001c200070300c034032890464100d26031403401410201d960704500404240b510114800040d901640d5401300810000d2016030000504041e100803c9414259a41e00890740700b60b01c0c5004610b040c00307009110650312600034260801c80c5000f40d41c11a45542c160f000039400545001459078140724490505500c2a044103041b6403004209104103111a10282d00604110904200700c0c015500114041d40580003c81c1c0a02c0d40801c00c00c400405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 522166052 1250 522164802 522164813
    0x30305130b070206070201030b0a0e04050d120b0a140d050304141008010b0f0d06090f0e07061809020307180605070317040f150f380d060f110c0a 64
    0x156801c0640103020600c4407034090780340c00054480080e4207080c00140f001e000d0002844d840c03030550065682909078130400c820000040340c4000740903c2d940302c0040b156000001c05c401e44460815143d04035190040803c04840410103d8580e0040074000c035580b1921130700d4150640e071080d08403034210b0012001100e514100300350101098819464801002c2d4140407125600b407003044201c3c2c040044c0400c400c10716080c0c80d8005401010319490800c01c40c44040348407805070446c001c0c0341520780280640040c0e0795005649280c0c0096100f00360b510903a050160200c025003002c0c256008014a00c8803102480d0324080000c405482252192038981c43d6524006005a400000c001c000020b0441403000180e1a0342e0700b4100a58413582003003104e04861710500041141d8600d40d000c0030704000c4498500c00e00c81080e810340800b40c152b90710b107089503512040d90b8049c4007103200da040901d251003000071445985c0721400c80f100d18180400c01100b98464004d668000030030401103a041200207004102 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 522167302 1250 522166052 522166087
    0x11130305060f1e06060d0612020a1401051c0b030a08030103120512070c14070b09040b040b0d08071110051c09110f040f020d020405010801060305040203030d180606030305 75
    0x410702034016406140c4501689003a0a94682e0b41c2e070b091480001050143c1d85171002d4401d1019040c01c20484250355018111044028640907405184a50000b16651100d01c6114140c010181c550a00e00352190845200044102c004140500d956104040c0301d0764043c4464660a401202003d403030354154141610840503031007102c4140581002450029000a0021907100070a0f0414201d4400c16040c49204a550a86255644c0c0a1140c0120310b81c24100e0290003030450aa078108050300042c024001202c3c201800d4a91207160310941600140c0030b40e0003085074034820013050076465030440101c3d6043c5055403205001c01e402152032804902c100e20140c144141d69102130148079101e40310b00362008505900a402079181400d00c03200360f200c5400c5000148900e040031541c0c0c00104102000035086406a54006000000001007d52207800788500681c3c004018515040b1f03036480901c0100070024000806c800c00d0302c107410116940d4441c04004500a03200c166840c0030141b00320b280355 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 522168552 1250 522167302 522167311
    0x9090105010608010308070f120305100f030b010504090212101d011b1101020f03090d03050708010b120a110d0f0b1c06020d0e0703030c0605070801080c131113030506 73
    0x260315180040250310782c401c03d190f0440b038004098a50303641041c21310203048502440090401c001e4843c100403c544d05901c102d00c0740748000d00c503080158442d1651000f0701000d01c8081d0849001c040140b042c1d1400750701c03450609200808446403903108120050a10600c000c40c00714055070b5108a840340090340d03c031008400300701c000030804120310030f0752407030391140109004042003407101a01144810941c112080c4016000905440e854130b90350917070b03850b003601c3c001e00d000a0800c00481c0501d8051000281a940218001400c0042c40502c0c1c0500c101e009001544894a40008201d000302c9500201720b030800c0c07003030702240902c40c003100031060312103d0b04050702074000d40c41c1300b070380404448140c00c45841e44050f01503a1007000028082c050a10480340c244c03030f4056802c000007010b820103003140d800751080714180025680c5c488213807001c800c01d01c42c441d825013220031800713124038186565484041c0c03542d5001a0f819801d04038070035150042c2c04644c400d43c02c904014001c0c010100403041c2d00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 522169802 1250 522168552 522168571
    0x31080d120e100b2106040614090a03030b031207061d2118090f0907080109110603041a161e0219050307060218010e0111191a01080c09 59
    0xda0401c120616a10b940b1081d00b0064183d84048051a540e40c22414041c9130540382c6003004000f082624882e25800e0030b0350203c850521708080407010310070713000002d442000c9010203041e0b091081e4030182c0c0580f4141e14826414040c0191504103a05d00e000a4a803060240350300040d5022030403001104142c40203010000c940c007100d11042e07000d004120380b4034141c08400b04581c5078980740d002c0060341d810b1044015402100c42080004400682021910802d2441d0803215816610004a401c0b50100c060207007500d2041ca252020600789000210b42191041c65100d2080b542046841c040e0364081c2c03107400e00030754400311004480d948500c40e40d1650307800c0c845039a4280703610000a583c1d699400855071704c4080d1004a441441070070300c15203203e50380090096664040d80b405480d038846e044000b40340030030030001705203005500c40c04084060000d00700040110311204410b8040c04085e02e40c0440d4420307010b000788070899040c803090034028030005000381643c110300410007095100c010034803c403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 522171052 1250 522169802 522169811
    0xa030c0206060a05010c0c09090516060c03080f0c130f081002180d02060d0e0d2703081c0f0b0102011d07140d0f0302060103031101020f31080d12 64
    0x406a0780c8a00300c100b1504c09090282c034280e150f140c40c0c5001c11180e804034800c2841d001a00090203c00710b030b404100d0a07000c00341d07108961240025100011209800b40000d01598006100554016061908201c009801c5400c010006202e401c81944a4000c000d011032188030070488444100810b00c40c4441c480025401c08501c0342070700d0003096521000d40d10480701410032009540302c000895996011408080c4032400d80c0c100e007a95076000840c102800a140900b007135410071600801c00715401c082985044100c2d285450703071403c40d0003c809880b07102020501040c0c502d00740e07101d5550f180d4a100c00105e608c0103264006070031244451410154420101c881081001c4d003c49c9900540f0101d002001d141c10b0403001042400100180081101224070500b03418581c0000b0310604a9100ea55110400d210f40e51600c2e080c0e0007000c07502c2010328010b0000d0801c044020b015508900104d0f002c86414420f80c84541100d89442d40c840f0700d20340c01582c5100c15290380b1064034050140003080a00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 522172302 1250 522171052 522171061
    0x30212120402060703030905060a060302180601050306100201110a1701060201090320032a010c110304060e0f0306010609080105150d030c1b0f090506030d0905060a090e0a020a030c0206 81
    0x580c0c2240007800248203050004051003058001d9100c0201142c00c242110010720304111070780700030f00c21404144d100700d4070080b50380d070366850310072940c3c2c0b09000603511281151944803e020301187c41d2505601955250320b401e103d1703800703610050b01c01a0015510000c060140500c0c0c04107011040e0400300459045c1101c1c84042070b08441807081d01481d013282202c0c1080c000c2001421802401400810040515800c590080d040030b18612210803004c02082007600010007034a0b2500b00c0000120607030014032041000c9400364281380031b0f2030000340102082d9001070000a040000980091011402d0745109100c2201d091082581c0400034060210340c0182034070000b00070094500004041023a40213001d020801d807049041301d0320108004070310049440d540c0c41d850305441c81c0508809180303000005000c9160004100b8410400c5441d280911400d100600805900010000c018000d1088000078050b03400c0121602c110645031300162940ca6080004037540da00800c018215444072042c0b1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 522173552 1250 522172302 522172327
    0x31d0c0f06031801230601022e0f0e060906010b0703140f0c120306010f0513031e0c080a0309062d110a05060406060b04080709020d0621030212 63
    0x40340a80403515951030750b6407075400d050040004410a20a54280084410800300200e00c03111903903d200b0700e1800d030b0740d908401240e40310040181984e040320040d00c22051b403000840412403000e84104042502000c42c00004191883c00312010384139031100c0c0c00c0104001c424003030340e0301401742c85032041e14091141d01c000345012000c4840d0a00b110000840c0840500b802c0201d034041e0007c2000da860704440c0d01c4401880c2c0d041250418007060101d5410322107144258115580d40e0103241d01c54010718155240e490903c60343c018142030008200c04a2400b041d200384070400180780d0400205503458040c030b001052000c1039407000c0700740702201158070400000342201345040002c003071111340311a170520401c460760714400381a01110300502c0766007006d01c140130400510550080a060000355658070208020384280d03c42c0c0d01a94104030003e00407600d00d500140300e0044413100110f48261603200390b88c0980103071780c045c1c1e21240d080e000400c201901070040002441ca9403121a0501c5e030000c181 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 522174802 1250 522173552 522173569
    0x1290906010c03120b0a151710030f0f03021207060606020c0906011b290a0e0312040609150c03050618070f0e06130f061b080a0c170a031d0c 62
    0x31300d0419154621101a915010240ea0003480044126441c61407104e101825144110a06540d403c5400d400510100e01400209040369400302c000b01940119849400b0071040c0c2034000c40860080f00103842c0c0c40380c4171202400205005810000c0c0803442c041019103003460740b246490191081c442001016a0000d811038121512003000000c0842c1c00d10f40b2210441d20841c01d260442625042a022149294404d43c418403c540040040040d8095403680d48e000d600030f419404c0210800050001e1490b03088850320500c1a00c1c14103082046034040410f40c0c1c0200303410000030f540c44003040254030f01030711421000100e801c140f070b1990800510003010180c03072050100603c03121403803044041e00c5440c101c56030501082c0c403032400103071501100e544c000d07854801c03000001d0260386194194050418400445d90380240000d00d00301501070180c6600d83d0110007a25404050542000654000e0008180501c5155030004074031100071003d101507017000c1085022030740400030060680c1c440526 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 522176052 1250 522174802 522174827
    0x11802061b250503070806010e18030f07060504060c03050105060906181917030a0206190f09050123010b03040b252114070f0201290906010c03 63
    0x718120881512401619040c20100c918410b40c000c4202c40d00508441d25010003550421001e481c040359031a0601591043c1c280181500042590701290341c54250244421440202d041170720b0410b0410720590801d50403014040d100f06440c1c400b00000c1100034410020110250f0a04115650400021441d24041d1901050050b40001540c5815181d281440200d0300b030000c04503017410900318030407005208244222040380e2048480c0c065003903000710175181095140c0e1b00518960380d800c003100e501504e064a0400031140e40b18609244000c05d4015400c0c6039001d0300011510012045113181030007030605910003000340e05030051007160700ca44c1c03c407070300319400c8120005a80c9a00c4910700d89003a00b541000c0e80c0a0540c0c0c072100302281c001a842880b24802904840500030514648040d6450f01d0800710300c0c1406000011003240c000c500610b40300e0f102d4030001880c10507041c107d0381380e8103070703051800803200030103404001c545843d00f6030070340c072500030b10740321652065507034002d00101e20800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 522177302 1250 522176052 522176077
    0x1005060315040f050705060f030a050c0c030307170a0905060f15030313081c0c03201204050a0b0915030a0b2101050106110c1e03010204060203040801180206 69
    0x452040d6408004006114884035014480d504040c5802a00c40d4043c1d10100d900b40100c501c0040c55150500a4901c0c803e00b00780b005141d070380c55000d000010800100602c8641c4410311407900394450400146104081d00c1e1120340d488000d00f07080c200c5040000389171040c11400c107140b100000c1c001040503504580c061280c044242c441d510455110882030310342e00d0300f5200c04101c00d28880780c5510807004659a074810b44004034030403410060315032240e8684001044e07452141200286c442c03085100002d2481b003a21501801c5007240c1410036080621411071008081001d0081e40f503c484120020301c0d50509181c541740c207640104030803400d0a400883d411001200140c4c1100e46500040384030f61008048000f0490011500504a44054400c0440798a00030020076054061409a618020610010700c00321144000704a012103940c03507844800004500c465640751401d00140000c0c104030b0300a580c59504120070582180d0340c007040580840c980a40f0384001d6180c40781241c140c8807440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 522178552 1250 522177302 522177311
    0x20c0a110a0b04090b030a33091a060f04061d1006090611150103030302120f0106081303030e1203092107030309020f21010f02040311010818070e04060f020c10 70
    0x5e00000c4c102494450050201c414010720078140100302d413111243e004008c24503003008005120081c081305c811003c010300c12582d00140c4810007001c2d0001c02d500c1440180b81c200c0040c1c401e40843c0c00e8510302e620030080c5140703141104000700103126429601088045504101e24078000008009500314491402800810403000300100300070310481210709400035103102030396524500280250320410790706001100b0440403412100085500c0c0341210f9a0b6560400c0648801400c0109498011422400e2643d02c0701100c2c0c01c040c0c2400f014600c0b10062044503100d00c0d1603048681040c41c036500300701018000c002c3c07000c0074444030303001d4030211074041c6000a481d048503c0451407003a49591000d50060f16a00e4040040e41450103032100e845213140280b0900000410500c10b82c025400700801520305c54a0003d5030b544078501c01940040e19140031541d0509003000141420255003240c00005c140000300002d00c92240078a03041e20071004400c51030429803031300c1c0301d480f9800d02c806c0c40902c580300d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 522179802 1250 522178552 522178571
    0x3050f010c08092805030c0c0f030a2a05090906040302120c1c0522140d031b020415060305101409040b0703110c03091302270112020c0a110a0b0409 65
    0x13010f58504442c0c3c840c00f2030f580c035440080c0d0f803a0343d40000c01406105108910b58804241804078401c0611a4048411142d40352085612035144944008903548401a0100007403a55240f40c00d80f4001d03110700024042c0ca00302414028242540060072a8890300c0801461a601d8030000b00c2d00307603640c003859101010340341520080b0307220b115070b441110404120345001c00c042c00c40d80860004580c503502080142109080070311811038400400034001c11030280d6143c0803103c9a1400208061000348006190b00740b00c24010490380083d000900025590020015200902c3c43c0070740c0174051000f042030403c0388940004406031781c0140010141030084007c10b2445000390040702e10100d402d0842903e03880c09500d4280d07039810403194140304454190300d4015a581c640f003100c080795034042c96400c1c141240b64611342140407080b02d06042001c588524401010288090800c100c240c0c0086d103d551082d0805a6000c8841000d05205d4048400c0c100150b91070b4000b01d40440e20021000300b0110316 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522181052 1250 522179802 522179863
    0xc09021c0c0e130608030d02090a0b0408030703090f0f060e510f131203050309010b010305010b03070315030b0702010e0d0201090302031803100603050f010c0809 71
    0x16008014001810401a8010250010064290035a00b070710f4910b444400400300790f00f070343c0d0303140b10b419041d401c1040710412200e03450700281003035180136144c07214150b511454041705074044c0c0d110b56280c1d080447c1000415620204000042904240e080c8113142042409203503002d15120324414410004801000f54a40c0c4901c02d203403034001d580c8031003145951441c4800a840d0a40d5a03a602540d041160a0510007142d003140c003804100c120364200744000c00e00e01c00a034009002c0541e9107c1c0028000ba600e4202500319140c4d80c80307a40c8158403410f02076600c84c29035200342c00440c141820100103019481c4103206895002c400c5203004100a80f14450ba180c41c2c400540001d0031040100c802c0200041c1c05400030050541618211014000800000c070300721642044020f0040e041085510030b0400700041740c001441c2c0c02000c2c0d51a140030503002504840c8168021511900044407403000144284100c825081440c10702e4500d502c2d1003615240c6400a08084071940780012410040012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522182302 1250 522181052 522181087
    0x3071707030c0c0f06030e071d040206040b030a0618140a110d021b0d1107030b0a060503030c071a04120b070c020d0804031b0509072d0e0405010905040c0902 69
    0x140c00110a902d0b040e00c4071240165800c040c0501c0000c28107000603058004000100481120980400c54180c1d40e8000f040305142270014200340c0c2d21003000c1c0f0011030b500700f440300114011410400001102858141c9440052281100890f41c00785091034514414080d0017483d588031500340000600d145151100c0a82e60151400d240c5040384040f070304011024402844004064a0310201c1d0b0050702e45641c101d81180189600d610160410381d01000004c0034451503079000900c0b80804182c0302d4890b0046855508510040c0c501c07503100c00303401c1000c50044501d80850044000080c0d00d03041c00d108050045031942080140700401c44070000e104140316140803c4669801400d20071885078509250a00c0d4205000a461040074103800001781241c40807a034040310005440e04000d03a4070540195098074a42d02c0710010360807500c0740600d9036450441419540c0d6602c2e11914800d00c41001480b0031600b0580000d8842c40c0341005000120f40c40c00c45a030200c2e00c1d15103000d41c0e038903042101101400c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522183552 1250 522182302 522182327
    0xb090f1306030620030c1206130c2003090a06050705100518010b03060f04031107171501050a05010c02060c010906020f12150604092a021507020307170703 68
    0x440c50070710007100b0420f254011001c030107502c2201c0d42c50f03201d00740103981c850310043e1a0320144150030001810b9640c1c3c0c0b02a03a81d80550300609841c00d44011541241c1a0303221420840009400d401004000c0c4801d040d00035007040c0000011400d18141f04007060807600c89000d5242808000703d804c8081003820000c844401504500911031070900d81c0c02c48248800c210356252595081c041900020b0400040c4a0700c10380302414002c0458849413400d640d505442c0320448024080d8120100300c40803042e11905001c50884000c201e016030482080c1205a0306800151040d000070300100200c0e0390018259001d150121290350395802e07800d8a481c0180f203028002050140081807807910f05403800040d000782902140c40440696804800070740364030b40600c007203500c100144001c4c41412882c1d440441c030403069040744400c10300540700c80071689101101c0301c001a0300c6620036000083e00f01ca00e40782c01c00301d00d0008500b408501c0d92410400d0002a404c0f00320500c010483c1814940301d003101e207014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522184802 1250 522183552 522183589
    0xc030712020703212c030105090d0f0201060305210417010903080109090b0f0a02040803030a05010501180315020306040902040207050705040c18030b0a0b060d23010b090f 75
    0x1003803540c0300070303481d040b1038441901c0e544c0ba081004554650034203c000c03542801940c80050f00303510640b040500f8110142c0c8001c94000559081129441c2442098001d4400500600361014440001845001000485021a414480100b00180c00001c504243c014030210a9410356032021411074640034903400302d940401000305241c0d5010301980008074541c02940c410301180e0b251441c0b4003d0b102100d000030540003203200010300e6040c00c01981a00800360010243c58141da07554900d00d550000e0340d14804555648004010b5903801c031003048414003207203003588005484c54407040400c06d42c5941d070110b0f0680001c0020301c42da40b0303984542d840980c000c208545961031420465500c1102d0302034140110b15145510203c0d50041d0311402e02c0700061850b12461600359580c8040f600f4020b4514001c543e16a03140311100d960301d60181c0f140001610303000805440e40380c110315003a5451030786142600344480c014000ca03661a41110008001070700e0052811440e0300200782c40c0c003420443c1141 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522186052 1250 522184802 522184823
    0x90305120f0108100605060a0c020102070f090614010e01020312130b0126010b0f2211030a110a2f120904060b0436060e0603061003020a05060c0307 65
    0x341114104000b4140e81414040320500308000380b0310303001c5076014015140d101500b40414003480e44520307000301e001c2e4418030594041c1c80d034540c2090611000c48d00020905501c03203006004403d21203448074004c00c02441e11003015421280044d49911400151412010180c0000b82c00464801c030141c5480d5408003500c4100d41c1d6a030074540a00c0600581a1890035911000d1f07402e1130b070140104041c3c81401404905103200c2c031000c0144401c9010489600321120586500742035031030340314640510f03120480c2143c1c2c0f0300d0f0101241088a140e003e0b0302500b04024401140c1e02c41d400107034455000f00c5888190490100648580580101070000e281280728034441034000a941801400044009540522800d40c454540365000d014600644d01c0e1011a110080b1270015540b01d079119640b0b16980803514160209801340680d410354000203940d401c0700c5c050001d02c0c2405c1041c5075000300c80000014110b400c56001800314101e91268511070000840e1400d00c0d6101401100d25250307220030f0010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522187302 1250 522186052 522186061
    0xe0d030516020a0c05010c060b060403050a17040b07020918010c03020c1b061210080a1101080f0609040b0601020313030605072705010302160812041b1809030512 71
    0x200544001c580303042290014465001c1114000100b10b03580310340c0329060b051098100f0004440659040d0700a850440d00c2d904032600c0c07a19100300510103140903501800030f1540c503090000b4106544c440201030901c3c200400c01c241c020020580f62030b90350442c1c95401980310040801002a8000301500b40340d4a8440c8101e546038240c1d000301a104102015510700904044544c0411205001640d401000030001506400f2030405180d41c09410628030000031900c42e92030914160250038101c441c403001180c00c19096030003034525940700241109a02071440c109010654500010380000c2c51001c5640208507140e0082c02541c0001c00109450340e4000e9490030800085c0c00c044d0b4103e0003044030805203000c000301c00528030b003817603101074902081185804011402580071081000588590940c83c4000640c58002400b1500d10346031940a10304207400c090b41c40024181001c00d440d16006070400583c1041491005800c0351090006100c2010341001d482920940c43c903c643c1c00b18400400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522188552 1250 522187302 522187307
    0x130f0501170c010c15060312020f01060f08030a0804020303210f0919031407061a120d020d0e1201090b1504050709031b150c020f0405040c06120e0d 65
    0x10304848104415215a81c5248486a00e680c038031000381d4005034404030002c02007400d010341403121581003640001c005541e501c4404214040b00c9074100140c1240034500300c140c500340540409080c1000c20013145074030f0086140d6807445901c1402c400d0001d004000350035540c013401685c5440e0411401403039001e1441070b410a41c82012184003800c80c80e820b002c118442da002550107025010600d0b080300300a0181c8080d280000c52440c42070b802d0508202840005006006142c0340c0a030403a81654052140d60400c11641015481c4091b1035108004000440c0e900141c100c0b82c40d0810f08004859082d90000304d440d0007255507543c10700e58282000c00c4204000032220602c01c040301d1041e0301480c24514100025540c058a440000910040c418008500c00c507142820883c00d0701c00141030190b4507140c0001d43d50107192080003160340c20920340198280800d000303030305200880302000103160540d940000782c0041d008000421544014805203c00c0c1503001e020480f1392401183c50001c2202c100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522189802 1250 522188552 522188561
    0x402040603060603051302010c0b0406020903010c1e0806100e130908070c060e0303030106030b06090a0602060610210c0507050102030a0c110109030c0206090f1905010906170a0b130f 80
    0x681c0f0001e40fa100000f0800300e44110b6101c0c000e41c1c140e480c4c1808016544400c2ca10381070191098901c55800c00001d9010381d42413042c4406a14a81c0316105400c510442d0414103800c01c200e00c005008581c001c010303d540d207403444140d442d0b0807801c080780180e40c00700c046000100844489600c1e5403030700c0400d00038880c040c805020854800d0507a982c1c080d07151001159410041c42d40550960300500060000354000c0e08000c6000101908513820044007100040c0d5011070741e8440d0b80540c12440030305c000c50901654030340d5000c0d414204020940e243e40c00c41c0a51402c80070700c2250542e520401c0070010b41c821400c5901c1c0a03003000080d512820440110401003e01c60302c00c101042803041a40000f14040c045d01d10102c0e00f41d1182402540d00e60244031955010b003001961048030502d103628550744141464414400088000051030300380700015011000580260303060103140400d0380d00d010401c080c0141d000c00c50303580104400c000540450038a540c841120300c03032241005c0a1001080c101ea01 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522191052 1250 522189802 522189809
    0xa020f0a152910141308010c0f0206180a0503220f051e01050409020406030203090115030519030c0c1e0902040b0f030c1303050604061a06030a1a040204060306 70
    0x1000c005040501103200514900305502c14400010b03201c03034100510300945100120607143c1003119855100c41a50075107580900e025652030240c030282446451800d11560b030441541c1d09144080e00050310010b9a40d10380100f48500071040c0076000c200e0004c00b0701500520640c4101125140c1c14003201501c280050101d418031241051400010003a201030034080451b18040c0c84449900c20000c240c594042407403521a0500c0010040003480c8a060f10050005005680c0d0042c0ca9041420178070b800d4030754000f800380803012106001d10100d500800c840003131b01040f050b2130310440b15a140550713002844d0480a00dc0403e544400036100341c1840300600e580080d4070003100c41d5a1281400001ca0080380241c1007141014004486a07140c07240c01144c000141e14a09400c016521054041d03542e60b07600308461a07000030052000b00308207409403040c3c42500c556040182d40c442c0003c02c10030f0100810900d0039544940880a813035a03107070b02c0b5200200c4040e005541c0c7d0780d00d030391029010f46128032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522192302 1250 522191052 522191093
    0x20d02010b030a0c0314010902060d0b0405010e16081302130c11010e03030105120f2e0605060a050d0906051017030c03030601030e10151508090606060a020f0a 70
    0x10212502e0040b400c10011030340140011056030071900e802d160401e1034500000301350f5079a000240966034040182200300020300001c1a103d011005220070b440b01a4406508415400103201c204042040d1803071640c19103140c1482240e45410482101000c2c4880194010748400e81c5019810001d0304100490035003030301d4488880d54540c44007030880307510300e40d1400d4540003030006201c80d1034002c042441100303201040302d682011140400381840c16024003c6001c0c048203002417610300802c031010040440810b0304100052410010801d684500043c80d02007090010308502901d01c680d1225259a4003d442000146407101c186c202444c82d90086880300300c5451041c6128803400070403905507107003140156003542c4078000150054601c0c5800c603040390142d0102c40c24118101d21500a81d01c0912441c14802c900d019403809200082a0300300c401c1007450703810021040d000003901d41d00000150341d2542d440d0950fa00c100d050450640c200800c071b000300c41d8407000340a40d0606c2030306502c8509 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522193552 1250 522192302 522192311
    0xa030c1404060e13120c020a17010506060c1f060312030f0f09110f0117090a1205030930041d01050d0b0103060c2d090602010b061c0e0d020d0201 64
    0xc402c0034580a0007164011a00d13400c1d50180000030780c0621460700864450308140d4107141c0030340d0000b02d416141c3d1b004040c00d00e84035000c22140150900925403c0700082c3e40161800d100c100260f515000c54030740c004101d4040080550014490758407040045400c140c0c111707a000d650100040c041c1c251131844010703881c1860303c000c0c40d0004030710032114419404403408602100c0d807414800c50400104000e410320240880044010018401d1148203111500140240d00d00c0e600c1e142c0605840c8586d4841000024000c102901c13a000610152484808000140910343c0403001720000070403009201c02c289000c90000382000710791114005056902c80780512321707070701d0b034007401281e100e481e201821690b00207004201041e00b42c8d00000ca445041c0c98495020300400d10000d00d88001e40140d0b541c900c0159404204440e4425100d001605a0f44000d121189252001410b18026071313800c074138804503041081803c074403e540311540d1804681c040d00d0310707603403a40c1c0c0c082e4603010200c0700000954200f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522194802 1250 522193552 522193559
    0x100207030309030810270e01060608010e010911040b030402040902120102090a0b030405070b1c0c11010e062a0904090309080f06090303070525050610170c0d020a030c140406 76
    0x1a04108282c4108950407110a5907815114540700001b103000c2048950342c4e008181c142c0c030207014002c0900066100d02e4225498140c0c0d08450440c16486190f04900d40303910707400d00509682c111402c440b40c8150706a100e031214000a0300428402000951100901c98080c032043c2045d0017410080c001203502c440321039900c5018590038441124018010b4100c008180885407200000c0c041c00803002c05071064642c1c8058a0381e0840e0f149550ba90302182e00c8080400d10700d0024006c035541c625490000d44140d062a4011485400035091160760720340c00c14500c0c090040c0401c0c1070b00c1c4030300f0001b0000c0c01000c01c1410098074808540c0241482c83c010b00a255030629400035a05014805c44e100030b615580d5085001c69194010503802c030307400a0008009202100c2c8406050a000e000b100600010f0030103149590403504290700685106180b510003c0b072140340885e294240c01400c0c0d40402e160241131001a640c4003141e0802810110036090115103d580c2d646900062030302500c041228645 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522196052 1250 522194802 522194821
    0xa0c0203030d060e270a081c050c07060e030705070e0a090827030304031203020d06030f050c0301150608010e090f160920030604090809040f0f0605100c12021002070303090308 77
    0x30310f81c05011640e0b00c06e411000c0082d10081c01408140380140e950596125040050300586900f540c1d62403407140b012450009014461161000070700c2c1510042d881c1044030340da402c1d1142001c0c0300c1c03401c811042d50009041c0715000e82014044640c0451b0441c0d880c82a0140a2800315043e0188200c10700744200324241820001308480550340c000c05c0409420006001c110080c2d408110020f0340a03807554400400900c030a07a503644414469405800c0d00c404210a26084070f0704a400c1c0030340454002800c100c21078102040c5819100b8242c200b03009a5268041a8034110b61074490440034490b200311071130090100c3e0718020580d284040c007804120039005c4840c1c61245003604c07510110500700301284940c80c2603440110341510a00003141410740030700008049400c1344030242da09985442002448038040e10560740544021220300c0041c1c0e042c01001008020301c0c0c04028003240410718036507512070003000700c0450200d80e11000c2d5a11001d40c81d00802500181030200d001c110b415000c201e0150 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522197302 1250 522196052 522196111
    0xc03040f030b0a0c140c032107120204180b06091203070510020406121802041518110910020c0303030106050a030b0405090d0f0504030209010905040201020714060a0c0203030d060e 79
    0x820b1741e68900104014004c07080c0e20340c05580e00100912007006904100310303141c01100507400c2030741da031110140360600303000d03040c2079a1200c040031aa20400047c4103110443d04e40e07500e44042860001841c2d03220030041602c41c41a2400070b6405a0000340102e144440000240034480c4034605031042c4001c1e5a00600690103280214000f18040107010841c203203036980710400d842006518121001983c1d00032504845000c076510382c107000c9040050111080111411014072486102000b140000030032002483c02000e441d00e1044007244440014035108000304004040300400343d95895039140e101800035406015910040303402c104060001c1c0c40e0038400d0740c1c4100780c003002a200000c41840100c602c0004500030030103100d0248004409602c42d807000c1740c0607124103c0c0002e1542024000a45080c0c9654070124800006281002c3d0780d494035825602e2030265410700740c0d107903a070f0391001038254041d1100000c112842c01c900001c03c246180821801030051407200ba82403003030415000780c01c6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522198552 1250 522197302 522197321
    0x2040213080319050c1c1e08240a03022e050d0c03050402090f1b07110117221e060921090b030a0204080703050c0a270906020c03040f030b0a 62
    0x40c0c201d40d42c42d1080c1b910002d00ca0b81d406d4035616118100b41a152071042c60000c50342c41c4034000417181c00c100728031006101e20074600301015100c103c05098050b000144107845030b0000134040d10007121030342c007402c0079240c10812400d0320610fa486801e01070b0b40006d129030046940407022034107007007141101d68024800c1e0b901a50300504112565516030310030392501d4001502076000d0091141d803403a0801004005001018442c0d0b03010080075800e000010400d49568845860b003001410620025000da4202200100107900f09180100c0403414118030845a0b51004580024180484001c005030f961124009610444404000c02c0440320036075024101c3c1c20801c00400c95a001c14002e800c1000b01440c0c0c420354141000d441c2544810703201c0e04040d03203a4002c0f070f2958011401c00d00646041c00c00c0101613303400b8405a501107040d511408100200c030011004150351b801942c043c461a0340440c0e405405c5001103a544a90380c03403680815001c81d00c001d9516441290110b51892a075008183d0003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522199802 1250 522198552 522198577
    0x30305010506071e2a030c06030513030f0e0604060e030f07050d0f0f052d0a150c03060b040f06031d030909090a02030a06021c0e030d090204021308031905 68
    0xc00640b82c01c4c1d5240590030b0142510341920f003a44009804920201c0722200c2256041c40d50160b51031807400c00c0580956410610505092004010015510403d80d11015400d8a012209504540b03415195420140002c9400084c0007030003141c0c20b500681d40801a0318244d045801c291041c1c400c8584502080c01a10b9000c0300040403040850402c1001c586603c0c00b91150400031141d036a51710f807814860789460031400e201a030000110380141180000c440030420003800f00104076a079980c4015503c8050740000035520852079103858800d501c000e010300a8180704564607a103418485034440080c2c030640c8002420540d01e0f8072110402035030b101314101c0d8140214140a213910400001d60300040541015118002031580540e0b01004104c2d41d8600840c0c0c01a039551181e0380c400c41c49800420405819030505032124100003001048038100c088442000a01d15030b01d2000501920807854040d014401060011400c10b80120041000381031050a03007003031000c040c1c0103545a001d100d801900303 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522201052 1250 522199802 522199823
    0x62d09030801050607111c02100f020309040504140f0309041a0a03111807090905010819120201020927061f050715020a1107050103140c0a03060f090903030501050607 73
    0x90303003072901c05841d9040c41584aa07103c8040207003c01c000740c83c082d1f40843d840c00005440d0341035040c2920184000105803904c4440803c8013900a941ca01c120a00140200e076030b040054148004c01d0145120040950b090b02c050742c60307180c2010741c1da40005003500e104515040c41e45481030b240d040309a064800c080e000b060310702d03c4d603214198941c1c0002ca1480d04800c0201000410b092100450791158189031690715042d07003042500310450f003058002d0780503a40045c0341d840620b00128213000480da841000b0184004618500301d02a00500809603004100121003444216145035410100d02640c1d036100610b645601c1005810700e40004180c2e0701d4603a04a007003042c1d51165005204040c0a4168080310b0007000140408030303445a0354160010b0048250510b003410140080802440d00740703801d1050b100040030712061080003401d1036059003c0010209441400394000800a200c1044091030482e950a000070241100d41030440c0028503110020445240500646103215003040d401f15 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522202302 1250 522201052 522201059
    0x702061e060f04061a07060c0912060e07081203090606031f0209010207121b060e1e0a0b030708010609080706050315011101020c03071b06140307030207062d09030801 73
    0x140d0a0b203820321072500240c482d180400d13402c0500c03419008013500840c0056540042c0e051000031624046640c004022041004001e4280041140030400307420800c0000e410307401c06c220510700394081c0c0c000c0000d401198810351000c140d03940514400c2c0f44010585040781e40fa40c04041c0c8417054155601a10410001100e0020ba040d50140c81400010300440341d1660b02c5a4854281c0170305030341b00325011101141c0058940d218400c0100c020121814842c1c14859884006190100c010482224180032400a249a6a1b40a0500c03004048000513140c0e60b0510840090090100340201700102d8000000007400c0325001421600702d0302a540c1c3c0506584038001d107003504404070400d850412034505807078100098280300800750300d100740c80207543d903100c58504a68a01a04040300708002c1e1202020004250002c1174102c4100210a0031f51f0341ea0740c3d0707941c243d00a00404101400542c0382c420b00c2e42e4070381c3c42010007000380c1c0343e4070b000207000d020ac40300700400390380c4041da0040000f000c070780042 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522203552 1250 522202302 522202309
    0x90a140d080a090b0711030c0415120f06021209060c03070f030b240c0c010503060f040e0f10090218160305060d0501090c0306063f02030a0b0702061e06 67
    0x1d0000b10b90b140760180381d2a0781c51001c452103410075441510b12401e0b42c64809082d107000c101918551100341d6090065150300c400e21540c40c101445031701da1282d003602d0000d040114004002e03d505511000454a50320250040b034040c1c60210b03501c203414814034010941c0b0b00b1104007640e205076400c0e550355901401a020031070182c42d81039011900201e5560f88407024868002d032a0440d584c1d170014551f00c840142d10703054500366596a400b0705200f01001800810b4440d0314036041082015034000c1341c8500081003440ca006000004000707140118a00d0420ba80c8840e0030100c5d0042c02122003841d40403451412500c281810788062600ca40c1440102113aa806504000e922000c02090300c0f400b02960744030142544d2034600c04071000344400d0f00c184100103092140401030003a02d04c1c14070364000b4800c0c8869a00d008042a85c0c4040c075804ca4540e51351004102d0000c100c0e40c050203413200240070385008610540d00351000b601601035a070000e48801040e1006080d42c1d01e080ea103141c419101c91003403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522204802 1250 522203552 522203557
    0x130b0f090d020a08030d1505010315150e1f120c020c040510050a0b12131e06060b04061e0e010e0111070b0c1e1203011e0509070203090a140d08 63
    0x49820041990000480d614113101400700104010004110041f01960000d02140c0d1034010707505040c600701340c126030060311500b0b52050b500c007000d20341c5400c2410201a00c401a0303010b00c23a9441664170242ca941c225140c0d64100910442da22806403644078100800d051700c50030401140140c2c400c0326001018a490b0304166001320035100500d8465403100301241c0d510303040341c0250040440009461748254804124964003c81c101088030416105a981101c80607001d594411099490324440c070a0141d10f50081008212400b4410341c1c4984d5030301c01800c003840b40250501000082c20314034070210300590240c450b0903016035961000c1040c8100550300c101d82c2d030314001450f108059012407a261010010f0100a6060f0010582084542c0110b200c500d5503884104484e0005000100769022090641e41560707182e108401084005000c02c0f41814082d500c81580802540184541150084000c020b000026030b422404c4545405403003044902000003550002401d400b01c0c2d000c903070380001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522206052 1250 522204802 522204829
    0x504090f0c0b1e13081b010206060603010501050a12180b0103120c0b071b05071202031e03040e1509010b09240d051801090b18150c090102120f130b0f09 67
    0x64001380703a8440307203d945030440d01003640e1800c900001c3c0c0a0015030301088007a5006d041280c8513445c1d581070000003881800390b0b017601d00a0080d440c070898650b0038507410a140b0051815003088034800d89007400780d4200028030066401007061422450300510440580c40d15070b13080303544801c1c5c07519194022a03404c0c0c0080b07194440551642a02c0000980522803007009001d0101201045405401003504000c0c101c824405140c90004d80007803071b0071010090300c0072500300302030b0745040c1d9803102184101819480c0350903900650107000450001c0100b07010307216480003928202c0c4114040603030540d00e41c0d54512404100c040078415003500c0b01f0f01c0e4000541c480c007805600c510741505503c003107003580d0fa0b4407000c984210803030341005480145076505401d00c05100c0018002d0036200d84090381411006010049160000510009240d008101844085590344940c0755a0303228007240088540100d5804031807494201d0000035a10340240c00e88406450f048416803600c2c150f44104402620301d00d1 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522207302 1250 522206052 522206077
    0x190e040303092a050910091b03050108150a1a090702011b02010b010207140103060e070806030c1c1104020c070b07050106050604081905100c02010203060f1909090501060504090f0c0b1e 81
    0x440c40807054099070b424640c1806c1040023503002080c0184c140d80058004034469403007520b1307084514400d0951241c10282402002524804140d01e04506101c501240c81e08483d01c4d0060101c400da0551140b0202c10300d203081201d2113940000300702c0c01d0702e0260b5260303801a84406401d11150700c203050024595181418005071140c3e56208040170000c00f1242080400c81080030003409040601012599840898181200d2352a100031503140f01c0b800e8201500010881d0f07030500b19501c450b0304542c60712201e01c088074215603907500344003800d90086800319140d50030504000344038280b6400751400c2d654103101400c56142c0800c1c1c0d0b0601c800a0403401d5615211b48912400720382d0311440f03000403204580c0d002680d6494030310700b406a0449290b200a0113400110061019001084000819141568000b088900850400c00d0140c14640c214680c81442c0076082010001c904501044040c4942c1001100b540e440382400d02c3ea000704030410b8101800340c20010b4184241000500d02002d004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522208552 1250 522207302 522207331
    0x10020d090323070b0a140909010905070e0909070f0f080c0105030403031b050a18081216021207050901080f03040b0c0a050115170304080309190e040303092a0509 71
    0x784030380c41d00d0b94544c0000003002d00041c0799040070341e02c5075031200c002a404500f5441d010a030000f144000c41d05102c1d140d140381d994004155014450b1081d07180d0800001c0c4a004e25080c10f2000d40e446003040d118440180c0c803071040c00544042004489801c5502e0400030b441586c10b0440192169800240218209640e4015a4010403802a00c4030450341242d515241c48450700d00001d00072961000808030001401941041107400c0011380341d10144800501548034141019032480e00381d0b0600c0c00961050524001307030104100019a0021520101d50403020780c1d03a04c0554540f40e4060100401c40e6030001c1006000250511303001304a04601d44085030b1001016840c2d0600311130300907421900c81e0001c42000c0003010710740340a0342c5a04d90a4000346140c146004400e542c0e03403249050240c000d48016480c1c6010002c1c40d54544000d18004448004070300c1c04c0e2a00500510034680d048800101d03000381d1038400c43c2540b0104494180c29555038070b01c0750801c0b08100c0d521500070080c03002100d00b03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522209802 1250 522208552 522208613
    0x80d09240e0a2c09011a040213030f0b07020d090e01050f062b110901021b03010e34030b040201030509120403030c110103090b0a050a06091a10020d0903 67
    0x450302d0707034124840c0341400c0400b0310f100c1d881032000d00c2c10050035048007a030600b481c0035002c034861482810b0390003003100c0041e50344a68030038000030805183c0c00603040e0441c07004c0703000600a845d00c48602c604069425038641c01d95444050380d00603114000c10000c40083c100601c881d0038032055400e900c0030000e00d480c0c2002d08480c0344121911107014581441041c0200d80d09000d000342c01000c0158ac00e00c0380741410040c1c9580000d54900d0f190040d8401c0100b45088048507880030342c000350052583d141500c542c1c90012112010040ca14030094204a5a440d80c2e606584100904102504e03070060746150692515001100588030213012840d02d4000e007111040416800320060000714807035100e03002c0010b042d0429481f0203200070041030501d8200a00070001580b0701072042e510603012040010340e80c403410f2204004041d681c1007807c3ca04d01d04401d081c03110031404c8211f00384000c1110f040d401c0c03064a40d0200e85982c1d00308820344c08103421510500c001541c1031841c01d036440601e83c011020444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522211052 1250 522209802 522209819
    0x12020d061a0a0522150803160b0c090a031b0e09070509091209060c0705220b01020f0c04020703020c03030301090501060906021908090d0b01080d09240e0a 68
    0x510034815410704691141109070a282a40000802d02118541e068084004040c0540050441c1e65440256a6525450601030f80b00031100544441800c898a0b03807043c1030861910b504040c0c040d580d44100e01d0011b01c4900c00c403c202c411296018003414185480c560319110401500804203400040882020071a10300091450384034612600041c01c50510301030038000d201002521000e06a040b00440c0500ca581031300440303a07002e030280c40069031070b100c08070040d0800381582c2049034008140350b60b2030000b0300000c1c00450300140d107045c00c111101c0720700d0059aa0700e009907807a51003034000040203c25450aa80038000003030090050b0b41c0d4804c016000a400c5030300036000500d6031035440c3c0040c426182d005103004082c10181c0000c00c0000d0050701c42002d1042c207041e008044050015010340300b512000300d00240d080d4418000d03412035031074100e8540c0350740f40000020001a0903003000602c1b440c11103159010050401c240d59a1400c0c2d81e0030407502818600e000701c1d04001c28050000d01c244 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522212302 1250 522211052 522211061
    0xe01230616240c03020313110112020307020a03030e0f1b04060b0d09050d1815140c070302031b01120b010203040b0309060402090c04050105030a15090c120506010c050712020d06 78
    0x1001e189503802c0803582c6296022250039041c004105403041c0300308040351142d03205000744075400c10300d80d04000203184012505850392080d040c11050003c4188003c05800140c070310b4180c0c0c8640c40900c25150007030501640d4401301c80d2101500c0e4032540043c0c00030110b004070080302d80c030043d0010507075988650b44142194021001d05000c5a03440c0d4404d401c5c81010b0150703aa1111a0340b03414500308102c04518000c2d82440e0140d0948000c5411048529074000d0720918060030540b80a40c0e2980084000e03e0b450703400510003a4000c1c05501407442040503a9660362644260503140c401d600000e8101820050405003083e906501c0100400308a111405001d14810810780c0b004050614152050003d44ca1001c1c00e4003030102e1007440706000036a0007500340d135803003003500e94005600740c2e104c0c891412013402d55100070f40c0c0c00d280c8803140b50410740c024188580340207804020710007a1074040045600503000c802c054540c0d001040d082c001110032034904a01d9138001807005510b500709482d05011035 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522213552 1250 522212302 522212333
    0x31101020f030109050c1c0203070315120311030a1202180306191107080f0325050720060906030a0603080d02040608130506180a0f05010203010e01230616 68
    0x510002c801008022400c2c05016408802c00846c1414070100605100c003c100c00360750703142001c1d0003000150489200c2c1c2e004440b80a54141d48580c911394a280603a181c103000f100960020b04c203a5006401c4540000850700c0c00f0340c40e0354a83d1440c85080540301700941015011740b505405401c82c804c8160703020840039010f00c01e2080c5420645600c801c0002c01c9031800030850941150a21030900450350200a855000040800c0c9a51301da841030340c120b45540300c10032980b604d11030f008240100d07541e00c140503142c001c0c8100d210741008a580c0724031144a0710002a2158080010080a15a8200000696040b8141c5031020502d261280d45020f00d40d00f02e45040380c0c0081e4042820401e080d48070f403a0641000c404900c85040c100d1031b469582d11002d004282418400c1c0c20244415201c7e402c00018180c00d42050300d044803c0178604c0c2c401d000c0d50082c414003039450005c0002190382d500d400d0043c3c0c05482d2200f42101604140f030140a40c030b4004001c0b09900c0d07403041c411840841c55200c42101c61 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522214802 1250 522213552 522213577
    0x6080c090d05250e13170706050411030f0c090c0c07080708010f110a170c0903030313050106050303030f01060f120f050105150c07140f06070506040201080606190c03110102 76
    0x382903001c50b8283d503440c10340d0312001d040350481e0284130141a0741d04201103030503008041488040b010940303000d203d1040c4100200f01914042c100418805002c2e00b410180300102c023607442c0a400001d09079582c0040c1c4e00e43c542d2150280c8082106000b0500003486000c04d01015901041d55078141c1a0030081d480d40420710b1a5101c01c0411106a03062042801c841440a00700b401c0030f40800c2c00502420082840411100410703010803488400001642d071420001070032039980b031603d4035407445911001003049400c2e42c2000380108540c500402920f128a28250b071070f6001d686010801c40342c0481001c0c0c00d005102c0b40fa00d0417440d080c1540207014040f07052034001708907940b409041c041800d0101d4004540c0301818021015404c5e40890b060b0201c0780302c94150b201600300080000c0c1c03a9020700302c9583d030102c00000c1ea14204003001c9143c42c4524001d880e01e1805503180c82c1809042c0c440d8450864000254547d40b81c0301c60300801c4000b42c014001d281c9500b40d190103c00c11400c980c0301040c801807 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522216052 1250 522214802 522214843
    0x31b04230c1207030515010e030106050a0b040f1a0f0711090414060108010b010e060f040b031303030f090308130c030804081509070e0c0a11100c110706080c090d05 72
    0x4180705038964035508070300b0a280400c06458503030781407454000306c11441410840940802c00240da007d4002601a140081080d401507075200702005640c3d000d4032421000440b000310004242c4030a0700315003070303014110390540c0c03038548014a02d0300c0315845410112099228003401403101c1d100e511020388610302c903211240e07260b40d514040c40d14000c41680019241d0303042c0650002c469a000302500c00c202000c5d11038945882281086600780c1c000c641050322014400b104201035100034003a211221402910704006c0345801100000960f10b000b44058007003039029004c01c4e00003000402411126000300c061488864803a03440c0480d80c0d00c0340d03005030203690140c60900321508654510541040142d002805810b10b8016041d140b00300051420800d80310110308000760b240500358044c418400501030f02e40540f551841d40340142644150140061a021010b16804000040301001da074081d8950700156500e980b9116400d601c080706003504001c6002c0c0349400200100540301d80c400341282d1614 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522217302 1250 522216052 522216067
    0x909100614011805030d140c0a0305130e040f08030a020c010f02095e0603030e0613091a0a03060506120a03080609131b0e0105031b04230c 61
    0x400f2200203007281c030141c000b141820821550002141c580410303650a00c042080389101008070540031b11009030040e03004440200c030406501400800300c00c0a84482007190584840c1002c0240303a04030b8004180300000b0004a0200d15600061640315100c036030b01500d00140c0c6526282512008410b250195401060044052802201c1514255220810b0325400218451031030700d14a040203c0801d000c84040411140b8880310000d980b4031084030284080b02040002603100806441c4801d9000809100c0240020318042d41141c0725600c41803100c001071410955554001c0062841d4400c0182c809a40381c45039440b003010800c0154060302c0c4c001000d1901d2820b1007070715640d040c40c41000780c01c4181c0c1200003d410240f442c0c0c119009031201c800580e00c00842030300050110074050407940011048030350402800c0e1010040d80c0d03542d20f5001c0d681e60b1fa2028943d603074a0b001040c240a64030705a00d40a01e040550008820701c0211504a02d440040a40d8800d500c400703940384452541c0004081c03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522218552 1250 522217302 522217307
    0x60e1617120d0e072d060c0224090d0605160216060e03070302130b0112020c031c0b0904051b1906080a1407120f0204030305040302090910061401 64
    0x5411220303000000e840554040d40034001c01d4070401c801030756030307560340c2001c0100c4001c02c00060f0060121004503003241480540038140ca00e0f61440b90f9600c5068080d00442da0a1040d80c0481d121a400b0b8500100f4144100300090102060032513039035056818800110541d540d45d0300c46481c82c2c001c0000045030b00f044074408801c5100381400b801590300414540e03081040386283c0000b22610380c60074240b05025040041d081481d035a02c065402506041c516030400e10b160f02034403030303111f00b625080a04151030f0f410320180d00410100001d40e42082c00381100100807842d5203c1c880c0740e407000014040e000c0030006841d11a0548064507d40e0004500008140c0303101c0100c108901e048030b041000c4002d050701c00e801081c49002c0c450400441c8404600c0408180c0c000f8400d0a4050308185074511700b41d1740003040d218007207413911b454030f05101040c01000c40b28400c4a0a490f00750362a14a014210303028044425800303081210360748a040d280150100c040e200f0350300074080681506442035a40c0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522219802 1250 522218552 522218579
    0x311280909052104030807060603060218030115080714010c06060e0618060306010b07060906050412020705180c070305130b0912010510180f090803090105010b040e040f060e16 77
    0x5106a000c3c03041c0b0440035000c118040d64102da504c5080560b440310186041c1018144d1030b48001c260710300100d80a00e0064200e009031034030200a500810200c0d0043c050300116142e80d03c580740e4a0b401103030061080410203400c01c43c1506060408001c04211544d070302d0121003a50b0b00500103041f404081c40300d54a42044c2114035102900542c04d514106040040c0d146d40c810300c1a07401c0c6240009d80350041200741d4122591540d0890b40400c40d91400341084403032901c0c00030803074005000d00500440c640c075040201d400501c4082203185e010b503607058402101540a00000e9090060a00c011130840f1460105003001d0180400003c0c1c48056010070700000b80d2140424011503414081042042c10301105190215861001c005032944040307107a000040204007000e05106090088110501c080400194050b03031105000b00a143c0c0e80c3c001e840035a01a50151802c016214804580864880054407a031a802070000042100700849403525041004d24030b0720391b0180ca05001c110100c1c06403203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522221052 1250 522219802 522219823
    0x61a0c0114010317071703040b06010206091513050a0503030702031c091a07120905010501031506080604030503041a0a050403111924020f1801020106031128090905 72
    0x2219950b54115a1a4891201c80c1e07541c2002000b0041035540c06e0201c2e0004111134a4210031100d982c07810241001c61f044401102d5880c0944540070205129550000380100b6580424424114070344403407441640b1030f012104140c0340740c4a42e82095000c2041400218010501d035001150b4590400480003d40100443c41c09049c510748005d400109241e002c03180d000e0b11003107904040d01c2c0c0e06c0c0c4030295483d0420400c000c02080c40c042c41c150030084c05500080c10b890240c00d5451102d91210000d83c15202940684105030f0001004240080d00510165030014840c0003034800403c1100541001c0c24421156407001c60307150803c1c0001d16421114440d89410b580740904031032040f0605030481c0b1844201e005040550403509a2100c0c901c12203084913510a901042d5030b501350440d9581855088680345850004458085a40b5503005109a504407035210103050a502007a504106002c0c000b26550880311000c08000908505510b00e040044d01d0044d80010f12903806043c1503141605049 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522222302 1250 522221052 522221081
    0x3071a0f0609071719330302030316030c050d03090311011518060e0a0903120227010e030f160f0b030411063015010806040b04061a0c01 60
    0x80501c0726980c0c4c400907494038840c00194810803612002d0081e590300400c3d1070960001e5252010381e0500c07403004280100c181d259002021801c0980b440342041e16004c0384030080d03050340204130300e010914400c0f0320980321501900b44000311001c10b4443d0741c14504603142d0080040e544508880030141c05c02c0700c503484180d90030300030442c030480b64011116400c032500408490140c0c2c0010b00c40159030b00c0e00035001901410200460a003044170300c03e405066008030407004070781480304490010381c0d02d10a450302200c50443c4541d000514001000c03514038441806410480d443d60a5000c90310100180c00c00c10880c0b400905000700c6099001038520490303000030302074201c0c1b41010490340040400386e0f0703000741e004801d40707200b806050005801071107008074070305920707540300d078041c2071030107008a00411959a5420b0b018161348000c00f0700d0302c0a1042e0b042038045040300c0041601f9040c117901800c18844040c0c130008035a42c41e40018880e0031140d0410f0142140300182d01e0254020a000c1c481e543c002d1207 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522223552 1250 522222302 522222319
    0x1b031a010b19140f0d050105010f110304050105071a0f040b060609010212161502040503070b04050315060307181e0504020303040905041a0106051305240c03071a0f06 73
    0x1000300032011246140a10304003c07500009691402d02078040b10b03d000e2401d0010341d0344050415003003016000c01d120f0540820705c1d416020080714042d030001c84101100340090343c82e05081c00015211074101140c283c980e400c07035440c5105048041c0300c5040c05421449a0030040749041d180c00d45001900030840c900030702081c00880c0c982c0c0d0b0000340c008038000380c8120082c0c031440035007080480654a010098030548541803207244a1034158001d2050320819815180c02a845208460548c400c51061680580c80302c130f0b2003a8102c012220340c80d0401c40040070345864a907642a100a08100c2d00440040d00f0760316800c6800e408903c1c038055014a0806c0390a11003031030550002620b0f40502e100b1100040d440304001030401c01071001002c110f0344800043d4400b0f58456800070304503080800000002c2e031600c5408511840c0080019007999103000500a81c800440a502d41c15080021420220721040c81800002200c1d00e02204500710007800c010fa240c034028800c2d0100c03030070140c101400341004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522224802 1250 522223552 522223567
    0xd05040b2208031b0304030f0f03020a09091a0402030a020405011b0b0402060705160311042a050a0509060406030b0a0608011202010309031809020a02010e0f07060c1b031a010b 77
    0x820300040216005030800f6201e6540c90201000c44a00340e00e00c0001100001c1000101900030f40119010388059032509103900d003c1c4000e034228407804240b4000304240c00c4040101e0503041d00700452081120385812040b00a03480400e003030f40c1003500c0e00883e4a401060601030355910a0b4008076090424031104107000f102d4a80c444640b901500c003030300070700340000c250003409400c10440c115003803108140c1c50200c0c1d503410b100400104400c10b00c1c2c4511300b080c02d141c4a0558035412070000c0b010780c00714902e4841c000700c0c040e19241d110042580600105100752200e0f030782d0b07070b002602c000d14a9031000b14141200204104c142c400c590404000c0c4640e110041c003030120071007020b0560340c1d42800c0026030250541400e40d08c0748645050003982003821000818800300c66000741c142c0240c40d4009002c50521700304000d8075940045050740150303000304002c0003554413500c4010000d5008100000400079071850340610aa03da41040c1c0322000f103c160841581c1507050812300405801d5100303400d000c00f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522226052 1250 522224802 522224851
    0x30305011e05100f090305060106050a030516140a11010609090c0503030c0c0112020f030901090501180809090a020f0d0204150309021c030504051c06050906060a1a0702060d05040b 79
    0x210f0943c031000304507504c0c4070384110501481181002d10341010407200b103507a445000400303a034070003021030b00040d09207408200c646c408022a0340104076243c84650712030004c08441507542d04a9600601004a804040401e4410a00c03840000c4c000400011070f54658608081c203024013185d009601a5004106c04030f40e0756000f283d15800d035802480d0060000c89200348000c0a80207000182120460010500032000350540c440049548207000030300c4805c00401009111030310360580a00328039401c010804141c941608056030140c0070500040c1001628003080310241c1000000040b1250700080a00255030f080d506480b104145c1d00d400d00052919a001c00d645078072008204103038900b00c4113100c08050040c0d041d03a02510029120b0b40f10034050b10280351a08a0540f42500c8080c51300c004181d0003200845d0451041d400940034000051801803042000144c8070102c48110000b4402900103a40e072a00405035100e0066001c621405c00d0300300014080e9028000b1168940381c5041c1580486 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522227302 1250 522226052 522226069
    0x3c0615030f0903040e010608040606150c03080916030b0414010b060702040b0420070b1302090606130812210709181508010c2c091302030109030305011e05 68
    0x1810141070300541d29a200c52902e10701a6420020f0203450300000414074990118031188900c2c080c40e018070030b01c8c0d41c526010440042e404685030019050807008004280243d44a50b00302c51140e003143ca00c2050740315900080d1071150000c40342d00140000784001d110b4120004a5425a45070007003014510403000680e051155020081c011601c81100454560b100d03440004c000e41d0701c90b5109001c5480c3da0100210354040350086620f1411a00850100a0303006c5100300030319030203401e009698540b101088840d07000310300c1848003106814000305800406201c42c2040c0402615074075210194a6003084200700070700020004034a0010030028415480361445040394480c101604049802300d03680405080300d41241c0d105044c8804c0005821001580300f00038171650b6a440110801403901200059581502520300c40e14031240c0043c0a444e04081d02034100200b00c05003003c40301543d010030b09403040d1410a0300403960314001040043c01c140304074074261303010b01220b40141e8100000140142e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522228552 1250 522227302 522227311
    0x4030c032901080a0f03020f0d02161410140c1002030f0106320408010509030c2a0f1305090a020a12200d0507030507050411030118053c061503 63
    0x2150031030840c4042c54000c1c003040c500601580196403110414040203580c800c2401034814520501c0840000c54080d49030cc0c50043c00d900030702603070309a40e01e2070b8110b4100c0b10712140036207003030030070085162054820088413900b1002040302580700d01d031000d9510307100c0364160f0050050129000c41440002202503580726062050824401c40d01c0000c0440401030003581c010b80202d46ca80018020b40d004000090502003610008071000c0180c0c4480480c0d02d403400c01c4004152002041c10000c051401807031506815002400c1d401107078016a09002c10750320142d4521260344c03c11800142503080190000001e0030310750742c0c0b400019030150344020050181c0c01c2410a410000340c91610259038070240c43c151240c020040300c444c103440c1d0a12603102c90310340c8138092082d440e282000c22032480000c1541d0484128680c07074000807107903c120700040c00d80100b45241c40300c4202407140140c4600850003050544442c44030b5003c0065134564100d42c00003400d560b10407054075205999544003441200c0d40b0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522229802 1250 522228552 522228563
    0x611040503030910030e0d0c051e07120f0804030b04060510060c14070e0c190e0109181e154a0a0b030c0a181104030c032901080a 57
    0x30030045400440043c2011b5004003c1070082ca6021851654040e90034040b0700d0140080d1603030b08824601d21200c1003500f41100f4040d070020001000340010700311421f0030b100d0050f02e070b9403104405d40da40c06855034401d030800c4920b07400d000240401e00c4014070629078429240301180d0307403050030020050003044165400610341c80c1035084d08040c00c0000d20410307009140c280941d504a0601c682030155a070802c030382440000c0102004d0600c118800d104003646424107840b41d4620300e0503d144c0604c004501e0f001440d607140c5a02441d4080d0b045016940c2c0340e000c0c0e564000038450065010410202440e501603880014000c01010007502c07108000a014001d05042010720b00c0c2890030341642d400c1c074855000c1300500003c20032643d0001b58002e55040038003101540c02a502e0042003016000c11030107206844800e003070009100300400d503c43d81025a414209600741a500c5ea42d008021619410445d880060400101c8811701c9000d6805100b0211001c040030710b40c14003900c60760f5000b0b003200150030f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522231052 1250 522229802 522229819
    0x10b03160902090a03140a03021005100b210c0901030c0513050907020703060504050d0905030a0b04060b040f1d060f09061b0708070b0610260405070f03060906110405030309 76
    0x100d9a42c044055008540c40741003a80c107464600310594580c0e0805038150702500ad101d4030294100400d100d010320a040e031240a40350039090548203146500711040510450717040700380ea0a11a07000805052064a400b07103800d554982e1000010f040c0c801901c0c508082c0041071120083c40940703100103d06651703003514031042c90780da11362040b480e12820398070241c9210324103c05d10003403110120f104480321000340c60340c0001da581e45041c1070362481c0190740640542c3c2c1d50b4010800140c0a5040342403030784001007001c94550070040d42d6104a9406901d01400f860003e81c104200e004d0034842c1d240e00c05000c088501d403138501490038584880009100a4030603400c1c03180050890b03845410740d20040e801c09800768032084149010a41c510080e0f0321907114580c0008100400c030310885100c0301400412280358100c143c46954140558800340c004c0700ca070301074400c0108034403204002d11070056006c0c41000c076080c025420140102c030240111410405010031090140352000001c890070000240d48506 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522232302 1250 522231052 522231067
    0x171c02010204030c0303090509010b0f1b0f031612081303030203100308030f0906010905150d0c0915150914010e0d15060305011401050f010503070c05010f060602010b03160902 77
    0x24020b12454200610807400b428010092584c001c40340030a070342d01981c1c454110398840e000c41e1101e01904102c01981c040400600910691603140c0d020390b0481c0c4021100003800240304181550425403500244116217030340082030003010071000c0030304e0400781410f51103400c000d520740710022058003029040c0b54002000c5482da50203010200011a0000d281c641c0780e04080411545030392040d20142d034184507031400465950f60034807400e8010704521030303070307015100843d421f00402181d052000d68910002140000f0f01d6600c0b0b000f0741103008002c044500c40207050107000a001c3c81d410034101c0401c030328150b041c4240d19007041c1c1c49034041001d08114100701c000800040f0480700c0b0403401000845803a040840380701080d002481078912580003440200c5031041c6081c0d0100c024440c10f64003060303490072100c0c01d5000f0b0004607000555813a055280c20340350303107810342902c1c50348403864200c5a44080401c1080d07030a12a96003101801c8002d8090b0018030b40405144880c140101400d0540c00107020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522233552 1250 522232302 522232307
    0x5030306270106032a08220f0602070314120a0e1c05030907051c0308040305160b040b01051906030e070503060c0403061d03030412030e06130309171c 66
    0x40d407021420408078150303141d600040c0640768900700f0b1018160b144110070b100c0d00031940c91200d044034607a50704000d0b948100486035804021081401694801111a00801c0c0c50483c0c42405600810300035944184924004000f5280c0d403218540d0306000f13021201034030141c1d07004941c00c000d60400220303081000c540c2c498145414a01502081076107c00103aa0254120001d076105000301e60507609043da031502440341e41840e2055000460000031000ea00180c050031a041d001b80c000d00e450360416882c1072100b0a41d42d03611318295134240800c0300b00410084030784025400741c401915040d103100340c0030a02d180c201101d80038482c103040c1c60b2006a410342c1c50801c00780009140081c2155035608021540b132055138054002501d01c103080881307060540070070801c40d1003145c0c480d00040d450b50781c4549a0818050010148000b05a00c407140000c1804040103402d004203209042142d00180e00c1c41c01030056050340d13100d201d840000301103c10302c0c43d60114643c8107094402070300020b03450140208 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522234802 1250 522233552 522233599
    0x909011214120a1815020d080a0c0909091b12060b010309080306040e0c04020a08010f080a0b010e07033801030b10051c05090a05071d01120501113405030306 69
    0xc408107170054003507030302035a0001c0c810311059100d407569803258480110f0310090756070007404a004200d120030100b280c040543c2c00352142d40d0003200d240342035011622003150130f030143d5170016030384503015603420062081b00d101c3c0700d40707160090070208001102c5a64a043c580001052148216542ca05810702c01030140b017005207429009000315070b241142100030f00580020b0103140383d201d03900400031804606c00506615401d4128034050502d80c6003501e604043c420042542d0209501c51414003c0525003901c080c403009a005e94450401002446803a02d020217980060704050900103001c0090b01e40241000005050b450a02d555141c3c40c08803400d804088501040c042e0302c1e160400c00c2c141408604852172510070801d5a262664a05124089984450141d040860001d0040014010340130103114118801c00002ca0000c901c214914600c1d00860000c0c05ca611103012006035000c01c281d4916040d904041640107811004c4c1c49a5030b0b80e010091515025046c8203841950341115280d5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522236052 1250 522234802 522234809
    0x207180518030d020408010612020306041202030424022b0f021509062712160204050f07110604080d0c051210090501061b030e060909011214120a18 65
    0x1240e90300c9500420f840000c0d4010720990055500e0309002207144803c0020000c0b503281c0041c000d1402e82c40b00c3d16941002405901c1d514254401003000182c89540303002e801d4240b81d107003428410102071142010381001d5080940a544050f0214640090101d107000f00c079401c0081d00c1c0110400001d0081a89010380f41401c514510003003004204a462000504900c100d05141d808c00003071021030b90328003425000c0780404825402801c10124000403a10192101300032100b480312000c4420340204003101c1054400c0c081403651030080000e01d40d000702044c0c1a01c44440c00030403007446c0a44a03080140182c200300030b0501c1c0c07158481025240301c2c3c2c2c20344030009003004848946080c01c96410b002e00036203204000d2070506020000994a000342d45200803049030403030711081c500807a90200c8140e8100d208003a401507051200c0001c98942c0c1c90124041d00c080090003650901c542450260314001a010403525030003001c0c401e00407202e90303090b04c1c201041414413569007003052a5040e040d021980 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522237302 1250 522236052 522236101
    0x20904060305060a060b0a0503012c04031205010f030201080a110c030a0302031501050a210f0e0f01110903150901110c16060201152309070c060b0102071805 69
    0x80100900c0b4012070f02078010541498204403140d62000d02e1009401178030300210105000b400104100492216010303202c0701959042d02103145c80d07081000c488401640e0075400074100c9010540100343c01d1054034051302e1044242d121a0789141d00082070244010980c0c10002d40700e09a05403c03007210317010703901100300441c00d498072500ba10070010000e400888581200603511000c1c1c10065020703c040b41c4c0c03c0c09840e55403648002030034800c2c45206940d801d00c3c140740c41d965120080b40c0713411840341804100200c00070300110b0817840d4040e403c1d20300341c0c250048142802c000d92484c607600040c07801d8200600d446004440e903200e0304120300404c01404018100344000403060b10569000c9045800141e0100341a5041d5844540407801c9406030304061100480507507060010351030a6440c00009007008090624060494021843e0b8600650f601e20205401c58441b00810110f8007905010003000e01c01444007d00d80034046080e084112a48080b030355644012441800d441c0c0c201c0d24009070700c00d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522238552 1250 522237302 522237311
    0x6180d032007050d0e0406030c030b13120201060f080114270d0509120d121a10050417031305040b0105132303010506030a030e0d0f08190c0f060e01020904 68
    0x90400c01d4581c13a43c10306000010f100e0348103c03500c1d13107454407030201a42d0704254240051801c0d0350791201c0c40704d030181c411040400b803500d503c0f00207442118501003807001039001041d035520b003004041081216401c1995264140b92850300c0a0008424659000040305980d450301d8508102000c07110381c044407000d4050052803d050817164018005041003101a90005164034501110030b44403800d100e1454001540c2194070003c08055400c000840c9401c1034100d031955442038005001541c1c290001004074801107020810719165240b1a0080241000a1440c180040c80001c1e4021500e005162080d0341c3c5114250341a4841c0c401e480080f201c1310002080340d03848035002c0b00160003c03c0ca00314134040c80481b83c030f050f060600602d03006607400350083c0f540c01203d0703074250b5105d011110500d820501e070f500c01d200403460701643c8610341c5026011017941c1d0300d4030240c19110048405017550a02208102220000b24113045ca0119650131178400a0902280194140a4030a1803942d99220307080 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522239802 1250 522238552 522238567
    0x60906020118030e150c03040f06110a020f011b0c080c0105042403020c06151314180a0203030703080703050f04080a0c03021f0e07050a180917071406180d0320 70
    0x4020801ea40309c2000510416540700c00484805004041c060200d402c0020034000504150170f128040e28414184010340300342c4c100204007940d1040000740c480060050003000515424842900010020f181c5907107403500f40710901420700340c20344030909001d12001c0001e440728402e0341035900411780081a1582418a041142101c1c1d00316195184180d44491140e4244030311441982c48400980c0380414490b51280210b0031222006120490140103e03401c0000695061004286441c4a078654030403d0800050040440d50300510300240c0c0f0184a0500010800c2c42007922005c40d4180351580c21502d69103000c078100074528120082c0d5441c1040c000c2c80c4c04400d90031403415070035040111100550b5480c200980741d10148156001d454140a03400b4411340b064003c1c01c60075001d0554507240494010507000a13501041003a2a408081c1b02c80b95035416051207803981055006044042a812401000d40c6405115400300d050690b540110f402c150082ca445004208950350455150f100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522241052 1250 522239802 522239827
    0x207150b030c040629090306010b04170703020904080d060e01060e0415140d1703010e060f010206060108070c050a12020f120c0307020f040f0e07060906020118030e15 73
    0x1412012688240100e0b188800340c1d060502c510000c54104c50240090905508828896400000e03031420920b80d00304880455034808000840c002e00144040316071f218038100f80c81800c0c20b0f0704003000c0b580d03411103c02000542d441300440382e082500319505983e1810004140c800034a003e5124a15414812000050302034108003022140401502d041c80103c01440e2074500960407130068045001d030501d81c50542c3c0c1801b408002d03105100e031256001c49503020145000c1508240e001c095003042803000c0041ca41000e01c0341c043e24503020700080c109030030070f000083c120080003001e504c01c1207400c034540000d11904000c020106a0000041c000500f203080c03000351694000502600180700786001e070071011480c0000c0304e803262a1080698106000d80d82084807105a14001940c01034581044800600c2c3e17500c00d01110341030f80c0f0000d20b48580b82ca403000c0c00c084072950000301564907040e4450200800303001891007907903240ca0315400038081000020310440802035007aa0014021491414121 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522242302 1250 522241052 522241061
    0x801081b0f0f100503221a04170412140303130327120201021621151b020f01090c0308070206270301110f0d0b06040b0f19030e1906020715 61
    0x80307005000406c1c1151407040c500c20165800040000110039411200141c0344128a50482d224220301c0c2d003015007012980d0b000340c11a800c9400b00e03000c0c0201110800c80402101c5491241c21005541189040380a9080c44c4d82d91503409000d00c001c0c05103040112004040300c0e1219440c2007100c0c610551210840c00952110b40b03422805480f62184035114000600345000c101c03188200740320750516403000c010b220020343d40c008a031034418040000c0f11001003801500c0840840c0c461101c80d1513450745000b841c1450079044490b1a074900103520002c1402e8007440c000b80d0750042070141d6140c0492020030030070722035424849248082d005840b902c02d1201c0c0c140b8000f40c00d04038000d105090a01070f6000d0988180900454404020020251050910b402c11000300301c0040038141019078402d0442e12551090103000c010030400502c0300e044010100e001c107425202480c082020341c030682c6d0700d6540d07200c0c4c5d003030418902410140242d0822000b501101d09081c0d2058504209170a4102d040001d0b1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522243552 1250 522242302 522242311
    0xf110714040b040b060a0f0c02120d080f090c15040902030f010f3c03051c1101060f060c0629030d0309110d030504080d0e010801081b0f0f100503 64
    0x403401c100540302d02d4585800b4400c00803000800251400b40020310640751505504600f4081c442440602e40142c1d4130240c410a0700040b05001e460441c445503002445502d000f880c0c9091011401c040c003100c1c0c01c0005016402010070760302c0d103249402150708080a401203a2142038268000030030055460400c54650b8101c1e00315501006405451b010b5401a0108100074038807208640c1c10302c4c00045166004848903070800c0281c840c001d5480340c9605081c0040700400005c0c42c620501c01801041c1d00003000c6680c0c4040a000b001000d041103503040003000301d807182c401008081144001801129484540c0c81c45995826a850b4125851290021000242c07800d00c04e010301140b600c42c09001740180c8c0b02c0241c3c02055040e8142c606410000a050155003d90801c01c0c10302011403003110800180007809403544400040080900005001c02c0c0140c00c42400e03038002c19500c1494240c0303a980c034020540101c0390344201000d0040480d001485011441c0d038800d130900c500114154000b0000d5005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522244802 1250 522243552 522243559
    0x304051305010302030607031d0615180c0a080702030c0a030e0406120c050913020306150907020f07180b060a030509070906081002030714030106020d09060305070f0f110714 76
    0xc0204440341216424030000e50183c000c14005450306d4840d90114804070020700040d02215084e14806203403841c201d0300450070291101d130341c4030945402c0c010b0700d51201d401d0107043c40c10728002032010b01a000703000d000001e022440c00403849050003801603901c0300942500b21a1400c40d18107008115480502505005074603181c03003c00c6902111200a00c0380ea00008000f002900d024140854080001c0c002e165286041d140e003001030f58180b1040f4013a0884c0c03210290304490400c20480040c0f07010f041401035500c03105060060040101d10b0710100c581d04400d040c0000021104c1c28007401c031148103941d0104000644100b01ba8255008500810301d0104450a0a4035105084115151b900425165a00050302c000002c80c69800460b80206107203020342440c40c000c4880b00454000f0307004240036070007458201085551110000005040c940b8081c452400c00910240c01417012a10000411500c030401e81060760060f0031000b0b20f20a00801c443c45203a81d0200c40310000c141d500340030b12 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522246052 1250 522244802 522244819
    0x803010e010e07022505060a080405190308070c02033f03070e150403020d050a05011103070e010c030903052d010e061f05040c0c02090618010b0d02040305030309030405 74
    0x80944030610103d11841c0150010150003100304040940d41401c0229041c510000640108a81e143c80010341100e00340b5413984216410986485400c00210040040c004c600312149440401e43c00b040840d080001800d100d80c44032011300200f4113003614940c10f18100070171040700c1100038641452640c0400079140701000316065003030341480e452000707075984070005480c1000e400f528500350304c403d4005d9002412a07480d0550b254040782d0f4421441e04141c650b038103c40348043c2030000c20700480c4041698804079514602d081c800180404010745802d0b8108800340c0c1c64201007500440003040596080412101c0b80164400300f0300e100440a640407141c200e402804641410050154448504084020700300558a4640300c1c2c0c4403150790681180605c030600c000040d503440b144a54842c0514903030301c0d01d80d850390074014800c01c14009041c040c00b58952050042ca04580743c005241564080e81da10f581d1103204082843c06401103400282990100006010031810004020022954240d40010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522247302 1250 522246052 522246059
    0x34050c010e010e01141204080712090501050f0a0c021206070f02160306050603070b0706060f05091005040b04111303020325090504030309050a0309062c1017040803010e01 75
    0x4848007494660640420005246584650300070824003810f01c8580c42c205080400d00c001000c40928152001e0350044d0b0006041403d0200160301800d03a00c6d1141043c1c0c1556180c400020a14032035407401d100340c24070105140c002a4428044030b196950010030304100c13101d050b40c4003074885c10191040004108d41c10702041c4858000302e07000000310000362480f22428a0b5444540c040e21006201a80c5805030032000301c0c0701107546020380079403406500c0004416003044182c0c0c064500581100d44250025001c02031500d4141c1841410b0340d81c1924082a00c01c86000404e0280182d50341d031464046000c28246002d141c007007001030880e8001c0b001c41f400954160301d0407810540c40c80240226826468080c044203000f6049030390442e201c0d180000761041c4a8507800d0801d03080020460001e441c045042000d2a4408440d405008103030ac001d43c0c448000c2d00c1164454501800034034018104008030340c00c042d001e504080000c52032800b80c03014034a018640310034a94004d0040f40500d04005d400071 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522248552 1250 522247302 522247307
    0x60e0601091409090a1e030905010806031e01060f180b0405040803040b100306020a020105070306091107030c060603060c120c050a091e1a0d0f0908090634050c01 71
    0x12070849401d100404060355003141032004004009107072108a00c00c50b241c00000604451504441c22a4070700441244422490014074115061f480740b810401d60005010080d07501017807140741c4104202e00701c9181c1d0b0702e6200080c050700341030317000a0b0000c2d00c0c410002101307451107161103024502d0810800440e654242004125007058402030400d00041c800078001548000c007040d080032a8070f03001305000369265103500607a0300040c24840181d450340c1c11700c142c290f09401103802409030f83d4424050039040c0c0c0000380448c0156400078040107619140b40081c844983c0c000c2d000785410250500004200c02405092140c04441e02150380e882d202c5040701d400d200320f0039941c00c11072130b9898880741d510b800b10851b00e410500c4550b283c01481c8080004000d00c00b4490a03500080c1d40d0300ca1612901d0585480e030450f0440e111084140382400300c2c100c0010841030484083e908215005612090003824950500030142c2c40c0b1400b2003045c2107891036801040d1040102d9504c1802100c41c15401507004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522249802 1250 522248552 522248567
    0x70f090e010225031103071406090606030d2709021905090a060503040318031b120b0106140c100f0e030a17060f04050c1911030414040204090f060e0601 67
    0x442000001540080c540c0300543d0b100c10318102e010f03240c81c0f84140c0785503c3d900e0450740150305c1120301511002085102c211700303000013032344544484d0203494640f4004010a8039481c803c40d1300410000101510f040c5100e080540080c14004880c3d07250582d5200e200c5038000303620203008141150518486101660f00c0b490032640d2203103010384103030103280c070b0700c24261813982015008038140440109d0f00d18000c17160685150065004e80d460341050386003d810b4240d401c1c2c540d0041d070001c0c902441408049580003100a0440390a4507103a5544c440d4a0b5034440c850142801201440c024807850139070448103500311000d6290170500c108040d04421301140c0c1e5a10843c2441000302c0c96804150308084601c0228aa02c1079014200340b142c0a4210001340c2100c104884080c50200c010a60003007282a4099202c000d800605203003510000300c0c0d01d500e0342d9000364881c80d280c0d00030401c0e40da0540d0716150182ca0081078000c40600100710030751903074000740001c0d000d6000c040701d0a00000b0320030741c4107490 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522251052 1250 522249802 522249817
    0x7030302070b04031a0a0908072103180b0618090d081e070f05190507060f020a0206040b13060c0509042901050702060f1c050108211308070f090e0102 66
    0x10048000d8005d800384004d040b070001d041580e020399070400000030881e208020150305118030420703240c034510200c003000f038200c0030000e0000f00f51030b040e8004240044c040e403280100c2c1e04001c45c192969074035800203030302d548010080410100c03500103102080304000381d542040b440c9601c07841042d9848010030141c5803040f0905600003810080030455650107400744020000a0349091441c0041c041016003150081c03071203c00000d14006040024007455211b40036541e01d419074103620b081c203c2c5400941d00c00c0c0140014000a080380042120462400c0b08181050ba00c602e05000c00d9040d8840a40250002e0520900550030310403c00c40340600164080c1e01018502d0310394091580000044035203800c001400c903000f80c1d0810008a032182e19a01508076001c598003802c1120301140031100503100e041e40024016880b48900e48203611000000c403012800380050161905200004a80c03070500540c00048180182900032403204000701851080c0e81081100f4412a0b90503100c982c00c0384034426 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522252302 1250 522251052 522251063
    0x10e22080c2a010c080a1206051002030d152403150f1e0b0a0e0325030c090908030103140102220f0803090f010509030a0c09050406050a093206010807030302070b0403 73
    0x20484400d00d020305021500031f03d4182d00010050b440f0030100d28244480b080f800e001d0380c00030681e10045201d501800c005140c03555100c1034550303e440c2101d10b000541d1102603030205001540b20032654070950140500c0c0d8280c803042340126030340c1d011180b0000d4031408ad2100700302051009540030028405260115895200d025180201c2ca00701152803400e2460a1981400b41090000c1c1c418011038900c00001d21211140341554550300d0203c4c2098400d42c005201c19040600003408a42440c0c00ea90440390402e424452000c009012a40244540803841c401c504d101c0c030304031070f0100340b80040d40169850b0081100b540da484501301e40d034038042d4100c501d80c03140006903c041554458030141400c5c02019003107132000b68141c1c0d560744181c040380e00300070400c903600e000b00014001680219030b003041000340108505030840d00c404242c1400c1d454254503500d401e0b000c40d074100101d0742210421820b0354082e00c905503191045603880f805540300a17001480794580104001180c042140c00312a03010 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522253552 1250 522252302 522252307
    0x71202151e0703111f15120606051030020d020d050402010206180c10020102040e07030510140d060e28020a09060e370e06010e22080c2a010c08 63
    0xc4175468007824900d942041550010940007031a01c0410500c207074080c0c400d29000c03a42e1400e01d014041a6401c41e603401041014054440700707042841e03058850b6071190030050301c0016003460b5220000e032051500103800c6070310000d0b24898040311795202d580103900c01d0342900c195454818401252806042c0c1245094103c602800300c1498001e10003c080c1c1c03124000581050340d60030303008134600011160100460307210000c2280302c03424503614402520991035044100410080030803165030b54040018082c5d5030390894820340d070100b001a803450301c0c4110610a2452160b5003241e80c0d00100850490060344182e80100c0d11428a000e0001516950b030040c011940c0e07000c2d14140c0495001d013054040c100a5090401015030035000c00010b840d0210000c100c0441c004015440c01c64140d1004004641c40c505210058003001080090300b114000f000352146814180340c4a14800e08841800502c1804019107403454043c003403a4580031b480c07004a1045003801e005548800c0c44140080030a1802c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522254802 1250 522253552 522253603
    0x70608010513020714062401081017011d0d0e03060108032209060b0418061802070305040b43030f0c020d05030c070503071202151e070311 61
    0x440c1d0141c00e540b4005c0c0360a007011001e9180103810306405450341607510108032190809030b080041007040c850828a09180c540c582526a82e070854024041c66485070800201e08015945c2504607201860403003140c801402002040300d969851aa011000461140d10280c0301524010039070f00d04941401c00034510306210035030404243c0e1410001324002001c25040814822a0382c41010040c0c440c1b000d24540d540d00705101d003444004443c2d075003240303d401c040051080e240700301d009141c0307148822409a201c200501c0e09035000c0c011303030700003040341078002c6842d0720b640c17001c255000800c1a80c1518901c3c0c041528000d4038030359403a00f140501300030640038002c0020780b04130f002039407101407450000c80c2da00381c1e0390020300c2d0108071250980c3c3e141d10208403400507240a000d0340c2c0c018907040b0010719505181100c02400e41d07036408000f9104821840384a68511104011940400c88800000341c1a819005401034980c000c5002540000c0c52803201050354003000400300e0201d1780c18441c0d00d140110 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522256052 1250 522254802 522254839
    0x1c0e1908190309030614010e090a050a02060c03071403090a0f080703030e06042d06211a06130e06060307081801110c0709050f06090114010e0d030c02030706080105 72
    0x341d09821001c0207440c800020104d80c09108050f041c85405c0d8030008594900302c0080b40401001c3e2921206030885082e841c001107001651024071035042c0e4159032200702c9405500d05502030408090329685903810080c1500c01e0100080c9800c400407a01a40c480d0748802c50700c4800c111500030310179140d0122100f80080390141e0000302e25407000070060351030305e070701d80e008410242c01d100c3c034400101c00c200060a42030a02c20304444040d10141c5042c0c05208400b1b2001c1100d08800d006403041281d4994410800071803030040a00c0d034030703405010b1a56481100907200340c0c0107003511503429002c110001050390340c80c01c802120b00603140c0380c0d1042c0351074130340f503141c0007034140700b100140d00d02e41d40d50000c8030114034004040c140c00e4900f8400f07442c01920304042e00302543c000500740703034003240d0a40c104203459507031750728990640d020f40c4500c01e80240c0c0d820050703c0791072010342681d07030101c0505500400c26501510f000303a0f46209030b041d54085550783d038003618100000c4c000d065000240799080e9036040f9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522257302 1250 522256052 522256093
    0xc1804020702040905030909010b0f0f0c01090c0e0f1608010b0c0f06011e2c0916090603031b020f01030f0b04020412031b02090403111c0e1908 63
    0x150020001450100d2580c00201181c086078401c480c43c1d00301090450304c0345002980580107100400d401807910950301c4000141e0302c05c82c0307090f03900b50b0008500140c4030701c000d41c4913071106036010b0700b918451030301c904402e420741d05c0031129003840854040001e80300300c1c42100310403080031003501e400800b40d00b0040d405829802c5000503a043c1e124000400310045007c000f05070003060203603503e0350a0755031211119080450350300710039400142950f0700c10203c0031543c21195213181c80f485030103880d1201c07542c413402c28510362a04102075000100c080f035000b94540c440c000300c0341702c0d4a4606e0500007408031000c03130126008001c1d60140c10552501d0709035001c0d8000005901c0480d90008121002a00003422600b00ba005a05000c82c900100303010550400001080310000080038812140c1c540e00044048000071310083c100002540f100c410311130b04025500c4680d2070098980480d00c88850010004403059880c54030400400e40c000c00e1050007080740800380c4207240e0142801c07540d1315a131240c440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522258552 1250 522257302 522257347
    0x703020105063f1516120504050322360506010e06032a0702100804080f07020d0503031e01140603010b09011107080a1106160b0a0e0109050a0c0803030c 67
    0x50259180c05640b141344040900d201e40303020345461448140005004010303610360101a2a402e1401083c0300104500000756104a0b949d48170032813486020410201460300c0399800f50822036640395010075500541c0a40090442c14021403240c10120115480300b99075040c0c48050101301140c1d014009800d01d6070003590b21158860a0140c1c4121800d10007490044561101d0000390010560104514000b11011001807461400f4171480c1829200c0c064070303104131201030704031103400610341c000c54a68205032568150404141c03a16442d00c441c2e076134040545031048218404014001155020100340300700c118080c003420071410340c2c3c20801081c100d5400b00070614144520290144080e6008210041c0507100100207003071050510f181c03e2400700c1c44081c040e0300c80d82c028498040e60b8440548150001c03a00f128a1410a450b5020740d40010502100421420b508041c00b0506120740041c500002c1031084070b120078025621940942c490109881344030301038108000651110103620382d1031140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522259802 1250 522258552 522258679
    0x18010b031524070b01090c02060115090e01090203040212061b090a03080c07081b100f09030611070308010509040b071d0901030b1906062a02030102070302010506 71
    0x2080c410481c2d0741941e14600b0000002e03000025401c2c100840425607600400307140d641803207901c203131800103511900140030b6400710303070f4200d90314084107031190001400400c000c2c2552038481d43c403030314000080d6000f240e081c0d00440920300d140702400c0c1c000078803c0c410310016000b8444003c05404d0044107030310600103241d200407404400310201740c40600928034a40030300018000710703107010019820240300c611925a40744000740c803001d00d0b403201c0007000c850980c079203007980e01071000d224281c400c1081d40d040501540d182c11081140007112038000c100c194001e8a40100c80c0ea81d800030040041030441e4020321440681020a18090280f034080038000c042c0250b040c00d40f11110042442032000740d0096518500c004288402c0000c0820f96125401d8400d105004c001c5c14003001402800340e09a030821a1040b00d08041078202011040240c52039004001f9940d801403400c0003400303050142e4280d84240d081c03a004074001c1c80c00312001c9000d000403080c0c00c00103007200c1750701490841c48414070b00760 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522261052 1250 522259802 522259819
    0xf0a020901050d1110020102130905040c0306091a280b211f0c030608060f0f07020a1e060b190308370f0512060d030203090306090105040218010b0315 66
    0x1d540c0c1d85d005900d4001d05580c1d00060300c4010300600040a0b440030390040155620703050901c0045100348a0b50000d0745d400020114800c00246040102d41c460345e01c4000344411000c007480000c511850480d4006402012a4100d1101d0248a0011208850101603110203c0ba0302d034410f520504502021000101041e80c01c844518201c224036403581002d0800c2c03036070391000c40c0d200b502d405100c1c0780f0103000790900278607691078540e51720100d10134003401000406621170001903001d03100704800201241c0c05811003150508001302c480361501c20690460342242010b18034500d82c10a0590364503184c0410200010b564a142c441e031045901002c11808002001c2d042088011041c00c0c4031048448000c6212541000d0f403070005190081021441e41002401c0041014100c0030710304040c0c12031404c8500990000803460241d145215041003a40c01d0f000d01c07010065091380c19817020b4030550083c0e4070f40811407101c070240700100c07c09001d010f907885000c3c00801c0f14891044d00c0742e500d0800c09442d080 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522262302 1250 522261052 522261083
    0x30703020310020c01050109020301260705061b0105010504020f040b0f07060e030706111305270f0f06060f0a030218030102160201110d080c0a020304180e0f0a020901050d 75
    0x2e0600d5102411403100c50780018603250010003d00c40c1034010725403c0001c500355410000d0036602c001c416120031000100b2440454035594050002c0340c0100b4008003401e0b9204204403203c1d0f603411005100900f19440d182c0000340e9418280200c85011600054480c9030901300200c2d100c0c142c21035040783c101c252080c04044c001820921808540c984000015501d401181c0340c51300584440c03030302c018040d2809000d020084480b07512900c059039411904030024100b40400c225406c3e1300400c84600c1c2201030418000c0d441078000b0100c1c010b090766a2802c002c0d43d00c89041c8805ca01c0340441c00155083c0c1004803c846d24403a501400d0541c640e4004564000090000a401d913000403c01501518003c01040308540c0c021664200304482e040280404441c20500504910700c0203080000b0100000742603500b0ad0b20074001c6038040d04000a00940003009202044020720a0704030302c501034810401050402c0000081300031019600030400340b020380c201030030b1100142c0c003e1001c0303564a03088150704 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522263552 1250 522262302 522262309
    0xa08060423011509050a150513020903160611070b0f0906070c0906320103091e050a030f051903020a1209060203060f09010f0519030b0f0604110406080406090203070302 74
    0x380300107039480c80a200705070f040040740001c1701c1c009080203411500d04011007081d1402c90b040c0e08121001258010400700f0300b08120740292240d04000c030f9050085e1510800308900e032130400c1007660840d07a104800c09450310b04155031180540900c40351540b051002d28002c50704c4100500503424040c10041c00d05519680d5584218210b4023740752150302d80d0002d100c10b4201d0010010354050418101c3d180e5058003d814084a0403440d6280c101034941d034558003131045803040045080c0310303070b84011090802800c107151109100356080f40003030b55940c10058500d10a005484001d0500d0340000d8100c50908015402540407940503070900c600c104040071030064a1040030702a42c024440960340e49080003c200c80d03c441c1045c03c5104070303628070045c00a000c4625041064410948071244844c1401089905a86440c0d000903c28825101006521450310480034083c4c1c3c41070350240301d074981003603a481d1980600e0158400040d456400200810500d0b003001c04207600182c15a501d0b5070700d03500131 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522264802 1250 522263552 522263561
    0x131a0d0f09120c0b091b0f040b2110090b0a09050f07030503180103140a02030718080f011406240d020f0304140105071205091c0309020f0a0806042301 66
    0x7142d0104030794405040a2002104049500c150044017412103207141c403021503850700001c1d0515016801e903034105011600c0e55030181d000100002d11118520818200d1614501700d40003010505004007203810303400300c51502601c5480c82e4010b0760082c032a66000700e42802030040d03035800d4270184944808504404401d20550b400343d40514051907880d418418210303003141641458034100361400f5420740c03520070007004294010400d0203016a0369228100112140a449000f1007a28120201c0c0000c400800041d0040c112a84000030f001140d5210106c0c41d00100840d600c540000e0a142d0440d00c40e52840521759044502600150920300107a00c203c3c126040700b550303000f10f19400000e0205101c2030300242c041009c0050000c1c1300c14039203054014680c00505e40c1c280c00d495101c0f004940300400c140565001c10300c20610782d10030714400c0c2d038006015208000c002c1c0c0c040e4800000302c41d19414003e8640d02900c1c64a8002c202649913544c4240b5044000f007003105030341c1c100d00c00c85001110203006 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522266052 1250 522264802 522264833
    0x1020a17280903140705150c010f05010b0306060703170405060712110904020304060b1203040504111806070c030609050d0807031b0e0409051002131a0d0f09 69
    0x21580c450400703000d6a04048580c4501c0200d18100c0c0c012012115403040307070328003a66802920000e100c0292940306281c030f44a904020380c0b154118250364880780440010303150808212000340600c400004551048800a00440e15040b2080001500509008009082c410b1180c80c0079040d80b0105102408011403c0d2400c0307035950880000d210040ba8000669404034400203410132140b020828a00031718451003031903502030b07600403000500303200350750380318400c81100a400d0344080d06200400135103030f6000d802000d109a00e450254042a4480030a8403c404200340d00b65000b8820041008000d400441040f2010380c4c20150100020301d450040c6603200d446030004020b804111003019002d502c008004008241c5881101804d9009103102003e50030842d05040c3c11003180e04003c0350181401070750181191103901c0340f031030100103c1d038010880205e469952806007a00d50040e80401c01d650140c1001d01c032000c1c00801100343e115401005107401154000410360220303501c25004040424 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522267302 1250 522266052 522266093
    0x8010506040c020d0207030b070e030a050105180c06040902030c0c07090b1003050708060f2106040213020405210118080c01050109110403171b030a020f0c010c1101020a 74
    0x184003850400340a403000400580c0007a11114032000c800a40d514180d200c00703032001001c100406c199a02880b4403a06c0000d010b400d03940009240d081c224060300090318211381e44600c11550110359440420311a07021280200301c5487c2c030f403400108001070741000d41941c00009007006402010402084010001c0a00c00e001003840b00d201001c0001c0b41601000c0401410305100c1049070240c0d015001b50303400402107a0014000c00311b140480c0d100d50440121480d2640721a09031920190700140044c4070b5403080740c0088040000c06048416802640f140a800940c8106143d940e81000c14051081009080000508281000702111001810401610189400690602005c0c1c1c01c1c0209409007407245803c3c07140c0f9003101d042980a00c90b83c071015003180021080c495040c03030140122920208800b0b01d10462a0b0300b4224980c030b07944401c1c4814054401e00c500c80f114041d000c2030528000005842d44c5503012130039184d05407031000c0e06800034110300409410740c000400300c40b1010034009699 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522268552 1250 522267302 522267311
    0x90c0a1203030606180501030903021c0c0b0901230403021f050f06040e030906070203010b04110405100e0102030a03020c1903090503071217090d0c0603331703130801 73
    0x905001e000c4034001e41100d001c02500244400704411007003001d001b02c400030318000507000d099081c22818200b03070340e06400c1d80326034206100c0901c680c40544880c8c4c1c1401203000350041d4607100a0f00303080f50708809101d103070144c02114680c9006c07015071388994868000d0042d02c911024000310340c60000e01c540310000c003040d40d801c1405030709051205c0301640f1545c192001c200034034250420960717a004881680b0b1056600007641d40071501c0c203420103170402c10050030500040300350501541c0ea82d0494001c940c0600340141c032589041d4401e148140700400182c000c2c6250403818801200654425032001116106440c0c0070300e4803941d60205035036810300035a200d8111604140400d802c0a0580c0e0000c200702e58107121000100b80c5241c0c890a0a0141d004d1056890a0040109185a1281d040540b000111080003e645501900901182464100703040316001980030003a1a5081180c203441c1d04e08002c0304144425903585a4207400b15807840304690520030003000d101e090740d0694003d1074081c0d449 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522269802 1250 522268552 522268589
    0x317040e0f150d05121b06010e060405070503040c050f1f0305091209010e0d051603050f241609170c190308030a0504030c08070308060102060907080a0308090c0a 71
    0x6010b60007000c24089030340f074203e20582e441d4955074012041d03c0c624605000200c075100c80c00f00d00104c0304245001010f5a11303e40c0d660710400c1c0c00c0042104c82d10700480c20940002ca01500c101c003101c0c41550300c00c1c00340c0c0103a030501d010701500810b5900c085410800c00c1005482ea141c00c154044004d60a5980204d00c42c5400c0218a081ca4102e02000d062504240100c0e00c29a0b0064048403008005a5925825401c9810f007145032241c5088440f20290031090040180070340403d80d00044140d05084410703049161026070102c400b07485003585150000408960103a1484c5080302c070a0030540341c20141251a0182c600d0580703442090a0300503442880301c011681440d00042d020301c0c014031038000000e031450310f41070414407005000c6040d007a07a4200140405000e00003c0c407103d5000510141c6401e040d14000d0a4440c0c02d49217a400741c4035600000d2480900007400d1000c0d161500041c0440c2d2a007aa020b40e10404081e01c040300502605100382c0003070711284a01001850255800b44c0c04040c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522271052 1250 522269802 522269821
    0x10225030f050a0e0105030a110a05031008060f07030903030905190605010b090f12010f022118120702030f0a08041802070f1e47010317040e0f 63
    0x114a40c12100b400000d00515804a8200f01158034859080c205284d1f25a1000c07840401813a080c820031800b003c0109002551692081c051403050951414141c00c0b90744882040e941c2e040101d8455000742401c00000e0721041c8241c0014500910905000c40c1c5000030f030ba20182010425804a000c0034240019003080c410036000302801001154a40c40c900003800c800304402d0203819200350b0240b920f118078010320000940c0600c4000c0c1e8100403c40d182d010305003251218030049140c80e503020401c14003140681d1503001d240c500b002040d10081000700d0658002d00e5194000c138005a03454000d20703140d58034010042c072440310090322a004040e540c0d4241485600c50650042e588403032117105100702c0001541000c4481d42154010b04010142c0314850030749003085030003a800400c2d129106001e201000169103404401440003c404030890390040100c04070f9880200500004114800040012440502101d0031298034441c2d01490151504d0300300020714410f43d6610202a41d0714104a503044 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522272302 1250 522271052 522271067
    0x902031b1302070b13080705060c191704030e030f03030a0504030912050303190609020a17071d0f03070302030604201519030219090302040c0309020604140301022503 73
    0x4481c031004604200c103075201d1504100c8024020300d4040d8480003400c0034804142d0550760130550007000c070740c0f403443d00306041c24103604003d0b550141d0011340d44802c0300340344c01090061428261800852441c1d9a203480031240d1040003007200d034050203440c84c0003811240a0009503c900b2062802041070f0425140081c90b00d58254060460742221103100000076034040300700c0c0e0b0801070103c1100c44640c481c007a1500200151f900141c0c0b00e61000a16800c01600010801e45001482946125a698298003511600c0358812041c0c3d0f00001a42d42400e2403504019050704400c0140441340c602c0e03101c0d40860319012041d90305070f446421000101a2810302c400b40310240341d40558110882d080f107069449070038054001d805080c41c05d00d90381500f81d948260f040d62070481444c04907190400b0307680009000140300b40002d03801581480385c2282810701a005070b60000b82d000d880c1a10b45480c003080c90b5a1319184c8002c55500d55001c00c40d00103401d0740c5004003240c0c040d20442c00000c01070380707240c05403014 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522273552 1250 522272302 522272329
    0x3020a1e021e0117070f270611070302031e100209150d09050601090c03050a0b060703050703021f05061c0c05041e050a021e04030b0106120902031b 65
    0x35029a484200141c84511024401d10303004006800e0990322100141c5512140b05005000c1c2c5020004004140e64408011680c041258880200325110103a800181e0800c0c086810a000304280d41044000e119600013941c4c82005002d884d41c8a40b641d0000c0c1c208500718030500706111041182c80b10030354051050392510206001c04601e402106008582d501d03562220803d00d000000c100d03022810000d80000040c10342c09802e80d0401e60f1104080310040c0382c0780c020301001034a403000003160390b240c0d0b110711444074a0040119051035551340c0c044465601000c2c0440c01c60040f01c4004a01c00d5017004456103090700240c02081c2480c0100502c001c821103440d11040c651041502500031034108072440c42540c105071000320b81d03a12100c60800c00d8603040400f18401600c0c100800800030b51650140c15101d005040c504081551001c48201c640102d020180080229600402600d8011442c0d26400e403c400d8012031180c244c2c1d00005d051a0400c2d04602c00f0b0002c07800705203424a040482c0e407441 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522274802 1250 522273552 522273593
    0x50901060f0306260d0509031b0d052b0804080403080c16030c03110d1709030c031005091212010603050a09020409201516022b050c040e060721020703020a 68
    0x83c01f150b00e00180d41c0e51190002d0400040016a80d8801e0782c0714102c80188143e04001201c0806001d01148400c1d04681450319241d021a5030101c4582403003100380c24011900920720390304180c1161503100095105840c0710505100300c000300c030500b48840c0d4008000b94010b09648c0d05039891800d080402100c4000458070074075207498045d0000d528091f454020071000c145c1a5201c0c4080404a03141030000d11980e40e0622821642d04000d400b141c0020307100f10384e04810389600b00c104000c5542c45006032030340407804030752410040c004280300364003283d4000305c100408100346495401103411501641000d0701c00c070034100885031909018070f8100c1140002524100c101d03c1c0c09041c66040741c044c50f003070380d01a80c180c640c00e42c05640d00e402403000003180703038000100a90310034074001c581d00900500441d410b001d54240340b500e600c3e06114011803200e261707000c0c0807079a90728a0100d4440c0342400c0c081d2440020800c402d0003428182c8050300410388030f50000e0145120320305010380e074134902c80c070320960 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522276052 1250 522274802 522274807
    0xd090510030c030608031813060612090201030b1302031e0903160f0611071202011e1d032b09020a030b0403120c27050901060f0306260d05 61
    0x85032290104981141800d2070001a4a203200204402800c0b41c3d500c111000d1001040f108011f11460314114076004086840b00424900000042e0540e4042c4c80760401003604004d000d0300e02c0c40d40c1e42084035114414500000d07080300c00701c0041c0300f9010000e488940e095012080140889007914800c08202071150b8091380f515103c217000d9a24802c018075184003905c80c07807110080007001042e501c0002d0f8000310500c602c2158a50203005078100001c2a6022840c65000080150061140040c017107502101440902900c4003004007500c504113032048200040300600c012004c0a0010340b201480740c01070142c1c071440d0128490305e00c00b03040e500001c200c3c1c544070581c0d005036a4545000216584500f403c04e05035501c0c00c055130803280d0409203403507041c144610b00c0a881c0d03012409074581222491a00c0740c20082d915502e842d62260f00549400ca566940148007540c000c09224185d10018580411465107031072070110040f00c00d0f045001014012051031122040503c8445000c0946260450 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522277302 1250 522276052 522276059
    0x60e04050a0603020f010c1a0411190302090a181406060102070f05130c0c0f26181c0206040312110d3002120709050406050a0e0c1b06090d09 62
    0x16a881d8040c0b440786d0600ca002038182040000002e480c03159901e0368403c3c80780d1403510b810f00b03080b188012850244103203040c0034402c0b420510f14004605803500030748a203020341c5d40c1500c4180101450150288a62560300000001984087c00b10744d2017070100c1c01400081c03c00e140003914000c802c1d0451020701120503030901007603c9448590740544500007000c6100052040c003135401c0c50303800718054400c44080220f54180040035038050740b10b0700d00c1200320b0701841003800102c8083c01134903880001c0751541b1481800074500000b081c08145030708612042412550f40c0014190f9020f50700c01c803849040a0f04920b4500d401245c2241104c81d240c0180c80550708021000f040c44410180000c07200c0d60000c8507515500e0244100e200c50110304004658441021805030780d018002c903803d01c0080d024a1b00800c9a00345800741408841c0084c02515065041120f042c0342002c00030064010b0305d5082c4200c08481000450315070b058682c03000548000d0501d0350344103041041c001c5009091041018080 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522278552 1250 522277302 522277309
    0xc090203070c020a0501030e0303040b2d040309090c1209022d0901120210082214010501080c010207090917070c080c03160b07230c01020c090702030a0513090501060e04050a060302 79
    0x281e41c055800329110205379240d02c0c82002c009116078178564902c44440c1280d28030035034000d056010318065215020030960742c00746901503e8442400e040040c4001614800e10080f42c0c00185446100400210543d0f09030540715140281080d20380201c403018040340700e03940c1000384055014005166001503030200035000305c0d20030b5144089080c00c0041040000d601d22900d40349a104001042c41c00700c061a109041051a0740d1440c4a4003005500e40790002130040b000040494100740c06801130b0541c0d500d0428148004c0090040944501ca0050301c0b500d05101e404006105152048030410b81c064189507803a86090780015109000350310803076945451011441000007221008405140d996159241c00f08410b140d03c1c61040ea200c4d007072844507031815404607031102440c0c0d0a03400c58001c409060200308190501380c8034900507800401020801600c15002040c20010b10380200c22110b56540d42c100455000341d02907800181e86400240561a2501800f90004009082800b03013500750b4000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522279802 1250 522278552 522278557
    0x70522050f1e0421030207063b0c0301230a200d0e0109110f090c0405010e19081605060a020705010806030118083001030f0c090203070c020a0501030e03 67
    0x203214915000b5000038041000680003410107444200c1688140000020050065003160208680d22800d00c42c290440b0715101c1c00c44050030441680101000c00005640307035114003000e008001a0151281c180800d44090280940010f84508200c1d40c5441e218551601d07190050082540c25003400c0100ca08100f98822601c3c45c480d180c800e01e541d81c44000840c070002c0c0b0720008009003950030003441c00184280c0001c02e01000700181c0720202030160000402141e17074000c0f607100004890034007050080f54403440d10080c083d240500032000300003207049507240143e4203a015007030a51003100c0001601264403805801418151005814480c01e003002a454200c24060903042000310f20018500d0354094018a15505000749207003050b1615082441c1241c0c801e00d59017030761240403001c0c2003c1c442b03a00c20700c0708404542c00b0f688466900f1a03440b442e48200517141912848242000451103241c3d510045005101a484a5000c41403d10510507140d1550b442141070600d000801c04917600c01104 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 522281052 1250 522279802 522279841
    0x40e04050f1c051c090b060312120f0907031a07020c0f0609012a03031d070e2a0307021c0504050307060302030c07050a0311100504020a030206030405070522050f 71
    0x81c46516001d06a9003002a013192031a1450b0f8507040c24401ca003403100340740419000300e00c00d40030f441c49d42c5d441c14141045841203550301d034807401e2000d000810076000f02c580c00c1d0f040743c88a4280c8460558940300d03101c202d051641020030032000c0c00207001c00141c0421400a44000940e040d9042c2200400082d01902810200c2410f02c00103002a10322111100c030640c1001581c05204014461030f410020000c0c004240000040344040469600d10140054200201c032200d0442030455079920b203505901940095540c1001411003001110100d1b403400918828103071580240001d4812500c3e48406074403401035107081c414200300030710854a0110b0110300751241414003590f0390b10303010b50411842c414140c019080303003e01c0c10ba038010903034020034040c5440150b10440300e60811011181c81150b4007030350020341c00b440811003000181400700c0a164003038050000e6038030195aa0000c641501c4840220414091094102c040304800c030f40308058003c5403409410066240401e400d42d103403c080c88 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 522282302 1250 522281052 522281057
    0x10806101a0a110706031e0b030d1209050604061a1005030a020c032203020108090d020a14030c0607050301080d17060d0f08040b030406051302010e0103020a090506040e04050f1c 78
    0xb0707030540040c0140e5601420f01290400c072000300780e50b548018000c000314129101510b541104091003005280a24808040b005001c0c0c4450303000118196484a601580902d002d5185d12140020a00620003a840340e8012000820001524040c001c050300000d400a44a404002c1e01440d159a010040e01e902480140700181d8036502010b506142d40210700c1c11f400c4801078132050440910201c066541140e03c00c0c2c84850458072206641921500341c4040700c0b005a001e4128007000c101014161500c282e00c0398150b13071030401000442c42c2010307011501d080214500000420414404001c0241800540d20303010040751801ea021f85000e0340090500c61290700c00284080910148410000c1d2950303008040720356456031240e0440c00c0e82c000322000d55185240c040022a40c1c1d0718820024001c40d4143d45940c44d454609005400942184407980c0412500c60000b084075202c4500500140000b40d01444a515007803510320328100d2048441c02554010107001e6030894414200700e110b808250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 522283552 1250 522282302 522282307
    0x301090f18030e12060c0d051006050906090103021b010614010903051e07080d09150503010e0f040501060f270c0807030c02010b22110313020409051c08010806101a 72
    0x48000441d0b1481070824013580f405204c0074040c0160611000f0704418002daa0180034596031170422050160b098410480491802c0005074010729083e4014600030905041c01428440040c024241c454401195031100d40e40d41c04017486444083d0b0154070003a0b0702440e091400d40e00355034580380c9404041400d004980700112210301c0d0704c0014042e18018003031030000c590010141000041c01e5002d01d108840c1400844901d5a00320351090040701d058035020803a112880c1c544080c14440b841009006079495584c490010400d4141c0300105401000b450f03052010f00c007600040b000b0030390b4500405426480c9002c54030845d03107810882c9c0c1d0781e00041504000034100c1c1c591704207134090301c000e05200da400700d80607890b801d103c4c0030076016030b03803000c642c00d02044511462107410070540320039113028600a9002038004c00501d850313002080040c1c400c1e010348903207401e0040d80b13441c550360598149010070b0515005007e8001c0c00c2081c0c960120b0340320301d0344c0e885c107203011044004c0c510415000207444400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522284802 1250 522283552 522283577
    0xa1104090e010b060703181505090d050a35040f061d0d0c06120b090604021b0313170105040b0604090311060a1505010e0303120415050103080301090f1803 68
    0xf944902680304015046541d29041460020004050221526250301807540089010400140840780b90b40c0c4a80320705240601803c10000d29405001c0111400d01c02c0311804000a126a6000d01ca50303100e844c2484110f1700724000001000304554000c003003903041800200000400c0004040840c0e0990138003803803008488014003292901e1040d03050304401404209010000c4105110302110302941d1415803a1400c14124015a82c070b510307125078005060400300c4c00902d03080c1d005102c06c1c4c0040c0840890300b80300110385411038200c91030081a40c40754000401c100c083d035044107030000c3c0f00c0d50020011840c10703903581c11118102074a170b03900580c0d40782c61607410140070b0b40700000f5480c889011940e0034600f8003080710180c1000034003a8103908030000d0014081d40a03104124620b01d004000d1824181c0203024000e40c00e40040055500450042503c43e4403902c0703206460185004181c5180c0d2907041c055114161200041550355a501e80160002041c1e00100364003030300742c0d0529210094480b07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 522286052 1250 522284802 522284831
    0xb060d080d090803070807020c09150123070201180612150e0f190c0206040204020d11030a0204050a06090b0715020903011a09160206181e0606090a110409 68
    0xd5400c1984081d85006440024810700b8070146125005940d06c0c8122a61071040890700d0702001c00d40d607500420824081401d04031603800300448404185000caa4000074889070003001c43c2c9075021112900380c0043c190041d5640682c44038540041d2401c00f0000e14a8071000600700c3c0108100d907008240e6480300410008004141c3c0002800c06041c000385905021b141c0c80d860350070550304460110880d8403581103044081c040c8400301c411a4000e0000380d601c980a00c00a584410b02c100c0107250b8030015103010500f100040c1d40201c030180f40041e01c50b03080c1000d0016942c40342c1c01840502102e03920400042c0d4040301140c1e070141c0c1c00008480086e1801003c4400303030158a0340f5036419424a0122119541b01c1512402c1c030903c1240c0005050721240c51448070407030880074010046c2c2054001514101e001e0344a0144400300c0c004580007046040000d030040850010380d5803107a0031000c10b1013400d10b0b003a506560000488441000711400007000d4030780c2485980303d041c034902c0d11b880302c0d07004848 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 522287302 1250 522286052 522286057
    0x70e07030609060303020606041a0f09040606050301110a02010c020c060f1605030409020c0c060c0d050c0708030a050d051b160f0803010803030612060403090311060c0d030c090603090b060d08 84
    0x8195400f848019101d00e00a0f403070382401c4810034040c40c0f50980c0c2482c4540d205c0e02c428901000074002c6084480c01500b40101031000400641c0c1454903020005020f03102403140c1d204010301089000c0d1110303a402d2009003034910900d045003c5502401101440382d650000721900502c0800d030007030b0368010020034401030300406c1d44c000c0d02e240000300d000150500903400038664a00c2c4401a01c508061000800c00da600654041031404d81c0420f0031005118010b01c02020340340c100d00d044480e03041d50b0701c120f20300d076034040a02c0400081c0c0c042030714090500c80b40119908529080c2c2d44120440c81d4030100c2e21140586203110b90003100b40307032000c02440403030801e080b441508000c00329625a105d44200b17680351320680d12a0b00bc0c0000f481350a00c0c810b07010448900556040c1e030f50302d4019285403900d5041e1a01c44a1103a441181000075200350300040058080580c101d442c040354800c85d540005c0d2081d4141d40c003d1007414140174241c000a503c90408030380c844800c4500c00ea2054540c180302c0410b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 522288552 1250 522287302 522287309
    0x6040c05010c151e060902030c03011406072109060f1e050408060c0c0f121c0b09070e0301050105121c02190c140414070e04020d020d2309070e070306 66
    0x25413412000740b1524181c00c6101c0a003600b584d00074003005590701c141070b00f2880b00b02e0781c044408405000600200900c2040303142440001812181433004a4a070b5000596181c00440704002185606204031908242c0000040a0714102100e02d20380c5940054900207034405411415000e000210020300c0c041c00c241d40291210404450144c0303846d000348113040e400301038101913a2090b1818020074140000f07803103964400d040d030701c01c1c00c140802c0728281c150951a203920304040c2e282e11105070640c603003402c55480341f54540e43c1d0715200d03030106e0145400c486041c2c002c0c80c090305840350201c04400002070511070303c00321107090f2840d030005000c0c12400d0042521702b0351303e01c00c6d1511030b0b0340074420034203040d000742c0d103040d45c91050100301e40e41040211500c0c00f10b00e21380c84659000040316140244060074130f1580240000d8076146c0c01280450403030380081c8034802215030347e4803031512039101c007821140351282d4841c0007071081c00c0c000245907582d803513131007030454507c440000509180c0c42a000300303000703 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 522289802 1250 522288552 522288593
    0x30106020d0c0302031b0a0501110307050711031f09060e01050c160606081603060c030618020c0a080c0703060501081b1005090301060e1501030b011b0305040e040303021b06040c05010c 81
    0x680814400c61b03038a0341001c030700c1a2040d40c20998409000348840e4122405030440340c6615141040380c1c1e5445085185900c001c0c0d41c1170080c580c6030004100a000d1206500c0381504000034020b00c1413901104a4894001d0904540e141404008014202c50110b0f18044019039a0304084041440c041d00136107080e8010446a02481504001880d8001d00c0003003038910805003400f0740c0031101c900701d084511500ca101c04030b0102c41450485a0104d80c001c0211109203400e94441c12a076449604180d448440910026800b2890070824002c442c407820b805080d00e0005030060307861140c00a1101c1e003000700312030300c11801e081034450100c3c080c1085034180352000d0024040d4658845030200703c8202107400700c228804882c204800381d0710902c82c00e081000705868000390700d202640d401e140c020700168102d041c0001000003013170320260030300254455071103581c01603602e000044485074800b20524103003c59910031814800050480401003095800a1800080c0c4090f036081180d921001045101c68 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 522291052 1250 522289802 522289837
    0x12050106020606060d152421090614010b1b03030c191106071d0d020a09020307090b04030b0a180b061e0d030810050d0b0a0504020402210403080c030106020d0c030203 73
    0x100000801f200c07158940c2c14492511909040c100c069402052003940c1c1c410048000d460688000040c2d070101f06154007601c40003131241c140490107600c01400f87c000c001c0301b180106090303030032214001e00c1d0810080304001950031030800c2c140080f614051030348082160117844450079146c0d4404d00350498000720500480c5c0e04d5082c400740c041c01446218040011080904482100c40d0400c1d450300e5240541c090400000f042ca4056580c000b904050503090400010007000502d0342c4001c800740000e10701404142c0b8032410103084180803198801c40a2903907986103410b001c04142c1200d8410741c002e4060b521010600c8501d40b10440d411004c0ea0501c5d88201c09403000003e25a0020a00d889000358024003920240c03190208804042410002041e101c4400700150701e50030b15030000e68010344040d00c050f041080001e94a800ca40380542c4c240c2c11900c0480030030050690002e00349030403117210000d1030702d59414a00c0094495006202c4001448000f80700c40c0300700740c170810403035000c000003042048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 522292302 1250 522291052 522291059
    0x1090213091a190504150302010e0409110d0320060c0a0e0f040e01020a0806221a040c0f02010f150303051e0307090305010b1c03210501060e0112050106020606060d15 73
    0x616580140100e500607442c103281906004441e040986c1929016140d40c02d001c10001c04000c00303418400b00c1200d9851a0080f10010303501c03480c007001c1c80c15219842d043e08507501d12050440c2c58211550100260b805441408501c400103c12140600c646103024403858081c0c1d804628061100f8120a4002c1d01d044603444200c0c60640c0034100b210401c0d51207200d5a2074400410a07440340481c10400c50811100d6016500341e666401b83e041201c9905600308440c1e4840c2c0003c0480d03090080d0103012500c80c1c220b01031000e80c28800c0c11602c204401040101c401c116100c146c124507540402001e0190000d034107410003640b900d100075885030035141c1507035134504035100503e02ca045100440d40d66003000e523000500e18080c40510072640309142c0d02c80035515551002c6600300d503281000d440c0960707901401d006141050140714041c200c0d40d00c07441070700c800c800001460715030071000325a103280c0703010018005245d011801c1904000100c440035198054401820000c000300e0307442000461a517403000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 522293552 1250 522292302 522292339
    0xb03030f071e0b0105100e09130c06020708030406030b21010c021204051c03170406150806070f05030a0b09011e050d050d0c060615110601090213091a 66
    0x1044040c0c800c184815020450445050448a550368003c0c894401c50005101034205010410401046442e05005c0711a141c0081484d00400341c0da082d14206070110504d09101d43c1036070400003008240700070019180307000400b0340c80303001d00d028034001c01d902e4400e500d61540d40c900403802603011503c1c0261340c058040385032034002c0c00507000e0300000d401112042d410307074040034069404440001d8041e901701a00d12400315500c070341d1882c00b20705214000c4080480b640d070081d0620b1003180302d494002038030001d6081c84404404503030311514160340070701c0c01c0001d95607002d0083c6d0301021007801c0090b1a80c54064070100034091461440da0081140400000c04600c4000301c480c10070130030556075a00703944505c1408203001c000ca0001e00a5400b803aa041803861188056000c810f004180000382c0039100e1100d00c807402c00e0002d003000059079511140e04d00c500c4c140305240c0180780c10703601103142c884c10601ca041c07040118403400c445180c2c1c58002040c0700c04411209210500f00400c1c2c0346650f0f105d040f83c0c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 522294802 1250 522293552 522293557
    0x110f010507020f010c020c240f0301081b100807050c030a120c020a0302060121020a06020d020f071d18070e150604260f012c06010b03060d060b03030f 66
    0x1441c0180310308998900aa48184241c138070807000f0354081c0001080180030710404074086188446150880462084104403640183c9070950310000c846d40d99500d8001040d113000c40c460301c8013044284060f0321300400c1d600e0014a104100960600411580d211030043e00c1500a10022013007a0000158100107154001d01e034440f1250f0f4001d040180540c4043c040f41c3d606000c640050140c0c0c00304005101c0c4a503200125980f5000d100c0a0761094501907000c542c00080980c00f41003d40c2c00813440442c0c25030180002c0545020480003007070300780c0c908591070411280310a03040e022000f030440816020107001d0740c0c482e101d0360b00340304503103030035a0b60000100b51035003c0320ba9920f00040c1c4010780c029407400038219002c44620b007006800c44003c9240d00c4200900300c0e00030045602c242041402070316000c1c051840c0f03602c00e03035440c0752500840804035070103540412040342460b00034034014407010105100341c036001402611405240a0103280250040c80300100150749440081124400344600100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 522296052 1250 522294802 522294811
    0x20907030603050d170f09120c0304080712061812030209040f05150102061b1207020307020a06020717060c0d02091201092306270102040e011e05010507050606060a110f0105 76
    0x1045c444942e40d00c1480d89202c101902c6040e040e03000300001e0720043c441da00107040ca04944e141500e00e410740c1d41d10b42d18a4880e465010700031700a2508064018000c0f01d110b080e50340384904079240b000b02080e035580083c421650324008241a408951074001e5191680116049901050208070382e0604201c4500b8510390144242d0062091000103100d10b400c6034100030141d80158025420a00380000b0ba500c103050080803141144018006040569103e104003001404160040c101541c107062440510099500c80e40042d580f01000307204980c0d410300304480071b901407401e00580303c44050b00040c0c040d910412032150300c1c6d030030070100c0c106218002490304035550040a44444450980010b80e0b12040103c0c0d00eaa4200e0b07980043c421046c1605c031300c0301019030720349000501e0280c13070348507c560003942a04140c8203c0c4450100c0c0391481241080b40d0064082420480d041481d1aa00c0c16a0307007000400141c0285004141100c1c0035004101c8001040d04513002d807141e00c580f490035140217210840c1d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 522297302 1250 522296052 522296087
    0x6040f080f0d17060d0204140601030c0908030301090903030e060108030c01050709061b020111030f130902120a0b0a030f0f0209060910030f080c0a0c030b010b0a0c020907030603050d 80
    0x74541650100c0004054802d22541c0c1c80307a002018950516602c1020020200b40c0c0001c0c08400080044c1c0c2c03244210503140c8491034078402c15041c80f0300010202ca040e00c80c06002e0041c3c07058240580c0c0d1000094a044450901c400f007008041da2804a018000101038030040f4403403240081442e41340403011340324401c1803100130000c40c0d42d41d4400300e451591a01c603a00c0407030880000c80c11010408482046007500604014000d40c030907402c010f1455104400d0f9007403290000c51040e040c030020301003240c01048030110660808050a1214401c440701800c804205595100e82c0c00c89511940300d80c0004580040100d0450700e90b90a281d400d02228000407442104070000150031860249511401424105564268541075648042e001c1c0c0d140340c01500c1000003440003407010360003042541400d81c0720f005044d201619502c0c16480260040c1c0200f807145a0501033015010303840b82139a080b560701107480e412641c030b51540680c02011260800b820390302606010301e000581000c4648001c02892 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 522298552 1250 522297302 522297313
    0xd200a0207030b13020d02040b031c0906020712030504230312120a090309060e19140102060f130809180c0c070e010b0906070212030a08010617041502030c0906040f08 73
    0xa0280029803400364100035801b444c1c4802c3d0760098102a4019810040042d040317802403540040030190b02c0300008801c3e00000c0040c0000e002d401d0313045c4045002011801500341d881c1120780d9000d02240280d000740201381c105000c1100110001880343d8004500180c150b4404540c4200c1c400c2d181c7c2c1c06078602c44a01014074001c13441c100454802e2005054140d50784003d1f207418041c044901003d00300c0c87c551300c00c07070100c09046a450b494220340020200500004d07250070b4114000ba080c110004d0807003080354001400c000341c94034011100d000726035001c0708443d5186a11000a2402e00e44024800260b0b51040100700c0403817110b1300100620490101201e40c41c0e0796800b40b5111140c0240100d0031402e00a11030b0814034100b150151600c1031000f80030016080d4140c0c180c07851a044640084005141200100040c0c1c2d000b0008413003081902d10141418a4582c507120b01c641b20f0505014901c07680080083c095840c0c400030fa690403e8018202607a07182e0303400c3d4102c0003002d540035103001800381 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 522299802 1250 522298552 522298561
    0x70f0e060f0d15020904020f030f0703050f1b0f0c030c010f0b030d090b0d0b0d050a2006120907050a08011b080112060b0319051e030307050d200a0207030b 68
    0xa2070408a0300750340702102c100f0703030342d082d0702c804010b034004001d06500035400f40440f10000d032440c8090340c401d001c00e40d03403101c45140842e0014141c600282180360721140b401e0038412a814401c1030581c1101154803010350300d081020703060816101d403c5c80003c0328000400d40080262042d04240c100c2e04112070b0500240250004041e21010804908008100c1030441048400500e20141500c00c10322080010800b0200021070086581905d00f2103482d00480c2420007084019960740d022000b10000d420003100c000000b1445500c11503001915042c2504000350300000b04102d540e001d002c003d021051019078034042d05001e040c0b0206600040070101801801061140205504a880b02a408a0100056143d8900070728000ba9075135003501071035560b046c440d010b0310000d0000c2840b070001001c0240d800720784030410400b0740b0b658980641003042840901a0322800b5215503007800c3c8000110701d41d00851400718805061029500000d0101e0302d604656004150340d022a40100c80b514a5640c5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 522301052 1250 522299802 522299809
    0x6030f10170d03090f0609050303040c0b03060907210e030a2c1905032415010f110f0a0309061b02060706020307030902150c0d031814070f0e060f 64
    0x100ea080c5a940ca9006056080482e0f100341c014040fa14002c88031002178001680340c0342d0984038010815112648000709010030410100c866000424483c80f00f01e0850230b0580006e803e0141c00303041c0d0410410610150203aa110030340c0c1c82c2503508090401000020303030070401507440b41c0003000f1940115010740d00390b1001401c11640c2c010303031816910170004401441010406a294000e1050040d0120440c0c0410103840030002445023044e003504490140030b15855150103580003e03e003000210348801d40c50805d0340c2140300e00a1a104e1400c188070741450040f0814640380726045205c0051140180038070034550014400415204540e41d40035080150380c02e48181218801c030000d4000c1400c018800218049a02950300400b4a09c1c021031807180b01d8000890010b00c08640c01149800005e04400400d000c1108264000440c181031100c44003071080244528084800500400c00300356601120349400e1121001500750004400c2c0071545030401a44070440c11594203010711400d2074001054603 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 522302158 1106 522301052 522301079
    0xe010b040608010b0108041502070807060c080f10090c090506030420040605010e1e18010f12120e040b031e06010b04080601090504020f06030f10 64
    0x24004000c000c00c0320031591200382968905a061140d90345c010300542c0e03000707411118000c05114030450404c082c2c031580c003000f0903c0c0c4000412038100007140e80240c6941e20590703512601a41e8404181e194040103a030640c451041200d400c01ca80e0b440f0340c010708040b030300c9071900c0e207480e6940d107000c1156600151421036856405142c080c0d441040d00f1000d408071501220f05004079403400740040c040310f44c828400d601039101e174040202d030071075502070022031a1809086943c0e20a200c42e00d140500e01d0a00509069440251000030600611241104100d82083c50640035000801054070010340c10310040d13801c0307511020303280c12907501480f1861064410428002c4032a281c940101d00303000b0140c00500305400b0501043c0b114510005005040d9038102e5400640d51311540002007810f41c22510040d44503400000b0884400b6a202801e4020a0f035040034044540d01d8030200440704 = true := by decide +kernel

theorem cover : BRFrame.Cov 522122302 522302158 := by
  have h0 := BRFrame.cov_init 522122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 522122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 522122302 ≤ n) (h2 : n < 522302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
