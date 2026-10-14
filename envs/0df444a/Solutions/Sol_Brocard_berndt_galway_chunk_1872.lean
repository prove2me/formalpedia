-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1872
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:58:49.784919+00:00
-- url     : https://prove2.me/submissions/ba8d3e9e-3af7-4eb9-a62c-a4fee866beeb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 336510791 ≤ n < 336690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 336512041 1250 336510791 336510847
    0x306030503030c0a180302060909100f0e091b0907121503140d170f07111f200409022805031e0f0109021804020c0f0f0609030f 56
    0x6820a1040c3c80c11650000182c038021500c03405101ca803074650201c121040702d07005058203181c06200e104110028800a0500300c018a0000d008a040c01c003c000c0c1001034508000c2c40462400c010444500e0f01c41c005001501c0c03060341c0c46904015444603a043c503000301c601d0030701c1c4242c2d850710394521001d488d200710640c007010503418000040c0000d0546440444824406071031a180701c6039030803201201d0605000009205d080c02081a1544454007150b0110280c585480c1d03a854031205281401d012080c210304c40b00501a040b4131030143c030300c10301d00480c1ca006603250110103036041d8040c4c90301580c030413050956800302d0020f944141012050090728a22a0b556003550074007940074009420940e01282d50b0300080402880c50700714074040901032400440100f4442c0c0c43c0c494618041c0d4000649212140c1c1c081c200200340d500c1d1400540003200c10007000c5c04030f0011003440c6520313155204511224aa101c0c0c802c0c05074129011084642450600c100269105d10329604e010060002200745813030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 336513291 1250 336512041 336512047
    0xa0e01090f1104091b05040501080303070e060714010207030c0605070504180b03010b09070f021b0f1210090b0f0708160e030703141b0a1508131b0312030606080708070306030503 78
    0x3103103860107417070060760300481e0100802d98079650010b5036030004481c260045034400d82d08507045d00d00140a8072440d4800c08103008880b2006280500703a0304003610860208085180010401c140c0d4010340750300052914005d414203280407a001c1c00b03080060000c803201c640d104088406030b01c1c290401c00c04008060280c0b1800e06241c01c00078032420740d1550100040c00358030030030702d01e03000a4481e10f640080014540725840008000704041c0303070116080078440d4401d1240703030841504640030b90340c0c405000c2d0308020781a1400c076070158280c0d207009102c1c0c01001070041c10000d04000340385000d9880407480c9014060100034001292404045800103440341c61814010460303c030300090070fa0f400000e19030f00c0303000f541041d200348007000e906030040b01100e038042004a00494407994240b0341c400b01403443e03011a100962511080d00d00028066840191071440074001c3c04060340700080c0220240c50200009403400c00c0c001d04500d0081d060706d0030032002401040d441c0e07109421500c003841c0c20206803a9 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 336514541 1250 336513291 336513323
    0x60d0e07031b0515031603060801050c12152b210e0904020619270f0f0e0106030f0e0d030b130e03030a090203030705150a0e01090f110409 61
    0x18084000440000450140703030b0001c151814001c02c0626100c4008030b80318115104c5500070340400b0035010403d07003010741e0f4038400144030209016880c024075101d00d0003562101011b03084070790030200810b540200c110b091a04450340d2102c4400390840c81c80410307200b455109121042200841441f07010b09004072048250a0711a1410002d198000d032a4555103803403410f640610808603801c4602a51100041c40300304c45c43d00c500300704450001e4444c07038190000252681054018803141156940ca60301460f010700c001042d840540c1d010b00585c0d890a104646070210906150724140241130405459014503403c41060742c12040084402005480c102452081c00034003c16000501714840c0400d40c00040040741c0c0c078421b10148000080141d0700d03650380e00c0c011502808418038126010b100420925001c40e0081c840c8107001c86a0030310705011401e01125840903946101c403101803603403400f40602c00003000100c6416445500110b134000321120900040c00a201e0042c0150606280b501c00f15 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 336515791 1250 336514541 336514553
    0x2030307200a150804140111030f04050f0a0f031407060e060919030801170312010303030c0801142805061602030f03030603151306060b0a0923060d0e0703 68
    0x3041c41d4206441c0e01041a540b5042d03841a00954180200494902c20205000c25003501070000d202c01c0d00030001c240208203c440484d0341c1c0c01181d440310b411080c0424881001014480d0a464819500c010004240701d910303540c0b40c0c60203000c40102480101854802e5a09003030382965012508000200094001280c10b1070310361004031074440a6000d0700b10070088500c08a444d207041681c1582d00d41c41c140c0e0a210b1107910100c88a584c181340c0e480240140c005141003442594041d611998001c200c1d082100310281540106820001000401b62030500003501c2d444044400200344162204100701d014a000780700110641000f0b0304410002403004c50240c056010b016107505c280c007240c0809420a240d00e489020071780c1c905a0507040701420b10040210351100a03046803045500903111201907840c003081f1a880d46c4191507510780401c900e41256000b10083c03009002e2045480c0740c0c490703e44403540c40c10f4543c1548620030400490221300c045031540c0f00c0400c6881c200104c6c0c0640ba1282495 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 336517041 1250 336515791 336515843
    0x307200a1103011e0b030109050102070f03020f0a12051b240c1305010804080d06060801061214010902070f0210020303190c08060103021b0d080a15050d06020702030307 74
    0x161498000c1a0718400d1504051141d03d034a00c10342e0007220040124022070401400290314190360564031082080d010600030300c001d050192082c9220b8000c003610b854043d003421002445402507421450b0080c01250f9074021442000202d490f080307969000070300c000c040f03052036031411660714424201d00c814000b440c2c41010305440e203030a034480b025594408032140c0c03502c90b180110318003060700c090070003a079406900e641750040e1003481600e0400c0c0c82011a00102e1b05250312010024541c40300420a02e500030001004464005006200340d070044000f80440b0b50707043c42620f40d1242e0004d8184140038040c0b08003508e0b140d00601c402d811000c03e8200a41d0382d0015104020820b0020b18150001d100600c035202c003d5000e03490340400741c0d8604006400a4019103019040c0c82060100c106d00e0f0141400004200302d8203880301d1003141404020340341210203012200100c5003160310300384020368904d80c94140907035010201682d652540d00c042801c60040380401807801c00a07000b80c4208004c2107480e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 336518291 1250 336517041 336517043
    0x3030305180303011a071713030309060516020906011101090809150a020703030c03140c061603060509011e08061008160510270b1305030706050f0307200a 68
    0x2200710566810a00a40c0b41d100030310440003821300f0710101e201c004074070b1382c00b500c446030007210040415010050007a915074045204e04400c540c144d0024030405800c440c51a000d40715500d4840c0c14031884003100d800c815803010010340724800d0940014810f0f8483c29004448600d40c000074172100f0103a00d0020215002003601c544034014001d0002c2480c103294045d110038240d2680104402c0e032031500e0540da540742807041502000790140400001000c501c000f072480c4000b0000502051403c192207070804a0008441800c05003480c4d4100119540c6801e103078192810004e400c0c2509940a40214480c022a0f102181c00d000711400c201a00c01c1e81d410440488400c40d00b80c4800c181040c000d9103921026014030741d03000c10882084c11550703100313041c0c0703c0e10743c43c43c002c150700350154443c00c54150301c04980c44001c0021000860618941d00c0c0d0740400000d003402e4008107001800d08601800d203000b11a4514244800800020304044c03194100581c0840342200800030766501c42105070700c0d401c007610 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 336519541 1250 336518291 336518311
    0xf1801030506090613030e1c080a03110405130f1d1615120203040201112e020a0807050307020304050a14040e0705011413030501140405070906300b0103030305 70
    0x104040c3c00400e000b8820b1402200d00d20351849182d070143d80780a01348455540088840301d85210344400000c1c1440014041d03000181c9a1920810003030075200d080300741601120702808100007a8540e540044107440c200c40d070101340000300103d902c009292110a165440152034007446401c0303404036504225602c81040c5800d5203890b180e0900b0880035040300f11002034000700c12044030240303590245402070700c14540510361400d940c01d640c0c50180601c018415031a10b914641d1410701d00340d5000c4002d84040502541003412158002e02030010042856050000c00170000300e00504c20310072034010340350040c0f07040409900c40914000200845444500587c60020607007107034480090580d088901c140d45802d4402612009001d50350012010403070450b010410110019a082c0110705410640400c401c0c4a4503003420b10030702c1c14030f50b0b911011400d450504188840c2820034104078041801c0c5507441800220040711503000f40c035000018004d89603440008c000c06d60325421060044000390 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 336520791 1250 336519541 336519553
    0x307050a091122051503070203070605040317010603060f06020c150702120307060f0c0203032806090e01020d18030e0904080f0a08040201080907050109050925020d0909091109060f18010305 83
    0x74031505d01900c810b5801c10050303481400000c001840503004103910a1180c5408002844c41c03c1040c860444c003a00480c010070b444140030b0004002c1611100b009200d00e200034090415840301061075400a10040c002c0508001040429502d894140248105061084969500050400500800100c03551400c060304110350002900c2c0300000b980d0013445001c00b1444c108100d40140401700c07500d2450400c03141d40354030001030301144511640b41e484517905c002690792107503484080100d0782c0c64915100c0d00c00340809440701280d40802c0c140283c14054072070700425150383c200450b25000300e0b40040045400024148802d641c400d882c50b002d83e01c00e0704d651041e030702c44400d40da88401c07503402038a0003d18580d404008919141c04507a800010340c41110141088800d80ca0b4207000c09200500c0c0580d12400807100e080e40d0000c502c9000b1309130700d01c0030032030f100d4590303106001682d0780d500d41440b0f103c4520101c0d003280d403100107201100c43c009110301048892014141200c07502440250303050301503a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 336522041 1250 336520791 336520819
    0xa060b07080a0f080114130f020c06010302180f0705030709030b0705181c060f0b04050c0a08090c1005090f06030711012a080a0e16080c0307050a09112205 68
    0x80328000d040c1c1b450300c4008218400c03450103005502030314841400a064480020b81103020140c4014030b0ba0307200321005031003150304500502c0004600c0c0041290410104005c015108400d00b04054001c0c05514015603a074890785c0c001c46030000b1759007025000c6045031051007100d542010090000c882480403542094511310200f01100c1ca0310080c603000c00c0f100f00b82190001d020380d80034240ba100110070006500ac40403012030100c40b02101d08412541000403429040d40d000f0000c103070b202031180010814005a6000304140c90b00c6010b0100c1031144c085203000440d80c55402484580401030310032038481c0741c250300c02455800c50161040702c651074025007010342c0c8682034038000203400702d0901c2020341501070803c4960010046c405800d030f60381c949400e200303980184205090702c41c45800060071141041c0c061400c4c114a0101640300c4c3e440810204019194600350100b00d42002e54006011038603080702905502c200c0d040310700078901800710f40300e0841041448400f03803502502c0c034441e10384007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 336523291 1250 336522041 336522047
    0xf0f0709080102390c04020703090801050705030106020f06060a060806130c050d0608030c0601050f271801090203060a1e06080102071106030c0403060c2d02060c04030201170a060b07080a0f 83
    0x200780c884c403800e40c03c40c0c05040442c0c20710f90000c15105d0310a1400c1c02d10302d6a64400a03007111415070728000021000001002050381c1040f900302d1790802c0ca03000d4107582c2000800240a440d0074400c20301405554400a4803e070785103054030010b0b100c0c070b02041c00603810409006200368040303858407002510341800840c80020002c15a004070f40c0c05002840d650342814200f0900303c0c1f901000d01d51015903541c80c030507504d00b084100c1420314840d940c101814101100000c0500c565442e4000ca1a8902500d030b40250341d000940a0b0000c1252400088401140404410301c1140c031b0140407403141452400610401c0540c003d11640c0e024011a906030141c1c407080001c2172009803036408204000f8042403001c0307400c1c0e41c400300740c410030780c207142007a4000b008601b0b15042050402c409500c203911001c40340907070103005a0341d10840c981c1d18645403505507400030b0320407074658602d007500b59203030340011b55a8540c0f40d0003e0b018101c07844120781c0b0f4125518141c0e150742d0106103101c0020703048241080b00180 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 336524541 1250 336523291 336523387
    0xf040b0c0f04090b060705070906030317130f0326060306010e1b0c01060f0b030a06060306050102030f030a06080a12140a1209030e04110c01140f0f0709080102 70
    0x101041095103082d140c00c2c6450040c04100d10b03d945d001c001041103000040080202100034900c2c40d8000c2511865401e000d480c85205d42004004501c070502006403400c103180c3c0360003425030b0041c40010b40303003210b00301194610408084403900b10111080707000003510400e40710340308220031001c0798056a25640e6040d20a00d09a51341b000082c05a02c104c040030740d10fa000381621111550000070b8a0b940c802d070309480146a50711400f40301500109022134000c1501941d0060401070a0601800b46041c000075624801c0c500d441c5c0b51a040070012a005501e2074004400400c080c1c4100c408103c6c86040ca0304542070111003220206000070141c00100c140c0c0e2043d04c40c2000240c8469040003441c060300c001600103644110304014400c81022041d946a200b0030401411185001e915100403180c3c01c1d00b141c116010600799942003004014901802c1907030164082d0022204500e0b68843e030710192841030564004441c41d50001c15444182d41d0000d1103940f039440c10400e000e1403400c103d10184403000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 336525791 1250 336524541 336524557
    0x60e070b1e040303140307020a15020a1106090303060f040908040608092e0507020c0901060905030c0a0b030c0c0312090a060b190b090303091804060b120d0c0204020f030f040b0c 78
    0x8011110900500074410099540710f1494010327038082c4065a07036012540d12402c401401c0180c2e010a082034800e42c4141200d036513800c02c400510703940c10a005a03176901d010082c105803240000a0850040391034035007045200700d03030125030152950744a010180804400b00c034102040c0c40303051041d40346926080300300140c45421003001042c0d500d0131407201c07000e020020525010b511a4000020054844c0b1aa280c024040d66840540b80e5051004140c14501601f0410748208808141402002e680c44112608100c03510f40f4159202c90f60203026042d0701883c404101c80074a4542000712807000814403a496502c0b40e202080350314280000c00c440100120144642d684211074144858083c940081140f07280c010b0480c0e08110740354001403012a445035101c00c2c0407400740180001c212041c02206081c0b001103905c070140300c84600140740c0c0c800c0ba00210328200903220710254195103036603045440440503140040c1d5285014102400344410030b842c200e0b1408200c1c000a4000c00781c81069512075 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 336527041 1250 336525791 336525797
    0x605011713230a0b0f09161418010b0913020c0c0d1e061d010b060f090a090e0a0c1e0e0907050316152604060e070b1e040303 55
    0x46040d5222002d20840b001038003660880c089100b8101d0000c20030510200620500314034a40b0b1420380c02e0035050540282003070041d030740481212812840d0700d00c0d50000b41d03040710600e0329850b80d0040025202042c03441e58610f6052681c3c0010848130b203100300a2000120544030f100c065008041144100e10075900010100d40001000e83e00c18605600702d42081c600a001c882540d0420407100140041d501c1d100703c68855030781032030300280d00440b104192941c013140020440d80e03000780081500c51042c00a10b80903038400042c251003030b9907105101800f4011b03e042c2040b0000c0c06e10580c580d103a00541e8241d03941030b1959400920f080d000c091861811003d444104030240c5010401d00c035590003d00a48028002e104000c0f41c662400c015601c07924800e00c9412840c90305c3e115180c210540c0c0c0200000802107402a44418480c10400d024000e40041915450555890400310024560500036080d640160400007682c00c02c1c22001c3c00d40300c0c81c000440b058403048070310340369081d109900c4000c2c08 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 336528291 1250 336527041 336527071
    0x60a150608150a03060c020309031b03030304020d1e0c08010e01200c0102090d062003090703080a210b040f05010315020f0d05070c0b010b2a1005090106050117 70
    0x2110400b451201d0728600c00380502d00e01e9601c0b6600c5005403a10742a0300300060740081910710303261030200442c85500c06100b1820b16030300700060200b0317101d200090000c0d0240c7c07103520b0320000700900c190100000041d1004002d002c0666440c2c540c603594503620601f400d030360030540304c186100030610407c4041100c07035a000003c46941c160a110301d0f0803c4110b5040c55600b4420390f00076454222805481724416140014400c2501d10000800141101e440040e20b400b40100404001c0026808060f00e0308544c02580b922800302080b2803440481008588a01c000f48102c2a90b07600c580002a842904036401e01100c02c83c0380004040750303400d10026110111008030404041d2044d8000c01503520b505120390f181100c80000c102c140c3c1c0068903148002039110a5075000e10001059250150040400d600c0c0343c1000c0c003982c0011220200b002c1ca08031143c001c8030390004802000b510240d400001c00c00d11903460600d4440e8000c01143c45002c0c00f09100803108003980f0f0150000c1446080b044c441c01368 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 336529541 1250 336528291 336528301
    0xa021e15070e030d120e0303181c020606131d0d09060c030219110a080a061103070e0103110d09030206010509070207061e140d1a0a150507020402120702060a150608 72
    0x402e07070403000c0d003020f80c142d0707408201046d06828001503208207802e00c1b90414169034550707075500d420010a00c142032400125094801254003055158222001301d901c14540710160003c00002c2021181112440c41e00315880e800d00080400d003000300304000c0ccc0710b40b0314030baa0b920340aa54862540e0b0000300141c011918141c0400641d190078580c41c1e0280304800c0e070350103001c0085a0702c02e01940114405a0001112104110113806520a50004502d000381541083c18000c3c210288c1200a1414141c4464014401000314815104440804030042c0000ca00c5820702035100c031028060346000740b50b034900251865000051450803614180e0703407038040381e56500304000c84800b014000002c0081000c0d10180701b0f01040054280d6404000002429000e14542681100840150f40d0f004540408041144e01458940402c0c4120b203420a260740711460b1000800034030a102c3c0d02400b03103144000b07025005030b001800a20a1200100407c0f00700b04103010703803c000001e0701c40d80000a1170000065 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 336530791 1250 336529541 336529547
    0x6210602031902070807060b0604050604090e0a1205070201090e131b1a09092a0c03121018090503181201060605090f090105030c01050a021e15070e030d 67
    0x15511032088008070314040344500949007681d0000341300f51034441d400b00d40c44d801e0003220302c100038441d802245c016107417603d07010214001d400740303100b1080626a2800720b15240380301405402d10302d0781c0c0007004515a004807400948581c02110042e400101404804501c11100d60602d0740148400005680300915a642c1c504003800d0b00094111140415100000c103052044640d400000702d02e5400c580740c06100043c030000034801010044440d84944000b400b070b2102c00d8102c083c03030f1000903206aa036040349400038a544100f0700b0382001114400100640c000d140100e2100350f9640043c448003108c441e81030f600c250786a000001d0410340040151107541400b80c014080c01c00400ba1608101c011801080360031112284d01c103c000c1940016038203d0740c07130301680e4014041d10880d06040e09504180120303a480100e0008507040c403500041c00a1054000c01202c04100d00d0311040094200125801944030205810055040c4640101003106140115001c210744030014004082050705040d0407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 336532041 1250 336530791 336530797
    0x150a0f0506091f0f120b0f190b01050f0c0f0c0d0506150112021801030b030d0212071110020708011a0f0d020105192f0307080f04050d0f03020106210602 67
    0x114020040560000343c4c5001c408500c00080c80d03120070300f0003000c0150a181c0d14078440240040071140ea080c08020162158035081d03500f90440000000c2c170300c038001c001620b5512a403000644001c0c004075810b080c202d00025200150405681543c031141d402e001800ba0098032403038010a560000c80010301c2032800c02c0411007a00405140055241c80d5041c24041281e004401c54201c08034500344148542d60180154500250280c00500103400c4440009481d00d0261342c0c80940460002407100c240100342c180d01805500081c0440c1182c4045c4102a61381c1c0e00d10b10170622254240310380c600c455920b42400e0720b80180c01400311040c03082a2005c202418440b640c08a0501c102480186200c59001000c1c03040d070440e98403944600380020386050030211086c0302c000300540d0481d0f0210312140000c400c0c2c8030803550015500c0d80f903101d121007100960046801240e0400c1000e06100280007110201002642c0240c0080105540303070440140041c001c90b5560b03505205860014001806e01d0b802 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 336533291 1250 336532041 336532081
    0x3140a05060303090405040506060916050f03060a03061103010f060507210c060c0f0809030a051903020904090b1807030507050105070809030105070207050117160c03030b03150a0f050609 82
    0xf5280b800080300300090032200103903070030390300344e401602000132034144002d0044d0042e190000d114101c000042004103544942c01c40700205920220202d49a80c03110282c84000c2c65100c0002d00c010482c12000b6070480d04244039060428034001800a0300310f0085045070385d4240c000d840c058008460035204920281e00c0100102000360400880780854464441e6111062007580e82406070f842e001c10041503e40090514002130300100416003019400000b200c5c0d1503682d25030300e02805001d0030410340c0203025410109400508100d54038081000b01c42195110f4003200a00300340c4000c000b900c0e20b990740c00e1340c0001840c40c0e004410510240d80268007503d02c0c1442928014070784400440403d094410030b03203241380582c1c0304040a00c00c0c0e40e00302c07101e02d80415800c5c45000c00d03071400031800c02465400354420340902021540b0041414807a406c0a1030740c180c003a0807100c00030129050300005000c202e82d180546440d0040380c489445441c041e1500604000b004901e09484030044031112509840c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 336534541 1250 336533291 336533293
    0x181302131202240d0504080a03111309050403110f0129010903150e0102040f081903080103030f17240621090a0c03030804030e0109290c010612020a0603140a050603 72
    0x10013030840002501400740b04034402c2141c41e845006609000e01954645003103221182410b1220341015807030604010300711a441500840e41e911035003000c0d10030401185514069002d10103401c0c000c00f4054000c00da00e004044250031907881400d000d911a0303450b0035110b40c00511864800c10126141090b801d0209a0000001640c200c0342081e89089a20642c007808182044200810046c0c0050110071a061f0148420742e24040e0346507801000240140002424841710242102d0154031600d02007021000401c0150b07241d0401c00c0f080220104d415800343c034501800040b642043c10708a05a8002c040e410702c8098503824892081c1000c800002c214542921542544202152429440034004c4d4000c1c2c9490401e42001d0030020401007044a24a061010508040000c014641628146440c0c0060150200307006290a51300307510500082400a40c02c16001242d4a4404881c054807076100300d4000b0a11b6549240640a8034a080551001440c68500040360350384583c2040780c0c07102000b8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 336535791 1250 336534541 336534547
    0x2010206161b0506150a120f03030b0604061107060f0203160f050d050a030b0402040302060405060702010e03010e0c0a090e0a030c0609020d03080604140609060618130213120224 78
    0x1204650268140715000e460550002d070501440e5400420340d030308070600554002c0300082c249890034a00c0206104000c1069041d220348e4000d0610075882040e0012000340803a5546030355030300c0102070103450b070b02c0100d01e802a40d10000d0814010b103040780c41d10400d82c0144d42041210310f00d054440124040550b1686030b501c10180003d12306000e070707002e807090755103400340c6800400e4001411118903403012409244100800d03c056502d03102590105c0700104d40040e501d100c0b80c40122407401c41e041c049a055130038001002c1281c100444e0002c040ca209440c8400c105641e90606000c0d5000c0f09007603070b120b130844503400e408284030b040512003050190300d0201d01190300d0b5010900b2200c08400c2a000142c400c1d062000e0b42c9402c0c0207600f2600d24415200c012401c1c8032000800080c0c000c0c06044c411030300059014103180c01c5c80006800750000528800758043c00c002004042c1d4404100d00c14114128071001c0388074114100e607006416000740c00700074220b02e81c2c90030029240501e94890b090785418 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 336537041 1250 336535791 336535817
    0x2712070501140f0c070e0702010b031002091801300c060813050f03030709060c0209070e1801080a03171b0d060b180f01090501080a020d06120c030b01120201020616 72
    0xf0401400780751000c00080480503d84280d5410504025100e08116410410800e2403a580000c00404001e0030b041c0043e95030b002000002c580000130801049604511000001c1c0104041e10300303050902c2c841c60400d0211440ca9080c0112414078070000c0c2400c10300d0750207010b640c0c82a0480c0d0b900500314a54069588199203801c0c0c50706007000032100e1694000820480b42591009200c0020111400c0000b4003c215900290342e41c80000e10902c200180c0c02121141c90369a50744001750044004081d0b801961100301003521019904015804101d00e44100b00300c0c000e0030f424551040303a81400d45a004880102d170285252b100000c15103015440302c074041000340c0320100030046610040081111240f142c4103210301002401075a50512108003c2005a80d800421041d0300c59014280141d40714600340b412070042c030041d040110011901c001500810480c40d046ca0140d03030250100e00003981c0c0e07c41c1754401c41c2d070507070380002e005030007003c08502605540c00d0a03a0002c401414000c0c024508 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 336538291 1250 336537041 336537067
    0x240e040503070507090501150c080d0504020402040b07030201020d0501050306041a040f0209131a062101060803071505010509041709030a0b13060b040c270902271207050114 76
    0x780f070300305d07242059030307000100030454190503141d99464080c10300004000c3d054403112010301958910144044d04c0b040041c2c215070740ea038110350181c42c00400e401c0d11450705e0305009000303411030307150042c0013850000007094502c0c00003145449181d200351f02398030b1400941d03103e02480704050000c4a403d00d0340403800c001683c0d040c02c918132034070220550745c40b4104179040c03a04040320354400e41c240c1c00030040d00348903a0b500d03200c6816800010004001509002c0300340d03010f00400c0c82c2e40c4041790502012074440104001440c4c4030407000314080052200c0d903218010003850b010162001000440b071003481501c41403011b070283c05e07078803030003804c1c1c030040708041e260041c0404045a44423211b5a100150008000c00c0f03100e00f07008400c046d5403c00110000050250014010042e10011441d1080c0c00401c0f0b005414001d0028082c4640f040d52141601220f02a66011102c600c0b000349000c004440081d00701001d030304410003121001082054a0240103603031044e00850071020200c02007243c0180104 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 336539541 1250 336538291 336538303
    0x90a0f0e1609030b07171e280501140a08010506060306010c150c050c0f01050c12100902220e06130f0b03010e0c150c0706030c0e10020a0501240e0405030705 69
    0x45d51104210b06194520084c403010008058421311841042110000c40500308170030b60100304550000348103407003010320141145000e030842d0300720750a10001040d0f001c0c0d00320003604184025680402080e4a96403403e090b0340c0c00700d50040e00038806000103110341d84500e80c0c0e4000780c0d000c1c5541000f101c140311100701c1680e004032130701d0380070480003e00c0c444c0c3c02d80f04114540c94001802e00030803943c1003581c01e0307500c0e511440498090540d01c5202041d0482e1604002c0c2000348014117085650310602e281180030b4421021a114040242820008280300602c060a10508008141c2907071001751401d49802061580181d0801d03913030300e207810016903c00344103268504a102d0014114480ca01c3c0c20454204000192514840380a025000c600e0f8400a40e071070a85c4c80178100400c07003580b035074000c960000c0c1c4441b2540c2e100b0313840000d200c525600412107081c610f015030024083d020035440d0752804034000042080f04900f419104000d041c1408042e650400d1050090302d242c45103036243c95107021 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 336540791 1250 336539541 336539551
    0x5060a0b030405010b01180608010306020903070824070801050916050904110c10060501020312060d021305070206070f0203300115090626070e1302090a0f0e1609030b 73
    0xa9514091401c0035a0082040351f18020089088460b00341011402000f00c401031000407c03040d000700f103594050790203001c0c88000d0021030085801c0100c0c008406c0c901801c1210044403104040c90100700c8541c40f5014040c140c0d00040c140a803e5100c4003421aa1540040d0340380c010030a041c003401c0201e99881c001d0b00d60340940705284030b40300c1c01001010350402044400301002c0d1807511800300010f0360080181c410714074450b1400c00c999521080850403014030000700a500108181d881c803080c1a5a901460040400e5421a541652620010390781500d4202c4e038080585d10510007000b896070002013a50720130882660151902d0312803625000040000c0c0c105e01c1488052416a602a40d44000c22100505091030200380b18107540c00c41d00c101000240c1a04500c1c00a0740014403c64001c0b049a01118006000c401c4d00c0c56004c0380b494002d401024882d032291106800008803440e00c150040b05450304440f5543c5181c0b0b500c4004000300c01d4010503241441043d500c0000491403009581e8492 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 336542041 1250 336540791 336540793
    0x1e0516050102011b0c02011b050d0804060b0108062202120703140c0412080f0714010204050423150d0f0302010902010f05130e091006080c030d0f020c0405060a0b030405 74
    0x1581003000280c00c1d15001c81450320b0010305030080e40f03251139000a00600f4260282045204403101003228092101040005040c512882e0300100800741e02c02a013911483c0256010080c06801c1c00044561440540b280742c1d0190820440e8408800d1051b400c8a80a0700000014a054520348180c1c030703000f0080704c104010036920581c05c103040030300b40c40c3c03217600c46a1005441c1ca40ba0900852000403e000c010150100710042407580958136030004440074540c00001054101a04040316030203980203000d03981c01941082400c4030b050f40c100c2038660484802c40c0071048180d40302110103a03555546161b480c0d10880c603070307000000306070400402c039085030181c1e00110711055071f40005462040400007410800c0001c001c2d64920700d4050001101750740002c2d50200d444c0c1c544503100b81c03400c00d4003001c144551f460f00710000341d03c882c0040c080d202c0e0350b03080e015103001c00c041d02c0040d100440d03d901c0b1390300541c0181f124070b15146016071055901c000000c0585501548803075200c0f07030a4200320703022034807 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 336543291 1250 336542041 336542083
    0x509030a11120a050a11011e1d060408030402010c0213020a092304090302070b0d05040b0c0f030112020307270f11040b07020609100c03180609031e05 66
    0x54640d0024000003a4008400180b000e0b1081c2100140144101e5818800b0050003040d06035900e4451804900c070740109000901c04000c0c41d01d031145074003940001c440039041c44d10340f9022900b049648001e08400710040030f0306c000d0303440b44ca5030388082c4d20080c4101c0c100012080b5482c0180d0300c800300c07800540d07140b440058031100002009005040607030091070300e4080e01010088480c0c88206030f61001801540c0c00700b00c176a000d15090340340c80000d40048080384008551003400106903849a071140f4041e04040d10980c941e011031181c6489480c0030000100000c1005000524841d01442c0d9040d01c003030202ca4a6507601c2c81060031641e6030ba59212800d0441265105084629002c4c6504268028900300503940706500740e010107101e103200d0054007500c04111321055546501c141ea0502d02c0207401350749808480040100b014080034000c40210300105034202644800c9030aa40035131f88907440310540039045440d1000c40050100d0b0551124070040d184900040c403e1050840d0103814020400c0c07 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 336544541 1250 336543291 336543307
    0x403060606020307110d0809010c1b09020a0e040212060603091002070b01031a06060415020f0a1a01060e0d0609150c0e0109080a0b0622050c0a17070927050903 70
    0xb0042c45c0c9030660a10445400003c0c001040002d82260703d441402d090031024008240780c000b061800504a4040030021100005070040440e001400c40d01c460382e680341624400b0204210423401006401e140c1c02021f50001005402d0110082d0b804c190160100c0c0d2000074015180000d0ba0721071101200d104199200400c10171800c2401c04038003810895070703a0b40514140d1301082060099111380c01e1071503141d0700700501050090144020114192040e0b800000d00390406020b038240080f1003da002d800000000b500c03a1090402c4224010010203071401802581c13221400341105600c00d940da0000c44054140780301646c4150010003489440ea0444800104005000301c4d00e01c0c2c0c46082d45400145915000891030301d006540b2230030450344599001810208248221040c61001a0091510703003401140c450703480207001161a50760700d40c00d154030035500c2c0440c0810140d90f00c03c04035803092000d000008841700d4004202110000e240519903171210204141c44003507071416110b410004103c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 336545791 1250 336544541 336544553
    0x70f0e060916180302030316052503020904060b04051008060612250b120f010b0403031b14030403200406060c030f02071706160306080d080c0403060606020307 70
    0x166028000721440100392501a5010714108400021441084400154503a483c1c285099900145401408490315086081d451100c0070140c6030f000e41d4188a81c0104071400552521900041d00e078203030500e03002c0741c030f503600b80040350304040d00483c1c400e515100040c086440e58400c0c1841080d0602da003450302490704254509009000e4019400303030407a400b107660034503400680c80c40c0b8842101419095440a034040d261540219000041443c4002540c0441c0d10703000703544540615100d541d03c50145c4d0341c540d1011030038401c41c8801004104400c03003010030240c00140e03241806000c2c1034a070003c1426100352500b1503120790801c4402c04441060410b154030f0b91500710b441618103072002c015440c00c0807000341c00b0810075030b801000c004401c0d02d40e03500e2a200380040002080f503910003443c800040c0c4a66070325000115041012000b48289103480743d441b9000e88400c40d01030501030807080940c180100e40c090b03030041c41c400461008110000c0000c0389881103100420665020350b4586c00640703454 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 336547041 1250 336545791 336545819
    0x72301020d0b06031e0402040204050301090b1b04033201060b040e0c07110d03020102071a250801051509030303010f06090b0304110909011b2001110301091d070f 71
    0xb18007925081c02046945a5038240749070001019580021641e5030b00e10025010b4400e80e0007030b6400d9428015490100858855094002c200115044941110044091545000d1840007800c4a65a01c00c070f405620f240502c4680703184000f0709404029980c185240d030a450a1782c0c07000b440c06000003010007032560b030b40010a0f04001c1751014240b420001e03803202d580c1d020029400714428100b00307615004242c001d504486440380d109000140e1141c440707100c00c039803200484181ca0445900400d900c591071854441c0a808034940d104c072552a420013003400001400751840c0740031440c04200304a40c0d60b5040000c3d40c002c09126245c54040c909000000303081000540c016412513400740144000110600803106400101f61410181c030713540c45105501400c00001e8036201e8154a40c03661404941c410325100c6103800f0803e160440d0000f40c0f4a13030f4200d541d000c0e4181c1003083c04fc00180080c0384d454010f04401d0118051001130900e4040c80035041064580c828110010940010004035920b1040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 336548291 1250 336547041 336547061
    0x14100327050d11070b0d05280c030c03180b13080f0a020c0105070503221203020c10091d100f06050c010605040902031504171b0601140d08072301020d 66
    0x2400c2134610b400c2d982510343c0180c8185044868442c00019845180c04c03602004410500454900d507202c43e4480d100103229000c4030f503000904120381c035213200b0f01a0040040060405401000004040d01e5000f5080f60103000320102c80c100a00303140105071520702a1180211502c981a611080c106029251058602250781800f10038400b41020130004415503060400c1445209446200300d1728601a40c0f915820141031144001c068105060b800030b0841429601a207040d540400c540c030054440500c01d01c20051802c00b014100410304c40f80c00001d541080100d12010130f05a115a4144248850b5030424000a0008624041c81f000240514001000c2c20b1300c003040441e040d5000300341c40c0d8040d82d40d503400709001e210201d000c0007495000c07440440a40360300a078440d440a041c03a08215040c000300cbd0105d1280d9400841c164100d0074000070100e800615890390b1142503510341c3c0d082c1d0800c00c01610110500c40301e032800000715640c6400c10300403032400144e41c4d0280c40e214100312175483e06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 336549541 1250 336548291 336548293
    0x101e080103080a051e04081006090b10050904090209040f0c06081e060d060221010e07020a0b0c130609171606120b031002030103050714100327050d11 66
    0x20041001c140482c007160480303400d03841c04666407030500d9050160f9454410098104000000300000e05001c04190701c12003211200313003844100e90b2401c0d14010b5400b0140d40b280e020001c1001829000e024000900c012000640042014807080d00060310b9a00205d4007a00c4180001c041e41c8200450041c501000d03050310308004d151400e1810040d034417000c023110f145480380825008030740e0682c0d658001c40c03140ca5100c10155941d03186905140d500b5640300cc0640b005122240001ca00b5070099508648581d140c2d500500000025484040c5001c1d4050003000c8034007000c00c0800858014103c0110213008e964941c4a806440e281c65004c0000340301d102076803250000d2203190011603400540d00200d0b030703040c542250743c031070b442160710007c10a0b8182c2c0c0e0303810301c5044e04002d85803e298001e58101ca01500580300001d80e204500241060040e482590040307524610400150003a401030007514441521402400b40780142020f031040501303001e958a902c00031824058070342c071180455041c07905c40 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 336550791 1250 336549541 336549557
    0x32d07050616030911010c020117010b0903240a0504021c060506120109020f0909010f0204080607090b07030503060919020d09020906120303181c090303080106030b09040210050405101e 81
    0x5100c3c0a0b11500417602c060401a003903090405680c8a1006818551004c001ca00015650342d20300104035408030446500030b0180015581c424003e05000d1f40e030000c071000d1404071907510b0840110080c10700034003c0742c2c00444c02c40e80d1041444241c3d05502c405118400020319401c000c1c3c04c0010750144403a034820b807a03040c284c0c0300c40181c5404044149142c8286c4031900c20f134480d40d40c19800f503c250308007000002d2000c54002020b002c0081c11034051903c6480341d40255859000700d80312485045d0000d4081a010030106240d820703c1c0b18103036407003030744801140040d034040e1049000341c4c1e1000c0480d4101985900401d410f611703010034542d4100c0811a441843d05a50090390b940701d0100411943d902c074000346880c030902000f4404c41203407184841011416801d02d844c090101000e0780030550008542030008100381d402807107506c001c4603006012050b26900e543c02c120480c0040500001044011321001a2544982d0155042d41020743c55014041c807980310140c040c81030500e40ea0040111403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 336552041 1250 336550791 336550793
    0x110324060f091603050406020f0c1b040504030212030403090f03060b15041202040209030a0b070f0807030204060c12020a0602030c04080f0d05030613110f07050105060111032d070506160309 83
    0x1000036424404484c10b01040c2641d45042c6030000b401206050800f501c000034401c131401d000410198104000d820864100081d401c042c80100c50003200c0083c0540e010000d05a40d17048190302442d40305100340307082050305172519003145107400d0741d5101300ca40c1501c3d070401000c2031510030840e400c160a60311000d82081c3c070300707400641000e816800c064013503a1b0004000f10992010311860300300641000012983d0308000800074400520b80c0792550000c2e40c55070100784007521a000702d0b401c4500c01e96408145003816126060a100010982820740c841c0c03216240000701e1a0025512881070072000540b10352400b0703041406c1c2101c0c0c0d048500c06411070703002882002d801c101940c3e0460010340d07000340c4481c9101c3c0c0800003800701803400381d181d00c400720f840d4480344401030050400b6445500203001e51f13194040151800c28000100d13801f1500284044590a0b102620500d005252580b0a1004401d01511041c441d841100c0c140c80342d402050411010444100704e80e40c1036036141c9004c11000c045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 336553291 1250 336552041 336552061
    0x10c0e01080a1a090906060102120304050705011b0605090c040b04051b090303070b0a05060103140405060408030702070b22060504031104020d0f051005010f0f020a110324060f09 78
    0xb8480700d0382e259102c2c0c80e42c0c00501000009201404090848841d50405051603640c44c54100c820500522a0070104940702c400c0e6025207020380c0d40007008024a034180740042d00d0903c080788100010340300807031006010070402d015141c0a041c1901c050070000303504200b8003054030740c1134441070302030781c00c100034000300000c04084071f00108022401551a038001c68000f03401e40c03149000140042c41003c0600102009640c0079038040d8400b41c07410402001c81c00d4400000140446001c0c005400101c001000f050101008545c409114410340743c40c5a00c4030440402500440301c07880d500c140c0344040030288410646c07603034058007903801d1a40c145442c5030740c1c9510003c3d01d907100f01e000c0d03600441c1a904c24038160b0456850500043d03401d100610f0068056901560f0500c9100e000610044490015502070310340001c1c5002e01b80e01402c0070b0a02d5450704460b0751818030001da018440c03519284140b000c040e00540001d540041501c0e480d0500104202d011041032100c01d21501c01e4005110300044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 336554541 1250 336553291 336553307
    0x30b01140604080604030201020901030f05010506092211030415060b0d0b0a0f090912050306100c17070b0a060b0a050a12060e3306030402012d050c010c0e01 69
    0x84040018000c0156940481c05901441d404042d86110740010300c0105a01034002d8034401d0001c1e40c04000ca02c070b118030302c80240d8400380724040c1c024000300121401c1c0e0400c0200520580d01407004034492000901036072007151070034440d00806130408000e01007000b0030700078a0112110003035000d12000e800c091001081d84551441d0001c030710f40e01c0d031010a2075102c6a142c00010406c0108203d2110741c0d860014004d8110081d085440d00d001e022107980250081c81582e00036100506000c045481031941901d0307031803401302c003680c050b402511017002d074800c50801005003174403035460198103007032039040c5009031383c1d1a40209180310b40600003094402e9024040d81c224031441d00e855041c2e0ba1544851800500968000034650581902081a84a158001e1102945041c5000340355000c0c41907460f280000340f0540395074030480030408100558032441c041c40405002c88d80d051030071802014803840c5509544c003c00d000c42d001003000402204288104840c06031282040182010854002403040f1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 336555791 1250 336554541 336554549
    0x20114030601020c0d14011b0e040615210603060e1006080a031419020d0e040203010b0d09020a120308040b070e01080406150306020f070521090402030a0e1e0d0504030b01 75
    0x105c0081814828000d007020480070751070001340208030700070f00341110000b1010301da941c00c00402c5214021042d603041c14401c2e00c04403980b40a030361003d5089124100d07020000107408903550b415603c12825162a51b201c1c06008600c24600066041e00803c10a414002e8211070b51003075503d400301c04c00034242d01082030074002c0e5240ca040d51800594600d1072400d402116102c481c99070024800304c00301034000612120140c500d031501000019414200300a0317100074000c0260b0b094052000c9800c005158000d05803840c80205450402d6131200038821400c03a0303d04040e0000382612040c00309000400851036040b2a19181040c2101c0070040040e20a840c044c0004102c60741c3e80300c044107100b0403140d03810061648281c0655940c0c040f8541038141c2c1d04606030a03642c40c000e140c00301c4481406215859440150945158107103602c150401c8003d403c01450384903c00d0300d03824266010b003005d1001d030556030f1a42440000c0c0540200015280c1034004460038140701040100340007080c0f134601c202d8111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 336557041 1250 336555791 336555799
    0x30c040308040b03340c0804080609060a15060207050f0103060e0a0f0f09120810050627010813030809070e010e181b0d021c0c06032004030210180b07020114030601020c 74
    0xe00e6062070240b107d0700c9076030b0240a081c020b020600805450110300c85000b020110340c10310100e42209101e58020744148160000f5a0103d5070030007880c1041c800c10210200c050400248560b41e030303000c4159588003101d40c64941d50340e54000d6483c0090b04d2007000400014120200018501f5a0361003251414071f40c400d009000140001400803400300810401800c8080c0000d9194001d52480d12400d9102c00e48000da400d180c012112003e501c80d441041c1b0402c0d40d0b01d2080c94030072064074184c8040c0006080c200903405200008582007801c41e005c5802048030300d1080040c2d01d0103201c80c46940654580000582d08102848100d0030a448038082d01480f0865801000304507900c002120f985103542044c9030180f8400108042c1301c034245414040742d000717850034085510342c401c00d00f01c810028a044401c0540034171040c005030034110310036411a046418203402e601803124100d003000c0440c0c0c0c0000c021440008603402103585c0030351026940c1c803615200c2821070030602c001070b480303100018401b405 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 336558291 1250 336557041 336557057
    0x150c0309070314011406040504020d0f1403040611010e1614011211070308010b0903120d09020307080f3c0312010608010311030f12030c040308040b0334 67
    0x21103003445003000540c0e024400c07480b00345a598209001e040c80840a400201410f40010154145400f40c14400c07a030040c41e0b07050191095540c00c7c0d600071044019200320010342081c4261075410002800a8410303034480030003004624040900b0340b07500091914540e04074000300d100950011854400f40d4250340883c503c427450b00c400485026084041d00408a41442d03803008044083c0b0000b400000d003e130740c90b007907070341e07203640354002180300d003540940d01980700380034441d031400700b81d0302410520601d000302054100705a0000303480c001a41d040f200d000d03048161141d007580c01c01c00440f04203404081d0744400c11101c1c159807544d09522100c0c01c51a40e500d07800c10003003590080c4101c9880c40d040341c07803510300d550710b070301004142c00c0c000d0000700c0e00c04c4403083c680a0700386000550301e103140340d6207002055103015240410090303400107000d40070748210030310022001448100c042e01c0a00188000c240d03c2e0302d80f800c0c00c0604800d5400d00d0103407101c00154058091080313161040300f400c14502303100c90 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 336559541 1250 336558291 336558301
    0xa06181406130b04050405060105030403020a060c2607080109090f020d020a0f0e0a0b0922140f0f06070504030215070f0609050c030c0f030c011209060c020f0f150c03 73
    0x107511801c0e03558040c10540c01004500b40c54500080c000f5103000ba03c081107035640702d40043d83e05120030303940600583d01194402000a60940000c520707200c5929105007416960442181c000d0010070590010146190801400329030000c04031303005141400091100e0030080c0c031005440340c01e280020303020300741180b444c5003503445150300c42c4014091503521000d49a99004e5501207070100350340e90b040c42828030350640081e2801410440c02002005038910751603800000c0c5068062403c8011603058010a00c0c4e82d407001c03018840860100036103000340c5120311102c0e034a00c0c20311100500e02030600c0303800d01003400941c44102031200d000031040d132002e0341c800513802c005012804a40000b41b206040c054500c0401c00c0104040c032030914154211914241e000c0104101419529006501a80000c0d40b92041c3c0d84940e4000c500011504000203103914952140f0b401e0b12441058440540d12502611818a81c10040ba4414020440c041c1041e0bc0464518030600103001d0000722206402001083c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 336560791 1250 336559541 336559549
    0x90911090703110f0d0e06190c020c0105180f0306071701050d0f1419060209041a030c01050d110a090806010e220201110a0c090f02130915080111090a061814 69
    0x40030000507130031200e1601c8c01c00440300c5204c1d051001c900305142042c180380702d0306000142d0b003202504140c5503281000c0c00b142c030b209a58031040421550103803105039001101e031018000c10b030250740d00fa502d01c0c000c5c4141032500040030006900031802a1074280782d03140801c80440580c0001b5a02c046030700701e82e00141c07a0503483d00801c0500106c000c03801140480c00c000c490381c0209100d4006640610005c0c1c40c0c07280794202950328490321a01508000a10580b561050300242210001108c0c0000d607242c42e40f40c0c801c560b07040490a00302044050400344809401001241c0c01050884a00c0c00303070b07103400c440710218080c00400d0061100d2449100c0c00071a0300031040400884107030390466203545101d0a0102905c40a0300c1034900262504052140c442064002c03500219056040c0c50201c61500506100900d41004d0150481542c4100413505220078051a518032112042c156101c4540c41e0030861000303040c1d48000140b00164141014581d944003641c8120340c03051101c0700040407410081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 336562041 1250 336560791 336560801
    0xd1a030d110a020111070806070c0c0801050601020d08060409170405090606160204090f1203050a06060203070b010b090d051905010b0a0806042a08060114010201020309030301120507090911090703110f0d 89
    0x68100c2d008808c1001001a8003060b00ea203c00d016101c42c400259407038041a08803402603601c0c1e40142c04c001048456140907802540c2c006001400000358241280c03105618100542907601c603000000408000303038503181d415241c000a0450f00c152130a094001140d48030380c100140240541d40b580310000030700c840d02444c80707042c54000a092016900c02c007c02001014111101c503042454000c0108400d44004190b0382c001c0d9020781100c58503403c01030000c1040d000304203010703405200d180d40714000a406102c2d4104882d80d4281c0c51901c480a49407050950300c0c40c0c0c032170a00655000408102402002400316040742e0003051101c2e031403c6852020803044001581140c041d076215400040b10700e000100c10781240d2180348807890101c4d90000481c241d110660301c40b80c5c0c0394018001030054000c02081000c505100340c00300c40220303640d190050141c6d5500d180a40780822820345003c03803801c1c18050307035901c00c600d403404004803001d807002d110550240500c608000c410101e840c401252141c2c1c48 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 336563291 1250 336562041 336562049
    0xc02100509012024060405181e120a08070e010e0d08030a0e03160515010605030c1818150d03020325020411071406071d03030d1a030d110a02011107 65
    0x6075102c039402d441c18138141c4c0d94140c4010317008510b0100003a034030b855500d050100c507c40b40f80280c0364445964000703d03541c0000c151180c1e42d40c000d000c281d8000114400090841d1502a21b8081072841c00d200044d18456004400f18180400003103191142e6981405544002d40c0c8503201540b6901c401988038001c20086d040504144000981d030300707248002524000c00d49111700221a5a000c4100c01c1c410b20030800c1c414071000c00c50600120708502c05400181c40d030442d80c6050001928203002c0018004254541d003880c02102810074000300022142d06141008415143c00208500703a6070025542e1050910140c12807000103625410314090b8002c04815640040c0180203854400858484039403041c0c0c01120310050350501e07090068400310f5603e1150301180c9506004603004082103480c5041106142c2d49030108002c0104061071512580c119000443c00010081c5402001e0510b009500801d03002440014083c801c0064400107680541c0c42c2d081c80c1003241440000c100900d84440c80d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 336564541 1250 336563291 336563323
    0x30203090d1407080a020f091e1006032904021309020c0d200601050d08121306060b0906070609050a020a061206301e030c021005090120 60
    0x400a020b00903500039250b880d105060a65801e1565054a1941c9200d5030348029045600e4283c82100d5241034000075038000203413989219007001e0901000704a04007281e20b0300b075030b141c030000500c50b80e941881605003140d01890f1895501d01c640040145105a00284502ca40e40000b21408040d44400b4241e00500300c08c9015900d612107225110340380d078505c0064a000988250107007900304334455034946100e40030000b40075a40d0900090055200b801e0b40c003607404040c10000342900c03082202080d84518603440360a0300355203003803a112040d200c15610008070359106101d1080c0030390302c5504a404c0b840d0700100005a03c15246031090502c003581c1c1c0e019503c10706a13940025101d070802280103580c032640340c0030400680c9078404500c1030b8209082c404840234080c0110b02800c0c0748180e0b0121024064400d0b50511000c4107824684c6c40021b40d030850004507643c16680c1103041600c0d074005400c28a0400d10300b8020307a000000d140000d200c483e0312201c200240c52100d0900240144064145d10303030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 336565791 1250 336564541 336564559
    0x90303040b2a040306111606020f07140a0201082a0d090203061f050a1203050a0915020c01110105010e071b060c05030f06122d0a1410020c100903020309 67
    0x4029094203e407005441041c00c00201846900300c1000711901d01c1c1e45681c03200510348003910350310000c3d04000c2c880440c094003040f5a2021562400758a00d034583c0c3d040041c9101440b610006150703900181c40100c51450311204421300c150f6501b201d50319004415101507c070302407145101d01520716020042c0d0140540800d00100d0f03421510f1071401c2c0050545004102542c030014000e070094548201003100c2000340c40480000d200708000c004400310380ca41081c1c007648070b47c0804506400310741d0110141e880380c82580d00950f0010401004240603000800407503150400060141380020028000c00514000750f022000c0c10700303c0c02c0b070307036036040fa07801c2014041c070800142042d0b1040d2008002c00910344001a40c51a1561082d0240c49000010305032018911405640c440006030281c40700300c0003660880c10020301041500d5802c0d024000420502c03003d040158103094209218100b81030041000c034403030000001d03000d43d11000d03010700041c1084403414100d0441c050200d080d64808010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 336567041 1250 336565791 336565861
    0xd030923070509090c06070303020919150f020a020a15020709111b0f0d03050a091403030f1012230d09050a06180b03092d01050f090303040b 62
    0x381081079070070035100c00445403540c0c000300c5c0d034603400800c07050350013907080095400291294002e8010040040c0c10302002689000e074054680d08590010240005510240c510840e03104500ca140c4003091b0026140d40038140e00428494004d80c0030714010080c01c4c4421a01d5140b003004a480104a0900100711280800201e640c10f0f90007808203034143c80d840e41982e20320502c04a4515142d6203d01c0040c180c500c00703088181d02500000b0403000056035651641000f140c01c01700140c01266415000c3e599a107062440c65200b1000580b42c2a29047c003d9400d02c4070040b01c0d071041208507000000c17840200c2c038043d03035000c402c0300220102040d40980c65102c03407a5030b045160740302901e07000c13183d04070801c0e08c0d4101290508004000901030290303c580030046091f5034001107401280c0352081e51404001217140d20394503111880102d8000210a02d50f281c425402c1c8181500044100e03101103060911000181e6a8040540007400316032180010800401d00e105079842c000701c80243d070844169107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 336568291 1250 336567041 336567043
    0xe1b0304031d010311090d03140a0504091d06040f02060417030d050109020a0c02190504020a170f15010806031c12050f0103020d0311070302091006030b040b030d030923 74
    0xc0282c0e09202c07440c4040001041d40c028003a203628081c4032240780341000d440d401005554010501f0980c2400b900151200f68410024003c16090440e0780395940d6880c0781c042c0301d07000c6621207d28031409800300b001d90340c0078034004102c01c0e030060f400c40030380410700c1800e0002035240d05ca00c0d8400d0100f420310518500a80d4404002340001204048041059a980c1c4161005a02c5003030300030000220794083d0200185460071840158040d01c240355171989444034080380403039100c55201c1d00815050300d282880740185454943e0711002da014940100d04201031644c1402440d440c200d414082ca01c40012050784081048641c0002d8002201405042a11018004400e000c08580c01c46040c400001e41281c3c450141034101d03540039200807800901a00c080b241440011080c0741a130180d0040040075940355410b45019204e8040c000c4040f82c80d000d8054211204010800c1c05a401c10304001810398000c01c02e2010803810b410049200a02898695140a41c0105c0b550a2030850715503e400214 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 336569541 1250 336568291 336568307
    0x801050108090c0a27020a030b131803050f0d0603060b030c090c09060703050412031814010c0605060a050603090c100503100b28020109030306120203070e1b030403 72
    0x20080c0c8036a003141c2c039809000380e110542108225000100e02104004540841c0284611840344210764002001d0618282c400c0c0c1c0c0c08034400f400069112038040c0001e00d05031640e89c04c0c180720030404200e152600c400804600c442824058140702c4041b4010741d5038002581142c40c8406d400c8020440c5130340b240b904100030b08140c4a400c4c000d20481440c003950f070034420151800ba1000328102c50401c004101003141030f85c00081d0490400200344800a00343c0c8003032852507070300e034440d8840c0d07143c250004c42c4049002d000386c4d100c02c00d104008003070056641d0301310041c050750744d41007103000c520743c3d6030b58010921034007080d0721142d0444400010018400c40c0800e2a850601c000c9918941c00c0c5a41c440403038840c0000e0b2805103000900d00300401203e03051000500102d140e802e95600c0050010040310000140c2e01000b20260351900c82d988101a498403c25024204224030300e081028160082951b81f207040c064031488a00d2a80840d810804005001c0348101001083d290b0703915103481c0c0140001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 336570791 1250 336569541 336569549
    0x40c120f0c18061d0402040302031e010c1e0e0f0a060305040506060409080d022d03040b060108090c0409020402070f080a020f030702060313030e03010c05180a0806070807110d0801 79
    0x6000a0b1641082a407110070940459155940700380380d5041c00d41e10891070707585a03103086038810b03030030480000182c8060100200d010350f400c2040740450456000a030943e440d500d4041c4c1000b0404030682c0055410b0444903601c20f40c149060281d200c4503d01150703928409200b4540e20681d2031600081807545904540c0c4103a201c0e9081e10004e8480c02c061009032082c0c060000c02c034500a001c07810070701c0c6080d800340208410103040104200c04000c40c403511803030f0910000c16031503000401c1200f4085840e41c0385800030820329048480c0d14003a81d03000e49611210112034810341e10b0300044020f550f9560107540c030482d00400700036036035600d6180c403040c6940014441400b50141c0c0d15080b02008000c001d0b031b82d0460b006820a0700c1c551301e44640e00681e2150340400c42c14010000d40500e02910248564004000f840c1c40300c698410f41d075403403080415410f4080c1403203400300c00f6051103584c40110b140345d0032003440d007058142c946400070f058070701e48088020700d4400e01c0f400b01c00d0804650306c000c44904132 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 336572041 1250 336570791 336570797
    0x1803181c0308010b0f0403061a01180f231509010f1b020405040f0b0a050711060118110c0f010203100b070b010312020c0d060507021218040c120f0c 65
    0x80d400640d2100029440503024000c6403019004100096010300100f0712501c0400c51646800d49071b94610003122404140d044540501180901282d6005803070b50020501240c00c45c1046803038000c2418a05103603009100584004a603011406060b40a60b04000346000700b0381140b607145a40702408940001004900040000c0703260341c401405070072200480c69402d03c00103500302e000c0e001d00001d440040c20460340e5100d01601130000c00c549941d424050071815178042217905084000408035030101110b0344140e0800c0c00100030a1840d602c4801510200800c04282c030f01d11844141c000f4041d80c241400fa50080d038030503045100065004522901c141c0c0b40c0c3c2c07481e2645030f240700c034014001c90500030036021000d4014000f14040e44d28080300d15010384101c0f02e0b01001800800d094403541c071000c940d62910354003031041c1c031901401100e5429501060141c02c1c03031038444080104150050420b80126900c15025045a1040d246901d81c10305000083c082c0c180440d40c110005c1c500d40280c9400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 336573291 1250 336572041 336572059
    0xb0306010215091033030203060606160213090803040503070605070306050102101104090911090601110316021c080309010b100504030605060f10053f180318 69
    0x720101682d4a0300a045500c020164406a202502d000302110710580c42d8803600110006048010f00c0c109081c0340c240c0c21070a101c424035500c1450310b0200c0c050b11940c0300e0201030218100d40c200140c2c00210940c2c044419a1180e0400b10201005084038040680245030000411040c05400002040344521403002001982d84000c402c80c1240c0080c05001d005800a0207001c4c00c0c4051031300710101940504008a10300f5598614a500711000b0f000c045600c1f524501d42034000345000e03001d003a441142030038640b0b60880c00c0c1c070b4a90b13100d219070401c89910040c0c10004000355111102c0c408880c440c0b48044002140e0b46080c00c540541003166503403442c0d0f00b0103d25180030b0038091501c240d01d091640f609400c040c1141d603010040c003001002c05422030684444101c140e55082903046400c407083d120590389085130001c102c800320451003000d0342c16020130343c07010f6801c0101182c00300c4200b039021004103940326802003141200414141509a110101e0301500c000d20207416060f0500d030031101481 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 336574541 1250 336573291 336573313
    0x5190b0601020c0a06031a0301050a1e0b010507080c0c100905030c010c12030b1504030c0510030e0a1101051303030816091d13080a020318030613120306050a0b03060102 74
    0x83d80d940055145074100320300c100304100160107a045112001d9810390002d42c01c800220200f821030341e04951300b811043e00d80814568444600d400f1450701d04440405100c0b60002c1c81c0080c196100745440140342d81000200894565400e120b69202c03040020a0b20500c000d185d80010040c2d4003501426101e4021002140380940c0181403d100182e8404940c002c5900350a00c107400403c40001c9031504400909590104004000003c0001c2c52003a020125681c1c1844148003441180304020400c3c5440c03c00f2000f80c0716800169103445903030040b590f031009015200120303000e024103e125502089c0f640d801108041d041600b01303206855258894020209115040710b0180f400e1050040d441500c1c0580000005550401d03580100083d041071071104090340d4044d210380c802590340d40140c10105e8080580d00c0c0c680048107aa240880080c2101c2c01d0a441c212010315201364014080003240e0382c000e6459001c0d40040c0000c02d4001e080e00d292540d00c5021000a41c001c071101801400380210240c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 336575791 1250 336574541 336574543
    0x510150f0801020a080f1024030c080717040206040b0d0911030d080a0c02070f0312120e1b0111030c10050a0c02060408090d080f0712080613150305190b060102 70
    0x307003210100d6503c4c21a50744481b5500c06601c0c030f010782100c85454040d14003013036840001240b41072400b9007201818104000c0c0b60001c040b604604620000c20014205120144c0c0e0311880c40f81549141d802e13802d019480d0f40c0f0000c0c03414402e0750b000700c00b640004541754086000396403100c0001c6004405c56076500c0c10100405445041c80031052000c110640042101c03c038280d8040c01e0145030500403a424680c5910a02d00281d5190b8021910b60700d00c1d44c2040100c170b501c40d41da61105995911306011048551800c1a120100e5046024241700b000c240c44d00c0e117038416049040314105090960b84e9814128009907180c182ca184240031720b40c03c0c0800301d0174014252003170080c1d020a030344c05040c0301e071075a07035500b0807903840b1191156200130242441c1000c108540b000346542085c03030502655800003441c03c951810311541d0104140089001040025201e80c001e41c0a04002c1d0900014034102c00720350000c1404298002408900c41e8412840d50100400c05240103d0b02a15500300c2c5591244012 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 336577041 1250 336575791 336575797
    0xd0c0f030b060f16050309030313090c05040b07080a02101805010b06090307032901060305040b18031b0f0607051c0b030a030c0f02281d0c070510150f080102 69
    0x341a031403c104000800644002c0f6180d18591051007580e11b03001d041d40010707103141c2180350942c0711a0303680b000c00c02c0054403a201c0c0724030788102c81c1013007410b15250074010707101030103980c0014001c8403001500c004524820300c20315500344200801041503c1c50141ca169002c02d095800b140d40d90302e000410405854444141c0702c3d100710080080916a01359640e003403041c1e00703414044810001001403260030030032603114070f80031700000d039000034803840c0608200c409900c01070301c540b0820000114540761340c40c01108460001703004002c2c440540740c0d0141001d14001c01403800385858080e15080c00034180e4084028030100b41034000801894030744119140450716400341c036030b81c50760080781854002801407149442c0d050107918104046144d940100f9140e000015051a00035002d2000d002404603e1406602914800040021031240820000f10402e0050849844100003140041c200402004000c1c4401280b400034404000c003042101680340c035900441a50300740385800411074880c14400d0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 336578291 1250 336577041 336577057
    0x4050604060e130f1a0108040f02010806150c0f0705120303041e150b1c0f02090a09120302030907051c0303090204060504020a0c020a080727020d0c0f030b06 69
    0x12185414948902600c1c44851038000680041d0034454050300761025220784403880b011002e000c1528036410040c4d64811100301c1c40641448680414400032078117000304c50400942c282001c40c9551505030001c5c0c101d071050030501c4015080012450714403034000c2213204069003024201c07502c0c540c581081000011440726440c00310340c018000600480c280d10070000c0c030b04214004420780c2c2c1c4010b48032444a510109070828000b9180c1007010100d040c45c07100e02c4c1e03500003c510030059502550741c5004400743c0b1700380b010b40304124140c003180c081c5140368898104594046030b00c212504c11840090040d41049460004c28080e4400016580c1041000b1501070110744c50b81c0701310402103aa0950007005c42d81d10a82e040780d40c49602242d02e8403107200070600540c080c0c03900d003090103072441000980c6c1d25941008030580c100f4501041441d03950003802e0b00401d145200c000e00d000300186050001c0c060005403c06803410447c03965120781d000207070107600d01c05503942408420612000d108083c40b50b400303 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 336579541 1250 336578291 336578299
    0xd0f151715070e04020403030f0207060302090a030308040218070f0e0a0609090c03201c0c021c050d0603140105070207052110020d0605090a0c0203030c0a02011407020d030e030405 79
    0x441462400012841c0e80042c0d641000382e00c1c01c4101010404036007164104074045039802c1c10340a9070a804000050040c9802d00c0c05524098040c3c011410541d0070703100060034802d0b10004602155a8611002100d9102a6540e14030f031a10703100c02000350200e06907100c00300d01da000300380d00d0764202446558107642c02625801956850403040390010070107030130035804041d92154201068820f90030b801c52050380c0d0711011519170400340c504941080703091840f21a01894218140e1901c0c1c2c000c91003450002c202c82c2d0760000a031225405550a204400443d038203a40b42c04004030811414091900190210742c0007000035954403a03041e40d491241d40203440e4807a60841e070104901132590800c001d00607414064a40420300501d425060340c2142160049860301c0307200510071424649040750b440a050312040c4640580c2190180d224800609282c125290014039914414000d4012154110201c2035400c0b00340380c00e000081d02d41c4010000040007074280b00054032940301c0001524140d41c0d0080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 336580791 1250 336579541 336579553
    0x60312050a09060e0303090405040302071403031c02030606130b04060e09040b041103030408060a050403030c08010e0606030604060e1501020d1403010e0a150b1206091e0601050d0f1517 81
    0x10f0016034104c07404a1000381d1511042003012042d4890307004050082c1e100350001c0030120b0030143d6819032544040355050181c0c2c02800220020480300740c84540320708101c0f50041e942d03250700c070200c0c820303105503007800105008586000601d520490000c000701e54280d91251280a211420004000402c2d50064010610000814045009019440b2081320020304907443e00340d075110100c4c14290704450200303101e0f668904120070706815004141052290349014940c940c10100b004842141c0609418010304010000843d6910703254405009405d00303807071021883c50310403002c0c84200048403190740180250f0410700440c80c00351120024169103130900500796030802500501404c0003e00005050344c544c0010f019980703009410401034615070358140d58a01c03601781001c48405018040e18010104035007081f101d0700c101c28101d810040324014001003600d401004030b40d113010301d010796200b01e40741904076903120800768070541e050340c01c0c00f4410712175a94810130710108503503855007901190090 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 336582041 1250 336580791 336580799
    0x705030403120801090912110f01060801150807030b0a0504030e060d0b1806060409090507030f1211070509070f020a021306080c0d080a0522030c140d050d0e040b13060312050a09 78
    0x246900031200032306400f254091526010030300e080d00c20a5001500d6a556515060303000011002d00601400340f040c020508107145966080700040001d1144611a907101d020804152203800701181d100c1009040036101c1041c800070f070740240784140310584a100d03116860f6042d1000446502d1085000900031810300d8540300041000d404103038800c952600500c1c00100c0050190500c2c845803034001c00a41c1c51000c507c40c1c02a10011204e4545581580040c00422030390b552100b285038030501614050008a040d8401a40390189030304000754040441c0002031000ca0542e40204100c50340e210444412348140c03024841c81c20f8003d0303000b90444004001020225000f0710090050020702c54100c03e001c0d8032581c483e1464981c2d50002c6801d514401000c002404100c0c16076040e1801c1100d030703501600210341d1500d0703540c000d1242c8030041c01180300400d4001e40c0c0701d074003403620488050300101210124820b07000060010707000c00c842001c01c07038509900d00c510980985880b00c01c9610381003506420 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 336583291 1250 336582041 336582047
    0xc04110d090206070f0c1e050906060703120e061603090b15190602010903030501080c01020616030b041805070f0e0109090f06180b071b0b07050705030403120801090912 74
    0x1c142d030003000030440c400014501c0c10b00a0303c0d80c3e000f03c00000c03119003098909400c1c440c0d81c840080280110030b100384071079036456502540003442140e1495481900c0d29090b80c039109508100e115051800890450b600c0010403130034424000d2401c0d1019641d40c0c08030580840342d6440c0045c2810a000c0c000906503010040f40c003034069401400c0003440003048070180e1204849402100050351036014000030560140600d80c094280d00002d4a1404a01b20000303548900050400080040e40e044101182d4000e40c00100715220280082c808100c41d81941c1c104d52280c03103c200c50610900c000000c1c81074001002105075240b1080484959103040c410740003603e9148000c3e100b240d01d10070107000241c0144913070714042d0840c0c22488a405614249031240560080c0750400b8442c42c0404a007914000f501110101c65000c440d03814107882d084802c031003a010740d00b0000c09911001501109000e08510390754984e944e662350b007140c0c5a80b110f00d83c41c280d90b0b80c0840240340861a0506e01c0840380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 336584541 1250 336583291 336583301
    0xf0a1a070e0603010b0406080f040201080403080408090d08031f0b0417070b0d09020a0512330c07060b040204031106180a090605040b03010911011803051c020c04110d 73
    0x191a10346205251007000810a0b4001e81c4040101000060304000c1c003508480720395132003007050b0012201480c003a00045c00c49000200f0050400020f000040c00300f05051069808420002e8008030003e001460481d809600070b03074a200c01d1040300d929103e81d079000b038a44402a1256400c490b03003070500d4003c0d50440c1207000c00c8410740a00a035440443c142080c00c000d0408140a808040f8814800e401400b0400c0303000c3e0407290007201c0a0000406440001035281c5a0b25540300414a05401e880600f21000c4030244524038005241c2092105200d00e0a020b424201d0041d5000c0140b20640b00c1000b00b20302c12440001c0c21a1500d00117242c0c189820405895180070b109000a8049541d60008285102e19045808100e035619024405401d20740f00d8018074940030b078000c01c410100303030321440e00d0407001c00c52450412690344008800c0b810072100000055610204440b06000f01000b000090030380782d090540148200d80009555280c5400b031502c541a144210703910348401c074030144001e06 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 336585791 1250 336584541 336584551
    0x30625030905011812030b151e040909030801080c0a090f0e01240806060f060310030803090307121e080601020c03150406060512030d050612010c0309050f0a1a 70
    0x541e4a44407080403941c28003d4284000b0549444564080d4528040b0a050180b880e164105441e200382c01c0304584034581c2d40b5400d614903014154942441c400c00030742c600c045001400d842c440200380040c0d039202e241c01500303240d842a1103040e41e0f030780c860003560b94501c100d01c1d0703484d803001412108014800d05a44410764604000001050069841c3c2c00070303081d904251101e00c50034100400e03000c0b20321802c034038443c0680400805070007941802400100022103000c000e07841110000041025482404031b034800450b844004c1a4403450722600c0300713840780c200c06420f40c0e0244a491101c504544a400642c0a0031500740746101e0074258408201d50025009000605502c81e43d18000195074003000301803008250004080743c2e41c40d0a10306401912410740c409400b410910207104802c14012059a040c024407207400200c80d03590b40001081c6e0041503107001003551a0950032801c403641900078400c1c0764040c1045640a1048160195407100c6244014060703070b040400341004004502c0a842e040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 336587041 1250 336585791 336585797
    0x809040e0a0c03030e2e081f140f03060a050406060b031603050702070b0c2b0203190210060e070f020c010e0f0d0c060207140613050103050a060b0c0f0c030625 70
    0x1d0701a410440c1c8001001d50b0501741064041e41098020a5100c41f002c0c0d4804006001074481c518111061007030446103014130540b014400341d121102c0d827280d000800c414000202100c41e1400c05022850040c0b000740c0e07040d102d480c100940071401d004070100301e034028400f811110000f5000403c0840040c034000c0d00810450080748400905070788030501a100314042000074150f4616441200340c400034000705c1ea0460000f90150078942d142d0044151480101c40b500c80c100c8920000d1000c900744180c1d140700c0c9666901d48480451024841000d0b0f51080c003164444007120307101c000302a030382c4102e41420540081c03c20f0441c9490340c01c0c005920038040001130800414038405603145500300005030003501c01030f84502d00804c200c004d0700c846080460800c5e9030891901d105030003003491001480c02a18181078445010031a02e02c106e0b84a54000c042103607503a91140c8031503002075181c2042142d842c0d07041c81141d01d808110f02c1c001c40c01074001c0c4034074410074404c0d41441c00e80303480e4801010480380c14 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 336588291 1250 336587041 336587059
    0x1050904021e0d1d0d0e06180d080403050115050a0909030507080304030f080f01030f060209220b030706080906010302040e0307050a0b010e09030304051005220809040e0a0c03030e 79
    0x1c0040250090044800e140c103010804204e030125031071614a13a03003000e070940ea0100103004040e07a00300359000c1d136482c02030720880d07651165144800340840c0d088454035000070003a803150041c8407040c0051301c02d491044000303000048083c4010200400d05004040e401881c1c240c0070040714040b41e1000740f81d00e1090030110b06010054640e40c00e030b80c10849040d03010841911f154503013168420318066102400b210f090131103505607100e41c03850078180c4200030f2505500103400c2c0250341d602c0e41003034400b0500005a00d180502c000074000500400d04584c3e01910480354007154440c0100b541c184103094000c02003207903038030356000c00028299880314194940020050f400c0032035018810040203501403820f00400d545002e04c03403002988003e0800005400c18001d10002a0700896a0b05400700a0b50340852070b91946042c20602d040480411101510488842c0040094040203000009c01c00c41d0708020020659130300d180c4601890100800851b0018410f000003401400300741e03903201000d04100380c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 336589541 1250 336588291 336588337
    0x102070924030b01051c08030708041721130f120504030212010203040312050412110f0a03020708010c02030f0406050a12020304051c02010e4b010605010c020105090402 74
    0x50a04502c0d003007620801082070050115040204c0c2d2802d8403030a01d030910000f826552a008003038080070b422002002804c1001c02e0038407800600b00c41e03001c010120354513070b100c2918206840f806e5241860030450b402c940c001a100360115040710203403039000814545450740903034480030b84c0403450300c41c40c042c07201c04e01006c005a107034030b400030207041d00b09400141e4034141400c029003140302d04103030250795074101820400052802012840c00c01e03414200710744480c0c0d0104a060405c0505480c07000d1902c10700c6000c800f0305038001a01011282ca6038000c10085001d40d504a0f1248985a80e843c03090404110400003188108002c10410426240000540069101486c01c0e640103903001e4589030300c0360031094204084d5403082d480940440c0001c00c1250078190f030346070f100c05c0c41c07074544a00344a551407800d501b02c51300b41c0040b070b0341142c0e01503880d03491024403218940c2079100b8003035035515843e240c8046103075405009002c00e0607030140c441c1c0d400c0c14144000c2001075032064180125440f20605009 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 336590791 1250 336589541 336589601
    0x708160507030c090204060e0f18090304030209061206160201090204090b0a0c170105010c0302010e0303160801090e121605010c0f260609130525080c01020709 70
    0x595100d040904081481c608024110814a4201e1010075204020802503180c000042d4500b070385060310130311640b0304003800240d017010310224020b0300f0b41c8400041203040da5021000b0029203208032044465a00d0303280a100709c0840f20301c00b141d81c030740c440c0b00070400358420351411003901e10440c8008200c0848580c0407405494800c2400c440c100109000e0000c200c00500a082d81c1580710710b0710000200c1440f06543c13001006210702814059140054402e251007034005c2d03402d00313040c3c2c0c0c00c4135600c0c2480c20b80e01c1103c0898405102c0010400c0c400030600012a000390b141d00c001000080c601c850242082c40c80c0c40d81701c1e442880364042c4205502c0002a0f00303028288407107146450303030019175100420203090b501c003440050000b0000c1d00c025a004080d8500450381000007500c2c242910354405551500a02c030701d00018040e4451080e0a801e005a02e440702501140c0c140c2d02a9902e666610b00742e40d446480c0340700389002d0b810a89044c040301803540d000c800010b6022030003008001d482c80d144 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 336592041 1250 336590791 336590827
    0x815040f0503130f1203021b010207120b04030f0f0c020f01050d090606050a05060c1c030902031606020c0402090d1103120c0a02040e070806012d0602010209180702070501050708 78
    0x841c05080f07014003000f50740ca41420050007070a00f005074100f004c00325600203450342c0e032a80702d02e501c040043d00c1182c15a4406c0000c1b4024080900b10f070403a6401c1418550360f9035008503401c1340050046500b0743c1640e803044644040f03000c1152100409804a42c2c2000356a88922138214100042401680030032801c5005010102d405448002203840c200003d1010042098001c2030158508101020740e002d40005c90081e04450500f0340c040c0c3e00d616134000c130702808000700065810720401c0f845400f82101404010f00b241c15940032106080d88050038001070740588900b1652041904443c14085050b08540c440156001010303100e03d0302c28461b0015090701300e01d2501d0340b240d200940c120700710306240c820388a4050714000100b845500d44102e171541e0750307014090040c440e9450307e2850b000d40782d524880e9103408007050305140301e161143c1c0020700035007203800094840c2d2240355581034000340300341805010311003583c00381103400d0505006603055402070340c1c00c881000c0d0400c10290001082084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 336593291 1250 336592041 336592057
    0xc080a05030604060e06031509011503080a03270201080603010b0a09140c130b0a03020f030106120b04050702100c0e03062a04050a03020409050109061d010606030203010815040f0503 80
    0x2181d880e030401d9410b1008444040e00445a4520450140700305c2d541d00181e11503000402400c04c01155a601035614058040114004211002450302204010b001d5015280d122116601000000d405840c0f00c03085031801c3c140c42145801005001016500c240003484c0d114034090004580c03541101d011443d41541540003410541d6114a40b8100c41c1e59041001e8101c4070013012142071421441c00070304440c404c1d20030310f4100c2d100050f01d030f00128025019a0074040e031412481c1d40f0f96070340c0d00d40030740a0840c0307611441c1410b2a2025000551500e4801c1a00841d0594002e100c19003580c407021000b80410071803101404132400306100d0503a81000b40358459030030241c1030402c0810360404404039142c112118042c08005000601c00350320f03609882012260100d0300810b8100081c00c18074010701c2c0882e0045c194074207003021000e241410f802c81d001c41d07543c03101c003c000c1c80d0356952084080317000030f00500c005034220010003507000c80d40c002c0031078202e0f0182d400032042c072041c0d6030340c40d00c2e5a00500d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 336594541 1250 336593291 336593297
    0x70f0f0606090b040213060e0a030c030b0f09031c05310201020d1e051c0203150f0105070203062d070e01031d03030402121c0509132306010c080a 64
    0x6024042c002d070a008601c1022400d8400b50b06092414400b50504000d60240b00d04000341280045440e541c0c0281c10001140c0100400d95020344a00741000c10380800c41e1030003021139400000c40c4c400c00c00042280c401d01515070710303404040070703809400b0040c0901400f002c1324400981541c0c6140f11850110312110801c21150100300180f07072001a0a040e10141030700d0910000c6414555140600c80d482e04002d0828640700d075440158007022003541141c00c0c0e0381080c051000c0200b2440c4603541c00000c001400845110100d4460880116400e201d480070007905600400d000c103c54098001d9800c40360f690700c1401c3c5114030440310240350760180c125003890006008108805455805110740013511081c44815600c81072181c0c40140d07684409040203001d00c2a0060b140c4102106000c1d80078001080051180e1a040c0c1600081c100d40180da00310788201c90350781484034020842e02c42c2c15a0040544421140a80c114000842540005089d1418080015050800100b90500601c1c031801d842d2 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 336595791 1250 336594541 336594551
    0xf0e0d0e040b01030b0d08070204091202010507080108010c0212070c0b1207030e0106060f0825021e060108070303050a0e03100617010c2a02060d020403150203011802070f0f06 77
    0x1001c20050352642020607042c5454960184105d813140c45801c102c0e1500724900c0c40d5512003a00c0070038001c1c54502d501600c0d4040350808144401e03419003089010302926513030890716076280c0e41c40c582280c00707061603400075a000f500100074001d01440540740150103130442071081640c0320300d00c240da0317030205003182d0394150014100440d040d0141f09409a458000000b0080c443c10b03c400030f4051a00da4400f0b50601c0b01c0040083c12003840031512400105007050707181010f400301c840180d6a00380014500d4650030341c010580440710000210a8100c40c924001400f5070780c656201654580c0c0441c0c81c41003080401c2180d401c86450130800050b0346541ea9400266441c0f9019043c4084040908074604a9041c044201c2e0003544c4101044803c03e400d484101e081d20140809048840e4900b6009400c000041034080400c911507000c2d10860b40107042c0c16007052115040c4600303d1109006044a051070702c826085640100d138003502032607100d1040e44182d0600b039283e01300e0750070b4411012036041f5121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 336597041 1250 336595791 336595817
    0x515090c03060c040305190807020d03030203180a170a121803031a010f03150306060306140106090e0c1b1f1505011e021c05040905010501090302130f0e0d 68
    0x100486640b024001d6050f81c1024116a565170300c1e44900309296005604040f024001d001d4403004450b212030b40282042407000003444c014010b500308441d0400d48400a8003010b03190840841e00d10b810a601111b21100031414a082248540181d00311a00300300704640c03500000c2d2400d01c24103000082076408512100a50f01d0002c1c03d0760b01c0100d0070b00e0242002c00150140c1d98102d49151181c442c0303418045164000414014094296503102405003070800c80004103115541d13200d420201c1c80d040c000109a0788500c0252001c030290720510201c000712a0000b0001101000500480003140c003241c07000c3d100998407945421040c0401c031686040c514803810310038415108a080070b002c03109468400526080000e0098400c40002c10644034240528402c2a03109202e162a0742d18015007040c0401210480107046400602074041c159103040004140c40d801007c221080340da004050705085901d62981001400e0320507441ea0f0f506441c1c20105920001c280030b1006a40f0b011f80e2450544148 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 336598291 1250 336597041 336597043
    0x11070b06060c011d06040210090605030a1d150414030406020303040809042d050907060e040e0a06090305040311151b0c03030c010e1011120c0d1a09070f05160515090c03 74
    0x22346501c02d0500c41010020008130343c03c1410b5940c030203120000003c404e030b031031140074085e1041052003103e82c2c0900d52600f240003081e00c40e4070b402140127680f86060040e01c120101d43c2d03482580160701c0580d10500c0001c0000f00240300900c1540006800071400c01d040300103404400da0080300036000a05da0180144416145206141d440b0f41408001c02402c1d01d80030024000c0a9070381480c1e400b49848861407002d052003040183c10780365101c142040b0910850800510540241c00100c03100d030140c504640d05464900c1007100005d10a00390180740c21503030901c80b14000007070352090320b49020b05080c854a6560030301c041c010200020002041402000070000c6c148002e8884400c45680780904e6188049405801ea5088a404003c0c81600344c450400b1800b40d80200c040c002e041d5401c0ca5080c0030040711421404900031016a5411a1600c541c8010340c1d5613020581082c0c0003a509000030181981001400c1140501850542d110114580c80078000c070a800c485010050784414148440c50078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 336599541 1250 336598291 336598309
    0x20f040e0601031a0d0501020415051309110f0304021f0206150415060c080f0a0507030e0306071e090e090105041a04051c050d0e07060311070b06060c011d060402 71
    0x780034070702001000b048018040c08a0f4081003014000d9401212007002c1000942c115005411102c2058014040202005101b42e01c00b000f195032000403a44001281e4000740111105890054192414101c149200321044d03000100700707a9010940305c0a2190506220b040c2c24140311590b40034002525101d10344034002d0080441040c080c07894003c12116602203640d9100503100c25290071000d01895060030b01941c021401c003248540000244030640903040401415403901ca40c071220380040d041410140c981c10201c1c2c0c1000410004c003180d51800044070659154000c150420700035a989660032042200b2045508000c10b130341d29400d0005004800343d0450b0400c1e42018402c0c101e28003552029103c00c4807408401404c1d40207503401000901440c00d440d210b50902c2820844040e81c03036061503032218a4882c0101007490324020b070800c0c51207a4121445690004e070080290703240c840601009501000c0644c000d5540d50504650f405c2ea49a14030151a004030020071480c1024010000064 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 336600791 1250 336599541 336599551
    0x31b0e010b040f0308160b0114150901080a0b01030e030715061406161a07020a0c0503071a0309071e0608060f0a030210020f010606090810060b030f0a09020301020f040e 74
    0x3240600003000681c144160103c01d9030361185140703480760440d4040d9040f0450300300c3c0c000c2100102900100b01c54200e1110a007100303800300c0b0180307a0200c620311202c1c2c440c810f1611550010f1203420008410b1941c0303401001800b6010301d40040c800c20814111b6003580c101900031101102050500c88265082d4002da40107050041100e1881814000c00034140303110310100080c02d1a69618410306001c10000e01102d8004c0844600c1554a03042500a441e03001c244402c4076405401c07400443d1034100000c103078003034078405011541101003a0340a112950401000f0f0140c602c03075000d0100b5001e0a059809406401c0d160701082103904040e409400454000c112034059030310342021016036034407118204102e0380c042d00c00401074101c411007241070504c2c0f0201c8130003c0d8200100041d48a903c034403010100c0b203031807068070310600c103d0050700b00b0356006205064411a05102060480c0f26440006800800061000402c01c41c2c1e540480e0076078000b8860810080b80c042410060980151f184a50003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 336602041 1250 336600791 336600809
    0x7050f0303012105030913020d0c0903030912080c0d050423090a05041e141905100509030c0114040c0611060f0601030f05040f170a0203180a031b0e01 66
    0x1d0740c10900505141141460b401d882c86100d0207920003804030910481d00783d0900500649000c0080300c0f0b140f400b0394001e80600070054078000f800707005980b0825130301003a80e40c0341c0d882800c00351034034a217900340d00d40440341900c11071010000709400c00c800f00f143d04070000c410345900b91164074244803072122014100c01d08aa02d0340c1401103000d56507070443c1480c0c3c840f29964000a80d501d42c0c0c107140a46a8642c10590040c0ca61500c0060612072440c04002000380c84c0d0701240e100718600848007420010401008009600685010b5100200c41d000a0380c0103880004403401e010041c101c09082d540b40c03807000d0381b100343d6010500040c420424060b1014003100c3c1024252501e01e1212075545510081c815a022001e0001007035441c0c4c803a40002c907a4210303254060003507042c64205003840544010b82201e44040004010444514080a403000030081c1e8019504005585042d1114207850210042e030002550b400440000c07800d5140c0d0090540d0384502480c5a82044d010001411041c0c100c4034403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 336603291 1250 336602041 336602047
    0xf0f05190615020303130c0b070c17010b13021b1006150503090a060b270a0608161719080316030e030d0f0b040606051213020a03120c1202010207050f03 67
    0x2480e0000100e036080031740303513001c00d480c0303916420101f9042c5616001078001c00d40002e015018080c03240008425107802c02090303091040d541000701d080350b08010b061501300400d1226062030981641c00742002420b48544440050144a515820301c40c042e10300e001c2d040d03030f1030000707104640300b0300706040700c2d01c500d400d049145060080506039500d8910500501d801d41700d00011815880d24580c048860320041381c80d100c0c40304040340c01105510105c681c1d4074560f1516100140541002070852003807641d0f18044880141801c2400500300c0903014041d981d84242c0119401c5000703404007a8040500545041d9140c0c00d003c05000801c401c1481d2030801c250400c0302d8840070306004022030302401c240c0300300041c280c0a030100140150024075000c1d5480303894480c0000300b079604440204040d40c04610000380b00d40d038001880407000f0380e011001c5e4011201d0401440002d106091288200405051a4022001c00d5a4001054800769161b4006035008510041040020005107038155030360005542 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 336604541 1250 336603291 336603329
    0x303120a0b0f0d0b100b03010627030201050712110a0f12090b0f2a0c130218010c080705011a010e010903110405040201092d050301020a0905040f0f051906 68
    0xa100f1000c1c0fa0050014000000412901104569000c00502c045d09005441e503030364440151034003071600081091100f0f0b5081e050141408000c1c03a4082e0f0354140c40d40d40c02d2200b2901c03040f50043c10300b0001001d001a0203800c403d400010020b08000500c40c01030014403c0480c501030521075201502c130000d2103100780f024820014060291000030082070039003511340404040204180000f200281130380541203006141c030302008030b5400b003ca10b00b954100c90345444442004101c1c89004e124030380385135994040c003102d917200b03981800300f05014202050403c40f20b0340740d144c00c40308940c4491075280d4000070303000303d0f558001406a10001d02404c1c807000b0240346442d03481031211000f060381d1040380e48a0000c3d045a004201c400302030201010300409100b2a24040044005e044071245802c9148038000035051505008171401020b0036a00c10603042c1ca44000c9c0b00141c4161030540e0315442e103490003945881c4c400c2c46000d114000030030324540c202d80c0408400003120901c0e0000d1401d1005440010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 336605791 1250 336604541 336604549
    0x1020303090a0204180c0e0117070f03020108041112060a050901090b01050405090703120302091e0d06050a1d011a01020f060114040f02030708090f0118021302090303120a0b0f 77
    0x101000390113880104640f2030b500e0380098040c2c202c803001404907110410100e0380c0580140240d041e00c4044c4032545141d04042c521650b5401d4502c500000c4d404d10510600065204004864010380300309100d01c0801444e50004a0a85607250060807580c001d00030410000307075601403550003d0000c4000c200c1c14150303880e641820356050159038091522000400e19080c1d04008400045400c60b04c001c611480e454001400b80d4005c515a5116885204080001c0e004140d0404005d1070b00800d030030100b42240e0340310f5000d000300400a0007803683d030307104c0450030505203501d04100344070140000550303500c1034200c4400005006081c50445d13100b034241c0400340760005081030640301201c1c0c1000104200000290241c070004400e200914008018882080d4020003240d01078000c1d0301c1070391204600d8405103803c030380301d101e000d0340640c50100450f005800d0410316809a00101d0f00090700d0440f4000200349942d100d0068180c1c010004010032590f1100c0b817140418043c8111001d20841e0b010700002 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 336607041 1250 336605791 336605803
    0x409050a110f06040506070213140106030b060f1c0615020a030305010b0c06072007030f02030c0117011203090f2c0609010e0c1e09010927020f0f07060f0b0102030309 73
    0x81c05141d000810740299902c03489e011111483c030744000d00000310180d44140015200303108a0300400e0820840c80c40da40b4003c404da494079080d21590b00e003031803004024016414003030080c00c1c00c0c841d56020085020162000300d80104551600100207030303992032030001c0071184140d0090038102d1090048070130061010540a0b0080103034508100c283c080c1c4079440110084c056211728403481035401c00410030022211007910b450080381507136134204080d0b0041d204140c43d01c80844c400c0b0240801800098119035052400034007030300e0507203520b40d154204070800ca41103400c04510703903042d18503450313401d030385040211fa044151000a401e10304049001c540341c0e58040c019181c0b03003410b9100041e5000c0006c0d00352005405200d000e510303a40d80041c054401c991120000b2800615420700204011040800e01c1003070321040d01c0e000c0c0786544003c0140d0000e40103400c0400091104004100808401c04040c0030f019008240009865110030307141e00071a2442c004440c10740d08140301b0010203500204207 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 336608291 1250 336607041 336607049
    0x17130605091510051e01020d03053304150b070f14060f04031101060e040f032106091a010f08091c0c0c05030609030313110409050a110f0604 62
    0x1000c03455454202049003401119035880640001c20003c0090b40318070b0800042c200c90040e02c200420300725000e00c40720680364280078140580d00031103185080e10b101350b004540c0890380c204245501880d0b0210110414001203000c9000848068240b0303451910340b06000c00c2250004a2941243c03802c2000491400303a2a0090f10b0b181c01c1c00c0d0700c0020703c0340c2d2520798603035855502c0985603180740c800840c503401e00c0140c800f940003406400c00c041c0181c005129640a80302c5c104039003c043c1d52195103544200701788800403010404084000704404034201c0401304188004880030640c44c3c2030101d034004913140c000700701801c20b50340c41c0c965074180d8100b14007a84ea030302140ba000260740c0e034140101c0c1c0f40048007d0070288010b86d4280f95412654004048030b509442408a800e602d6511810141d40e0b690a60352240366070070400c04100181120b05d4007075181c43c80b0304484010680c01034005412154103140c00e03106a000352444108002d49460203c81d80142112800001c01d81b8030045800c070301a07406 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 336609541 1250 336608291 336608303
    0x101b020303042102010b06040315050f0105030705040b0415060c050c0d15050907051c0204060902040807050613030c171516030e0a0b010609080d090602060708060d050d09061713 78
    0x5100403c0c18801e42080190007006092240d40d903030f0b64540b030803003105c4000801121a1820021034400304051072002d040741e000030000d11049080400b000024016520603560155a40c8130b0044c4040502c410800140415110b08442840c0c17410980c2c144001454014030800b6070040080000e0035000390000c40001010000800381d640820302803a288540c1c00a0b80c0c40781078441d521912080d0006070042e00d40c42901c003440700035511000c0001f40d005601a14480d5007020409000c2e5040c03c1003e8000560f040c0b0758a0500c81d48ca8551481319243c40d006000070031080300260320503150402c809412080c091907564590700c2d004042910318441e0b06603100825450300c2c60034450031300401032070344142d812000d1100d403075071b5032000079100345070f240700f0b071840c41c083e491164000c9030045400300112102c2c0e4026140c190f4400d0400c030349000004080c81d90040040101c0d00c007241e0304006050b86500f158555100791410184082c01442d48068440c0c02d0091003001c010307400740c24812603a00c080e4007007 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 336610791 1250 336609541 336609593
    0x2030601120b0417071b05100914010507030c060203100603050c1218031c020a03060b0711090c1207020d0e0406050d060921030b040609110327101b02030304 69
    0x1c00d41340680d21400001509241d5801c001c2412031441c86046800c6480032144450032045440381a501c0340001c3c85054075290b00c8002c0312491394001d00c001c10b403640c070a15241c140c0300900d540b01c000304c0c0c1050b5100d10383c80d03541803010f008094040c4030300381c0c025000d00c00850500c40e104420640401c8024420203149036040402d40500e40100709840755241c0d0084074100355680302c003400000f50406c2214200003810b040b40001d0600000d0f08448080c1d80000e82c881081846a00b48029980042e2484148003800c000b030011014102c807446000b2880e940c05080c0308407240308014100002e555620f440745180c41020010366645254003058103500080c08542440c1d45e040038003c403180d801c0100c001b20f40c625581c114080c1c0c103500002000c030703044408100e403a4032a40c43c4811545204100e06491078200b003c00c0501c50004241d010240b0050719040e0b188440110b43e0341418682c80e5142c5007035440c0c044001ea030f0903d01036a4080e080d410304c000c40c11440c040d02d0f00c10202c1608030843c0006400d00d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 336612041 1250 336610791 336610823
    0x1090b0f0d02220207030c020906040507020628020a0206040204050609010b0405040e190c0603050a05010501210905070902130905040803312a030203031e09120a02030601120b04 78
    0x3c002494000c4211541103440e0350341c50a0141c100003494808038401d440c2d140014400b0f28180c46a640503030040d5005210035521140d880c6514110f48880c426400000c3c80d40c170900d5403103800200120790f200d50180c005800c00303205010a86201400c3c0ea4490b20901d401440410450000c2c2c07800c54400321400301c0c80e481c801d0846801c00b1000081c000d2403ea000c040e81040c0303d000310703580e07003240c8046d0b07010000351350f5104030300c8120362083c06180d001450001e400c0c01c2542c400310345550b440e104024009603807142c1c1e0b41c500c1c0c94401150300c4010765a40200b800c3c0303010002a600440101140c800511a03480d10b43d0343c209803840014007103c108101c0a01001c03100f80b03060100e48001c00c036020742d1182c4607030381d04100d0110501c0d20201c000701320941440700001e0250030068402c50798054021400c0c511042d80c03010348034628050700f010199080c044184c4a41e03a8030080d049610301500a05541409801458105401600045e43c001510690180062040002c4950082c1c00200c4081f1307101d41 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 336613291 1250 336612041 336612079
    0x1d0d0c030504090219020d0804120e040f05150f0604030c03080c0f01050103030305040b01080c0a0303050d022b1b050403020915030123390708040e01090b0f0d02 71
    0x1841c0c0200070303c148003080c03261140e0400101405030203025001c50310808011103084441000486004020311850301d030503416903005103c80c000301c0300c1c010300c00300e01c03003100304103142c01c4030000c44075900b80410350103841d01d035814a250203001041081d1041c40c5410700710b4550190400c250311008040c82d00c0003d5245d29a1024880c150000c0d049000900a550b03590600a010b45000d0360180c486e004240000a203000000940205031200901842c0d809443c5032010b07070380c41c2c0120001501c059000c0040d0409a001180c00c0c80f00d0b5281d036409070014006244961080310701190013a80070300703a1300d0380e00d45031a0381000a403001c8030750440e210300c9035a40349160021000c0c031001c5250340540c2496526a17051200002000c00765000b030780c403c0c8440e0340d0240c9450840b00c10b0b0109141300382040344203108054800c07090150420303010410515012050343c56502d0f55005500450750a40c41e8001803040407000c0c0201003da440854000c12966100303000a1115041d503580207100780070b040c00041504807 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 336614541 1250 336613291 336613297
    0xd080705030301080a1b061d0111011806050f19020901021c0314060a050d02191214060c2502030c120c010305010b1312050a0b04151d0d0c0305 63
    0xa0301400781e80d01c035652441c00c81c0d81c1d0350403000c0440c0c2804180c1c80644c01c005006041ea02219050760702c0305001030000491a5150181402103070400c0004100d440c15000f00740628284a0281c1305404004089400d1100849d000070305840c0314003040d071060048031150001810080c005000d001a40c6903030150051f4600340034002203102c1f8240228809402030b0f00b5502041e0031005183c804845561041d04210b5229418007905900110301200d03080036007040700e44410419541d13010b01c80c22075240c801c40701c819448140101c1d4104514035000c2c01c190b00c1403010a801001e04042c103402d14110005611089a4203565411503100b402100c4c025503404003c0c020144070042d2404800f506030240746511507880c1030000d40401d040000000301044001c0854988104203400b05d1082800c101d1480f103540340290060f80c4500c00c06d1900c40c04030380100c105034052841161400310b01d410f402681c500361007125001105040f150304502c00c1081c00401c0b10080071200786401d010380320a5140a9030140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 336615791 1250 336614541 336614543
    0x306111317011506111b130f020705010603140d02070806010b030a0213140301060b030c030a0504080409020c010507171303200a08071115160311010f050105130e0c0d0807 75
    0x195282c3c400050840e00010b0035000c2c61401c0f42034031481000100070b24804044021116040b1440c144000c410f02003d0380020f203244104040546010354540343c5d1829200260401e444107101020141c50044c0200007000c0092100c0c00507040d183e1901742030303540740d80052154000380100000040e0300800707107504880840751066240242e20f81c0b45d052034014880b409020741c1c001d6103050804118940040140d9110782c810408292070750b51076140800281801a00c00c031400307c82400045012070b55130000c0c145c11030b01980001040e28041c08000c00c00c003000c01d28a09081350050500c4244e06403550034000d519051300b8208800040501d01200241c0e415805808500903035001030208902c2000900219001c2d505200b280b030800e03c1004613962115a4010451804000180d0070342f2030003003117540443c0242001d61284900b480030300d00751800e0b091000c0080f0381c1c0b00014403071840c019900d42d94003801c0810030800104001c00c0b00e030342c841108000c1c40c440c007090390880080100e800c0484c3c04c82 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 336617041 1250 336615791 336615821
    0x302030c04050d030f020706020f0304050d0516090207050118020d230304030b0103060b010810060e0303160b0403090803090a03060b0a050a0308031005010f050306060a0c120504030611131701 84
    0x403c1d180d003002802014502d00c2600140988500014950301c00955481d4107803862024602d0f291a0034100b01e05684501001c54040c011104088140000c034040d0b107008120200016070b5440f03142c5001030840708a9008050800c059664100c09070303c680301c1d500c1c0c080742d00a06051001c0705081d1040740d08003000c12103070702500c8005008010010700090140c102c1b48035a0040c407050030301c0300c019030341072070103c5100d503003580110350030000d442c840c04000400400103020707640362661400343d805614010a500f9504030f0a408103010415038001c80c02e000a1803503002560404400b800001e0002001e0701c00071b004587c6403289500c8035681d091410006150080c19001d100347c5d00d00c1c00b0704440c0c1040351405007040380001d0002c1e0550003003441c0c0d000050306580c0c1c5451a070b038110810690350005030b11002007001e0030a07a040041d00040b0880350542d041d4442d151150729615100050303900c031290100035060103010500c014010000c0703220a44984030302c0311001d00c49030070ba03940c01022003886036013807 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 336618291 1250 336617041 336617059
    0x7120c0e1e0a0e100c0e0907121107030e0102010b210705090406090b0f07051c0b030f06010f05040e070905070c080d0603020111030c0c010302090406091109090907060f0302030c0405 80
    0xb0b0141507010407507402610003504c614000d0300c07036000c00303c40d00c281c0b000000c240c02d03030558034941c900f200c0342c144e0040c3e49040442844c2c0c120100700044906020340380e50304010024480062642126000f25240c60900c020b00000004201083c400c216004c0b2090f50f1a0300b64a8000166509205d00400b030704010304154014541410144058440c0c00401d54280ca00a80401c2004c4584142c1d5032003901a40c69061400f071140000700d103517001881c28031030040d40e240c6500c00956420b20900c0850708034080201420b506001500000e04210381c0074600c030b5860302031849000c80380894204c0417603c180e9400074495652110a650326940b41000078010000081c64600324443c5901110a60b4000c0c1c0c3c801d0178001031049220360360312900b82d03d000594410a43d03000258401d4000306020307140a070020500c503690301e040d0001e95800d0042d0501d00580807621040380e06208484681c4601c0060080c20613516020000e052543d6803030072002090380020001b45814041ca0403a4001c01e40a003812035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 336619541 1250 336618291 336618301
    0x1c0203120405040c0512040807020a050d060504060c022b021612031b081e090604060305240d030305060105070c0e0a0509010b030c0108130c12030207120c0e1e 70
    0x10a41d00038001c040c412460490313558589840360042c0c600030070800116460584031a00c0e402d9941d00b20140c1207921524003400400c1a444845004903070fa480b8010110b0942428a0a0030540350300c4000f42c0115400b007079030b8510a01c605019883d8051070841c104c0740010782c1002c1282004c03640c0c280c20201c1c0100400c0040d10518801340c48103046d000b5903801100e40203404605040c10480880584011802c2c0211440003955841c605030222260500710301d0040500c000c40e010340c105500007008280d480d0200040e0406500300c215960003410443c50040140c0800204210480b00000d410140e81c0c5e40001c9099001303e04071b60004d60041c064440c3c444d5103410400c3c6d01c941c1102c008030030380e05100c04515041414000c0340740c6502d0040150491072700840044a000400804841c4002d001703c0b004404109940011005000603a24001d400c6149007000782c6000300c990303c2203043c0c00c00500f000c40401c0c11024100143c84244201984070b031200e1202e028035001e603c024240148454003404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 336620791 1250 336619541 336619573
    0x106020f0106080102040f09020a0c050d090302010206060909150a0906090606210c052b030e01180602060705160b0a06090f05060904030e0102251818021c0203 70
    0x20448403080c5000740541e64882088a00380c1c01284642c512150589a007888032110540190031141c0d0365240481c0c008450343c4034149010040e01a1401180214800384190350307040c0b11140d403183c000d55009406007081c0c402203a0b40c3ca02d906003100c45085800105640d041ca036004548019044041484115220308002c07000305903038800c40d18405000c8884607c00d00c040b480003811190861112050711703180c442404203017039030032500712400e01d9088000300c6030380c80200d000b9204900907900c500030135840c80009001c0c0e245c03000350740c2d640d110320807400c000c03440c0c1c001207580d484031071071400c0d44d1510214000c2c0390714104e80040060100039500700300000008541c0c052800c0350002c500030300001d084c5100b40301c11103100b560039a401c14091400200428001c2420052409062040740c11144034440364111005030f07076112400a814525042048916440d00baa04085c0348510400003000f6141c2a45207d10034150000d000e1a0028800c100441c5c2c0903101c01d100d1034025058840d4a02c0000d0f0070 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 336622041 1250 336620791 336620803
    0x180f08010213060315031104060b0f0912163b060a120201020a0807230a060c05030129040f0b03011514030f040f0204090b07200a0b0907080105010602 66
    0x910034a282d0510001d02036100c0d01034500c404410400c5940c10303c2c00d5851b0800b445c04164040c9030080e889030070014502000c14001c03c07142000e900e8003620b800941080010000729030752030f000e5540c000e07402c0041e83c40100b80f8103012103203003290407503882d12000081080b40344000400c007103e072090311100c4144000c0d5140c03d40704070012542c200f0650340b58400041c26080c0c0c510081d005901c0100e10074001203142c0018500c440c06080b400c00116002540038004950604004141c1d40000d141c0004210382c40c05150154440b6041043c01d560504c003c0c2811078085072034000320100031403088980da8502d80c0c106c4000c3c150480403441078645034040b0120130fa2080c0304404026a58144c4140c40034801c0c0c101d9000f0b6005801064a182c58030181400076100c09081646c1103005490087c00690303540c4101f080003071080ea079551a6150407a070141291041e101c505602c420041c0c0d80805d45640844c0504d207842d0300071440002d0b130301d84120a916103410f03a04120200e45c03070100007003049500001c02c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 336623291 1250 336622041 336622057
    0x13080d09061506120e03070210020703050114040b0a0f0f060f051f0206071404120b0f0a150512010207050111040315020f0306120102070f0809040624180f080102 71
    0x18064844406141081d0110b02d1185030002642e07006803503024200b81e0400d80040400900b01c82c00d00000b80c0008030703500c4001480d1005640301580030020440c0a004030090201c020310f02100d00c1c90703d51191040301c0002450980c520b9a0740015017120b1032146d00c403540c07000204004100e007a481300003944814006010300391041d031008541d142100d0040398261014411640640050f480ea40800e543e000000d6400061801042c00b0108562210075004002c1c5802805001c1d903900f026480c0f48002080a000320a040381401309040304404060301140c201e800030341c0c046240c46800d14003107009000e8000001d103603508001c44584820601809041624041ca50401d04484807881d61001c9125079400004a0002403002440d1823809100c45031108440c1070001d4601001552850160480188121743d80ea601107800760880c101f80c400c3c007001e80394a1032030205101c00c0812880c0e044280b4904c00303003002401c400403407000300c0701c422400081064140b28101907403540f262034080d40080c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 336624541 1250 336623291 336623303
    0xc0b190b03030903030405010e01050c2415010804110604120501050601030b030f070308030403170f09120a02070b03040602040b04030308090114070c0f11031204050915130513080d09 80
    0x4000049840c000c8203ea44019004005500d45403803d801501e86010018440307062110501245000180030310142200030240a5409507207400da100785403211801400303541a0824600880001c1c0c0d0b0040001030304a9007000141c0c07900ca0340300b80055910b205540090038541020407200c02004015009035001c0c10007600c042c0020742046c4181a6510803001918600e03074080c00c0c040000c0744042000795009070017485d0000b104002d5000d001f0368441e0a50381c0c0e846c1e040d56a800c20400e00000e00903015a4441c503403919103401c1586500a5480c050341c01601c0e00c0c0b20001022404014541c0c0c12035000700310303032510103480ba0313500e00703000d00310780c50803a4441031950905003007588285420303080f64032504080d1202c07404412103484881581c0c035440022034950019407072000b001d580800a91100389281d6010075611824402484000c03000070300626030030f900f0000030008507034031414440d2071070f0740200d80080d00b5030707a10144081480080c000070b00600d90020303081083c40650703004100400d000303032 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 336625791 1250 336624541 336624551
    0x14091801021e1309050405030a08060315041b050411041a090a0f060908060103020a060c0309030c1403070e090c0112090f080405040506030607051c06030b07030203040c06050702060d0506010c0b19 86
    0x10513414244c400403100103241307405c1084108103050081007070a800440260446060f845400b100c010000c0051fa820b45082540100c01c20034841e0383c000c5070028001c00c0e44d0610541341400c40d070746224010b0703005d40192030b0000600030b0813400c41a000d80d042c25200030503400e485650349041845292081c000c41000820042000c2035164002803d03d0499034040c0442005501c0d214080701d0760f0506000440400c018000f0000200c3c00810341840070f400044202c2c1110303a40d90003050b2900e0020f0f030011030104242c8041142110700495001d8080e032080c01c1c410214044100d00c40010488040001e1940d080c24040809120040740640252071096070200055111039042540d1203070120b035024000788040101410800300c984003005002e00000c00070030050348a69039084440021203801000036404420003040c4020100c2c01d00c02030801c1d04200c2d28048854011410030b10404041d5401140c4400105403142d103d0002d903180741c2e4010f030304075205044c500c8001140b0110a50035502181c280 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 336627041 1250 336625791 336625799
    0x2603030717091c050706242c0606090d171b010902030a060b06070602030405010e06011d1f0e0a0b09010812400f14091801021e13 57
    0xa900b20705030403c00c4003c003440b0650501120550701c12102101d1050700c810f0340e000340151046141450012a0050418031030a054036150008600d00c1540c5408810ba0320703c040400704500810340141003a100103079208841c0011600070821100000c0c54198090704901002c906680074264680f180340d803171070f040300e4915032040c02d075088050040c2d1302d42c02900340c00c00020369a81c0700100c81c280141c8114107080d440d4840c4812a081140d0598150b51100e18000001c8400c1c004140500340c65414440c0703c00c0c0400b0718030520800104200703901c1011070000075800d01d21704070410080000c2c03080d4003840d1034480c000030040c140894044d40542c1800001152015020031003090910046125506005810060700002041102c0e045442c00c007440746101c44034155449599007090b00312840a40c00c0c46c00c0c40f01d410514091317006089819031007400c2394040c1d4902c295079400000c051029800001c140303035402d00a20400e9002c00145800fa210001e4810515014101305450940d80c102c00c41c1d80c03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 336628291 1250 336627041 336627043
    0x305040c05010c110108060a0b0c01060302150c07150201060302040c170a020f07170f070f0b09280c08032709060d080c01060f0b07140f0601260303071709 68
    0xf48006002c00005244030b2203551041030303501e5220380014401d040782540d41003100248d502c20341255a540c0d448038401e000b5401c21021900306c5203400740b6024588540c00300400c2d1105600d0080c2c03400748802c001c540b080c2504c00d4000c0300156800a10400880c60b5900000d40422013030100461503603551400598007560034400d80e419100d0280d0168640051941c2d0480c611444060f00c1009542c04e0100b80c0c6145006000340404c240704001c00080c18005040400c1211030091000c501e583c002e0401c5522076602c002100c9004513800540c614444552502031726160340c0f900302503a148404a42d481c245150040c1c03500c0070402090902c1e072090b00c4c0b0400c0c00f01003034044406a41014412802c100002e00c010020440e18643e040006902600c071031200c03000d104968042c11204c0c5001c50360905002c07404009040c0d01c22000e004000701c0c513280c10380a0f119071051181c2281301280080c90040d000000040101482d2070809613662803909500141282c50104421801c04403400c0c0000c0c8083e00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 336629541 1250 336628291 336628307
    0x30b0601031518021e1c0204080d0c02041e020918090303060d081e0a0e03150609090106080a2a240e030a1a0a02040e04080d1b0305040c0501 62
    0x5854400b40305140d00f4582c1c004440c0c41c0e459000060103501300010400010355660b03030380c030f0800e5540d44290740c1d40c0211217400c00d00010f440c41e03403e000e10420040040e4100010403d4000c2400d052000380f1203180e00000300140110341000400c0004c0407c000c54149141d401080c1c0c9242c12920b0000b05100716281129408044641c0301d11a0310030000300c0c1a070310b00a015000c889110303e50403454440c02da1300640711030400d01c3e00344019030408643d2089284c4c00020751081c04030140e0080a410382c40e4010311a030400c014103007134054100d840c0401c801280a401400141030964105c0b400e5243d87c1c0340141400c004165142641c4402d120620104000383d00b01d28102c42110340e403402088103100f000000d0340749132800b040a01000075003088050f102400850a40c600900303602100c1c4584050800c10790300000c1001f9540340c4100024822006800348c1e80c0d401640004055407100d1401d00400001c0120411001d604041d202048040d5641a00881d12403885051002c078001d984800641d0121 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 336630791 1250 336629541 336629561
    0x140309010806040b040b0a030b0106080f0708160e0d110406050a0803031f120503070308101208070519140f0a080a030509100609150f03030f080408190504030b060103 73
    0x2008080494142d03e030540040000358002800003620149031000116900d000341c1c0100ca031502c14070300400c109900801c403a0b40c00301600e0800a558904801e00810b604030040c06609000206402c40c2d50b13044c811444921162806000b60044e00d00714282135885014000c040c610890900d50b002c42c2c542131002c0704004441042000314215110280c100c0c0315101c1175008500782d041b00c408000b460310f0b00b80c4a0240348a005201540c2d07205030b0b13410003c11001d0010025100300e500d48004100c01c60350010340840303840e000f80d0340c540c07190014905181003005000302c1440405d568080b103824002c007400000c070a508004116409000020070503603c40090240282c4039031070603c07410340558002c1d042564840509800d03a464880c2d01d09110381122090f41180320400e85e82d40220110b10141c121090113003100c40d10008030713a032555074010b11420b00e4610403001c203ca8840403604010041d403e849a484045150558a94100348020b1480c0c004d4403017980e4009503503000c07489139402031240c15000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 336632041 1250 336630791 336630797
    0xc0317281506201002031e0c0a03090602040e07090f060215010b031504150906060206090714060f04031b0b031e0c0904050412170702030901030b011e080414030901 72
    0x15494107009541048548010600014143c096580420300a00a0030022403005200607182e09080c0c1100741c41c800c03c00c1100140c2c00d500018862485051003c0e14031854803407070042184603480c6861030181c05113511a100a45a6405001e640303074101d5420000e031500441c040400342e075501c00880c2ea07a0380c055502d40913010302d00c1c010700c0a00e044400841e03009411501c882c044210103404a01100d00c0300b1410000041202821700050000b17000b114000e0040d40b004203840d0401c1b0004d0383d101c070350354441d0009902d40c810200c1400c0d210881a00e24a107501640252503590341c0c2018204807807462041e446081c0f00c658046015007081065a008159100303444011080c00c107401c0152410180c1503103005c1006009500740c950340c0340603c1e03100e01d11880c4888800341c40a9800ba01c940079001085501104090400942d141d0002c00da0399422400d20700492252204401a80c0b40910040154800b8500d0700b40c001900c1d4100c0c7e1454004c0e489a0700600d20640b180c0441a243d00a0000035800 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 336633291 1250 336632041 336632081
    0x305060f0f0403030f09080d0e06060d08030a0c02071e090f0603050331081005060102030703170c070f1121030a050d0213030b1b0306010c02010c031728 67
    0xc44e101e54054285800c25990000e00c0b6003480e1101da80030740007454a0740341c1a4650781002c076890010b00403e90003040982e42580c59104950f141e0059000c010520029695100c0014003102d100f000860010302c0501d241c0030300d1807400c1c01004070b00611b0340a002d00560806041e20304800480c400c040441340c00001035410001b100501d10a004007000900306010380041c0d40300310ba100d004c0c1c0204010500c0e0f40080c0020071604401c88183c0308010001c0d41550800d000440100350030110340c007529003c0c492844103a680b00c400050352390080d004043c01751103840385c05400b081a04101c01100c400102c5800c5002d04110300c090f8802125101c807075425420a0080301f64090103440a0a199002034002508101e55504403072800c0440b68015114101c40a040c0175072070000c20f140300401c10040d05c40900e1032402070f00282c280c0d80044402410011a10b0030b070010305114101c969405c202c00600c605081c00d02c10500860313044030440b4550140700b0042c0c0900c0245152007418008030810f218029 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 336634541 1250 336633291 336633293
    0xd0c060509010b03100212010f0311060a11060a0f0b0a06051b0a0f060902010906081509060f04050438010909051606021605061602040c03090f0c0305060f0f04 70
    0x90034010300055155901c03408100010f0340c05114000e404e00b509540180c855450350329030389540a06034040c0000d2481c0c400244040740c400004070942040603140542d44011060040f589020705013610603507401240188007025030f0039000281c0d80c803440d20301444100e06003010030410f0a0640310744408160200f0036071001d4145003c00108034407050f81926101d0600c0d480d04140756000e2141190780f00e80d0750094100715a08080500040c110a2401e4441445c10000001c80030303a064884a01ca0200040000d119039200e090800341218082c0042c019400c10f407038400390340003e007104100490f42d44080c074045d10403940b150f510300e800140303da004d40e40d00e40107802001b852500c0707040e50b031350007010551400780b0740c10ba280e14000c201c182e00908141e02030300d102c10b20091003a00100d2140c10100032501c0329005560300328000c1c580407900010402441c010030b500428a05c0001000d00700c0400003a0f0501000c1400c400403613000358142d804603654201c2000000e90304980d40c1340040801030100d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 336635791 1250 336634541 336634553
    0xc03060216150e1020071514090304091a040e011d030705061302010e0603040b0f07170403140910020a0b0f07080c0c1204080c0a05040506062709010e0a0e0d0c 70
    0x180700455050b00100040045d0031000c034042e444402c040c0c1d903c01c0b922440c1088440c561141e6002070342101102e04003401d010349480d07103d22891068050a035140c58845c145500c1403c078000c03034000000d204000c10299640c60a02a10103010401440c04000c0c6110301c4100011045610391907000f000741a00350350f1a150540382044241e401c2e410403a842d60340800f1510b4007402140914041c01510400d1700e4111304400d000c0c14024402c01c1000703206850100d901602135185900309506007021180c240100d201c580443c02080e9030103a22211041400c0701a980100e020000c00740203c000c5c1001755250010f03d02800d074140c0d80c1300d0010704a040010b44601c0d16070054040d56a41c1404d50b000200c284004500c150000e400407241a045804442c02038508040201c00400e000d4409101034a060710002d482401202100b0100c040808844015005034083c00d0703101c028000d0114207256100d04d8444144001100c0d807005035490300d001000c00401c00a051840901d441ea0703101c0900880781c0e108 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 336637041 1250 336635791 336635801
    0x902040b030714040f020d05070c050601060207241107141c02030309011b08030708010e070206010303050405060703090306021207091710020d02070c0b09010f09051302070c03060216150e10 83
    0x303200d03140e0700b030110787c9000c112409007034003e89003503542c407440d648282041400c0942c103901941c00d41d0311204081202c680c00b00f4403003102c000350002010004904040689030341406045054660080c0e001c04144280300d0504800c008c030003540d021580f007032155403519483c1c2304c01d48042d6040e0f01c103100002d015032240468840003003180e842c003401d101b055038501d442500251007040210344114014020400c00140003175100d501f03480189010352558030090a24880c6004030750281740006681800c1c14000da51400085034404801c42d999590040b041c1c0c00c0c0769003030700c2510000344a01400120705000e0361600d050000030341c1c040c00351503c00a000c42e009600c82c980d1420015028084000070906c0c550b81c0c04010840240626a02d0500300d00040200c040300c07580340240072800c8410b00240e00e07000043d004060882c5ca005a840c961414689540703101540300500c000e00002d1703040c15043e04180030200085c8940300341c12550b00c10085da14280c1d00c031003003e0f0042c3c0e88074001c0c41e60100c04d941c01c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 336638291 1250 336637041 336637061
    0xc020c0a050d0c03061811041b08060a080f070501020c032404020f100e13091112011b030f0609020c0606091017030c0607020105010b0f07060615030902040b03071404 73
    0x1c1d43d00d1550390340c1d6004261850160504901411417496005000750039044c140801c03421241005030144407004601b088a600c0e40440c100480000040c600d038480c188101c0240c10058100ca508501c01240c8076900d0449003d624014000c00c001c0c80c070f950500283e003896030400e02483c80401c00c1c0b08080f103810707148020400d0368803d41401c1d04001d5a210343c1211810700c0c2c080d07540da49828141c50203004000c03080c0c01d00d0415075440d0207169404030b0700120b405018000101c40725200f2000007201d2501420b0508101e81c00b00c11a20418090560161302c440740360b0744034075001d00100d5a2519000308902400551790000d420850018403986094480b00390312038030704103686250a455011003010b00c190075054614070782c0005803181d000103081010ba82e01000a2000303004560401c3c000403924001c020b000940080085105420018981c05c0940a000c600300c04108031911024001c1c0a03186d02201079005a10342007066001c0d05012401c0000e40d05000001905d150001080c04020110391403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 336639541 1250 336638291 336638303
    0x2030705060f1b0c0d030206150906030a0201050705010b0a0f03111f0509030a150f0b04020c0a0f05010f0c0909052401050711030a060212010b0a0f050a031e0f0c020c0a050d 76
    0x3250f481c8942d2145d1240c00d840e0301980c02081e05207000704d40120002c0581c1900e5201d4506003081080d5554005900c1c50410780c2882e0094456905187c0207014001155490303a004c81400310100c0d071450108080c1e0100c0b03000e0446c0d520450030344c405004240741d07600e0111161911600b110260240541d000b01344408000d41101c03042c8066848503890324110a01c071302c5400741ca500b003039040940b41b8010800101c408880440c50b01c10428940303130761071304c042000402040b508218002070040c294032561040380e0407641031007942c18540c401804030368203006402943c2e140901142402d003c9820281940240001e0412803180b014015181500011340488542c20103103080c4030151401e11820701382c28815000507803107407a105840f4000d504140c0ac013001c0180300384001c1d03901591000c0e04200003034460420a070740303204030312048020300b5a0001c2081c104099448180040e006a4130041c00801c41c88020040b082803000101d0701c60420750107242d407080021205000b01d1a049154451080c8111 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 336640791 1250 336639541 336639553
    0x4060e0d0c2303010e0a2904030c0210020c0d0201050306060c03040b030406110f03010e061c05250b0405102a03180501052217030702030705060f1b 65
    0x9036801c021040e40c1d4014900700b078200c100c00c400030241001c145500300300c110000c2c05000b441c2000b903a80d401c820301c000303403c000d01d010751040403421016800840305681c80d541c914515080c01d002d4509514004200d0050240051884040d17202080d02030058078010301c0c09212003043d800448190300f010f0311407540b0034001c1146d646240300030030040008003038001a090301c91810b070505808075036440181e40c4443c1410004000b805441d101140e0549009140c00485a00d5460111b01103c08001100c540316440c2c0c0c0d1408140b110010f50041400c207103c000c0e44d45411860122400036203a882540c2c030014040c00140403a140030103c1e00801c41d0b0519040000d20020680300901030700c1361205849802d01c081c2000281940140c418145a08240d0084882490a40024034501c180c058041003c648401c0100a03003002551080080c400003c40e8960182d0a2078006c3d101c0d4080391080380310b031164020020712810070704251694964030100460401400c0c05800c84907510502c0001d645000e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 336642041 1250 336640791 336640793
    0x4020102030f0c0106030b0a0e030f030a15060c0b010510050901080414010c09150203191d060a030b0306010503010911010f0e0a060809010c020a05100b1305040803090d030c0504060e0d 81
    0x70b00c05810b0401c24840049102e81c511300308482c0b2110003500e00da8170340303060400d170140b0001c00004940740d41103480d1400740d49503110403c00009200c0b44642da150350340c1034800055015804255411a0f500031031202166903a50010002c00d4000302000c1c5022403803c0c880f02d0100e41c090010240d2090181a036a08885c0305136040d6403c44100c414401e02051002c0d40600250400d107403459810317111070004520301200300c01ba1030307074203038018281c4010444061f450001e005001c140d80c4aa041014055588650402c940a4054403600310f1103402807050300c0000486d403034140607000c600d03600001c0315020105440300459401d0103a030320b80b02c21312401c002c9000302504c031601e03444001c0a1566920301103041a4250a080d100141003030300c11035010080940108801140d41810802070410029608400c0703004514036400c110b010b4031095103410104014006100f00461064601609450450400321b81c01d41c03c480310310b404200090b1040c0400d0001070301620b003001c01104014484050b4400da = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 336643291 1250 336642041 336642067
    0x20708040803040e071103070203060c0325020f010e0309090403030e1509031b0105100b1e0d06092315010302040902180120060f07030e0709020901180513050402010203 74
    0x40f6038007400c6580c07544001c0103c903580c400c0e902d03851114900055403509045400080e914030001c2c1480c1500301d000000724804d810340d401051408070a0460003d420320340010081d40b125501540d50f141035082c1244032070704110120445181c998010410081911a0340303049004014802c00c0103070500c18080f0341c169500c58801000e1040103190b0042d075554426120102441003056404000c6038102001e01960b2230407154031000703032655101d100d500c42420000c40100c0b0b08004901800311800002c0e191036261160304008180c6400503024421420500340c03006e80c400360341c10191042c01f8003001142d00da0004092034001501c0502d0098145603c41e201d031001c1741e001c0070351540c243c128207816159558000300034070213800c43c200050b0b1000110b610303c203807505070041500038001201c00020f07681e40d020358400624800722a08588545496002c828025807120f40303164003242c1d02c024440ca81706134811488058407009081ca0300000342d0b44e203924001c2d110213401203044d4002441000e02c1d40c02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 336644541 1250 336643291 336643297
    0x6070209090a0215030103020102030904240602070e0115020a24050114030d0201180209090a080f040f0e01030309050405040507031b1d130b040f0f03030c03050603070503060a020708040803 83
    0x44a8002d001c00145a104100d00c80f0300c00403210b44e4140080c801000541c3c2c01105492591030295404160103214901d4052448070301d404a0241c13402c06480810095800103071002036403100007054440ea600c2d0614481502404094a030041e07102d0f081d8080000c044280e040321082c4015082035020466100c41c0e030a944c000d030480303c1404070417544419145001c1005826400d064002003002d450f1000c15170200004001010b8000c42d080c401064075014200041044d0a411420f41501c13212070312214140d17035200d44909031451000b0b0a0104240d035403400404d04036581611843c0c90140b406007840080c0c10020029030f228044da95000000c02c50801c41d960101120364030001c0d0881c10700700c1000001164100030310301c2c00c0140003044070100d80e049101030290340245c200c0c002d99841d0311740040481400e800003040307083c000381400109034050304002c81e44c10341070310309024a0350758400741542d5503198815140d142d40201c000c07a509070b525500030200708cc000c10411749069103907101c0d589164 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 336645791 1250 336644541 336644551
    0x12070b2805131110020d0c0809060c0607080109181514010f090627021c020a1d011e1101090c0f030b060603040803010501120e01091a0106030e071406070209 69
    0x1100c0d44035500700303c801c030580036098000301c4014560300c00010000b9034500c4d20343c0080040c46400e100354010701085905403a48a003008100a98448030086040d84030301c825900c450128440900104080b039560190003c84451560702030250039680d12414643c444a01c1c120340300703542c0d0701010302040f003c514056010341401c08c40e400c0201d00d4601460b040b01c0c52640310b2203600e51500e0f20001d0f6200300840b00050030110741e0700541c5030810000901c450648540343c0380780e03152002030410b00702904a000414485104039201426200100064561182e01100790004200900c07a2208060007807460600c502c1e8401c0000401a02590318881c17004d500f604015608a0403010400c1003103c17500515078032001c1551b640d411414545e680c18498003040c0101c40c140700045400d1019202543c0c803098802c1070180080c0004c541074100184650800c801998500c511200080364060282c090130181c2c95001004040c1c003450180652a051000120198850010085000940d881c1c0c07044a0140b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 336647041 1250 336645791 336645811
    0x3010c0c0c090b030a1704150903060b041e0f060503030703050309060c040b0703030504020415090207030806040c0905011d0411030f220f0312050a0b010212070b2805 73
    0x1040380c100503114680590110a499082103100a4079450100e4000c01341a0b0060801e0849010142d110a490007103030000b03510340c44d01c2c0307410386916540241c05e0070481e8010f45c1d0800503410440140803d0b90001000c03421002c60076464400c0301c02850f030100710031001d203440c0068020740303880c0040d040d0780c0102d03070a60005602105119048406120311500401c000020500d0646408a20200c0c1e010307512024080c165034600003425521190000c2d202241080c4d80d4958041c0c403064164000c0d0031845098000503200d000140391400c11b032080d080c4000b09500c0d03594000f480c080045450b888100400c1c42d8204101d02e0602564441d80940d00300b03207815040360341e08c81c900294000c0d60b02d8001010070210308299495250409600c200c2100c005401107592003180116080c00e85040c04030340100e00c00d0520740f1f820803001000d03640c404030340c81c00700341d0a032410a1803040006030305004d00036014100c00d0399080842d000c101880c03030b0104404030f00c801c0c03044902c0c3c03030b914000100c40d82202d089800d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 336648291 1250 336647041 336647057
    0xa0c030206060901150807090e0c0c010c0207210c1502060619030201090317071406011805010e0a0203091006060e13090b010b0f07020301020d020409060f120803100503010c 76
    0x40580520405074056820303103e1400ba036140a54a248180e410703001c0700113020748907000c1040148a4040c0b103020303003983c120b201d100381070141c20502168051241c545481d440c0030b0f903c1013000d00c00700d411811078550300040c40d910940340000e5412102403501c00c85410341140d40000e14440c1e201c40481e03541c0e40740d4026218a1605201348040005410503800d541850400c00340010707a0082d68150a4a4000300f5030b100036440c44007006060705c26a100500540d8074040c80303100c034400001d2418141c469031415200c819828403c14010f552080c0035034000180010700280b004091640511b5101c118807089503a90005a0b90200c201c4095810940000c0d20b0782552080b18140301244c12100c0880460400150203079440c0c0980450040c05040d2040b103000419000401c401c5007034405194000b03000319554001e821180000794050301ca07016120741040300000300283c05107001e1040754080c1c1044850030f2410356541c5a5a0300c000c110400c002d0f209032020031642c0f424861803003150030a84034951 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 336649541 1250 336648291 336648293
    0x114040f140a0605030a080f1e0705010e010e19060504020f0a0815070e010e04090203070b13140d08070b06011202030703021b03090a1406071406190605061204020301110a0c 76
    0x10390f403964018600079409008280c0c0000c100f042100c0700160304038810394803540310300c00740c064207a4550480c6200660108103817081c0007043d4000d808148282c4020840c45c01c0e003504060315035560310204039078024600039980100d0002d4104aa001d44024036440c880401d01001030316030140790304004060390180b52101d942c1120300c4481500b00c003150a001d42040f19120000b407005000790503040c003030b40c1c441b50703c0400c40d101017010340d0140404948440e1500210618182400b07494441c94800303451024603403100c2c0c103085030320f29610f0b03410000303051900c0140d4031010640100036190b64104522801c0504001d200c91020310700641da5903601594992889038050744e1201c880440c291103400030040c49c00d840d40c800300100e0484280d401d004803c0305400c00050105d004000029084030907003541603030044404079110b4800c003440c9858440c081c00380e880c0c0c01c04850150042e03540200c010000c070020181010a01903100c0e10060010a642c00c941c4045403503508030250f01c07404240f10401c120 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 336650791 1250 336649541 336649561
    0x120b09090d0908030f0403020d140d02010c031a060f0a0e030102041512060b16030e1e010f05030f060409060e151806040807230d090312030b090114040f14 68
    0x9000b802c0100c000c2d17042c02000c405240c641d02c42da00c4001c0c03103440342480600c2088220120340070042c2c484415140d02c04032104010780a40208121b9078000791810382c0c0030010f11100c2c801ca06141c5406803080c0d0400040c81c0b00c005050b1b0060f4280701c02e00c490700600e0602035400340000c0001e468011410450f008804402030a40e041000c0030340c040e01e0030303c5010310860b00c0302c07404d40f01c40c0c0e001c00c60381061141107401c082d51410000c00c6100d401452a400da0940b044a10f03d220703d241d502a07035181d02e001425030b0215414001690316070303100c0846101190551400f81c2291044500550000804d403070301d10f5400745411404985c9107030b045c82050801c0484000e40030300690003503240028201914050784ca142a5128945006110369000f032000907030100c5c00702c000d0310700a40100031910f0645c0d4090000e402081c083c401250502075260400c0145403080c081c0410112001c1e11141450f4280301c4440f84c54406009469007281c3d9840b40410910064050b03a94080c541ca90b441d101030a1540039070f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 336652041 1250 336650791 336650807
    0x408040306060b0a30151409190902010908160512010905030304061a060409020d0b010f0f08060102031e07050705030105010605040605130b0c060a140907030201120b09090d 76
    0x8000018002e001d015900782c2c1091011101d01d00c4c114001040c41c1114240380158200c901a07400c40300d02d050b405100040900901c10140ca95205035030078981f2200082240b0000110360b69034001c140c140b01d84003040134940011000c50310506008408a4555141d281b0708151501a00c40050054004100e2400d0410607900128241e01c0280b01020240d10f07416034900c001b410040c0142c0d500c09480e45244044001074102550081105641d20303502e440400c040e4002421090200303182c5583c0b503006d58010b0f448804144006d80390307486182d440140c240e907020401001c80c3e055010400400360750a205003182d0303101034281050780380c03a810707a42001b61600721280c00c40c0e4000d0707140c000140042900442a90115841454038968501202114126110842e4020904240c0115000e260590046400d80c1300c0c00c500e80b82000400d500303030700d540707000d5000340c4400130250042d0b901400507500c80c90021180442000c4085035020000c4081020031004070346c0b410164010800940d200c9500c6110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 336653291 1250 336652041 336652049
    0xf080a17060a081b03010902041b030f060e0a050618010611071508010e100806070806040b03120d0f0e0a0b01080f0601150c02300d021906091a040804030606 69
    0x405200d181c240355040c0da450301d500c0c000c40070446011130300789801c2c3d409412407005198042d106110034070b80036581410000d00b0b01521404282810b5503025580c865101d1002203072004028031400d42c8410300c15030001c21015104c079030082030200c26818100c00c90402d40d8000c000f141e0312410703c6188181c09a0611000c1d400000a01c010901600c150b00c1d80612820706448106407490f0003501d40d00101c1001c40d0031544035904a0081e0007c00103c150070200301407041c0750a8500740040700b1584209a140e607690340e42e003c02d8900c281f0100d0101e0081c0d0340000c400c40341d0340708002107043c880c031042840e000800307004941c0c80d400e001c01401402e0050041a03881c0d144903000b06810350501742e401c031100402c860a0b104002c42400c104055507928190488001d5001c8a403411071001d0507641003a58034000541c2c03801e403142e10a0703080c00701c0c070026411441c41082102c0c90700d4040b4960b9418050410124140c90f0081d510100c2121184a02005805544110509961546189011025903800e640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 336654541 1250 336653291 336653299
    0x71704180506060307081018020a030509160b0912070801020a0e010807090b030a09140a1101090501090e100e0108030706050601090510080c0c010e07050a120206070f0f080a1706 78
    0x1e000c4292549402e44e40c1050351804c24015664500600f4440000700354050800c11001300c180140d564a07a0340100b01c00c2000f039909000b960341c0c1210160b0386031401590a5190140c07150700304001500d00000e8040544001c01c0001c852840c400c042e40707803c0d215040000965400500e403e0b1240c0c11000030074a0200030f080485840c600240045e1081c0741910070401d50307087c000001090803402d94007100710642c0c429600032081002c05151a0b980344030340030844000700b407403100064940c020b4460030704850059441c180d8603800c01c000784000c0c1e00301914248044841440c08034440a0700ca540c2c60181c4181001540c4501140c1080c00036594040c00c0030f4107200d080c00090182d070b00c1c1c90100b00510500da0030700c052a5281d00c031a010f26803040d242c0001c00c1d94a0001b09140054000c50040103c81045850700f001c04c1d00d41d0200c1c6150b0040800081d4030150030030a40d00014200002c1821550241c0000c2d1181d445540303a410b01c9a0182c94100d0025000e480c0c040c482e5142205400d0f00b040c4240c13 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 336655791 1250 336654541 336654551
    0x9070c020a0314120301031a010e15040e0703050d05180409030c0303020a121b080c09031e070902070c09152624072319030207170418 59
    0x38011448008540c000501a00d00a0303004294110302000700144034402903040a03038941e96401d10030391100020016550380e040d48400016050713001070b08107004410100c02d1070500750320f54003048000c0800d810043c81c94000d501f40003001c114184030151100b070940d200c0b980e03507004880b1481d40400c0000c014070320492600c8509800b003540030008a00341640340c10016030300c0d888a4401c2e103404940c480c080b20386504103070b04400da000d100841090058442c0c0c45980d11a00c98440c4007905010b1070014641583c0311515804620440d009540300f01c45180040c1d0300c030552182c100b1000d0380d11142040c0c1c0c102507000010000c3e44045d100c0c41c2ca4003124403011010540c00c08180a89401009030320022032100301159902022051103904140d2200004220100003100c80d0f250100307404481a4021851011409460200c140e0180d131102403114002d5140035060221800754044250003101019070030302584001075000c44601e07074107075007002030591518900350115080096488039002e607035082c1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 336657041 1250 336655791 336655793
    0x8010909080a120f050a0c1821020d060c02010504120516060519062309010b0304120e03030c07080c01020a0b06040f020f0a1d0628030b120c09070c 65
    0x294190b0705118000c0c034001a010241d501c024014000e40070800e0107144c17800c024410310800581c409090300c01103841d40450041140c1244224030214801c001c0d21041d0403100c1c50703500c4034001110480520040120390040d070036171030740d004955039411a040580c1d52031052106000503400080c0045510b4a0440d01d0561140860804c543d030211004218586480105880142005410350f103c0d98200041140540c0c480954000c00610460003904080700803680e4458241141128140c44003252810304d1500c55070b440c10107501d05101034408110840000070f4003a86e0520041c4100c1d9407a2008200d2181407180d0507062586800a85041d51b21501c0c016000a1079100c0503980503078219800500e80800750341b200c003c0e11402c00100f00c017a00000d0011801600f2a075542280b40c400503400300c2c41400c3c030050200e24032412440c8044a91a219625030810110401e078128013542e140210300060f0010110761a403c00c203101c02c6182c0c100000424050400740300817903000800c2d140a1941c014a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 336658291 1250 336657041 336657053
    0x209090312011721180102010605040f0209090c0703050f0a0203040e010303051b01020405010c0f020418150e060124030912050a030b0f011709160b030103060506120c010f0e04050108070608010909 86
    0x140e2a200960000794044404247c3c000e5014800500010f0028040014510101070003544110b0344540304225107404601c14443d11415140c0c03150785601c980345003200c5018a0402a040401898110321080002140414028444030700840c441c1e01d40980301c1c03864038483c2c800c0b001859444446607106000c00c000c540e0344460041d1003c1d4002d40d408080301080d00204015050381010200c91108046c11482000581904400002041c5004004904126a200b0349868013841901c609810b981c4003010400709040307019482040074140001c48202c40d5690300002c01c4201c07505c0002c01d038085080185160103028841030140115040c1d4200741044001814402d440025100faa0382005c00007000306000b0003905400224103550305090680c2c406d54800154000d0100315039480c24003022844904100c107600d550754603000041d00c40c00360f20740011940303003032001c2c81d031010020301d0080e074640303034983e84160b0b030183c00004007400d502c6081000180040034107030f02615010f45085814404644 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 336659541 1250 336658291 336658297
    0x102010e0105071e02070f0b09010219020f011209170309010f1b03150b07081c05070801090c20010506090601210506060706020a0305040c0f120209090312011721 71
    0x101c0c81813441040803e04500700d24042d91900b0010061004810204000303e01101a107001030003682202e404140d001c0118420849010000303400c0001a0140d0b0003075070051101c000071607030407c00061890890340b2a401200d01c0305d2038070341030000c0000911000c2d6200380200340e07510388555414006100c0e40c07840034403011080454001015590520700c4c941d0301ca0310031288024650b0131105601c030b415604055401e0f5021b1945100209141c4149804a0015000301489044141c580c024143c5c03030000500040e05110310150200b0400e00e00308600190340300642030262861600008451405c0400e20030702c81d4000e0301a40c10301800c00e82e00079034025044100009605d90b0600072500391640000710326103010303070031009040500100ba0101042d500d5480746101d1401000780f646110f540d012070020030043c50045280384a00c0b5105000036082c1b1100e0582c01a154000b100c1c5001c1d103855101807492020703080101c0103100380b100242010010407481a40c2003404001105c030703034000d00c03150803244 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 336660791 1250 336659541 336659567
    0xc0f19091203170c0c070803091e060d0f060518041a0606070f030903140604050d090f0303030e03040b0412030f0525050708100b0108150604050613030507030b060102010e010507 78
    0x614900010f500a54820165013415178800100c0d8000c1c0d44a4982580740c2d001740300310754010804141c1544100740c111424006601020b0980e502c0d2a00301840c440c0a022040203500540d91183c2c0c0004240c1ca451b000e001d13242d01040d5100d2214101460064081581c200c1000020406102440501c0d43d42000711954160300c011403d0000705c0e14501504c0071400780e0f1010700048030f0303602e0307440003103c000c82c2c100c2c404c0d0f00c01c40c291450350704440b41c1517948a16a0064400e00f904071502030000a0281c1e21141c0500b002c403049034281035481e000b5001e207038400d81151117550800718804007016003056001c0780c85000741c02c22500b40180e03030211201c41c90a01001120181c0d06c50b000c2c070700707011040c000744000c0d0100d041a100442c06220403070010f8140d6a001d1800110340c3d8002482904503803e140640a40c0100700074507051030203041100a8000307182d00070207145050350005c00140f0800c040d034021403080e006c07007440345010400682111103140801035a64104802c102c2e001e80d1004000f1004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 336662041 1250 336660791 336660827
    0xc210c0503030915030a092013060807050d1e1a0f062d040f1b0c080318120406030504030f11070b030c070218100501140a080c0f19091203 61
    0x1c0e0b500e03404c000024001c064400380202e444115081d880e4007804003007508103403013030b130380c40001600102c1104100d40c02b034402c2081c03d801820b82400503140a508402629005810402800c3d0344001c010440c82045c1c44111a400070341003209240c030400e11100380d40100c2418088400703240070b001094194500900580209515400d0a011440103082c0c1240f400310152042042222070300e6080c00601c862403007003600010150940786550b200d10007034420146d1010001f402d540721181c409901c5041c0c0c0494440d1402800500201074003035101130401070102e81e8002c1080e0820b820043c0500b201d1a00d000700b00100d54a10220040c4001841001c4803810400319603030b541e95154001c0c0c2c074099104000d501c51070f45600101b0746d01d44000014080c004c104d404c50090b039540c1006423012680b140540c42020341c00e03c003118205010b00085680001e0408480d07140c03011301c81c03816480340d21111841e0955809416586105640580d8400241545d42c0360400107102548000e440040000c51107204 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 336663291 1250 336662041 336662047
    0x9160909060609050a090b01050f0102031b2803090b0301051011010b0a08030405090c0901080103060b013006090c09030803130204290103150b03040c210c0503030915 73
    0x1c115065010000911034104100b0140c20065141409011090410740d40007480f800003203018902001c0704440c184051b0019882e001d20f110a00c400c140c207080300050207018480a0030356540c003e61940311004030000905280944c10700e000b4100180795048440301c0700c0280014803941c1ca980d9440c0003401c000b42842400401e000800a0140810303490007034210200b40c0d000120500e0020150040d154116900b2516a0b18000c14100034000c13000c895002072016401000401c9072540961118141031501114180d21481c1070005c5483d600c200c1d4984034540d12200c02900010310031000a006801400d002241e86480000e01010860001511603400040480d0440302c42229040c81c16a000c0c2060015205004420192012604001810340d12032410a0304540c442e1203200440f1100c2422001518284090410a500010070031114104c1460300401e0743c00801c40c80c0b003c0503245d0341c504440d10003949840740c0303140b516a01442c025441409500640d540d822542c0084a50b04031071551 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 336664541 1250 336663291 336663293
    0x13080105060109062003040620010c05070807050102040b030f01030b0f04020924041805100b0a12050f0a0c050f0a080715170103050c0906030c010206041202030c07170609160909 78
    0x505c90b8100034091203644000600040d81c0b68102051a81154007605c1c920746003500303000410300742d44901318141e002a00400c8010b00140f50440035204090040c000142480e46501c6803031041e61042e18184003201030f0400400401188514030742d40010b0b00c0b00d081c03c060034036a002c0f42d00380801600a441e038034a401403100f02d020055080100b0b040c4010b1043c0020212801c010340180d212401c2034445000b0301e031100f00841ea0341c3c040c024081002500805815140016080e094075103000304807020700a032501404141e00811103605510300400c440d402c41840d00d01000f007480050314515002e034240100402c0020000305038882180e43c01120405090401d51080351148101d6850b02d0800740044004414040700103211254100c043da13180440b911000201a965050b000b80c3c00c0c016489800010001061000b840e40c007550755004503820421520006810221607401400c0f14010010440300241020072102c0c1e040021003015001049604694040320740c1e05005040c451503c540e1508 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 336665791 1250 336664541 336664577
    0xa0206070318080313140d050d0f11070c05011209020901030605090312010303021c030e0c01030b040608030d050f1501020a03050a020a170901030c02031602091305030a051308010506010906 83
    0xe5980b60b489005a503a0340707400d8a90208520130300c0030940c1c52103032528103d004020002038a81c1650196201c0604040c070220044018101003982040280d84880c04d14801604801c0944007140c03050501d46643c1d0304100004001d24801071a014040d42003008030000b588604c1100350640c1e030030034404039259030380c000840e2a5100300340080c04d0360701c0580000000d0650106070441a0355118a20910b84240400b044064421103a901200c2c1d8005014502d42503000754042c05115202a00115074542d45d40c00e818203540000048161f101d487e10104040c0704607021400e64032002c4031090400d201d42c42c2c00000d6403502e1030500203050080014100344524000c1216982c0e195000103030102c00d501c00295540507410a04415002c01c3c1000454450280003105881484110009032402c201d0240c0030003d103e00050061040c43c8907002e440340c0403400610017400c183c0381d19122141d48806802d1410800001540180d8990341342c1003d00c51660780c000545000c582003464508440c656100c905 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 336667041 1250 336665791 336665831
    0x20703080c160609022806170c0318100f020403020405010e25030e01020d2a2a0602070b1014010503010e070e0d1b08011e1e060608060f060a02060703 66
    0x3001c0401a01b800d00d40c54000c5854607041030300c0c4142d80701003100c07409960a001c007007019200f034011010240002440280c202594030500c1d81e82f41e0071522020400d1003d402141d400304405038110350000b07030500550900780103060040c41c459080034000e25100105000520344042d00c9401c810300b2820490301248260413402072000038030300855075040b022020750000d144a0300000340b24125a501c210001c20102840a07900900c1d4444200c40060b11740300c04808401c03200b81d2940e01c01019200070105a1610140c90418810100c14103d4140036414403210306d0540d01c0b40c9081400002c142e0f001c0e036440300689044841d0001c1d0f08034151a0b00b442619454040490aa0801c0b682c00100040c0601c0411070110f000980180b00d00c607d88132400e03070742a640d590006020503150009214908003056010741c10310561612003100d20364000c030030581a600f184d030005000a0f4000700380326241c6880704031f14000c140e080310154a0420356403406911039000500c914107042c0c1d66607001c80100c21548030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 336668291 1250 336667041 336667069
    0x402030705040314031e070b061c06020705100e03250f0206070f061a09040f0c0305060f01031a04031b0204060801020723150a0905030d050703020703080c16060902 72
    0x140c94014650350740e50800071001580400c206c9211696109903012240d80c20342100c01e11040d035603481c0a01481c0705610740381518061900702a14007140280c8081d10b1218880e03c00340001c421884828419a42c694191290f103400c1002680c0d8034030b144680034030326500e03221324030032402806050250300122082c00103900520002110390403c00e03804042c0100c58030131501004809856000c070307503551410040064001c02685c0100c3e01140000421607101413042041407442e40c0c8a80d512420300109503a0030720450561001030080000b0404407030055a1084000c0d400c91502d6100203044480341181d8400040580504401f591180e411003406001180001c0d551a00380f854a030007882d80000c80810002070350007041d0341900011a050350b0078121200d80e010745456455140c0d00410541104a50600c400c000d5011003800500401c1d200301140d480041e00d074011400d014100500041542805280800805c02d125620b00c6400411a401042c001258210341c80816a100d0f00081 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 336669541 1250 336668291 336668303
    0x30a08150102100f23160c080906040e0403080a0921110304080309010e030c0f060c0102041d190608070b0d020906070c050a08030703021f0b0a03030815061804020307050403 76
    0x4110030305a1458005010701045d10702000c4103000780440140f01020161540d005100c4144032040c103441c42520100100c0d0b0041c4d066602e00001040018176903881a44a00c1c8410308800403c4181f682010916a0042130341034240001340d000e0b40d8209a002c182c0e01036a00300e5a41c11101100184500c0000503000b069008480d07545031201c0d43c03140d482e04980c002d00e000800c421410b040905011680250042000e00804505038018040003841e030007071002c42e06d441d0341c2408002a20280e032182e41c0502c00500668414030b09020864484112400300c0e002020340c10000c0800017280001340d04d40071900160007403074468083c03120308030280c49041841c0341d01c0000400c01e1002e114000108a0468000303c4500100c80d503102a016145d001c0c606015000d80c201070041400001440490200c048541034006840f45580300091000d00e21a0416000665542c0c10003d4200143c4078403192500c00b19020350030301c00c00a03040c910744e0900110060195802201141ca11030054040d10051135100f1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 336670791 1250 336669541 336669551
    0x40e030c07141509130c110604030e0108071b0b0a0603060203160f020d020d0305042d03081f0b1b03040303180909031b020f03030c0c0a0602030a0815010210 69
    0x1c408059042d1100c15203e10a02280300c40240f491204811140c040c800607042080081041c20001d00400901e103400043c0440190070510304002400650302c224800d450b050b10f00c0050b074000400e058401483d400600c12080c44415002c0040800c002199a10090042850b610402c030300703000d02050350005200d80c2c0040305004c070003140800309008100d03069840c246803032000d45080340c1d01c11130040c0302c4000d84c1004800381c0400c0d00c250452a48070b4007410112854900c07084c401c61050580b40054006807542c001c080f810141d01402c0710b90000044850698500c10307042400e000742d4401d201744403100c8400544401003009005040055150400559440d51750302d040203800000b40f06801c01320bc09041501103102c4a8900c0b03060880d0381c141c2d030b540941d66030381c020345030450f1aa42d100f0f030782c068600c02240082c5da130100024503c191a403400b4001a95030301c000e100b440100c0e40c10003000c0d5002880810055944003030a180e1203040070369007028101e41d10300140d082414015129a9030343c145 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 336672041 1250 336670791 336670799
    0x3062112070620250c150507020f060c10020d0e150703060f1202060a0c0c0b120606160219180e06070e0a151b0b102102040e030c07 58
    0x9a002c00c01240300c18110f42484200e010802980344190404121204a661034400703050980074400d0b5a150310540758045081c1d01c2d56184c0b080700b520f2082d044001500020b0006c114184005548041442510482c1c00c002e40c0301c07402c030703210682500c0c002c41c0141c1c08035118001c280190441c1c0c89481452003a10030b081d080d00c3c404070b0290011110000403c0c1055070000b02c50344070800320022510030300c81c0c4040d0844264200142a0303c224040010400070700b07011008210031030003885c010040c1d0020256140c008200c90030f452f420003400144520b0050011031040003140e00e00c0c0f08555411900b980b10004408a40c40440308150006a07144501aa00d030341c0c126031907404400da212420301259091380c1c1c0c0ca0340440c0c81c012070f5404d15802c0a5040d2082005002000c2031350181105410000038407520032030000c4030024046810388030040c8020600030500d0340419618068001d51810841020302090032080c40075480c10001d00a6566038900768179040d092058410744641901a200c030700f61307a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 336673291 1250 336672041 336672053
    0x7021801030311070e0609040206070506151002010501081e030d11090f120d181a1803060c09151b0f1905120310080a0305120c0306211207 61
    0x90000320080380010305070303025a06000030036a0484115106890160386d070071080c032050f990060000c9800c0786007881348200040c000c2c0000b0b0310403144000340c4440d0f45141c10404c403101072502590b0302507900d0030380144619100401c080b1a020701d9850481101e8450f0001c01d8518400c1c13014030f4648602d803800070451003980100031700400500311103c0540c02025020400e081e211800c814095134054440b402619007e2400804101042c0c500f00003555518407480412803081c8042031001c001c0000c0843c05840c103107601d41200391058008118910700b102900780980306084120f4401c205070500380c1c01c0908007000f00c88850107103801c168200120101017560311803042203680405e0107000003440b40d12144000005c1c03403036080300050407400224481d00007a40e0000c1c0030b20528418600b008241d40c0c50070011440d401d80700381c0d28681d8503071000340c0303200014001030908a1402e90410a01915a85000c064542e4900818a007103030a840c44c1c032010700e010408003640e518000040380305018411 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 336674541 1250 336673291 336673339
    0x31e0302040f0905060f0108060307050316150906050f090d0c030303090605071b08030406090b011d0702010b0f0105130905090102040f0b3406110a1206031104020703050702 76
    0x2c00b4601500c403039441c0d02d45081030320750442d601900b118481041490755840742001641190024040d100059280ea0229040502141c0400f1407002445c0c41000b0121000e600040e4509140c6009040c3c030b403c022000380b440c4100c50450900180120752402941d5a8044910b0401d9000c81c0c40000d181e0340f858090701502c030820b02a5016032500000070307100c40c05250064030192544c030341c0105040c1181d850300460741004d00242c4c1c000366200c074070314001394840c000280a071128011140b040c0d22090302054014000900880869040c680c043e01952101c2a90b082c17019400d091690b01c0386240b41000d960041c459100701901d500b0700041c003481640c19030007081036800512410041c0c03500c5403603000292103046819041703003100394a14a8401c89041320140c0707820013810888070744441501e440041d200b0130700c080c2da4416800107401c181c6c55001000103c8811581d8401d000451554441881c0b01c070000301494026900001d21008048c410011107161039030041100c8200a5010407040180c5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 336675791 1250 336674541 336674549
    0x5070b13061b081605011104171908030402040203070e03010f0c0f091805070c08072010080403030b060405030f03040f05060c06060607032a051e0712031e030204 71
    0x20baa140080e8440c901950900c0321941d0000501461300619070b210002c905080001951907541c0c40004c01c0310712011100a100404280103101c1e003090310844003504014402602215650100700c10500107214070003641c0d4000d80407640182c480d0b4030104207503100140450ba90358554a488003580c2005003076844880c91441c1c82d43c80040071219010296001ca200303000b29405d514940c203031a0400e2040760061030344040780c3d182400400800c0d079540301d21508400d20480e008180e884230800604114029600500421504884854284403025100341c4000e00082d0070151034600301e02d240c0e101c080c1114003c0c070f4054201da40100c2d810003550741301e400a02422014003180700001070070307141041c00d03a2420b44144c000342c02e480d122601080040e52120904900f4000300c8400c80d42e0340225030000340100056880000301401c09868070900b03202c0308001c0203108010603040380b2901c100000702ca4054035408034030345014520504060340e1624006007000c081e0500c4025a08501c0d80c1074028204035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 336677041 1250 336675791 336675797
    0x23060913060c11071a0910030603020604060503040204050c162a090603150903050406050903100228050a020c040b1305040c0e07020703020609210f0f1e0d080405070b1306 75
    0x313144c4403c2405142201c0c40740b50814a0b1040c02203140300e00c1e121422035180e03095414001501d0740c1c0d82d03001c03032242e411a50124011420120820095041174090300d40d0000351662010b1038401c50503010210491038003000b800c22468042007511200c140854403800078009100c01d040a995102b072a005082503000c2100c4000110001c41c400b80100c0c003c0084195040e1a4070382000c0c180b110449454004401c0540e0612070072481d00d0442d605840200544552543e0355040c0d0b40c001080084186a09611441008810482c0c290b240e030340815135180c4060225408a02d4032031280000d40c0210500c040c1102e420710340b40502080003a003241510484140d440c08100c1d580e907000e020303601c0b00018840650441800c100e001420301e40705c10400d101503812034002884041b103191051400c00340c030100c2d11295100c149203606a0f44100050000d10041032120582c440100103410744a2104400c1881448003a101040401000340903178000f03001e03403099140d210241100c040040c40081d1242da408 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 336678291 1250 336677041 336677053
    0x6020c0f060a1a0a0f050108041109130201020c0d020603010b0901140d06060207140603190912110111340b1e0f09370501090623060913060c11 63
    0x100e040002d0f05004685c00b090060101c64034000040d541042d005004031100100c1d00302c4142030fa500c20451502955002c10110039100c0103100180c0340102007074916200b40707509012000180d40c1c6508890540b90300a11080c0c0311007507440140c400380d550042031001d449010072102c0c42c91116070700030000c484055084448041da03c026020091860841140e040300c0104001244003421030180910004961400a0702410f551500c1d10020036000e003400024491a2030f14002783e000b4000c40d48409d280038180c3d4642b1140401c220914148040c01c1c10700442c0315100020392000c3ca07030300d0000301c1d600040c05184928020600010302e49000c900ca00c1d052140c04040351030313070000c00c6010f842096020010600c07100040ca040300e1f201860308030f089028001c038846030030500c10010b0f2803020611807000071440c0162480c00c3c90644100124440f16000e101c0c1141410841007084641c00c000c040d503130b2240d80c0e1032b110a5003110000000024000310300f841c0c101011a64008038003c404031480d821307115 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 336679541 1250 336678291 336678341
    0x30106050d031b0f08070318080f1510031707051b010c17040b0703021b040b010203030703091b290910050f1209030403120306060c06020c0f060a 64
    0x70440c04140005400111251400150040c0f024078801c50709004502280c2c02080c03035a40c444c1154403a010803000105081e11042141d08070703200c0303007014061754805030125149485610355903a01a080d44000c00e82514049130620780440031010256400ca1000000001469100b00703440c4c1c0f244200303c400d84560300c000d603445400300a0b0f8000840b416075032f1802202c071680752600c032140042e10b100d44a0004100014107002c102000b40746440c425000b42c840380c00c0e440d45c22048245a03c04980c0618103002010308070741c0c0e003c403c59900001d00e0500041903032150038110154103012034015001101844c02003407a5121159019034050301e11841070064186c83c030001094007503070240a810412564403450309a0040001c0c0a40d03207192008913081000c42d01506104020039200c030708140e000040c00b0300c240480f03c06c45003040525410300740035803440e1903801014901421000350203958007240d17121740000c1c18413030f24407030030000401c0b070b60a410b049018100520313010404540900c140c0705811 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 336680791 1250 336679541 336679549
    0x5060f07080f04300b040b060f09090705041406060f13030501020a110d14090d030c0203010c0c030807111b1305070315090615180305010e1623120106030602120603010605 75
    0x40742050740300c81180c178151150b98a503562000090301b850b40c48503101c00e01d4803064075103411083c0b080c8800002401c0700c81c030300002d00003150f54003981e000f04001c2c030a007003224a440d40400c649901c1c085070002d5640d0142c01400607080d4505402c000d1a95000041c81d0a103a58080d0103104503040030401e4030312159002c0020740d001c0101c80c00044c0124414081104d1914009220800480c024140b0300c282540a500281c02c40f0010081c00d40410b84541c01e841c18140d2010590b648a13007141003049181d42001c045030307661000d03040900d1494201020103c9281c45a42d0842ea41c0304c0d58440a014600340a01301801074aa0307410b0320400140a0200000d02c038903540a080101c3d481d683d8500c1c1d9030000100110703a0491100910107581090b40030000001e8001d125403e04401c4400240c1246031003c210604a500c243c1d02480b48607070f07000d4210024500740ca0396405806c408441d52416030a108c1001409820700e640081c000301d2010485207001c0507600d200900c1014124020081503464400f08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 336682041 1250 336680791 336680879
    0x5070203070c0303030c02120d0e0d08090a0215070209041406100e130303021e041503060501021e0f0d0903020f03010905100203132306070905060f07080f04 69
    0xc2e040c0740c2d00620400119019620109846807644107648064074183d13040b0403194001062851200d079900b600c02d40d4008180051902c1202c10b260607002428480d5a0582d500014030000c0d109042c03c0751007080c040703c242c1c12034150035030141402d9000e00c2d06042c41c440c130f01c0c1c442c0300f480d071580114400100c020089416480c1600d5560182801c81d4a81e100c12842c1c0c80c100f0f06080b01495400c200c2940c4c1c03941034412080a003011522480d030356504104a2000b602441300380301d0140b41c102030007840683e0b004241c17440d00790120140b0014450050514034a0002017000300105e40c0142144c010209500001030815280252401c804003041718060500b2a801d110300604260025038850181000075002150000f41c007e4040058145039100c105a10001980300350b8001c2d4502080705d0304e0402800785aa0101150911030340d05440c0c440424800d100c0c01e601d00c8043c0c00d000822100300940902640c44140c0403807000d54480351100003e01d069600203004004c00200c110100c9c0030754600b505a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 336683291 1250 336682041 336682043
    0x5090c0f0102070324180606090902090a051509010603140c030708060d05070e24240702040225150507020706120209180118090503032e080d030507020307 68
    0x1010f08910f15281c403206101c030f10500c81c100074003680000d00d080406014800b024540c03054452280d280130f18041c8100c802540c048a2110b080140c51405685e07101c1c000d981c0b0100303440012455a5501c62060001d5008850f4950b0251404001046140d0b00d41d000b5441d480c03000890010548480c038815045000454000001071605000911682010440c0d505c03440e102d02d04541c2d88645030300030014000340440746149942e8601d07850010f1189800e00600b18104241d90340301c02c488500340e5260706d074171611480250750000000d065085464603812241c04803040d010703a54181b00035440714540101c0040b01500c03200400da0036100c481602d8415280a180759400802009117803005c00e8484003001c0500c3d10f51a94240900700060300c404007049609507108904038095814210440441c0100b0010842550301c3c02c08420001000082282d401401c041285240c4200402403481c0b40208a03103003060100304070300002a18000012034107020328440d00c091120781d441c602c2c103d03928011020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 336684541 1250 336683291 336683293
    0x30c050a05120c010e0a080304090515010c0c0b1b0a0501090b09030336150a06150e0409050a05100203160c03020a060f020f160b010618152105090c0f0102 68
    0xc0c41d0f800b5800340008070840c40c40a0a01d141d03080d030b1244c545082d038000394004401d2545602c1041000b410300c50459036810801d0034190840c0c0c159403501d40c00485640100805c15200144940c0e601e0516000100900400c00445400c00700910f002d5000c5e00c0803080448044800c0408034162000200030317a8841c0e0b880c180310b0030040e140d281008044040750304c6075420030040b803240c284440000344840b40102a050701c9000c1d003418044260012914180d001c00b064500c070032031101a0f964440d0889401c4c205c1182d0100721042d0700d0510034141210700703c004005110b4407841c100004a69006144030340c0c1191074600c281c040c0301e50152041c00605000030010b8111400007400034026603c0784440107880035005003050448000840707980d0048200880d4076484040035402c210144110a000d805546003c240c040c060108450080b00c280c010003042510200c3c811503a284282c07007450710080d040955807010032150000e00c000b003809803190560780c042ca2203411200e0a241007580c08080c81a4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 336685791 1250 336684541 336684553
    0xf0b0903100203190504050d0e030715111e0604030e0a03030503010302040e0708160801051008061306090b0c040504050601142205060301030507180e12070f020406030c050a0512 78
    0x10001e03000f0342c001080203400b10300c0700b00050080103603485128402c5104100520440d40140005030500082804107440f0340c0c0103150a0108142c1c45500d00302c445120b040542251080400ca03c0c10401070300d10300c0c440389903240a02450300c180007980300c0c002d50103500e03030742c84000001017442321a02070b500014000c070b40c0030001080142010b82c09008d10448220aa5a0485c0c0320281d46040480c0101d0301b50303d0080404060007018400e1241030342100811032900000d0303140500751030702d03084014010024a000c01c61400240075054001c0320009030b200c2c0356400c0c540707070070300c0020b116810030b00605010304d2809000800c654080c190344480c020300003448504200c20340300c10100301d14050849070b00d0000b040c4c500180503100d51000d14007070361040016140c51030814031110340003610701c14084c994a0512070300101c0600042500550b40c41d10203a51503a400315400c009442c200c61000007504a4988400001407100c078503d003400703480040b114012442d035583d080043c20010031415007a9a000a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 336687041 1250 336685791 336685813
    0x110109020901033e190302090408090613060504180203060306010b09130207080d0c08010b0f0304110913110d110609040b15030603010c08251e090f0b0903 68
    0x580300b003540081c051180764445005141c00310070380c10120001e240c95100c220325140c078503281c40c8041c1e1480545c4a00080744492441c1c001420300e00f40604007400441c030014200e0f4054440000f1030300203000d00d43d81c0c000000d6030703003030001d0141c0d01c00e10034482e02c1d13008040500400c01d041d00840703005400c010010312541c3d09181000c9255484203461940c030080106902210394154000b814546000c5c0c81c43d80c0d1550790b650101c40549030025007010420100c08018842d84943c0c0050303504142c07403c1009910783e44c50307103005202582c02c2000c080e44041c01100308030024001c0c0c0301080030780b0b01c140c4c002800baa0408050102628011500502c15815440744203a0b90400c4000f9000c1d48c40010008906c0300d40d1080030404407081d400c03001802040c004200070081c14240143e514003201c920b08203401c3c1c80d04025040300a01002030034014400c0c0d00300500c21491080344c00707518020b140049150b8030103180f00b01510b034402034420602021000b4000042c13a1100f081990b11a404c094054070f687c05070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 336688291 1250 336687041 336687053
    0x30911040e0309150d1103070903060e10140405010e0d0f030f090206070b09070b040b03181c11010e0105011202090702030d15050102010e0a020a1e05040507080711010902090103 78
    0x41c20303907000c80c103101c01d000c00b0103250355412010782142d07200791500d81d07103101c0b40c0340c0c442c155058030401200c854001c00030710403119402154242244c1c1c1002c0000740041c54502181d003080c03c40380d546481c050510249400b900da003000024061485440200000d920200e40540c40d42e203600701c3d04000c90480d00c05901c846000703030040501e40b0900700c0001403d04496002803201d80011b4001d40b1010015410003141c1d440400c600000f40ca0198103082c01c0500d0075015003424032005104920102841c4084941c03018204082e8444c0c0400400c004030108500c107000300982c480396180c0702103600302040c2c810100f406120701d605071076400b60351207202c040c0fa80a01c034071124003070708840071444100710704082101284101c9086030300c03032840c1d10360180c82d01000a00751001b003509030103a500107664940050f504d4044580440d003c03003641d000008001428829420140e512054000e401d110170828400e500203d40c1e031098440c2c0c0c84803044180d1041a2608988204900a411a180f03000500116503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 336689541 1250 336688291 336688301
    0x709060e011e210e03030403110a050604080c0c0306011523090d080d0204060f0306080c1e0a03170a1b08030705030c0903101b0e0303040323191203091104 68
    0x43e80c0742c0612549411600c443c08132100001c03050011741000c410b200405a1048140c070038a0140001400260155107402e900d4610240c001000d011000920343e0000da0306100b9021946001001e5030241d607520003151004130780c440707481d000245112601401010302c503041340340707104428160141044910014020b04042e4800250b42c1290280042090407281e400284085c0c50b00381d50798280070304841d102038142c1d80681c21110454101015141880c0c446001d030380f404056074120504088000d07404a0350b0004160000351446225045c0400684040380040c07000b407a855688020a81001d60440c0710110850b0004007109010000b1a007141e00c124050f40e04240307a04280392904410b00006403401054040030641c464030b4482c0156100d4010540003032070720003400c000180081100c002926442030f4040203001054201c0300358004092a82081819040d840444200301d410051148031075100c07100842d01c1000d40c01100e03e041e8413074040c5d4000743c3d611584020031080b8510070000548 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 336690647 1106 336689541 336689567
    0xb090102011d06190e150105090106030905151e04210908030a08040804091410090209011b020d0204020a1805030c0f060d0f050709060e011e 62
    0x501083c0b10790f0044074240d01c044414030594403c0d005000d0000041807900ca411980c0000a15000d00a4103036002241d500500382ea072050200c0a4544641c00104103401214034100c400d46640d0003140c02030b03182c08030000417545e8962844201203080341d09407040c1b080c130a0010804004100c080b07010010380d1a05003070b014105101c0da07030383e031180e03034091420041d001c00014180070101003600c1c0030709084c100502804900300903180388410705071188940c180300c624000842c41a41d1080302d4500350f040c0c5500307103c00c3ca83d003039058400b500144140d07004021202241e005070345501c003c007929119034603802d80100d44413040250855007a0803c6010f0303406000c400e602680c0e4600d00d1841c1041c2115404c0c0d655100c00f6241001c0d1075010b040c0c00c6854280006d000f40950401c040f00242c90f019500c0250340d8410100440702c040309882000c0018802c82602401141303d00c1c2d8140d02c0c4 = true := by decide +kernel

theorem cover : BRFrame.Cov 336510791 336690647 := by
  have h0 := BRFrame.cov_init 336510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 336510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 336510791 ≤ n) (h2 : n < 336690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
