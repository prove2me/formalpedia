-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3576
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:04:00.736668+00:00
-- url     : https://prove2.me/submissions/b2e8ad90-5ce2-43f2-9490-b344426d52ea

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642985611 ≤ n < 643165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642986861 1250 642985611 642985619
    0xa080c09041508160f21050102030907080c1504061d100305150108150105070813080a020117070e0d060902040608011e060509040204050c0d09030e10021c03021602060301 75
    0x2e00a81e06100d51005071059260390b040002c0c0c808500e9043e11060f440c903500d42030a04290510a44010304110031600d81030701c8503000300e00d0a1001d03500a450180280841c5464660810320b0000b01c038410382d12601d0b000440724201000c080446003114a107003800020680c518503e00301c3c010b0102c24081e0401c0303020400c02c0400d07515038066841412448810480d0b07004030001103c01400484400d01440410204a50305600450241942c680b058417224541441000700398600080742d44018865408403910804540c0c02c03140071040f04c2400600300810f894020802000c040040c140c15020340e40c0d0111140600041d40c00034a04c081c1c014100b07028076640d803480d0314000c203001c151880600700e8074054040c04601d1401017078201c23080103206156945580e001c00c4020100504443c84510040240302c0414007a8060100d203540242c9900800344040f00600030025184944001113401080300030502d003082e84128080d40c029841c0c01a00c8103841418a10807800f401d0010798802000f200000d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642988111 1250 642986861 642986891
    0x60b0d270b070f030519200f0408010b120712030504121505010f0503060103060510030c06110d0813330501080c0906030d030f1b030504020f0111030a080c0904 70
    0x1d00501c0b0726510a545103206440450031181c0985400d2024001d0398007031a1882076a0f0424161035444131041c04c8100d10001d030482640c2d00000d82404112030200d070030441c41c8800c1c4030781c2c42c02c8001607906580f0b84550b03800c0d5584524003405000c1140945010680c00d0500c50010344000d000c40a080303085000f5503007840442c074810f5100d0111480e0400001080001880c103c1d507040361000b6004000a900b16510303040640340c01442c117050306140c410004045000030000800901260300c030240002001104542050f00e50381c0c00009010203101804910400300300394501c10f40c1c00c982101301c2c800240900414840501490385141c10039080d4503400b2400950165049950b00800c480140700b0600500080d0340c4202c078511340c0344d00000d801c2514a0302907003007416042c0301c0b02070024400c403c3e5001040303c1101c4046c1100081d0741c4d4000c000450a000c00c00d0000d9040908118500c0c407039065010f541e91241e081078404119403000819000300c55902076500344000204103000c0a40604921 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642989361 1250 642988111 642988133
    0x2206050705121510080603210408010c0516020f011205070e090109150b03190c030902040b0307030c33180e010b0412030216030305090a09060b0d27 65
    0xb140b1641c100101150100f8403000080075071540141015851106800d8207071007901000782100d4050141c100d8000c501c00b40c500c207040040b900b810005485600f0203003468211103500c1400070510400b0007010900d104c490704800321f01c1e6811954031520340681c100413161413100c0072031080e0311401c1c4810b001040c0e030801884c1013640b105454921050307a80d40c58410503128980700a4042018505003840300845800041d548007103801e0b42044c1c00320707000c0680401c84039a41c0e0703950000b035541c190b00070441ca02802049040d00b811402441018110744235510481031394480c0316032a0015000291b5043d4a00c1d011403401141110740d051840720040e0040c001d03207100030010b040d080004002254440400b4031980c140ca44805c0c01c14101800c00d034a0114140801c4829825842503100080401e0601894180594801c3d03440c6070f181d54440c020700c6180c040c1070b0841c1a84078200b030070038030090703804000395428948941c001150f0b042d808240710381c880740c2e16010f0b0b845510807010014144030000000b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642990611 1250 642989361 642989377
    0x30601032d050c0408060103080310060f1409010e0306100617010e010302061b01020c07030203070605070506060f0d0c030f02010807030b01020c04050c0f04300b2206050705 76
    0x30600550401c80304800c6201c080e0010303914504503188141c1e01280003680b01d030f40d0010081406a10b0103444181c0f00d440c0a409a1003111101400010490810141243e000c01004a03081040980c094000090308002100d1002c02c180c44021810800f643c1c0714458403d40801c0140654220741441810f0020b140f42c5030190101081556501d02650150144036504a4541070001a126400c5030300300201c0341c0c011440150303190300d0710610415185080c8010600d80c45140c0041c10142d14601c140350a00489501050501400f0f0188030b0102d1400f0480755400b0000311501c2c901c07142100000b40c110784103164068445c00300b43c0408810040c50410301d00040d07000b40c89000c2141d4500340214252002c0d04902e500580201050448508140d001f5a8101481400c0e0703d041040d83d16007000250000da001e280700d11003801c440c2030742501c1420000d01e110107c45040501d028030340c07252078031000042c005410b03103081c0d20000700703848030541010810329900800501543c18030300c100030003581003d00b0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642991861 1250 642990611 642990617
    0x60603060105010504121401020f040e0f0601051804150306051315020f04140307050319230a080d020c0a0c090c0e0108160e03030a021507020c030304030b0613050a02030601 76
    0x3002045030742c010400d450454495441004070406559568800e1a01503200415250b4092007161440b07070701c54014001078140f11030314040e1440c150042d1001640058403050501200f00003c00745000040d201e80303140d240540707002c82d02c0104085013200c00f02c126400904410314160034890550084600c1c00d0800e800f07514a4410440000c001100300c1c80798240e60030340080100310030043d0040e02a2034141d4042c00509031200300d655200400d0400b03074031104200844004000b80c1e8100188440c00303a0070b404441c0c0c2590045440384c40100d503107540190000d403912202140f4448174110302d07011a0007100030322003a600503100c945400c5103401028021aa422800c000c9075600307462040340c06012030607050352909600d407244955112030741010141402000108411200940c804000800400d0002e9005060a4945400110f5400009840c500440d0803e9440700060ba5001003030703c0c1601d801c1441d1780070a46803100010418005180a070b11294142401c12040c0082c03036014520030388080e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642993111 1250 642991861 642991873
    0x5011202040602150c0c1518010e0705011817101a1e030a02090c0a020712110613090e0a0c06050f03190e03070525180f060b0c060603 59
    0x5860000303030300650050703400590080c4483c0c00592102c9880c0358001c20040400c03841c050010b0304950038410001e9280c24120b50300d0382803002403078250165880500c0c001000300b0559208000e469100c1000f40b01d110b0400104c2c49910041e1403014440b44000c0000f88007080540100c044504d840d4400d000b0017560039480d00e400014520442c3c0620b900043d8010b000c003004189528003542945098101c0075051710481407480300680740c50710b07010701402d13850a001d5240c03480d42d18002d2a11078290062840441402e250f48002041c11a405800e0301d001c0340c0c1691079100b00c0a000c0321142f920341c0300414072814802d10049080d408181410410b0007a80d9403d4800c1e1034001c15074162145140c0142c4003001000099a044510010122401d4903050040740105074403408514503082440d060b942ca4200d10002a201282c620407407400071030801040016a1400a44640c000410380111071203036160701d0f268515a035141c0c020005030181c11b100307a4a42c00503001e06039480d5001c85145000380701d00 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642994361 1250 642993111 642993137
    0x807020c150319060b0708040e160f030905031e0712080601020a2303070321140c0a021f0e0609010e0d0c1104110702040c030504080d1104050603010308040501 70
    0xa92a40800e001c0303403098051454480c0703a92403003e0210f180300302ca046561100d001c2681c041300c50007405801d0184004503140d03400e040000303542c520090f1516031300850034240354445541219250b580e4000728240001c0d075400718140319085100e1a891030b01c10040e40303d001200c0003420000f030581a402303110709142c080c8828106590b4118140c9119015901007000200051a039080d5451001d1089050260016881114500d5600000000c0303020074a445203110074802540c083c02d006844004052241c1c104010b14555000c0020b445001045000101d040c9060700801400003101e602d0b035a40d0351161081d080080c02000c01c40b542030898010707600814403080050041141002c50640a800781c0a4004000e880900c021042215240701d2910032010650f102c3c4144510b003009000295039034101441040100c510f50003c19003418980f1040c00049440042a40c2890ba441c400010304480c0c4040c04424600440e846941d205000000100810980c6805407084510030b88800d075244c400c07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642995611 1250 642994361 642994369
    0x106090501081606080c0703020f060721061802030c07050f010f060509040203030307210203070f09051804020f06040302041802030106061707030507050912010615090503031917070807020c 83
    0x70720541c40045d4080c000300700d4080d0a407009045291003401140c0b80ca14507009803900303241d803c58810f008103515030046400c00d00080c409030065040c0c0c1d8030800506050801c403121007008101920341c5654084000344080c041d200407922003a41140803104070007005c1010390301034001d455401d245541000f90015a03401c2000005001307603802400395003107503034844003150080022644000c5e4a60703410201c00000425100071030003074805946040480b22198809826161981c4c45180146440d94086000781802e40d2078507005507040b6940360003804103100081076800b8507080a03605c02d10705040e10385641007441401101e0380c401e0300280712203603840d1000e039048a00081e20f4585612040002284503119a1243c2e5110605081442c1460360714008201121043d03850310b40700307070340d201d000b4801c15000070300b0764040c0402803500c01034190030140407903100c2c0140c0c9001072001d5148400391540501030241140c004c803529a214130513140c442c1004080c24004d450850144c040c000c00c41116040c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642996861 1250 642995611 642995653
    0x2d0f061d030a1709070f06020f1b0d1104021e0301030c0f03080a2f0a060f05070504061d040203280902090103120903051c020f030a171305010609050108 67
    0xb910346032504001d080c0002c40d14203c6004050003054012070502007034400c204841d0f0805000e441e8014035054802d001c045182c910382c0001d1022401c0040c41c10110b6039225800388910580c07106840c90502510400304010b8040c000e410040c030210002c0b15001042840c000e9812a0701900d4404003e564410380c8005540c5140800f4055400030020140640d00400201522a0300d004440c034091842c8140b80d03260400bc41c1c0454080e82050201c402444400c0c06014111a240c14003045541446100548644a10b115503030601444002c440840c40d481200c29000ca24040c2041d59245040368000d1541c0c141c17a24651500c01405a4074958003580d480703010400c0c2c2c1d010740342411907400d50b101c0c1090814880107180800005000210000e1700a0081d044080e04a03a80f807804c42c4660300029042c100072014941d807507070040c000840c41680c403900c03810b851401541d840080c2c0e21010301c0c07001900c00c6250090419800c00400280d0750259600c154101c034405400ea40d030b860314680181c0c8407a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642998111 1250 642996861 642996877
    0x50711040b10050f13150f08060913031202030a020405011806050418020c0f24190b01021e030a170415020a21060815042d0f061d03 58
    0x2c00d44600a45150b004200600700011000352940c00c0169602201400340138030380004850100051010000503081151008100a82d0510715828039000b030105500c000000d02d400c0c02c852104c4064020300d400f803400320100790701000c0159524940554540080d5000d441000e00141c40503d03e140c0300381492400c03009942455844601d01444c0100b028201c0c02e0241040845503070030460003244180400c145445a03e5250103000400c041e055826110041351003d41105118241004402900d03444802006c480000380001c18115010040340342c61810304214140f00c8042007400d00c441000070240c1168800f41d03585102d83e10380f114403c091407400340c60003000c01516800500410000b6000391907041c000e807a2191341c6220b6050b104070500400010304a01540d10340c801e000c0ba800c103000800c01c3c07100c07660001d241030429584104005001c0303454030a2165000b1860003241001600300c3d407041e07800203003144007400c9a05101d40207000040c24500aa80c0011344031861303038401300c182c96070740c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642999361 1250 642998111 642998119
    0x6031e0b010f06021b010e09040c2105034801290108040314070807150207020a210209190b03010605010207120f06110a1205060a12030c060c050711040b 67
    0x1d20129204034030300703d050b240305d07043c440c90641d41005501c1c0c000c15144103a0043c02854030961800c02c034120001d200046849108030700d0948040403510020485407450030700b841e007050020007440c0c480f6504000c00d40c00070410b0209002c1c48000038000c409803001e001804000c020350115100c1003090800e2010503000c0402034240c1c000829805006070715800340c000d052900708440c10103900e003502e610007001121070314030115403e000e01404500c0c5070b000d51030b0021f0171458040d03c0e4000032001800d5214030071144044000104e00b080307a0002d410380d05030340509048094100f802452100c0380c4000c500f10209072814008030020700e4140118022a401a0040c080003400e145605e50900e0440714143e59a10148a075030000408a12400403004c001c00c0c40039860701500f12004182d00c259000c403400d464140030070320100b0796900006a0440756601004040c80c00c0c2c9140694101b148074401401035490034207010501070f0010001d20500c0e01c42e4040c400007a42881c1000704a0305030403440c0ea00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 643000611 1250 642999361 642999373
    0x3030a1d04061a070c0f1d060a12141207030c030f09051509120313060210150504020714010507020f0709151202030a080408030406080f04030c03050d06031e0b010f0602 74
    0xd910950f000078200356024400050b000c64a866828403444226401440d0306046403541c1c1c5030040760120490340003001240c82440e51b80c50840640714442e51140041c010b080c0c2100e0b0500c40010030003070702c0c522180b50032032980c0759219401c0c00352507a0701a0605502042603a0000016a84288130b071506984004241c00400048000081d61580014120b150844c020300e07050441144208040d140249030381d41c0e000e1725036091800090510340359a0070894040c0c02c203910f440520403905102d60644205550050711004241800c0b800e4078070140d50114503510b40380c2801586903010464403000d4600008455215a890b21010111456072000f607403a000501001e01450a840b019042c1607400102203070703940e1501d40c54490984d445a80062455800003408000107608107032425445403265403861049c3c94140c07000b41500000d81001410007a00290403070280610b50b00c007501075030700400e404480808200c0700b0a141c07801d8031019151041460000a0801e4484203200300703582e941c1d800b40007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 643001861 1250 643000611 643000649
    0x6061e0305070c080f1b070b120a02040b0c0c03060c0f090d020a030b101806030305090f1c0c0311120a03050304020310180c0e1506130503030a1d0406 66
    0x10040070042c002d00100a01c18044401066400c1c01034810b41c170040003802da84042080504d0300d041125180f40b0f0340c80e00001e40070815120320320191001200300443c5807640b0754690444100030700c911380040b4280301020a4071282c41c000015808041c90342501190040e40ba84d0b07c54a00c1d6010711040501611010031144002c1d09200c42c0d954062440540401c8002e038480d0340344103040c141200c4201d40d13031a211104100710000445d18244051260004001d00c50851310b008200348500c4d00402d019680c07400c00180303180c4502d542c0b8020301ca21905800c603184030519081c403141c54207110a0722041a014403418091034803120000e07403e99217000800e9008003c0d901515030b500000c10590741801912040c010062443c0142800c0c909140d40324402f50210349064000200c0da6084010a031000b0f0f010003001c20310541c11407410785021a0450348031050b5400107400001d8a030825a05400042400005290841061104104406c071007900225441c1d044c0412162244106074440d145260700e01c07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 643003111 1250 643001861 643001867
    0x1b030f0810120f111206070306051005070b070917010902010201150b03010e0703090515010e070c050303060418151d0610030206180307080708150c0403060e0a0f08070606061e 77
    0x8004644141c00c15030b901130110001a601c08a0742e441000303140c104404000c00740e6898402c05018110885145400c0a6100c500070120300440f40300a1890700254045404940980030760030080c00700740c003a803d00002c1c04d80150f010f004001c000320702560815050045100040700700005440020031128210ba01c1c1000f083c8a410026040c0c60a15549501c00008143c0070700c042c0d410740005201000041d490030700b0301d00128500134281401c100700c0d0031880001807808030449030406801c481c081800443d0324440c00c090350b800307070009000300b00240001d010040107801055149003030003600040301c418071040546070a0100c4100c0b0612261910a03c018a0007002030400482c21580d0f42d0980d0703242d0340c0884e182003056000303071070f059114132403c200080040100742184850303081d14a850782050040c10f54240150f001c010503c54540020420700c0d10100f00c0b60040d20b81195504045600070301f04450590700981707056031514103143c030101d941c5015464402002000700754034455401c40788030803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 643004361 1250 643003111 643003133
    0x23280602030429042108060405061206090d02010516020c01030513120207140303090f091b040b03091c0f08040c1a1201170706030207031b030f081012 66
    0x2c544200c050074200c3d0240c2200c050781020320406403a0024a41000d0030402034545000d03012040c0c4000c00702420740300d980e2013081c3c0d82e0003050940c2c01203041e40701e0f10f000403d644400c0480611900c00c030020071500b041c0010b10360f11080700c9900200305584508800c1d0700c031000d002c0a1074025910201c46090594800e510660b80f01080304007645080300c2c90360714180c5d550911071003500142c2c0100c2060000800d40e0f48101c4019108400031403810b03426102203060441ca05414611400000b00003d81c0c0381d64040c070030240e55000d0311603c0d50752a04c543d8120b203190425540031120f840b6100c1034030f00c007984001c0410503200450700d46190404103d00211001280148100c514291003540026107007444040c408000301000a11915840e138001c06d400c100c48164001c03410044040b5410108100c00325030360003507811034a405079503009182002c0c2c1c0d1515140b4405e1401440c070740c002c0300900d07602035051400315810707640d69071268540c10410034200c0110b000c0c40759905000303203488002881c540c0d19 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 643005611 1250 643004361 643004363
    0x170c0f012306211c030b1e1003020c0a05030a02070f06020718020306150310061e0504061107120c05031015060f110d08040210020a031713232806020304 67
    0x49654400c44280070208020304c0b07031140004a51200303500006840d004044410004c0c1c103d0500040c04200e00c005030101e60034920080500d50300050207850150140300c2980c8160300101102c0c1d641003404002955600c0e00e00c14540d1081c1c15400c0030030040e101044500807160385004a200d182031039801500254400707401c07194480d158844040ca506802c40103184903910699110074140d2820a02500c102000c010554000c6410083c115a00d41c001c0c1c07e84042e9101da00d06040c0c1003100e03049403450070030140c002240d00100340c1903c00403c100d00702200141e51060b001d44000000c8103540c81c040d1486048a1250000d4104050081d244145600c47c100c0c005407602c807041c00010310190b03003440d04031018a000601d0b82000c100a500340308011803502c0d4202d100501e010380050701d00800307124802e192480c013641002c0200d400b6800b611140c0545a410500d005c235582505222040500d2441d41100d01074003900c40351208078008100c4104007501035062241044c10659600f000035400200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 643006861 1250 643005611 643005613
    0xf13090803062b060c0c0c1413020c120a140f0304150207051c20060901150e010b1612080603061b0f1b06010902040608010f060c170c0f01230621 64
    0xd6034004100030000c1440107020803c8400408c0200000348040300c0000800081850b00400c14038a8102c0001000c24845003400c50094907030801d00d40441e494907940c0c41803a01058045120f4076071000820003180120701c20021141a6195064180240d01800d08041c0040c2c0000b004005080302c003417080320903082d5514050307541508448000b03640c1c600000200382d039603010004210100381c01744260555004040a2400318038034258607050641070500aa8503008404510301e24104c5180d020100f030640e2054444190204c0b160008103805000c0307070f800c2e2080c403410300811402d00b05540c907110101d4a48005a2800c0c58030082c07402e05d9403000c0c140400903510700d070235039055040501c081406016038100159950389000001403030500c041c0c01c640064171480030708008480e003245858078800c0d8000845140e003095510200311500552000d50098014000c5c502c854840640c00707010000c100312482a01e224081c0649011840c0440d807968010240c00c40c0004400e0900d0710141e400800d0700 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 643008111 1250 643006861 643006877
    0x14130605060f10020105011e0e010902090109030f0506040b0a051009110403020a0303020601090c03020a0c06091a07030b040608010e0604031107081501031110020c0f13090803062b060c 81
    0x10010504041c8030102c43c5005135981c000605c0070b901010081c249044a21070742180190170980c1d010300e030080c10f00c0380815a65000440a00a90007070320520b00540e00f111152612480b242401901d907070080380e0440e10484a5400240104501e10a80d402180a8003005c9092400d04160343c00500c1e8400900c002d041c0f040c00300100507503e11f24a207000e580329502910b0a94034101c000c0003560202e00100007810b0062056400c000e9000307000c0844140c1044022850002c981005a043d101c0c1d510003401d00c820100811a84603010b410146032104280c904001c11070307444200c00d00b00c4e00c1d0300e03e010290340c00403004240401c0c400c500705140704031600c06845000da0b0301c0204610304840c1da0003801031030114400400502407a2900d4400082c426651001104900300000351100c8105800d28403034040d844881425071101040e13034001000b4102e041285c0d003560300f08110070b908210b038041d2140301d40c081c15038500040500c0b503200580000760890300071032240da01c071000ba05002211008002c510 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 643009361 1250 643008111 643008139
    0x30f070221070e0703060302090f040f061b0207060207080703080903070803040311040e0d09030326090109053018030303070f0806030c0a0b0a0203130603020d1413060506 75
    0x65240120340501c420020180145407030740c440320350b0744010882d60525150540810250700c9419906611a00040101c1f9803541e9629010808009049005d41007074034112001c13070741580c40c00400c0c410008603000c4400c020b070784002c01c0b03944141a0064941e50341260f0350410010344400e010301344400c0c005040e00d20582e2170300c2007541385401c0780e0310507150503618001c0c865113800c080c030072001d400042d040039190014440001800a00c9944001020440c10001665007000481e80008400c90104450f003064100140c4840c06050040c20a13a0207010300f445204080001c03003c0405184140380c4500380745160b940302c0701c0042d009810b480c0c5040c000700c003104100e5030b0103000541c8516030940712450301c151042001402e1842c0100701c03501a500c181c10b075440c2551048220811104522070b003650b03982485800700d04500590599140100d401840800c00701d8141e0098078240d0910002005400981d00e0148407440701510000104103051440758003081c420703004942d12810240c45681e11a6031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 643010611 1250 643009361 643009399
    0x15140705010204170615060901170406060909081c05070903110f04051e0109020f070b0a0b09010f03150902010e1212180f0904020916091e2105030f0702 67
    0x8038103845160411000c100000d14039411606c10000300b0b0328100d081408500001e001c0c80c014009000e0500c0300c1000040400036641c1000001c1c0a951000740110341040c40c01040e981c01440310700384816034840c1c00640c008440e1040520480540d5503240f106842c0d503c40c0e0a0100036541c409800400403030a150050300d842c082c2c10701941c1c001f440d9100740c5c200804441484c4030183c00c4034200c240104803030300054084000381c500464102000b0340d142d8544481c04401800000b00140d0054855000020f5290840d01c0751400c4a01690380e52101d80c0d001c0110200b12045158000e01142e09030001121034103154485d10b13814015201103400c15060a50030705000e07004032403404051a80d03907200300082c0c103200c20f00000ca61815240c000301800c0c00d50010740b00080c001c01070303404880341c80aa00e1200b0701c01c024907801020200301810a00703d508a58075905091401540400c03042201e940e019045461180c81d00b180d00305d0301550070180000001e42c0c01d68440001a64801c14403d881880341c21 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 643011861 1250 643010611 643010639
    0x92d01020a1101140403092304060806100801090f0b04140715030e0303190e0a0609050109060e06040302100b130608151305030f0f220e0115140705010204 68
    0x1e068403000e015901000400d0f0940305070590404030352000c5010710000982080c100015a220290811003603807480081400c0b401d84008000d92041c1001c600158045012850f81d001d400301405141803662036140b4203003600d02090004201d40b24030690b50000c10707400d0302c0d0542c01034410f4401782042030701c0032281454050280c0201d1410855050003a0040e600351207011046100b42000c0c6003076140041c08201e505200c3c8180d0481985c507030400740e1030400188020ba80c0260310a404100196860405a00a00905100302c0d512403070201154004480003401c24810b80d89507006201c2056400351800c09444074902c265000049001300803c5100a40250405003c56030010106480c3c00b1a4098440a000e082c0d0030300041000c0c0c01801003074010080360291807800c45040d0b034079520842803240d03071301c1400411a03510042494451203006a07240407011600c039200d030300320142d0b291402070707003842c0104210401062194464401c1c0083c4d400161000d0f03030041c1c0005042650711064100104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 643013111 1250 643011861 643011877
    0x50a1704050c040507030614100302040503060a1521110324041101030b0618010c0b0c07030225030308060a0302061903061505040b0702040f11070b0609092d0102 71
    0x500b0803041280641840d00c41e181c0e02086503d820b0201030b1800c41c008981400340c00141c0e0044d440d02443c6e900c1c01d4041e404460051001404403a400d10f041c580c000c0040c00b1980e842003039494008000200d00c0c01c0b88480a0300e00e080700d10400031000b8203540d09040c1c0e0454125050f014081c100540c05581e4841a080c41d00780d203101c203031070400c0c94903141c54413a890b103451801d410716280c940c002d245a141e05094031050b214024801c54811094030040e41c044203180c02c0201506208010400c4003881803000d03291451294007207441c1002c1010280d1f00d000ca1140d03942d144810b81c20b8040022900c03c0c2d41c05a0040c00c05003101003515241d402103001940189402f0408180100c01c0c0310100d549441200d000b040e0b040c000304a10101c50200424a100714071600303070002004107090095564560298048860700d0350100000141c04c4038000a642080a00356040c40ba480c000580030305001e00381c3c0f88242c051001510840d61161000841501d01c101c1400385a291590004444142403004080b40c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 643014361 1250 643013111 643013113
    0x300d020109020108010905041e1a070309050c1e040b0f030a052103010608070e030c0429040204050d060c26040c05040207150203070c02061306110a03080403050a170405 74
    0x41d03078000504241010b0384180380380fa1902d030421010540e40035040c4000c040701181d504038510380342000900001480f661030036101800d428000501c1e050b40c000d0b00070b103200310280c0300e402d1001c00811200c8441c28403c1024507036508015000340c903280c0e00c01c080007800100707406101001b01e00407d01c0c0c5a82024200d403d5030125904c1030050000d4a07110701804409100707031345190f04007100105641401b922140c01d02060403092030065a00740004210f400000d842000795041c40b920b10b0615001010619003c009801600f450b1340c01c090088400703a071406002c1c0080700c82c0540c1d4940c02010280c140c3d0301040040c04000010100c002011114108004c40021003800d00e81041504084a80d00a07449148108000e0700011201c10001000300341c04074006860340e4815800303607030562045200075800140001c1d5103070020390018442c801da8000c1d5498020700c030040100d181d555142890041d0102c2d80d100c0008000912032002415040010f1600400b42c808401c58800d540601707840446003 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 643015611 1250 643014361 643014371
    0x20a200a0f08031b040315150b0a08040308010506040518092505040b0924010e032406120303150a09060b0702040c030c0906111219030614300d0201 65
    0x15004d03000c0f1141d443d4918030300358a071070b06180d56281c0703001400d106c0000c080c140c0c031460000324540c0c6540d881d400610540c1000365880c1041d4400400130541101c08a01041100e400030416003844002c3d5010f07181c01401254401440303408004015100a0076a0600c0c4102c0420449201050f5000f01c0c1484c540c840c4401d00a003418108004d44601400450003040e88008210820051450825280340d984070307403003540d154100040300c002c03010596040d010702c104200e08400c050f0703080c5100411403210403045030648403241001401404100e11126036403060022540c00001c10128440d226802040f00c2201a03641001d0780035240c4a43c4886513592011442c00151304190084008200d200c1c6401c201518400380054901d541070300850301000780b0803600c0c00c0c0c02c460400c100c416142012010a489815410301070f41d40d11010264900024241400062031703451180c241c55400400070080021141d1010101c4408854a13240c00102070300a1140301180c0e5007403080c03a02ca2185503001081c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 643016861 1250 643015611 643015621
    0x50d030c050606010e010e060d0e1f18030203071b1a190806031b03010e031317061e04020d120201060f050a0b07170c06250201020a200a0f0803 63
    0xb0510b0001080ea134144081d4615846040c2ea10511814005070101c0c2e01c1d030344070321080d10410010150607aa118142c404c80034116500b01143c410710b800000c0000c024442e40c00d80180554802c802a080100564410b1040780c0c0095854400514000c00030409201059075034208071803d58600e101e0703070020000004041c03004941c0c0e40f61104280845061403001401d0071341c0880c1d41c40008002044800070760b001003400300d070b03400e40ac043c8001150b2070480c1d8840041a038142c04941d6a4881c00034039010280703040904020105460b07100341340301e110000c9410181d0f072100f403140b280144100d17405000d41010100040711107421600004017503000168003410044108440041c079044240320381006a8200030802200342110342d12640070304d01c00301401c601c0c441d0030054042c07400011402e00800e0104107000151000021010b080c00400304800c0d04e2070f03001a400c038800c0c445510006070150740c4440b00441d010004103501d94100040310103075103054444142c5c22011240c02c172034201000041c84 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 643018111 1250 643016861 643016863
    0x4111503010618051c030806030a060e030a080f090307060504030e040509100f060e0606210103030806040f0204081e120a0e18010509150a0312030e070608070504120606050d030c05 79
    0x103c050030040d106001c0b0603022294041840c09501001400c201600c400120140c41c02d010020100c0d91041d41402445030003200f00f600c9410101d010000600c8030030004981a5035400c410f13018481060140d850454583c4030040038110042080d000e0061091082c6a0b9403114840c440c031400404015116014685d00030005569a08100d019010705122061100a4010781e01c140c00910454000380d48410b41400102d03211880d03102042c1d1090250000014150842074061190408460030071080c83c030003080900328096400343c0c401550101b0303426600211b0303007291a00074414040c00c944040d0f41940020f10b50f0b600c035900100000b049040c0c46061030500f1501081920950280814990b06040100701c42550080900d01d0b039850000d2080b41a032540805a0007a40e0003081c050382c1c00b215500301030058180401080b200340b080010000b141445040704034000c8000b69602c900e814900010030308035550041c0700780c80340b070340d9004001840ea540c4070031300c11814442c1c0c031020070b034491500700a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 643019361 1250 643018111 643018157
    0x20706020607050a052d070c051f051b030a0905030f06090c10050f0307032901050a030e1e0a05061e06040207080c070306020306040c090e041115030106 67
    0x114203550161060004040c1c000043d00e1004406181c600e45599044103890f12480903542000c502900200c160880e100303140d030042803480d010782030741c100f0b156031102800f0b4405001c200308003400030900380607040c50388244010aa49824002c01150a0040d881040c0c00c41e405007140f0070215103200000c21142c1810320011031800941c50103040e952415880c465107a4030804150f510500c090741040210710302840c01d031498a1018201203031285008540a0000c099903c1ca0140d1404180128540d01d6242010b00c030381328806039a01402c1c1242c0c0001070b009004000d901a0303da019440c41025001c4103e0b40c2d0119505402c002060300107002d00b405070400e8800b41245804046001c22250b00d406501c2d28690000b0f0140c400580d9210702d030400381c440740105840c03d2078900850000205124550f00510701480301190104401a0501401d0b44c0100c6544900580c070042c150015020807501d039102580c0391005448034051003070780d1560440303580c07098100f500443c0c1c01074a1050041c00700b40827 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 643020611 1250 643019361 643019369
    0x406170c04020f0307111002030403053406050a090209090d0e030313060f032c0709060302010207090f06031703090c040509100f020f0d020d0c020c150a03060e0f070207 74
    0x204501d011031040c0c11540f0f620000f043c49040c00045c1081d00c41104040000341203040400d50110b480c1d0509160082140e4040c20601d108130020222032450303002800000504c0081030a0000c0d211401507403040301a003001400e01d00c040b556040180c015880720503a2a100702c0f04030014180c0e1084c4100b024060490b1080c990380658002d1008a48150f10300010074292440750a00d4584405210821400f400c0ca041c41c0305800146184400e000c100c04100f40000c41c3d00300d00c10f80b2011511401e04008403515880b003e80181e00c441c00c2080322140550003492400880c0b400401c400d40c0707940f90100c0042c600c0c913504003181c2e070000400440510500c204415828101ca0500503410041911940c030f10b401083c2e402c03829030b1268074280a08841c4d044840d1080c0802c22180c4a100045880c0000d4101d01a4445028203001e9415546403020920b41354241c07000b0010441070601410700e00d500d400810040003810707624040407070112a8480304500c40d0003502d90f001c0b1f1303a1800310f10090500b6001d601c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 643021861 1250 643020611 643020619
    0x16030506100b030103030c020303090a09090312020f1210240e0d081b010608010c11150c1b07030605180f0703120e0a030b090312070c0302030702040b040207020406170c 74
    0x5801d00042d03956100300c0341126014a40484e10509900003c0c0c2181f00b02d41c00c256001c040343d04005001d88980c1c0121020034041e8030703440d1040030f08140a02c04da101d00c018035840d1900c10402c00c00148242c400301504100007036025040291610340304c031000794840075030026468400b4001d18030990b20101c00c0070005c0c1c050399400070525141e6205e180a014560498070050040030f0072204c050703400d61102009045460003071008043c242c8028103400c00350380b01140140180207072000500c40416080c2d0007110110741c5c103031404605490a10312071502164494050003444c03000004110f15003d55400340840c02480107035060b150010b03030720704010f005010441d604480010004500c01310f80c845a1410207040074847e4030b421a002030542201038100902e000164000d1107103400c000406410b4650143c860072055898020040da01091889001001603200300910702c014181a040800202c0c030161002d81819411750024064070300941010701b81b00e0a0228401c0001c500700f152040c0c81000761 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 643023111 1250 643021861 643021891
    0x705061b1e101a03100c0f110705010807230423010906080a060e090a11030a0b241309050705040b010806060a050418050f06060c0d0810050316030506 66
    0x10010303a44400032980c95142c101da80b002180110300e074603242018107181c01010303a07241c00001e0340d050004128000300c030303400181000800301c1d216009483e1000a10b8850005084840c54003004444507a001005401081800c030040445c044080c00300030076520310880d40a8039581061200200b45101441d03c030002c129040a10701c0c1a40c00000307440640e0803c3c40e04029661740d064080e00540300c03c3d440150102490000c101d0500c2d40032980040642c03090b08201c03869070480c0101540c80d4100381c0d02502d6014a1801f0030714405801c004080a410fa180001000d100210001002802c03480846000c080e02d604c009000c00005104480140401726807c00c0802c000b50002807450308014203840c05414002a030f402081e001c0c506a40041454500c00c1051008030342115015003401d07500202c41c8107500010505615000060322000c0030804010300c02d080325910b00b2560b0f00001340c00d100d4411803641d170104141d00d05000706003d01c61050a000034031880c504d0a035141000c0200b00e100280100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 643024361 1250 643023111 643023163
    0xf140307050904050a020c0a05060a0f020319020d1413061d031e1201031a0f01060503130f02030d17090a052122090e0a020a06030c020705061b 63
    0x404282d9468040603140060755070ba414198030000c4c89982950740c0716100d0a4040f508100c80020090310540312008240076041c3d24058038000c0e03010075108068944440020024003003241c4d8040c01342c10f4a540700215520b0448110444031510540300003218920049140e01170140c0c50140b41c890b02480c882d02c040c402030b4960340d42e499018281c010810001d40c6d0174144a842c00358001d1343c40c521301c045603114407035035640351200340782103041c1c82d07094a40502c0d00000d03201c114510040d030485100e41c640c586543c0d9010341c9030305038044804d4110395a101d18040407016850421000258a0721b5441d8107503403822045c0c40e00e0700010001d0603d1480e41c011000400000c00119107081080010248400240c18401031400d10f0f0054071039110b48540600d805e840451041030a00007120b03a58a410898407403180b104035210034100c000650014130404d000c0001c14800e034000507904100c1e106443e90309440c0c00003da0558060780d8040540f03201e00f506d00c0243c070010f00000040129881e8041420081 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 643025611 1250 643024361 643024367
    0xb122a1315170106140417011b030501050307061b1202100e010902100f120e01150501030c1e0203070510020306040501050109060f050f0d0e060a1107201f0f140307 72
    0x5020b2241080444141c1c481d003401c1082c25200580342c407c039541c02c031200082190713000341080c070481003c4070040e0031441e00e960b01031700c0b0300f034165100503001e841407500b440c20030b882c054040f284940c1c3d405441c0c0d1408001c103081280305507200180b81d02411401400040c03800c15100120f15901303891b45410006030042e5a02078003012100703510f052080505a240d032054404040c0c2400090f905401c10140490122041d84000744203074690003c141541d40324001101200c03281240540402c4c4181c1e1158100b12301801c010751600030314030440341f40001c1070756100e007460b08900417443d10903004014000b6a142034001d55000d40001c0c640414903600d040d00081001520b034001d0001d0203000a0350740d110744c1955084460690100505024000e07a41200c280e40340d408072100810703585048212444240020304982030550040e04900c81540d0691003100c014034550003865210304407007407950748587c1908586001807007030384a51084a0800e080608100071401c50035041040400401c5107080e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 643026861 1250 643025611 643025657
    0x804020a3002011e020312010b122a07140d050a05120604060f061e02010203060a06031104050d051612020901092f0d060b122a1315 58
    0x59641d05000c961005000590b503e02c038592202021509402688030032030380010040c101003a1800c2038584d1030780d0b10381e07419507070380500d0944090016580012550098500740790380542109090562014480a40b4040307483d440304c00101c800c070114a090040b030302c80506c2250f071170010b1810010701d0161010001413161046442c941105080c910106800303032941c1d0b0144003e031a00c01c4400400c5c580396103000d01990743c03003c1c026680903400114030f400c407031040c000d6a005842c007412a01e8401e08101c002d07405811028008440e81005000015840d520000c03811600780c02400588080f016010300c0c5191490150410780c02c111007039104c02c0040e16140500c60448410910000d150410b00c07509602484410000d201c0c00142000b00644d030f00300c010020014000d00039000c0040c030365107082c6152140a071b503c100c024100b60000087c0502318102d0b501c52544c03000d00c5641c4480240180351403154000a66000e5503580b448414400c0303001c2e078000e41031400102d00b4018140611020a401012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 643028111 1250 643026861 643026929
    0xb04060503040213110703050702240924040b0406020d030501050a090515120c041a0904060c0909020409050106031d0d050a0215180712081801050c010504030804020a 73
    0x14480011001380c16561780120040b41c03004145998030446400e00a0240e0040c05d03041e403069a03801c1080311980740041c8051401c2500c4c000050911144030b042115054600c8000d0103811406841c2c2d40d400a0001e0040016000500069880300d0500800a242041c940712070410300d49000b005000700c1e0b90341c041da43c08550307090b60041a6070361503141d1001d11306982c0d0034264218540b1805000030300c0002c103a071404001c059504201c0003108610141c017060f43c0c1090240c01c080600041404070b582074002c03041c050351031308113100c20a5540000c01c0c00c0360f200341c2c0041d441e19900d100500907994107024940010590035801c0040d0008040341075110b43c0c10340c0b48402030000004915580500a1241110b000d450b40c0390f0030b007a031610b684c6034140c0003c61510310000d80244000030401310b4429a031014507a07004410b00b0b040c145001d2401810740c0704031403020f05101d0309200c1c840400310300340141813082d84682e80311b6520742414030501c170710a243c2e50442101501a41e60008031442e01c0c0030700c0803810b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 643029361 1250 643028111 643028119
    0x50d0305090624010903080a17091902120a02181603021809040c1e030203011113061812140d020c060a0e061603090e100e15120105010603060801060b040605030402 72
    0x8940100c0059441641546c0000c1100c500810007411082d0003031500b0280d18041210507165544440300303a80c84000d80f1801c1205003c1c10054030b00035060048100114140d10403c40b0710f01191b64001810014800c81400030032598001003003a22171172076508502041c814142542015002c058240400810101040c050a100c200080501207242c004800400f140b0041d01c06d03c0e81c10600a20f400e40043c08140e010350b0038004084580101e10701244d107442e221079064076440342030840c210b071070003a9003004c1c01040015401c08501006408809503c140c0302e03103500052381445c0c940325030510714400c055400303540000214030303226110a401c541120500e460180b034030007010800501c0f0f6000e0503c00800c050504001c40c810181c1104000302681c42880c034040e11a81d60f9601d40301c911135107008210401c200a0042448221404414401c0340c400500662034003001000b5030703003111340982c0541c1c0000c0e01e808d010800d5030400e1199201a20a07040520f00e801d0514101409072303c4003030402401 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 643030611 1250 643029361 643029421
    0x14060c0a18260709050c070c0803040e180a0b0a1a180c1b030412150b030a0206160f0c1401030501080c0f060f040f14060a0c020405090307050a050d03050906 69
    0x105920a004030005004c1c49001004075040104000259404c04807049809a107800c0c404159141c00000381e80880d040032803c03044c1540c1e00390351062411803000c2a4007241c07081c42004000603c503202214400c0340c01030300004059461184a102c04008441c1890142007005020719105102c07100300381d4016002105566116600f001500607070095500b464034074000441c02181200d0905541c440081c00380701e1200034028941810021560706105159040d440b000c1600010704100020702951100c82c0c0500c0503104058540102001e44250200d070701c50310303032581403201510a41e56143c81c0f1200307180401c15581000c1c2e4059883c0c00383c8445071300c00d01250902210a6641c0821103800104001c4c00a403101d6403041040c401c014140142800080024107400344c5040c02000e6600c180a5584c0e0a5690721407078080c0b0008000141580956000410441000c584200f21410101c0d2280300280900108400000c00f21540a81501c016401010500900711040c0d101e48507122110480c82c00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 643031861 1250 643030611 643030679
    0xf05090c06130806041407060807020304032d060c08090a020f0f1f082706070f1202041409060f010804150f06090f060510020304030f14060c0a18 64
    0x5004096940400000c0c40303404100b0080081246c1e40c40c8141c5c1890081790f5141e5201c49050300c04040441c0c5001c01a4818002000801c0000140081103440600e0780001501c07001460403030080c802d442512500e484000341c180440d40501025801300e4400c002d085009443c2d400214030700c0c6114a240e1088071001e0b0000201d641c1c40360440c0300c5148c0d0154100740300d10200e00142c5044800c80750340d60280820014911031180d410316000c1900701e05d90203401d1989d108038090b1001543d40c0a194100160044140c1d20103c0e184001c00c00703402640241c8031460b40440400032000c10090486010b450540c08490071130340c2104041c0d8200e40d009050941d02c090303080503c00284140912008e58900b082e00010385410250f2001c2c0e08a03100101c24031a00e81c41e1010301400034810440a0010b07030040108101240c0d400036010452846004c0303c0403041600c4a0140c642002600e180301c0080d00015545003552300005034401500b907114404185601d8005840028504000c00000d60046890303111 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 643033111 1250 643031861 643031887
    0x2d060905030f070c080c06040f0b0c011e02070204060906080c01110309040c0306080c040c0f0c0203010b040c0305010e010f0803040b091809030a1808070b090d050d050306040f05090c06 81
    0x1c2c0b1400c0e01c0b0152640720700c00b90500036109032061285e0f414034010707508810411305000c000c0380c1c19500700700e10702d00d0b03045c0c542070070000c0079400420400f026558a0b00804c0700411f41c03401d884000050fa140150b100d658600401048644035031040341c29524125040180c0075010500401c4141c0c01d00300042e10b9880041401d046200b0014010390141c5000e82203c12280c2551010084d50014401c9519002c0040d00740000c49050110320404030350381e8891400e0305071040d48980c480c540302a002240d0f1040c10800308040e110740f50140d4001c039458100500100c442708448600502c858900c81044a2419404984902c9140210035034a040000c00e80081e8940310340400c24400704a140030010b02e45121016143d4100050040c00550446030904c03078014000c0342c0b1001d40310322901a010301c0d0702d0f00c09584441c0e444030f00c150341c0103015806030b1008200c0c203104903030f032030b000316251940d4915000c41088100d0348030b5030308000300a250600340a81d1080001c6c00041e4102c041d141e280d0381d070080c0d82c924 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 643034361 1250 643033111 643033117
    0x31b010f200102180301050609010e06010c05010e010b010e010903080909060607020303030a0603060c021612050114072105040f020d0813030317100b070602030703060906122d06090503 81
    0x1d040c200d8070390501c000807144154001d01104a0848024080c00554020035080e5081601c8283d0310030540001032003408001010b00b90400030504100882e00c4a50f82c0b4035003512240f145201050355241c020480f90b5070806a9000d41050910f0096042415030352071005d18011081d2541c00b81c21782034001042529030008568842d90014110783d22403900013904409401e8900080741c02c182045c000e51405400064020700c80d60812054030b00050600500b1080c203051544241c0c1c0643d00c4800605000190070f03202c1d4014042e503910b01e2152500085d02d03020a0300030385a0ba01c44585000c0400000c01c0050240001aa0381114902034507441810506442e01039619085094180744500000b003542080b0005010018000300004580d0380f0b041035200d50403984120209654100030300000102a540115030011a9080010328079480345004c90031220150401e00300d444140c00c143c4144000800310790b220740805044404000140c210407581e40300228001460551a0301d803501c00c00c5002c1c81a = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 643035611 1250 643034361 643034387
    0x70c1b050d050303060a060320071109010e010f0806040b070e010207030b16080a020403021f170f0402041b020c040207030903020306040308040c1202010507080a020a140615031b010f 80
    0x40741d4405401d00300b00380c0341ea005460f5940b00c2c44415500140c480e0080c054141c0340550411405107000040c003a22a5aa2040e8001c807284070300390141001580e01c1c902140d0103041d01914900d034540c1003101b402c00d84070f029084072320290f02c26401c002c00a21081e034030b15131004a0303181c0a04407002c4400180e1070180075800c001c1803030340c0880c00c0040d00f801c2c245064880010303d0792014001d03110315148000724030950201030740102a42c00c3c03035141510401c0c40d00c003c042c12460a56a11000c2e80c01211030b6507401e0fa800e003040c0701e8060038070056103403901500703a9020511200c2d03440704071404e4020390380306140d0144e10300440d008100d100606000324242c000554010f02950030900c0c2519000f0826541203d08690b1080660808074040c041c175949455030543c183c5640d4941003003a1203041054004001721070844c4550801e2000040100c4400b0701e0a40a803001840740742001d0001c211407c0a4103a9180a0350109005009038038160202d1070452400b0300300742000340110502203a00d1004411 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 643036861 1250 643035611 643035619
    0x10020f031e120f100609050a0506300406050c130e13140a14070b0d050c09040c020105060f01020d0219170711030c0a0b0d33031208070c1b05 62
    0x8014003c0742542e03060f0702c90000d48004d01d942c251213100036261000d440c01203580101f49504140720318107102000b400c40020050580c040112603140030340c0141009611231240401d14000c0c04200022805515005128541c43d2801c00728000b034146024042c91248041040c564804900c00e4514100381800c42e50b0004416104c2d1600400e10a80e500601001168052014503600d0b0036440007140407419900c54400d05071421912140d04005050064881100640100a9040c0720b96851140300f9450b01d094001207020f01c0d02d18208801c0450111685055401c02e00d13510003220f902140c0340c90301c4000640c2500042603e401c00c8522500388922031070810500007000028086107064084001004130211011459200180a808003040c4210710214205000d03000c2c00b0020364011082002042007809024100224035114a00030301ba020001584144020b109001900103003c0004d204c80c00c00700703882d0420b4000207001d545210401b800c0850401003103511840f102c0e2400c030040500030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 643038111 1250 643036861 643036897
    0x10021c0b1315051305040b1f15180504050709051c020d0f06050108150403110109080d0608010605030f030a0c05010b0a0e0109141611070906030b0610020f031e 70
    0x21000880350b2070500695200c4d038404101602011858061540320360740c0710030b014100d605c0d035013036001480039200919004885c4043c3c010a290170b04c544c0050159203aa95207110050010041400d4108103030029030080341042c5c06c0107081034000c0f520b80100c65080d596004030030690112408881e00c50031009510003860b2001c3e0707080c806000d810886481c0074007002c002e40d91740c03888155510742d1074445000e02c4078418400540420700a60345400d50700300520000c00c1c0b0f0746150b07a0b12015540010400010982d44240920030700c04240304203400751506400403c000b00c00300c000281d42e0b001e14800300c1e04104000c48071801700f07c020341003a0291240907010b611010348401c4481d0510009006064619140420300151151031001c12401a89080400e401c0700c9a000022910019050161113040c0b080c0d400c0021044030621494000314022101c50410f410018104020010585c00c502e0841d404080501304d503030004400c8491031800c402900c1020441945100214010b01e080320b140110b1031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 643039361 1250 643038111 643038131
    0x905061e0d02030609090a020a030816140708150c040909080d050108100c021504020915030a050f070b0301031a0402011106150103060b0f030a02030a02042610021c0b13 74
    0xe401960064108940e403000a0b0340310606c507a616010410003a5009900503420400329a11344020005800d5205030300304030b051036448500d2006000c4071b401c003003680118030030032003580144040d007014018201000c51070304250443c8009805180144940d4680d02d14210081009040c06c0f507101c0d9503d070b00d0901c810361791000b440741c4842c0c411340300c18201c0341814250003000e840490125501c4118091200107500d1fa1303001d004961500501071264059141c1c030010080d43e003000b10b000300f00c0c403400c01010301c00610000d50303040c032580354483e4200700c2e000c3c4014000a00c900750f0b103070804400101500701555450004803070384000741c00800f550303000e00018020841c5502c451071203a0078080e01c060000720f950341070100c02c6114400450505110910103e0000010f0b41c0045070807442c0902c01504040d107030800644108220075900c1d001c2041c40344035031404107062004800c0c00c020228210304090340000c3d10240c0300009420400b03696a110b402508551701d940350300ea040409900100414808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 643040611 1250 643039361 643039387
    0x2b0201020c1b0a080a0c1809030c030804030e0d14010606080709090f0b0409060203250e010513051c1a011203030506011205090d0206130515190903050a0e0109060905061e 75
    0x266004d010500747c1c05030440050709245028001909505954101042c00c290302d00703d80928000d8821030400c00c1c2d09a030600295a19000c0190035801801041560180c0d03090300b90031156258821400d03c19a1030400201c1e9411400c01802c440441c070700800da01c10300106000c0249070002d503e030340c010700e404d80c810207004a65024510400c0c0401c3c0c2d0113281c0940707a03031100d00389241c03800c12000284c1d40b040c25012544074070060000c3c1280b03210a0b038040c0307403160005103000e03840100741004080c40c1a20703503042c00b61b4074801c03404882c2e15000401907541003138092940041d071000d000d002e0540f03c8000c601581d01ca0382100015400741d41e801c00070340c101f1540d055100c0000c07171040d10062141c0404910410b80d400001c0e554140c1c0030004100528001d0344000c2038031030081c41810603c90001c480380c0c2040d0180142d906182c802e40d2a140d8825424001810b140c40c042c4020f41003040c07448040c0902500120385400f61241243c0e0280c85030880701c801032141220365081c010001d00410b08100d00e03c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 643041861 1250 643040611 643040633
    0x601060903030e090402220e03031f0611030a05210c0a0212090901030f020111060a020702180f07050d0902220b010503090a080304142b0201020c1b0a080a 68
    0xb00c65642d95810740d00388010042c1d11481620042c2d8011000588a502d03585a003482440d402d0014001040a0030030f00711250031600112780d15030b90303035084a00149a40e80c413442568058052030418071095070304c208042707a59005645c241c1c02401400600250b0011044958084181040030941c4030fa15203041c40d034605400c038400e0304001d4440c00d00d00154144c1c401d02030360800d40002e40051007581c070790784540701300c1089060281c3c1404002c2d43da8510a040a001c03461058069040c00359613211a4818080f41e506552a110940e038800c20038085e400d4000e400031034002880d403a1654440c6013042d8103800405034421300961060805d4401942800080e94410304060101e03402c00c4046e0150005603103d00c001c94042c412078006182d10701c0068012409150400e015800807107010340e407005240e2804c01d98051420740701442c02c1c10310a840c03100282c080720b00c031400c0c4004e505080081c0c59084e0303501c864540620b00b0980d4554222100d45074200c1020017020250101c4e054603041e420403100300d80e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 643043111 1250 643041861 643041863
    0xf040c170903040b07151b090510030b0d020904030e030a150515180c041211150c1506030a050a0b0a0b040b0d110114270a0f0e04140601060903 63
    0x300d00c90340081d8a401011007a502215000da908519018680d500c03200007070007149070782e2519070780c1e03000070444030001407140740281c101501d079400914100701c10409180a40400c2400b0507080c010480d425407581c2c120b1741d01055040d41d0176101610303585410b90703880d8450403100c2d4245c03040b40080000d0210341c1c0030420b440380d00d0b0070301000300d03844240c803011030b807006024416006a5240030070401c03520740740b64259004ac041382d541410952074840c0b000400c0803040068619030000c82181440d482d00700802d50701780c54552030052030502c401506070740b14030910010341c1412038803600042060f01e05004c40640ca66110050f6268140140382c03168039107000f9960100c005e89880303e000c0b910b04040c40368a8140000030304d050700100e01d969600110714182820035042014a80c02c0d0444c0381000c5c0080d11107c03030103507100400e08031030b609450070500050415074070070300c00190204100f0110140120076902e016503ea1182d54442c00c0a451003c001081c1c030f04a07200307410001880c4c9610080160a036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 643044361 1250 643043111 643043147
    0x20a031203290d080a0e030d0e130623010207150203031006050c0a060b0102030c0d091d15100c150b1201020705070b031f03060203040303050907060c0f020f040c 71
    0x595102c0203202d101c2000500c100e074201030780640074000b1442102c0a0400c00d40a0700d44400004203010203e07040858500200b400b2590702601c8005a01e80769441000000d0308040c10003545c0d190035401c3e907100706105045a80c000f5920b0004800c0c9e4400d0140201070310103c2c3c04224000c400d200029680d40c0300315150485480c00c0ca1002c525903115408480c07500c0080001041109180c0c0c07603100040140108840c154482000041e28a0307006211100c02003d03151102d07450315240c4901583e09a904802c1880340090200c20001150852000545101010345004440c086216001d5034801000240900f001059455846040146e900082c4594600782c03600e1601030080841c1509074084c12800030304a400c079000522185c407c81000c0c40d070044103030a416500300d071605400c417000009500300303440c42a0001308000605805008058100002c40c008005203407414500070000d0020f290024860340031a6080030940d43e400e0b50b00344900c8030041040000e202d0081c00580000c0300107403040d1003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 643045611 1250 643044361 643044401
    0x1150c080f040f08150604021b0a0f0302160815090c090108010603120311070212030f0a0206010801050c040b0304030804031205070329031f020403050715030b040b01090b07020a031203 81
    0x141340030209030740a8900c072408140d00651603903000c00002c0d4020344a4641c034801e040703040000300f0004101c030009050040c50145090802418001c1c141a400c1d00200e00103200c00b201003144900000305100710b96a0300124841c81e8a8406210342004000b5007e190b100300d8030f4001107407101040d880801264070580701c0003400240700d5402d40544011704c1400b101403600380507036005414001034640b0640500c00540b890818508140f84140d00007940240040c0d10000040c0711000c02482805c0c1c0110708800102c0c1040d1601c0e103c858a031100410040c2080090381c0440e04160096440c91141454034a0601c40c902d44201c004005005110001000742007000095203a40c03a0f01c1c0003a003030b03098060050300c001440049540720702c003040208050020350811001021480900c6144043c2820303a0b403020400c3e006042c0101628400c0940c40e100d031345480200881a80c02c0607584084075032a415075516054140006082d4000d5a40090050410301c0c45109a0942c16848440300340d51860300352030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 643046861 1250 643045611 643045619
    0xd0e070801140708041b0306020d0c0219020d081b0109210908070510170a151a0415020102131e0e0c03040f020307152102030f01150c080f040f 63
    0x303030046040e03d40d0804505124045008201c000500025114403135000742e555070f6882d44d40c0ca080364455100003008554030101105541e40c144009918188920b10b030703c1c0e652910b500050202080c5140040c600c0a00244440c004090101c80e106081c1c04940200814641800c0c40c0341064800002151a00d0f0001d03001d11546010b158a0380940d0640c10040014504000c1441402c2c90041c0c100e40078030200045241511903c00c0c49648030b40124000400c81807450005584811101d07004803001d242411001c4c8100c24044040e030f401c41d4090a4440402c000e00300c0305078024824520b05040400407111302096000035030b0000214072201500620200da80c9030310142d00307507505071004520b01c0e03420400300c8d011a40a0610740159400107094860865440f1201e40c0e842103005000c001103000440300d40648000400040c0310b07100100000d52961612081448801105003d8680c242d00100340600c28907110b00344000350310760710080055075030041e180348001c0c07a00903100e8081000700c5a20042 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 643048111 1250 643046861 643046891
    0x60405030a030b1c1b12060c030b0607050c09040c090c08070f02070609150509100e04050c03131212060b0306041107170315150304022b170d0e070801 66
    0x1130304122540c02065410b0f52140d40e2101540441c00001c81144403c4d10086a0104031a00300200ba034802c10001039a920141c40c00f400f690a000b80c018820002848a400801c40120303c00c006040c04a51087c5103540e1850402060500c581104940b00d2414500c0600a900079106078010030003900c07170201c1060310a900300d07500d01050007001c00140c0071800030041d5102a4680f00d002c42e40030b080042c00d00d1503150220707800c46103601c148400140d8000c031071002d90401c0d10031039801602c0200020300d58a44000705000c40401d04000400c1034041e0310300d03400c1c103910a20b0007403890505240140456581c0320f13114209904242c030110700c61450b000c1030707180b40f10a0408441d0219400b03800e841981c082d107038100d8103681004010400c41b00c503000e030b6481956100d007004400a003507a181940c030390130700380144840082404010b4000c3d4498403a00c01d06440d05110a4103881e6102d803041c0500095152901010302500c3c650409140c1083c004842120780420903105603200341c00200400c02d90903243ba = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 643049361 1250 643048111 643048129
    0x9011b0e011103090a090513120503220218130605010f0303020606031c0c05030c0303040602031e071211130806090609011109010c03050c0604150c050408030f0702030f060405030a030b 81
    0x135034402105c1404009160003604680d43c84070b85071074140799640140e241d00062105100040000031000010002d0101d4000f01600c85142204210b881c00b55065020507941e04000b41203501d10781c0d8a00001c2c3d608602d4809501c0216404207051140356511714142c078590b0342c580001c13005401200c0001d042800c0000308080030503003108101400c0e916001d8107560b629003400042d031345400b082003180c000138001c000540c040e80c8240001a83ea00d454000080c2180844030520403600a80c01404090381d07002a0225400140000006040e00001d250090314403c1d6010211560358000e4006a038a5011800a208100311020b41d0004d640d0056010300b00c40060780c2c034081203070b0144042045948510b031740c41c1c9494841e00f0b090745803240c265400c07490909d04540072107040c6140510f00c000d2080c2c6005000c840303030560074040d0809040c42c014a45900900c15014008040426080151343d0100103104c1a101100300380e403110300301800e1603074490f0301403c21080401d08250080c0a10705140b0f0304 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 643050611 1250 643049361 643049377
    0x90a091a010602012909191a0418030f03050a1e0209091e01031104110c01050108070603060e0c030c07120c02100c0b0403140d060f09060603020f070b09011b0e011103 73
    0x8038043e1a142008000d0791a0015047c00041030510010b228260300511801c1e002c0c0c0c040291401d1001e07030b154200720a9508242c00200032030408860344000039001000c469102c2010b0401080b0b0341c0c0c1c0e8114190083c58061615051108005034004180c04980c0c01409004415903916075a0f645030400c8090000828460000b810610001040815042c82e01446a80c400034004540c0c60340d00c3c084404a41c0004000c802c45955603401001012010000400140301030300f000e1100903d0032092b0741c500040100169003c010010000310a00808401c41d880c0300e40c03101040700082d1464000408120503e04100d000300000c2140b001d21a002d04079001303466900000f0070704190f0301c0da681101c0d08000d0808000f400e91003400142d850821a00440340589401e07000160000e02d8216a107040e2003590748003005052041040c01203026100b0121146e0b02d41000d4191120f441c0e9420300e90040140c14080403410401d5400c0707051485c1d1100c2c03c40d030f442c5801d070389820344810041d42c22034481c440c0e018 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 643051861 1250 643050611 643050671
    0x30705011701031509060204081531020d0203031201061d0a060e030a0606120209010b161704080706051810021917070305071e08040302090a091a01060201 68
    0x1004000185902001d40c130651300e4640042040140c0395160740a9810540240c80d068105602c1e9001c6083d100480f50f81c0010003841502c60308424045403511120021005854516038030701d20819500e0360103203898420f90160480e139581c2100048081c21090070b00a0303200050007140c0e43d03c120005480303810801c0b84010135000456240041c2a071300c032201200c8036905406802104400700b0214490fa5004202e0540c4d41c03160324203a48100492060140c11445d1452410301c00341c02e0103590b8036411402240e01c408100705207005048003885500940d449140c3c2441041c0002c29060751110181000098109030601c3d00841c54040002d82d40c0c000c42e100006a0003200425011008100d910710810b02036611180794500c19146500544d10000065000c24070014000d030030440c843c1902c13002000c452400035811081a52084241e2041d844081c0c490188000442e114841903032020203080d1b84440003000c04039410b0010b0f01803480c240b0801c0090351902e001c441c00d1416518028203904c510003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 643053111 1250 643051861 643051907
    0xa0801150f020c0d06090b0106080a0c0504120219030503030c0d0e031c0510031406150109030308070305070921110607030503130309030510050a0614011e12020d060503070501 77
    0x1406224001c40102e00503030710b040d103860518007ca0784040b0241e001e0300180c1d036000c2d0245800a01103090360240100d00007001000c020801c600c0081107494250154101c40c04a40e001565181c00702c00c10203a040074000d0300001043c414903540ca0310042494000d680030910905903648205c0f80c817400340c00b9611401c110000000f0aa5117001c1d4813003907218151543c00304410f91280c5440b06c8408207824100034030340c4a4014084000e0007460b09241c416001d28000850604555008140c8000604058141070700c4402042c9224014a02d4034050030a02070110300c954180340310034809026201c41940e20358881024035140c1d0401c0b0f0100d07450903425031034192a51b1101c0e0302c2075503a4940f07a9015010440c1412010000507420f01481543d00c200359000f00d9076040400d004000c80c1c000b5401407141c000d00503868445642c0100c0c05030b1454124191034aa10744500760142c607001d00c802140c00a844c030000c0c240c0204900c03a88040113843c0254102c4840b00d460344015075044010300c40b08540c1c0503c1d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 643054361 1250 643053111 643053133
    0x614060f0a0804061803050909010905040f06090203070e1e0a050106050f07050102190c12030204230d080307030207150504081b031c020309011a0a150c080a0801150f02 74
    0x5202410707042440b543e000208211700d132a000d05c0c26951010101d000420010b003444491500d002000e0251220700d00400290a059403107138881110908020180d54aa45400c000d40d501404110000c00705842d401e0140d2512410100210150039003645085d2203d101042c510301c0030707109035810b990300768640501d400d601d40c01d003140360b411485040741ea942d0200004505209030180310782180d1055120300d1125041d52034000f4104289611502c03c161041c00300f001403151074820758007421950320f06072210204a44c0032074581402e000011300b00c1040001802401c90b415801080f10301e01428203409a1044c1406c604103a0b4416280601856024084408003080401c02841202c1509048924004082c400d07042000000e44050f80182d1303021082101d840c1081c0988290052074116603486c26400300000382000c80d9a024061145499030841d0084900440240c181c00e604030f44180e80380d181a82004000540034025034858000007003540000c03501070f06402000f841e140e00074100b001e1034 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 643055611 1250 643054361 643054367
    0xf0c09083c121803300714120a03060807080d050a1e021e0102161b0506030a020901020c032e1107030207090515151803030d0614060f0a 60
    0x550030360605010310b09200c81c2e816481401002101c020502d0410740c0742c80da000301402c00c1c400314030803403e07060900c0b00c1510740000c0f004074181e000810101551030350001c0c289084903854400155829108000704940d560f800d590103085440901e0b50284291912a20515218010340c8558100c551219121482c03990040010384034140c0a442c6c554400c00402901200500c0610408409604828007021100c0380307904983d1000e0a8000095242114030003920220b10660340001e0000c440b608104c96100c415003a038440102401409591030b4140400300400961256134500c1c007604c24001c1c00507090601040210a5000d03241d0b480009226000d4201c8020500c01524070840d5541c5c0300070481c1d55000f10180c401580207a008200060500ca080e0b404c132940901074507103200c2c941030110505e41d03495a80560100d2050340322502c03959200c0504446084c00c1c102a54140000f01d0744143e41c2403164800d004494800d1103a080902c13904040c44001c1c440c01643d190042000c200c400341640c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 643056861 1250 643055611 643055713
    0x2030601050d11013f3e0c0a240605060a0f12092301050705030a0c0c02090106031517030d1a04091401060501030203070f0c1502130905160c150f0c0908 67
    0x12010494601940558181e04042001c013027220340d0785c04055034150001c005503c07890700c80b02e65501003020504010004038140503142100040261407440405064810200c0c00d4018207410801c2c0306458180c901240308288100c80024004a40f4200401da003c1c1409031600429058a9951840c2c9580c015440540b80e003900c5402400a41001540181c5400d941240241155540003d503039050b5106080750103026130003071100e00d01d000320008a0746c202004441042e182384100161031900c0c030726001e001c2c0d46414074281e445403421551001340484481c80c8100e407048400200041c0391a440103508900065644500081880f1000e48080b8068144000c4c0c141c000e441d084031a0390303100c101e40c0c182d0f1305c2610b000c000b03240580300811503042d85010321604004140e40d00c0c01a110f655500900514001c03001400078039814052941c6541075030701802c2c40f041c3d6400d040c4001d01003100003920206451180701100c0c0b20786a031100b00c001000702e40c17101f40842c40b149882c0c1c0420451107000c50030707 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 643058111 1250 643056861 643056971
    0x1050d080d0e0601060507021c03080604150801060803071403030c040e0405100903021c0203090622180501150315091e020c070302030601050d11013f 66
    0x15907410280302c1c040030800046008110540c2c0d102e50300c003404d106011010308a1040304039004101118840002d803c6901141c2c007aa05030703000100a201d001020300b080b03580e0f0340304a505519141012600403004801480300e5070003040d0811301ca030030300307000c0d00d66030721084a802e142020240014082000f00e4485140c026014408450407e038602215400300c035003146085000d81d22804d50441c440c40c1044180d10290503500295081c80c60000c0840c07558450500a082220301c000e804084917029002214054828280c050141e00090341810004140c01c2c0145c00c0c0c1811445222400ca910a010b021031200000721210704481c5001341d1107024091911003005c00d80000902e0300c003544018400f4108a840c180c1c01050b20f00e142d8014503061a0f01a00410300800c2e01c3c4404402041c5400c0e1080003001c02860b24105501a2454249503e800b00d070030800212402c500341c0e00340030810100c0f40d5084c5d040e9201000340c0d0102d010031211000b031381c0b14100b1011841415054207003c5a21640c2441 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 643059361 1250 643058111 643058137
    0x70206150d06021201140616060504030c080a020304030507050603091e01060504020f04030204060803161e080d050a0f0b011b11030303010b04060f03090c050607060e010e030703031401050d08 84
    0x18600ca0380e564007a078026070301d000b130504410001042000c204451b8000380b4032040c1c5105162403010116080303045d40c40900980540e03142d00104040621a07486d1b0b940c8141c02c07084154841c001c0a900944950040c481501c41d4895010042054681101140e0103000c058004102a0404603034036203441c003900c5070079030095588000c000b49580b5540020100400c6000c9010f5445086204010441d6070381d03003003044540e0080c880d51070000e26408031000c001d0b800554508010160946412100d9003509000307014000101c3c1c1c10322813140c40d0b00b003e400781c07000400074041000108000b10031030300200c0742140022f81160b10602071105000f0452883c50280403008400c40002000c17a1950b4800e0303000360003614002a041182c5075006101034455100c9103401d100112080c1c556549000840c05207610a11001a04008102c5668084286600e00d02c00070b00c40184c004140ca5241d401c4550705601090074414004170324010282d0040c180c550007002016202031640b5480d20320303081045c1003061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 643060611 1250 643059361 643059379
    0x1506010e010f180824100501270911040e13051c021612030f030203060d08031302030d030b0307060c0b010b0f07080309030a0e0405060102060610120e0d090e07020615 73
    0x6a03260921151001d1009510001c003948002400000141c03001001840800705096084c040d036039201349c034009100c00010000c00401c4104502d100c03101c03201e9001801c1c192401e1004001c1c02d0510300a017044404449440400d6a40d074441ea882c1e40b030700808003c0141c0c0061011034100e80d8006000c039440f210b44d01c1201c0020260f00519150419541c0140c220031200d80200ca04240d80035101055003d070900e825815030400502207041c1e413a041600619580000c00000c614120001c035028103150000c0440d01e8920310b145001d402800604c11090207030140c007001140c9039000b00d8500001542c032944000d0355a1030304c02e0b00312098120300402c041d040006c02c00240403640850166000714403c10240d9551291080060218402404014059030400007040440e80e00420a26801442640c1c1900100b00b8804211360346850f10401c109d0031460041d0f880300040c000104038882c40201e44801d1034444d100d80c4203120405d0200d0784600140c0c48000028032085804e030754071018080240c9845070f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 643061861 1250 643060611 643060619
    0x230d05010302090649060608071707121a0a051b07020f0d0309270c030608060a050711070b1b06040b0c09060d02031501031d03090906060c0a051506010e010f18 70
    0x44496404001901c2d06d0341c4031074043c03000c4c12050101d400140200d256240f00c3d0f0348803c0d0517a440d51380600c241610304400310840424800711841140e03d090341d04500c20060301c1c0048050b0300078501510465592450110b5405c08004448111000c03950020141003d19280c0010054200322150044080107000e8800255400300c50986200800340318400d01c41a9680c180503801325a4030092080425042c400d08001469020445c0758026641e640003040c03e41d00c1301c0c029990203030146040d101c240301d07013400014a0740e400c202030300c55600003d005402c0004109440703562140152409445601c624011602e903400d04d10040c010b102020306041e00348888500140f0481e04120b8882c0c06001d59814800d420350b0380341c42485c007440c03078030031807003498240d0b00703c42940d40d025030741120f80941c08003030100c0d400d5550081540d145d00300e01c00446001d400d80c1c1c41c10715282d41d22403e00c24210810304002c9450741d1700400011403d50f1040e9100a02c09070221030840d010b0030f59804440014003504808a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 643063111 1250 643061861 643061989
    0x3102030105131403030103020a150e1f080a2304061b080105091320010306080a240212070c060209030a0b060111010b06040501230d050103020906 64
    0x35100340c44206402c86020014140b40b01004400d001203502500304000601c0103940341c600300c02c00d5415005410040e50b02e140402d4540119420049a0040c0005113030041d950501410002e0398845030f03104941da49034100d60700203580e21131080354000d000d841e10b0740503500123040b4501d52103070040d0000301d4a41541d003000c501c1040050190f43c00280700c1d00040c4900e04100710181e400074500e05600d260340b001a140c841d02c0d090002c0d90400301744050000c0c02000da01c20740284000d401007106032407030131006282010143c00e90502004800991031412a40e103040b41c800d503601402c600340009090303520703103400b114902a500320851700283d091020722800c0d1000c02c009107070507224004446490078800005040c03102c94001702501170b814404802542d8440d8401c1e02c040311003c1c2406004079004e0b0080d8810b9402803084201c4000001c103004a04945e00e4201c981260300a84400c600e079251001130160501441c004003150540c21040707500c043d6042201c0103459801c03151031482c404404424a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 643064361 1250 643063111 643063121
    0x6071b411209061918080d0f0f0806040b011808210c03041806030609030e150a0e0d06290f09010806040b06040219080603010e0f101e020a05120a0531020301 69
    0x10740c0e01b640c04403160b0b0a00d00c0e00b00c000104100e0b054244503003041004280140000d0005142501454841c401521300d64003a40c101611220802d608a10362521092010f0381e4030110346a07920314214000140320301400c0c0000300c500031180c0348099131410b41404c10290034100741f9207082c02450703900d84001011400c14840e640c0824070036515119210b12590800c44018650014904414800c201512100340c0081400001940650340910070100b14100714004001c4040000d100404c0780d00b10b2004500780341c0da1105840350032070380c07200080d4001c020301c04911800d0041e00d019074481000b140100e244c195910358032003801000546003e84018191490400c10311711031010032011818455589000e02030346084044d10b1000342a00c4100a101c15620300d0039080d500c0d04207684030380d05d540f10b40b98000b100e01d00d2000310000359030f40d900c213120080655001544220b8548520404108a103503140101c80c016420744a0166100b01c000d880ba00068141e0810289060200c030307196401070300c0a00407 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 643065611 1250 643064361 643064369
    0x1107020d031e030608070501111207030206090d08010f09020c010f0e0709050108060402090402060315101707020f1e0a0203010609020403020306071b411209061918 72
    0x42d902a400c841803181c0071901c89242030702c0c141421300783d003804807001c0000c9003002c803002482c00b40000030a40454031b081c00610070102c2651180007950805044d00014468058403040741116581c4a4070711003265840c00a005003002d02030000703070400c91601c0c942c001c6c0543d0803094000054a003001d0040c00300302d030407114186115400c5082d042202c0d400b00d2240300e00518982015000f20b10b03095001440396400244002e10400e000b0020903000002100c410444003409480c003254074100c7d03500035000d80c603608020720b80800b01800080c1e20510108600a05001050040114a001041d404451072004864210300d20079065804007580c0c023400f50800030544103100581c0d035400c5006150602000518560902501781e807c820411120540c4496032034000c00498001c03c00542c0c00243d07160042a01d090314114040014514181022b400c21503071565001c031000e05042040c0740c0618021404440d50040b020710070741c407000c840858803142110461911658541d154400c0966421413504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 643066861 1250 643065611 643065617
    0x90a090812271c03020a050d0e0309090705070c0311030a0503030f0901180b1302040b0306160e010905060306060c0c06040b09011404050919331203050703031107020d03 74
    0x4803840191440c10204000003906805003000d08a0383d0040f101004081e400d0008156000030007040340b91248040da4400b4100a1042c02040d030309106059981d04001c80e454450740b54400441c00160090040f15140c0d9802031600c4400c070300d10703140e0101c041c804070f03c050341600560303080d0340004409000940c4103485c20680b81c466424540c201e1401c40300010030309100750410741090408603030702c806a40e5101076240010a01d00050344045000391441c4050160188514000e01a040c407884140a0341c1c511595110001130b541100110f86025940c0f080c0743d0003442c10004a01c0c02c0c2003010062104a020901301d648021030b590201c4d50303a80c001ea0044501ba100881c1c500382540e40002e60701903000009880c0da04240c282800188600f034007414483e4000300004950a6103005900242069204201500480c0e2a04194803507401c00f0255105918241c04001280c661507001d54024110b0b09640c0e03140c14031807103650950040c644c131703900c000c86040c003030084600581e110426031003081c0c442d507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 643068111 1250 643066861 643066891
    0x1050d060f020f0d052508181507020606010e0405010506040b1b0706090333020702030a081b0106120f0212010e1c0206150645031b090a090812 63
    0x40b151004481c2c0301c409141d0301b070840c081c416001540406015009110b10407840810041090200c3c42e03c18820000b081580b400000c1158198000c41c50310703c110402c1e00c464081c254144c04200494409015003944580180014440150302c41e000d000b04468507c0401240c64030b1074000e038600303012640f00c3e000040900380700740b00b0405906051298480380484102041c030640708094080e50903503141030b10f80b07079003c211002550740400c107402d940794000c400c0700e980708000c12a01c400384242441c2e80e80c640d0f080c80320018914018400484545420074401403c00b00303142d081023025591840301c10203641d2140d09150b4000018041c100100c0c3c03e68400b41200e0300a0f920190030141c0003080c3c0c0c030500700300303800000040d1501401c80d00e1403080302503824030880f43d07034051041031442c44c0403401c0b1341010420b14001014243c2c41c1022602c1c0200d00b1141e0714148a980258140c9600c0b02064218408101003841c03c06950004821284285c2100b814051604100c0d03138611800c4a51055041240c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 643069361 1250 643068111 643068121
    0x18020a03020705070923041e03031425020604020f04020f04170102030703051e07140c0a0501020c0111040b2203150b0909030a1706010c050d0903110901050d060f020f0d05 75
    0x792804246986e030840680c503e45401d44a812842141c10b41c3c1100c40365000001d1810140b0990003c0080d00324403518a03401e05252540342e24040b1504984980601c1c8041d400c041c0ea400002c403a40720760390050680c11000b48d24028003020350000c81c3c6034601003409000c042100c001500384185080000c0c0c3c001070701da2415420040691b24050564024003101c9070801c40310300300803000d040d80b0841c0c0e4100303940c80c904c1180315456240706100d100c91090041c0361b204800c0040c1900203004103401d00000744010300c00080b8a580354070a42c8a4280e000784104241c402001c4400103800c0c03c1e00c1c946920040d0540d80340c45103604c01c07481c140c00c0807160360740d8402507149180c074055898101005000a6080807440711000d010b200c420007076840000e28070340004c2c12580c820800440301961010944584107040303c1e01a00382c1406c0c0c00b00b101d840f85150112412814603211850486000400c3e5a03049082910b40b140140085460008102d8003080f000d8070150010004042d001c003000d00004240ca41 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 643070611 1250 643069361 643069391
    0x71a25181e0e0c03071d211e060603120c1c0905091f06031a040902030a0203070806160804030504030204091104021303030e0f0a0e090f0703030e130618020a030207050709 75
    0x22060800c0c4441000070700040f41b0361210503000e6020180040420003459012440d00d02c2c0c4116421500c0d004042e80000441000b03010900e45d010301c2081c1d045801d50000a14881000d005540580c0000d5020410550b60480000203128180410341840a0342541f04c0d00820080c28003140c0680e0b480360b03000c25008400b40b800300030900400e000c0c0b03400c000441102c8074001c40d005200d03c115124945980441e025940d0920100e100d0550080444910540d43ea001d1920340740d04031114800062003080054109014114980c403070340d4142c3d2000e01e000d08650030000100b00c80a01a1100c4022941c0c0d00103a8071244010b000c1e0312019400d843c5414a5883c00501003040829000e00400410751062403d8a4800c500e0b01500c1c0008034111050343c501d40d800b4a0b0404010b4214028440c0000000070326030444002e0540e00b009451540d405001c05040c41c0a498a92203408500c6003640c54113100d6440a80c0604150f00c0d09190241c034080403511211f162111a800180b02c140e40c44039420381c0104 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 643071861 1250 643070611 643070627
    0x501060e15030106050c010f0203070c0201090815010e18010606051309090f080f07152c060106110703080708041e08060705071a25181e0e0c0307 64
    0x18040300c040019030014a000701542c001803144600b400004120200b0313210080d000295040080d690454407032070581401001803064403000d0b070108001c080007080381003000c0380400c0c0700c00c10b0f42200340c01d503440c104250344101d000818003520300e00c40307610360084a00203015880c01000c15030303140c5844a610310500ca02c001c0c090b600c580f0840349440c0390315001610760f1030307005407040e0081c0d1083c2d00e4000c0105004aa4812102c008110507920801d4111000c02d43c0d0054551000c0303c4520500c40940040c00303898910752030051102640302d04d0040011900c503070b49920b903c2d0708600580d000c07540d0760b40d02c0e596079402492040b1040704c008541481031411807041e040c00f05004000502d4001d00d85250581c50f804094038810411200044007404c1c0031030317140740d0302c034101000742440c0300342c81c0504c407484107005048801c00203061129649500944134616140b581c0744620740d00e03c001d03450100d05651107504c904005821280740030780023800004240c6628030a0308081c1080340d84e03140051000340300ea4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 643073111 1250 643071861 643071887
    0x10030302010c020d0c060209032d060f25090f030807060b0d0f0b070201020906040e07030c021f0e1504031d0d1109040c1809150c080708040f1203050106 67
    0x1500901644c1d5010780d22070004100780d90840c02c0180c0ea41e58010119042180315041c1003080003600b6009070443c0d040c030041c0142c0c2e800d004240c41641d29101d0340c1c00c82231102a2180d40c0816011020410141c03000d241c07003644000d09003401d031412503844028030712210143e4001d40f01a003011907000244074641c020200d250000719925106241d5965420041443c160b80107404814aa40000c4049000758100c4030f01ba0b03001410162969503c0044048000c0200d0702540080e090034070b02700c0303000e000203a920599120311a007080365060008100d00289094482c1c3d0415100e0281c00c036162031580b50782c45004134041da44a15192003001550000c020f20048d0345030095252250660100b0b44071801d000780e103101164200640c0e03c1d18100703032030010174542201004003880e03104441c0d501d140d0740c03105001d503100710440304540c0c0801c0904002c50360b03019410000716400500250720944202c1140342d02031b11419603d030054216403a000c2410034a4100307000845c0c1c1e101c00501c2a580c1142d0100000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 643074361 1250 643073111 643073113
    0x10c020c040c0203040b0a050405031c172208093006010509041e061a0f0409050304050d0212060109140924070201060e150f090f0f0c04080610030302010c02 69
    0x1030310700c2502c029981d01c01ca00c506841d501d00030544c40b100364420f000b00c0d030040400a080725554035001101da4100d81d2407040040c00f140349030034003d0701203414610003446482c0008948184048000b6459001103240300304480b0290b0400295103035584110185805c00e03002100d000152400400032420702130903851a1010340c5c0708070010080340e40c4201c41781c1d41c080e5001a594030303d842e0910000c1c814001030070000746481d040c442c2c04060f0000240b112190410101d07181d8044000769418401101c0904101400756001080144104e080040040c1c00aa1024041007102c9042c00c0c010750808000703821099a1580368101202c40c52a0081c11941055004014040400300110304c0f095003501e1381000c400705c2c414440082c00f105e0003981b00d88014064080c88030701d18030b4002d0301c500c00030b9504140180725210b41554007040b8145540000d200d05055404664a516410403007006610020030307003417a0541c100004101004140903030b50043d000c503043c1c240e2460030741c0b5001e42581c00c142568011 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 643075611 1250 643074361 643074371
    0x12040c1a030c0a0e032413020a05041a1509040b01030b030604030f0909090501020c1e0304060311040506040e153102070b0c030a0e010b06090105030a060302040509010c020c04 77
    0x35501200120703500b0006621901e540e0300400201a107041034800c1801d54180540c04100010300740b442c507a0f955803201c0b950408442c0d90360a0301030b91141b8003080042d401080c090000e09c01d03130605900c4006500550089039a41060080000f50342842a04c0300046071080170804440600303090140906090302428117100454900c40442e50352000240060308110507a500c0b400d41500551003d00a094020018444040a03081440c081d41c0302042c40c603203512500100450000c0030261803012240e03800c002e54070341031800c3c204802038008101010160b03201040001402c1c0d80b600b0082008180449170f09420707160101202c403640c1d4015140500410740111000d5600100280020620901341c401600c5400ea00c49030200a00409078002d20429424042c0044040024041d6209110001e17061014020f00d40c000d900340c8032080301c425001380c8140101d02080d8042c2d0302555003e900d158001070180c1da00d03000901503d20690700d00e00184d64440c01d10602c00d606200400500c0320030780341401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 643076861 1250 643075611 643075649
    0x507120903081c06090e0307051c0f110c0604140301140c0a051c0c0309261803100f151e05040e0f0f0d0801150e04021b0312040c 57
    0x40e14840e02c1c1c0003a003030380003801ea8000c103804144c0c4040040c00a22034100000741da58041c2558a502404007610a80320b6021104c90220b090f04078100c2c0d80d4016900c0001d1900264030582c2c1d04604140c44200c3c500518112280396241c02003e04020208041818844410801418219132a140412099190b0901000030b095406000c80e5280c1015251056690203502141ca001200d00401d02d511142800c41c1c00340c4460b41600404115406407056407112881900c0c0c07030800003403012090100300414000d89070309000300f00c080f40209c5000b030140c40504203c0c2640d4401c5881020420944a545003142c80546066859001c06402c2840d119816800944249103020508d44a02e910580e101c01241610032824410101d4010f000d9081b9495602c04104040d12000307410341c8100000d0184000190884162081091100d442d4460040d050310400500c8081c2d800000541d4200394010602c000340102040280138010721a0507000365828030f803620310301a0a095020b40d6400700d140d10300f20 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 643078111 1250 643076861 643076873
    0x30d0c0e0a05090709050d050109021f021011040305030c010f06090c0206241207090b010503011512060f080115050d050d050c070314010c020601080715140d020a0507120903 76
    0x842a82c4040300c2110311a03130f50803412180703514680c1050342c000303c065005e54108003054100344880d501c00c441d803100c8148030121520716040c0641d00d100050707201c9241c440c18000d4903482203109450001407117142c0b0b900d0b910392514590107402c4842c580da64616425069803924480d27031004d031000182c2480001310080b4000e50721100600b2030342d441c0404440000749000071200207504040c01030b210b80c0241503110052600c0780200c0c4941c0107401c2c180b03031901031507621410883e03043c1c640e80d428098078603000710000c031044150211102952503440c2404229180034107009401040741034000301e609424100001070488d515800a801418900b6154000550108111001103c1032401c1a15000d50300c0c10f491600c602648007510200c1d448140e0043d142c01904964048011a021a407181e40d8a280d0241c4d40d100c14031403580419103010503240742d184281c80d44110240101c515909103000b621410049a00040351440428000240c41040045202c0042c290a06a060006403546151109 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 643079361 1250 643078111 643078129
    0x5090601200a0210050415090b16051501270204060e24070c090e0f030d0c05070605100509010e01050f0103091a04060f0609061a07020d1202030d0c0e 66
    0x601c0c440c1600950320407001030200240b05481d03030000c182034001c80310200058003503400350040c00301c404104c05280c10018010309104e0122a01a1451890120f4001c000e44c410141d01c0003c94103030092284041e02e9058405405020b0075240034240e560014041a60b003500e54080704c40406e40c2d006110822541e46c224400c0c4200c56402e540000a6400000041504110010384134541400101d0854144070543c0d0b642015070705040820402d40d00802a0340b596a02c0400522240741c1c0100035460126440c0c0c0c004010b2200c0a080507414003c80741d4405080d548201c59aa602001c05030b010801480c041e07032181c0c0107000521040400d54140f4010808034000c81c07503614145a20341c0b460804100321034400881400c81601440e03090300309498490b003d4440300005034031a5041c0304020408000511035501141c01603411011071a010883d20360480c1c205120a0b40d2155034803019601003400610031100c1d10165502566075103c62a2104c012100715541c484100080e00300200240d03220107140c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 643080611 1250 643079361 643079387
    0x405030706110c01020316030b030a0c030210111e0c120607050702010c1e0201090605160204050915181b01050a0804060e030f251e0302101406040605090601 69
    0x1c08200b58000580b854490710909180380f12541c4000200100d488904024840110302580d0a0206c031040004050f5907102c2d003240540040b03081d890400062a1040e0090000051410300283c0c050410803003504040d0300000c42101824401d040e188910f82c140542d1448040450366446590a001e5074259102d00040800d0140400058004150ba010304040c0d01d015522401d9801c0140385068545180b08404d00308070b01080030350700080b40320350050040d01d07000321420500c0d0054a05980800c80038143c042d0403001d80d4040d03269840449181301281d1445808889581d0a0100c440c1411a14100c82c0100300307941000042d01c0340c252680e1010841c0c00101031450f1450150301c650811000506030101e42d040a8400000c1c0404614410000340940f121000390110094510016988662640c03c0c0020401c03054181e20a01b005204160307041540d007c5e1040701d603c11902d08160085610081c07440031003840510030040c0f146000c0c02200301418060b945044070342450000039002c0154001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 643081861 1250 643080611 643080623
    0x50610082208070605010824070f1b140a0311031608030a0b1e041a03070618030501140405060a0b010203030a020a03110f07031209031409010e090907180504050307 72
    0x220031014880800243e5078400d0300520100201e50751141526a50b603500a9171502d41c004c00c0500d64407000d06420014850b200c4d075140c40b0064051110201c650030000c4812104595144140201080d0201c000c1002c622150004000140d03803402d010b0035100003c0c044401c5a40200044168402c1000c512b540d0240e2090005032249c0791086140098044002c2203074008606c02624074a049104c1560007110b00282c0b0100000080112040d803424184800e241c0c040d44440010802184a0b442010007400d0304080603c0a030f850365112400d40d81c0688882c100b400c2158184001d004080c4000e94001000340404c100c1d640f0a48000303921b030301008201100c0690b0108241c462070f800380d048100c58000b941c025a958004c400103d110b150044c100c26000580c016481c8000703541c45100d5099580c0d015140c4040031001c00c0a82622a80903542c2c01e030402806040607800c40d2252080b081c003414100000c1c105150411400000000346951101c4e0001e00300404d11002c07803800700803228425002a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 643083111 1250 643081861 643081921
    0x80c062211011b032601030f030e030f070e0709080a03080a020306060c070b033102090406020f13030308090a031e2c0307050a060f030c020c04020a020105061008 71
    0x60750030a88658000c0d0344007400060a0f401c142e0310841c0d40048248070910462050000c0c50040c44205003400000c1c0801050040040031900406800940000c002d086890901d18280fa581c04c0504990104c0e50008203003040c04401c86e0054103910140c40300030700510703c50086440041000a0140c24084030b161b000000c500c1980740c1408940644070b0100842d80713090b68620000e1510b500440c1c0003825084440e480d040c40e8403007000582d01e102c2845107000c24010280d006c1183c05034005c1c10885040d0340c02c0014100f20071129002d0400c1c0d00002d01c0c100c1c1d11740e26500b030140030240004d002da403031030300900c06550009802900300c9180c1c1e071003200940395902c507101c02a40c03112000e4484030140068070b001440007000b5000035906088040e41505c2c8115034072800c0c81a9a03d00d409184040703031406419141c0b280c4a0b03402010780d50b085104503203040003904045000c07a8807114800d00140d4480007003000c030342043d03070500f1450226403400003c145031000603031781d94420346088400515058 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 643084361 1250 643083111 643083143
    0x1206030f0307120813110d14030412170903031b030d0e101a03071202040b190312170a0b03070b13030605010b0f09061c151409040c151803080c0622 65
    0xc0040d230080e041203007086135a21900c401d103581c41554805c0d0215220502c1c40402c19007101c02d0001d03030b1910b50340a40114144400c442840b4125242405107103814071040c070455511581d140680e111942018014040d000f410a60f0502521000c03252145e2124070780c40d18603502d071030000f80c5174200c1d07080c4195200c4400b00c0f440090023400713100d0a01036001c10620090003299139030903148404c80c2c0c0b084030300c0c804010706000300b43c0b40301c95641085514418100002401e81e00690028020701000030706a8034282e0f141c141130952600003c40040b03410820440c10310410140b441003170b024042020130203003014081c1d4040354040c801c1091050190308089403050b03988032007010b003000304202014280702e1445590100714001e4038902c00d0a42582110f041d002030b504110b44004d00690b00088011001410407010035198a5240702c40010040e80c03c0d69251244681042d40700610b204086540d59040915211450440c020780701c82e20642802d515541a6400c2d0351002d40704903440a0183e5056000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 643085611 1250 643084361 643084373
    0xc081501050d0e0102041d07050702010309050309090a0b01030f06080a0f0516080312220605060f090405071d01061e03090f0b040209100302061206030f0307120813110d 74
    0x2a0b50408070039282800841d250403030041d0090010303100042801074810320010b0400ca01c080c410740c0c8290109034208581c5026512a40064280c03500074030480f8608440040030450014045030324009150342d441c4160184d6a050140c412a600380c40d80a001490030002096115108200010221121440220100f04d0305001503444007568444a210941d030790409551a070b4803000107140d081117a0000110003501d005900081448241003000899800380e407a0310080202510040c0d2041c1c01e5011940d8a07078500380020310a6200c2c001426655140c40200340705040c860948080b503403c41c0300140f004550045072000c074601d040324000081190401c003500100b40080300036010940c9102c02006000312400000c1c005c910079a010130700d9695070b00300207070149030500009600c10002c04c10101401502c8940c0c1b40c0002c2d0040c03c0d0362210004120041c0b841c0c1c0710480440392810514a004003242d0052605175200c002c60950108031055551814004000c41070418410700d0262342034424840 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 643086861 1250 643085611 643085617
    0x412020307050904050d0207060f0c030e0f03010f0f0f05010608070e0d080d05100503030a022e140f06040b0f121501080718140106050f0c030708090f03010c08150105 73
    0x7401800b0f840ca5401c19040c03032030700d0324030a1031404003600c41c0301000581c0f98031441c0b540c0c4401c010756403980304048003540d048030708a43d800764041d030191504488850320344d400e100740100b0081503040080e1480c3c400062006a8242c44a100900d0345040300400c445c40e00458003d900c5081494070f003246000b45000507014000252000e0300707100c4040f484a80750245036104602a08400d90050910303982d031402c25640c0e108420a400068012440784090f4001d00815482c201184800300443c049010b20568200c61341240c0c0703914044121800d000010b0900f140264108005079418030070549000042032203059030009850058505056680e08042e0600602c2d075103181c00310110000d9656400840d0766031105000f03078200944100038284203200207200d00c440402000c0a8003140d030303213001c000b89c030365030401e10f5070000103001044581c9640b20140024194035209850041d21000c05200380100149081c8d15940a03a1511680d801c034035810002c0154024441340c00302801003091001221980 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 643088111 1250 643086861 643086869
    0x40b0405070f03080304200f04020a020f0d02031c181401020d0c02030318033901020703170f1009050705280f081012080c0a0b01290412020307 63
    0x20880c9000f20030007106100660049025501d094118001441c0e025074499840210365446040405284010300303180d009040340070750a00684440c00d0541030500d00b4111080100c0303006030070005420701c510700211900c60031441040805c2201d07812003040140403010341500500305a40180e980202204250115400740c02c8040b02403043c48605a07002c0e40d290401c0d103010124106901d228845250000240c0301012102525403000c0c101d02240101648010b50505446842002c05819208030900041401510a5440c802c108252012990700504081c10808440c41c3c0841846501c80c000c22024044d103480e0f4400013086d441c0c90100751010320420f481e207241403241c0b02d00140308041ca0a00000c913010103403281c1c050b01200e20001c8811500454580740d0051200c0700a11400b0b80e00ca15807003005100c2c0c20000c0c41c03c4014150303180340c103044100840d01c00034420b0051080340e003200c00c002c145000146240705003035090004c1081e2400303507004031040391004840c1c6505568040200000030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 643089361 1250 643088111 643088129
    0xf100f020c0a0b2205121308030a02030d050106030504051e07170c18160c0c03151509020c123103060b010e210a0c1517060108040b040507 61
    0x4007070310f40705803040740c04c0760000d00380c1503800070440144004407a16842c0780d60140103000107001701d20484155400402820340c42d00408000410200d50400c02484c1c00aaa5001182c9648440312150107450050308074600701410807044c07100007000011200504000120403020001503c03001c18034000702644040d803003a8100008940c0080c0110303081d040c00034241c988488080400040460b20304040e9500300003003100000c50620300f4440d01104011901c91460b807904696280c031040041d43c4000840706800b5070701c1e01a00e00b40304101c800c1300000c1100d6034096080100011883c0e440e0708e1282410005103034001640c19644641c00d681070488403041c0c0b01480408003d4048800f58030640c0000c803840381c6062200c804a60041c0c0c40084d62a1340141000420740300040c120061400b9503041c0071040c802d07440d41074000b84410071140040c00c0181120502c400e441d5000410340d13010541004c08000615041c03000e6640d1100c11150f0250f040040c500140c0c540e0319119242c2246648141c0385 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 643090611 1250 643089361 643089373
    0xe15030d05090a0b03151908061e0601021c031e0e0a1a040f06020a11010c02010b15030f0703020f0d1a01120c080103020f06090a1509080f100f020c 65
    0x10454001010b460040016940e940f44903031251542d460b40d2005076150b888408451550142901e06070711152922401801c4040003599240480c1f0300e04001510943c070301c00d100e040e00540d440c41e00b002e641d502901c00d20080454031552481e0b640030169008078001010b4954503a01001807002d000c41e220750304003040401200c445a0310342c0d0b84801c5019411036002c030038082c085140d11004128540500d0b0450601d0200440c141c1d5400001c6d13201c80d030504e040c03081c0d900c5840b83d081000e224101400016800120b241c465030800c21158009040c0320250460b401e00c140205040d82e1031040e503000e41d0782d081c0140d0b200c1c91480080614003584449001031420a039400c0c2007030b01c501180ba00c0fa850207032680300c1c280041480c00001c0ea002070f0015000201488010009850176030390b032600c030030006402c141c54a030f444400b05141c148550441110722000d509012031240d03001c2034010046c19150080c04401c2030000d044c5894004691000e00401d445000300307075a40c002da80c11650030800703003021504 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 643091861 1250 643090611 643090633
    0x203060405060901110a0516030306031407050901080d1b050705060a09180e0c0420161103070524040f140310020f04090905010b0a0305160515040e1503 67
    0x142c2e60a0440e494007141d4204912002d4180d0604191000010380d0740703890382801984107030203d8400c05101d0a42c00c2503161000000403c845180812408030303004003803d0040d0424003407010100d41a4041849039000c0b012a602031a0300901003540c0302046525010404150300384036141580c10381180b58400f00000700540c3c407d80151001c0700f2602e01c003054014454000d6000804c85d0101c0790392006076007004115810b40d19140d44280f44c000a09010030310b002c00100000c40d01500410304e002000901203051078140b040c1407443c90b50f2401c08400801003282030030302140343c1d240e80d10450031200b204940c164036071000e144299006080080d03000740107240d482d10100111002100410301a000700b0000098443d00d6008039060382100040b8545020314217a50a001804c039014255065580c402d17140150755110300c004001140a40002c00350712603075004844a0036015030159104010001030703044042e940c43c0a4500700c8402d900e1400703007a0b49140170b240b00d224100c1105945802403c9902c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 643093111 1250 643091861 643091863
    0x303060a12170313050606030d0807050c100c0e01020c04050103050304030b0a0f050a05010518010320061306081801091703090a0212030d1d030d1d0615040e03030601080f0a090203060405 82
    0x44000c80c0900d0440b24030380c440209249c0c69141c040e011500081c4c100001452050052000b40103401100f0f049a01580c0780204090444200700c48020000d508101d14615540e41000000044601101d0030405540b56540c0c1da40d41e40315500c401000910300d14001208180290b01210884000c440180010310b03007041d03d240200800d005051140203018002440054547d42c9203060700c0d80079144101301120030b55000080310000e041c040c0d104408101e00d54006400e124494003c0420740c8410b80c1d01d05004060082c0c00a5855408680e80e240501840c04940c0010120081100301d2040031360b00c2d114049410700b400f9005201030740154402070070400f40400040200000c00c2c001d0010080c5010b03140000d481300710b030180d040300140d000303018507a007092803035204807040b29843d202d00e0154440060034600301f010131038000d4195244041903800501b058000e456400d625100994558071300034001030305103203025000c604450550000910241c0c1a6401544965001001c540c9a4500ba1801c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 643094361 1250 643093111 643093141
    0x1020a02101b080903070804180f020a02100b031908030a06050102030a0c0f03050f03130b130507051c12110c0409021003090203030d02070f020a0e071e18090c020607020303060a121703 81
    0x5504003d04d843c004a90b00c5004e032081c0c490300b103c035074080c03b0080c00c181d07103090140c00900c0e00d00e0380c18028252041120305409400001c0d291180b08059181d01d0100b462008403085036200a040d908108600b1241d20f03404140201100c0d8444445070307110619090886d20307400790905413600800c000041c40303940e14010380c80e40810b03849400c0804195036604049940b90005600c001d04551040405108500d031100c10505011072b03546000303041030b0b455110f0403440c0c0e00031102a0082903004420600741c031002d0055540812040c1c4090021031500e40c041200036411001c0300080541c1c07401103c045550500c05c90310561801c203010754035101c0e20304000d010500d202004910800310b0204c00203484908480740c03880f8140503110401103641c03c04180d99040000503011080012006100342c988000c4030450002d030140780400a04881b01ca2400780c58520080e1680d02503600900411405950f040881c1d01542d2755070b40300d60441d00c242e182a25a94a011000994252010082009074601d040f40 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 643095611 1250 643094361 643094399
    0x40b0c0d0207050f07141302030a0e070303091401170c07050a0501050118050f0907120302070302040c050406020f0610060e0a080a060b150304020d0b0403110a0501020a02101b080903070804 83
    0x50724042695504800c0b10304c10070701b200d0307034000c080c000b8113504000130b941c09036070710981c3c44c00041009000402c1440c18149a03030400c0703000c50b0050f02c060100e03c58119030701d1a004001e013400441c0b44401341503049040d200503c41049a040003442804202c03092000080980d480340c002d014a503181c5c1042074907003c0001041c404245082d00043c550750b02185601c1c004c003c00e201902019042010010f40050390703210640a61051900010040c0c031584543c5184404503603e4540700c9003000002402c10980300b10811386940301406100040d8210074a090445016051591309542d0340008607110500e198080385460055a110703000340511a080100b803207000f00c0c0c001c152511440881e407001d0205460194110307540c214007000041d007103400036802c5030086c200f658625a03160049071030804e01d090100c405035008201218074540400c0404114075841c1c3c0c060225180795115040304004a42080c41000001004036580300001c0c002c5441003034020002d140d40c0c036254000b1721081c12581d91 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 643096861 1250 643095611 643095613
    0x20d020a08031b16060e06041505030a0e030901091e03050303012c010621020d0c1101061a0706090606080303070e01020d050301050d0b0a0f0c0c05190b040b0c0d0207050f 75
    0x140b40e543c401c0b00401c2d0019050740e000b480071501070401c1c504803608601040c451f50042e45c1000007160034070001000600284940ea0f0b42a86c03403803c001200c0645508010785201c5070f0042c081e049090381c00206190035680c040301c00c400c102800c490b00aa04540ca9403015045000010010401c0452000c16685c0c10290f104802c4160700880b0140c0114202440b5500015152048071420300402848048120414060140c03c00f85c100034040119400f41603a03c0115400365080d040500c820b000701e01c0105281750507141c0c0180907540c0642d50303200303120000b4200c6560740916410080150301c1a80a0201c4900320b076200e191448002d001841400f025501500c1042c2060005c030f445075044a0607604050809e8500c00e5031a80c400c9981000038040051503030b00c2d42c0e200b11170a115441020364401e00703650ba1203111021030500340d0910b002c140304003140d80700c00950400880d503079078207950b00580e11108882980e5200b5125480b24040c03082701c00b098500008141c010b1010010701340d02000c040d40 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 643098111 1250 643096861 643096897
    0x1204110a120b0f01180b01020c0901060c0b060f010c1e050d050a141303030e012a0605010506071124120a0b0f220204090e03250302031204020d020a0803 67
    0xea5090f041d00d003442a0382c024013540d0f5800c0b0950420f500030801440781801210801e900000024104442c241c2008000458100b01d031000c0c4820640001e801c00015541144620300050000b4168603102e103024001705803090080c05c02c4400710200248603900034040e50020038440800071300310351011110034002941c0070403601c1143c500030121001c6515400c1400b203403e00d15603055819046030b448180c18010440c280860f81913048100ca941030246e9951107d19094500e0186d04684040c0c01c03080c003543d401d10682000030b0308040255000d20013140c6910390803440c5141d082601c88840003250880c00086800d2130003152110009024a4941e60180f1100192006020400310501d504581c080c0b00c038107115161008286103c400c1c800785071005071829860b880c0d90010349120f5240a5200c0d440054104142d0030078041e05070058020840d507141148076614000d60b607000e202c20036081100080046411903036080b281c8807100340c1c05005806101da8031828552613070089100104054202 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 643099361 1250 643098111 643098121
    0x1c06060803190201181212060f09060803030103080d021b0d0f110105040f020415080105040804050a06080417090105072907020f03180103020f160204060b040b1204110a120b 76
    0x60240080380b00d040c2260403046a900c0e100c180d10300007070320809028041f500022403085400d9000300e40103480c0c100d100711301e014a000c85440840c0c10f075501001c5260410b200500000c2d10b054200d411340d10382c50f180942c46241110a9040c0c601c100541c2c03401521a20600c9940da0341c100ca20401c03407101d282c94044100c05e0401100c1e090700c4048174001c000c119106003040c01454181d00c05030000c0d10305100402015215031640b401c581080d9016110842c0100701005549882103011001d000b10b031505c488107042c035980c0d24001d012000d240502444010443c070680b40d100302c043d1740800d50401c9003010990600c1c5040100c50344251004101315a4640008401500004001340404d00d050003c41c50303c01410084940c1d4001c101c2128101034080003044504040030780070302000c42c0f5244d1030900a4035148100030031601c15600c0b115046c40184420024150940281e07221540d4039031034800305565500e040096915851629544490842004602c01c0712080c0030b000307080c1c824181d449543c1c41d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 643100611 1250 643099361 643099363
    0x723120d140c0c03070308101502060103171e0903120703110607090b07020613030503041715010b0909060109090528050c07020d05100203011706071d1c060608031902 73
    0x604444400c155001704600c60000f40300d4031005a001c69070f1000c000e501c035241c0300c540c090304c06030142640c01640098014024044054840680711100a2002e03180021180012211225042ca00141c0f0310022078000100d403400e120f22002110b01070810f90b952105c514000e03002d031701c01d40000b5210303109407000500c5050113003500c40c00780c0f00b01c560303845d041465540c00c00115a0202c201c04080201c041400400180200003030f00190050102c0c4101c8107868041c1c8c0c506c0c10441c40b0f8080911924280108070003407c40301200c0015405880f40000c6955480058400010b01d034441e104243c81c4c003041201221140d080c100800c505500c440580c404603843d2075040c4c59041da0001034044d0b0821018005251100740820014816001d417007150495800f50412a04240d004281c07841714605818201075040c08201d900852a0030400040d200506c85404140401080035006006d106400103561501030039a0b802e1036808002804050b807525011502c9800030440c0c00002c2d49101c1800c1503042c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 643101861 1250 643100611 643100617
    0x50102030f2202150f0c0a12020d0f0c1202010e0d0905330714060f0a0507050304150c030e0102041d0124080c071a06090901020723120d140c 62
    0x500240041c140f06801308210010b5440071691103c8403804020796160f0071420710100802500030702806c00d03034406040000e414401b0300c0b00321071b0801070b0345070030046296041801d038814903070051107040b1140070a50060f401010b48149031242881020101c0700110303072100441055410985110355550348003100e40800402040d841900304c02127034103207000f2405150240c0f81c500d010707035056080512011800d5041020a81d0b4190f4803059074810401803a58600800b50411424503001e8a50300d000d4450011160483c11402c1d032164650f0034410030280b180d0000c41c503591801c13008550b100e0742d85451100c60b0311144034008810b07901000008074500c041e001241c1c21407c2c2240507100000d003050840c0e03820001040541140d5062040b440482c01c0324000340701c8038018080c201c10a09251003003103540ca20007051014680e004103d03440c001a00150348454004442103a04044040b42034140d090076035000007144100401728047ca40d00540341c0107050608640e41c0c021231585c8900071400d82ca84 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 643103111 1250 643101861 643101863
    0x106030c050412110d08070303020c06011403100903300e01091a0a021e28020c150706090804091a061c200a0809010204030c120807050102030f22 64
    0x10030700300b01050004aa88514a4000382000c1c0170005c2c982c2c640c040350700b00760002e500003507001c078610504020400107503001d054071075a880090100c510002c0da5230b003014401c984030326440d00310304006c250091b8061854201000e0305040c441080f148130007070131000c3c030841c04809420121040001d41043c0300d04801c0030341002c1c0e076022800440806c0c08403900c0207403010000b207030300f0010888960001d00038426056a50b040d02c0340e40300940e82d25060490300115404180840d0b101548545c03540008a60300007080590320310004206582030307045103000d646c001802d0182050010800c0003070450090090b50907100d01003240c0d10784001440c100e0180d03080910341240e4200101040b40001081d800e102d40c07002c50000c9502d4a054541240c180d801d0010031910850114207a0303001e681194906034810300d000001c504181c951340320380000745050f00c1042e841171040c000c4c1c3d0003800704034400c40d0b12958000c0001d6541e414080d154072100107040f1282d401c2102d1102022004154510000f1816 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 643104361 1250 643103111 643103129
    0x1c12020129211015030501140121030e0904050c100504060f0e040b0d05060a060506120c090310060e01030b010504050f06210106031b051206010e040201091d0106030c0504 75
    0x620500b41c0c1840c0228818205030407403050b070a00c0030042081d80204110300000407084590380b4074500c0c0140c02d452207401084130b082a80703001440085950b0083c080c0b40549031042c20b0400c2103d003010b81d40385181110194001c1c03004005c100602c100003a8008903c9030654400741d4010f943c040c11a401d018500a500002d444421a401d5007442480d5064070f4803801800010010320301400140c00f035035200e130100e4041c5c0242c41000701c8984103119400003004140c803c98a01201d904a0015282e002004000c3c40080030074411011749041000100e002804001003100c00c2e1110520910782000348000c403500003141d400403c543c18140902ea000724401c1c030881d146034449104000e401c503100c00c465401c41d0040c04c105039020b8405d01682000307500419143c6181d000c2c07040c0d800380340c290350f41155008200081111001801c00a203960449802c5000160642c4072840121100140303a400b485400301040ba00102e9061394281c2d040c100c0340d43e81c4007040721416802c8181c800780100d21503a64a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 643105611 1250 643104361 643104379
    0xf0807051e090717040c0e09160b070f0804030c0f0902090d03030c0203190801080c011b200d0308150319020f0a15110706090f03021c12020129 63
    0x60030302e08010303a00b004090500380f0b9690b41c644131181e402942114281c03440d40e00641c040122840300810f543e0400009400b4140300c1d100700080f04151a4070340308a04140b0000590300060021f007480c240290b90b444028540e6503035803811b00c81d01c0c041150003104d407000644d440010b000e800301c1c421160700e1013001c1c200304c00d116001e8806800618000d030a240650100b04544440c0a000c02da11828888441d200d1303500550405507501c5c81d14441310215414000c1c0300a0a00c000e1054041080900c0d500440049e0b1031821403141c04181c68089c0c10058100f02948180000c141d0405201d920812102c2c80744122009080100355403180b6540c0c15030b0040c0500725401c8d0250600440d5481500c078040c2000136850340e524684000d00801005240c00103024021102c0255010301c80070000b07094510304140b034603061078402980e03a142444000d10808016054441c1c0708214441040400d4020707000182a0030b100001074040c2034051407a80038100c4024011a135800d08500680c00c0b241c014043c05a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 643106861 1250 643105611 643105669
    0xc10050f0f0604020c0c150a021e1c0905130902030607090b03060f18251d060c1006030809180f0c031306060b1c0203070807120b04060f080705 63
    0x80d804103000e40e405e8040e42501c004180c503440104840c0c08030381d4900715940d4681c900e001b400c09903c00c0c40946115040a0080c216590014a0303488545460407014031034040c520302035451455550011f60440166a4a160300301501c0d07000c1740a2a0007507085d01d080355901e09007100c80400a0023613041c02401440403500504084201400004000e042105503071621801d03003100081c21203902d00c48090000060301c00108080010403100518103001d049a000300e112007011040c4040c10901420020801d618880e2042000c1c0b5200d050301001000055164240007013281e000a5129010741c5100b010040051011101c00384101d016134031412081d2100020800c2c1036002800c0c07200352490b1a05103502090a81c8a03100040200c40c012554503102c00c5010384104d0045c501106003140b041c8100701016400039070b1542d00c01010b1405854142d240c03c030032001040352022080e00f0514000022039000400c030210800c1da40580200c50600b6900e40c00c00c048280b008082040d00840b12100304 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 643108111 1250 643106861 643106869
    0xe0f101101020f0c0604030e1012151203020d020115030302070306020a111507021605030c1302040f0602070801110a021510030803040303150801150b0304050c060c10050f0f06 77
    0x4008200110016140080f0030810b80d500360012103003115550000c02c24042010307000680e0300d00f4510240c40f4000c40d120b4403900548800c0c40c142c505110103403105109284043c840362200e01801415017501d080340c042e410700a50301d03d92102420059860303e903010030800072103c184070840342e1650003840180e086640380b9020b500301d84024024424210300301b0300b001109100e41c0d1003100b90910480c61900e8592802440c00000c0544003c000030540400d100980300442e012101c3c420598050a0220014507180300910803584440d0202c0711121003c10815408501c1e42d084840140003030044610321603440c2c1c114854811180b01592140f03d807005044903c0b414184d01c11500014640495503c1c2c40c0c0c041640e000715401c500181d40c51b0b003020110360040844601405121008002c01000b06a40b00b2003400140030f84000030300040002000c00800700a84803214402600140d1078907040d5403056036510104100404050820000460000d000c41d0254880c46a19401c6034035900c56100384 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 643109361 1250 643108111 643108127
    0x130b0f071515062318120a050118030207080f030a300903120510170304350102030601020c040c0e040510051003090809060c071806060e0f10 62
    0x110286480394031298070762090b240540000c00c03550700d13500a0b01a000340d040b10008071554a000c42c8000c1800340a40681244110001196042d103600500030307980341c1a14507202001c0402002e17036003080d441440c280c80300c0a00b400c40c244070b60200c82007162100c3d83c0e5501c0d1050352803404416802884810401481001c0300399804c50300c2004600318601c40e90154028000c0e25441e140780c552100d8000e810036074400085510121458007c118a08041d6404262819280f0401c03801c03e2810500c1554280d050003100c000b0582004040307a5080303610188d14054064a88000c51142d521518685d80c4006000720fa100e6101680a000854112804c100c002c10072074450b070007000b039481c0384041300d1f498500c10f480c0500110007424006601c1c0c2410880302071040342c0080d0030982081d00c1c08000a03683c0080d00e00e0030000301c45c03494884107444112850310803527070300c501c00045100328035031003804290b4002e10990350035039240c9080c4105202130004070b6980e1400c0e55040400c0141421034284601c0304 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 643110611 1250 643109361 643109393
    0x604121404090f1b11070513020f0c0607020616020c0904032609010b010203040b03040b04020f0a03030e03070e0408090409050f010c0504080705010f08040f050316050102130b0f07 79
    0x301506054650005504582168811800403079a548000c2d0000c00300050b598102c0c2914545007031108800030501d0b4860600d0301c40c150141d101005003402071051034058032202059120001c2c3c0350401001c416656880540790329015001d03041c0440c40c4204180400400c1080c0c03078005004084068050241b164001441541007080300526168064101c0c02e070000403d8814101c26120b04100c0c55040c2120328455000b41503503c20401040f403141034074144d03070703002d6089071401c92150350301d0010901084202d11a1544160404070100816812241549000a0560440b4821500d9030349004001d0003c0e0390150940d8000e2000002c540381c42e400003c043c0b4030940c2a90000c4020100d603c4c250303121400c1080200704081401d003ca03510400500c00101000d01e0142c0f646841d011014081150180018000044070010b0f030040c0b100c20421292401340071401d00e0b40007072241c01d01e58000d4022103030302c0081d101c0072840041c82d0004602984c45004070400d031945848140d540b0750710683d4007400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 643111861 1250 643110611 643110647
    0x30f0307020c1c020f100f050d0f0c020d0908030405060316030e240903032a0415031b020a0206030a020723061b070f0201050a05161211060412 63
    0x440741102c2e4032821151401c011814000303041c400f5451040110035500b40d580725006200200306110495444404000103d481d070912a5485650841e120050300e52111201071090401e20360400c01a400107000450840580e81c0045603510707411446d4680c4124862654000310900100301140b00c911016050448a414005140e8200305401828004001c0304402c0c58800c1c1c41421441800000180790f01801e28001b542c650315101d4020007000300010b150040aa0340c0078107204141e501ca0040310003038941c4000c00110381102d200020050520303040d00d50090550450920001400040d01501c450f9008001c64110303699540c4200094114081c152982e2104003a20072103145001882982441c1360300181c070051070010f44d200c40201c2211003000c80c0c0102000000c020400303804050360b800c0da0910304660303500c2da8242c0440d024000c640001c0307044200e01c22440100000c40c0c4115030110041e84603607003501d15000216480e603c5c212005082d01d0704148880707155078843d241c94407080840203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 643113111 1250 643111861 643111873
    0x201111c020c100203010501030e0705030a030c0503040e190c0804030e011101111803011401080a0305031e15030c030d0804062703120501052e050415030527030f030702 74
    0x900c03070b030f440c0641c0081e4040311968000014001540d06000300c103040b03032141004000035840c120200360386400c006006003c000c100100d072002c015050044031b008044075001015941446410284000100303045050100d02e0049400c9070940201c00c5548901c0c2c040d1107290b9142083e800642c1c0c510071901c0d21440d2035698203c5c289000c2600f4003d4401d0140c0c210380c05000301c009005141c01c5900c00e00070b601d0400844401007040c51000913034403902c01d91500d0082d8132a100c40b00700740141144141c13104100e02c426001c10084400e420320b0084081011400ca81880d8070305002c1c18bc5a10310040501e00040000001a0100e00550065440c0c415000311141c0301020a40310b9403102c40b04600200c0012322969860903c1055500030980545400c4610f80003501441049010351600c1000c9100b031014000e9202c1c48030703030055003610020f00c001c07100f040030704096600090041200310b404005c5035074204c0042039a01c0301c3c81c2848a50311104002146080b000d000800500d4200500d0340782184144 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 643114361 1250 643113111 643113127
    0xc121002070503090a0906051f090f0806040209101401050919032901050d0b15131415181302040212070e010806130c05160c060f0201111c02 62
    0x40c4014030035140200041d58440c07088404012101c04030364010440b2506000c424891035031035090007401d40d82d40c06600b000c0d180c5651000d642010b03142d031100c2c0908201240018102d01c01180d880e06c82d9100b01c2d50b4540e9a42d540310f03011908140b138050620348042e0040c000a0720f5008000034071890314020301101003200c5211411050340c1890300300701e441060049941c40300000d103800c09503400320150b4480f40b4541c10b04010814110300c050000c0c20003640000400e0245028014000d42d24601606c00c0e0612024904010007030901500703400c2c2040d003074030300044400c4404140c0455281c0014000711035802c03410f4410041c2c420190400c101000d8054a400045e40ea520003020143c0c40019440b4142c41d007208060008000810b290341442039140800110366100b514080d4620340c00400002c0280300d00c44c0888103170007503203400c1e285540710030408002e0000e19029035086031965038401900c0c600250702242a01e029805101c1098402e100c1d000c074900700e5803180380361061516001801c01c150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 643115611 1250 643114361 643114393
    0xb090907140301061e06112103040206090d03021b12070302090c0d06090605270a05070e030f060105040b030d121a180103020108130b0a0b210c011e020c12 68
    0xa000841542c2c01c45c80001c0202c150000b208941014044001d425440c5080303158035032003040c000c180c034050280000014215603801049d00d1014a000d042c00c4070300600d91401941c0d40340318946a20801420a58194036458100200007440c203200d03001c1c2c59458074517403d03c03004100c00f0300804100d5505000c100c8040160780b180324000c048d00c0d880400c0c164604418854218000190201c1c182d200d805114503d10b803840700d560f00003400d08000161540c07510f100f01c1c3e06c800d0350354415034180500005411b00880006109040e90b600300d030b0800201c00040300b0996951250703420300002c1815407440c0030110503503600204040c8000c0020060221170040050701003030356680307a080d02c0310041c80140103559200500a601020040b24039400c00d03040d441b440c1060100a061090540c1c4034103c400c03098036004041d866114100e600310a0101c0c880102c1600c5082e446030040c001042c87d84070024468402c00a402240c043d0b070040d02000d5007401c1441b07054440341d01486402d1040e20010202500 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 643116861 1250 643115611 643115639
    0x2b080405090f060a1502030711031006120c080601030f0303020d110c0d030b01030c090509061311030a11070f1e0b07020304080c0f030d0815060307120b09090714030106 74
    0x40d002d0401609103081c804000303c80159070060b40303103a0300402414510030b40000843e0300c2a908844080401051140020300d001e40e40702c2c030340030038a0822500280003034040c00020b20b4240b003040302c0c07510140c40303004050382c0e102c00b40f101070280d01000b40c86801080c06030f0700400301c01410300000318100180d06908d0740c541d40f0500c034402c5180d000240443c1c00981c14821140140f100740307410700258070b074841c00034908201070081900c00e0510700c0210320140e032882203003c15600c03280803c0c402500c0000d84420a0f1700225000722800703040c18040203070492000c3c102c0d0307040c0c3e521040f00140c22004d0786800300480c20347c9000135207850300040b1640100b902d00c100c1c14420301081c0e0042d6a110b0820900509040342c0d00d8042d4060480c19902950566004c103441010140310316020003c0d649080d210742c002e201e034039440c1d0303003000c80003090080a940c06000107107880040c0d1814403c1c19454010311100c4081160040199005044140400e00d5000004031107548000e0011540c0f507250402c0506910b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 643118111 1250 643116861 643116871
    0xa050c060c0102070b010b0d0c1403010504020f0d06031a01080d050412050a1b1508090307030f1e022409060c0a0212030906060102070b0f0d0902150a020703020109052b08040509 78
    0x207e8045103100d1080c80c00e0140e4180b034515480d10f501102e203c030324100c0090006008042c070a03500401c10308070035606481038034458000030a05003c1709940e070400c0d141350b10710f07502111308003071000c000428000000581e42024030000da41c0c0078945442c0c840c2e541200c029100080300c0034002c52080c0000705090035460481d40004004014000e0300c1c5c640002c44120444420f44203110130309042101101001c4142d4290315007508010454080c03450302100c00d0500d02d849a044540700d4104902c06650020314100340240600c1400e86d510000c4c1900c00c441c100c115000e0600358081000154005c8205001c0c10407501c550049807004203400030000785c650400c55825103198070a1041110642c0d040064000a1640300041e0b031810101d0f140e5060f040c0704903624049925100c1c400041191078861341c8281d00e03105071010f00d40314044007070004d454401522041e40082c14540f00800ca62424070030325401b019020030310005060a2001c80110034640034000e40d03080406100020380d5442d0055018456 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 643119361 1250 643118111 643118129
    0x4060f0f1d042c1c0e0603040303060302030a1a0708040206190909060821031014030c0414180c2b0203010207080415020d0f051b0f1b030a050c060c0102070b01 70
    0x200f28082c000918186107a41c500b00d1105030824181403050f0492403213156980d00792140d50796a0307160700b01600540140c2d84001d40601c1aa01510b042c864081c40150400208900a00f8203890f003941c1150711003000e6402030b600032010002100b00d48181c1d940003d14030420304080701304c141c0d910046400c661065211410315008201078049144503034540307201440424143c0341c214100290f1000a11100d4002d150303000c140c042d065103541e6410846d1000e2442e00500500c1080d5080c11700380000641580ea9005449107008686042d01e00414070607244840508104139400222044c42c0c01040c4405040c0c1003c00e15495000160b10b0038001003c00034003c8104030750f11031a10902109030b698245000086400070055041d1041d030025a0008400f030a1138007031707202c4009040b900001280d40b0780c403100d588101c20001040c034001150201d01c0d030900710340b000844100342d4149501c0307010740d00c0010315a8100d4401c2500ba40381c00c4000c0e050a0700a0400181451607039039502c8031101082e0050038034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 643120611 1250 643119361 643119431
    0x60806011e050405042a080303041406071e050f0c071d18030403080a0e03010606090f0b0309030d0c0c0602120f0a0905100f02070f0804060f0f1d04 65
    0x42818509240c1c001004161410002031a054175000707600180842e20003e0801c249200b40070583d83d40c0c9015028000c00c0c0d054940d030781001e1400f410801c01c1e0b0400861503005803000100c0c00b81c060391030040e10318814184080d041e00c4803034040306d0307643c0902140400304005201804191100b0409900a0f1110000c0600101071514202c280e06100420b8655030505650594078032610101c244c60071260300034005900c61010347c0c0203659802507020341030b416600c0c195000607026031019090082350b00b040007111001f511991110f0300e80c801110b5800f4294400c006075080c2c1c2e41e469002c00783e180300c6450050803000c1e503aa2a2404d992043c1d605c011014110800e01854405a0520680086d82030307008100b0b0040d541d544075103a6095511000c0034035640c00c4030007019015a011101041e0388014540400c0300700b4609640540c1260150302c00142c0840d40c03000e03019025200c194031141003502c0303a4012031110440c103c0d451010081c0e440c0c116894559818410107070b010300c1c4803007071a82080054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 643121861 1250 643120611 643120649
    0x80919060207030e1507081312150c020f060609071103030109051909020f10030221090613050703080a140a2d0f050c12040e09070927030306080601 65
    0x5456414000b901c03590400341e005c1d80c0d100e9040100c42d02039a100820310744481e8140329040329403072150710521030603007820003c0c020841c06001ea92141d810180f010881951b850b9000c80e0340b0b45401c0404032040d449800810400d15000307000c107502c00c0ca242750400ba600c03055028541150000e9215585c1151500103000c0500b000e880070b00c3e01003e140303504229502e09a00020410516408070600030350368410004855407103601100c0e80008110702640700ba004800001c0c0102508036401c143d6400780d080450b40603464020550301103078002c4001d042150868540d2900703580840c01c15002d00160343e40013690841c0040140c11070301c51036120742c103071410386011008044815041a1140111041c0c0b840445500a15201200422840c0c40c5445e0b04000022618000340315201040b60000418000b811b41c0101a04038401c0d50460241d82c100b0f40d481044c1b0b000d8840520804030640d00003183c00c080c3c000e5003061410308500900d004928561f0752001070b410070b0402e8002c030019a25501da550 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 643123111 1250 643121861 643121867
    0xc1009060e0105030705030703180503041203030f050f011a1603030b0909060c040b0a090e10051c1a0402040b040e030309160b04090c1e03051b0a0f08091906020703 72
    0x114650207003056131852070200b4008055100042c0b544007899661000600c0b40840710303956964141d4840c044035525525400c02c0c03418000c051200300c0010f82480c03001d030100145405054014855030300ca48405900b8050310340c42c140308420911012034000c2c407a400c08046540a0b000c00a402900c002a005240c0c2051041031032009143d1000c560101080c0b01d0541894800c880c00c590840c950036803140b01e2814102c5810801c0e5015026004046080c0301c24000c46103010400c0315400c44494140c22440910101c080c0d0607000302415850b440781c2c1c0140400c0c0352220643c1d02602c01880052000000800607040301e003003034411030b215030020080004400c030800842e0320b014004007008035403a10341219140c45d44181e00a007281d254403400b840a00b140140d2540e4040311080f00002c42c000600c041c0240100b50441c0c290728000b090b0030328418203501540403598005490340c2c500c02d4464030702600381d588040144c00c03080148282072110b01a00b80c03424a80004d50302c0790301c0150b500d42c5541001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 643124361 1250 643123111 643123127
    0x3011404050a0203040b220b0108030301080c0102070305150a1404150b0111060411030f06151504030308040219091409150f0103150f020705010e0105010b1e09030c100906 75
    0xc02d803030510400038800400d580c08103c40d0320801028104004030160700c03c03000350415901d40104a102c41c08004143e15034084050340c16aa4104121003000c40c01e14012a603d030058400900543c0001424040f506001c00000740c0c444070042001c1003600380d00c0d01c00c81d42d102040f24180c501c40c08c0c010018003016018041d051000a003441c20000351840003480c640c803000702500c018026600c100c212040754030140110110a490305003940c6542c5460000c95403443e284800c0d152055100c0300068088802540549050742d805644188090f501c0b41e0900445800066600c0d88800500c0b000151043d041d02542140054486400c00103051400340c0c0c03860300354000a00d0702c03154510410030440e024024170850440380c1002014a071001c550140302c1c014902c03404003144e1743e03000056050600a054110750b110003c80300080089a13614a17407900c05001c2c8002c850480742c5090181c80e40031444a014128204004041c3ca104140040029500780070f20001040842c0b490300e0104819a009a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 643125611 1250 643124361 643124371
    0x30903091011070b21090c030f06010e090604030504120f0b01080706080a02120705130f0e040210081504021305190513050f0c1b0a0501020301080f0304050a06230301140405 76
    0x41c46042444841c1d05ca61243d000c4100e400481c1100b2000a01901041285403280e950207030545800001580f03455440750400d000c2c0a40007540400411282e000c00a1020f101e01d8140d501c4a00b007506080101a80c101840000d4944072041c00303032540890510316641c1e000784550320003050a149001e9015002c2c4030001c00b845103941c41409079904182d414900c09078481528a0855500c4521503400f414440c42d80c0c0140342d4251001602150321460810f555004a008071003080148681500031030391280116a41c5001400c01602c0d11040d081c03540150421007010341c40741c1d07942c0e6290008107405465400b4403010028070401c0400c52030504c4032420300390324000b410901092a090f100500b0190300603101c0c41140000241042d08600c000e0792390054000007109864080d20300d0b09040b4040d400c00e0082005078094101801c54450001084404480000d086030180d5454404d003a6002d14540d00755050561107403040780124003006000718043d144084100e4400260001030100310744000700 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 643126861 1250 643125611 643125629
    0x106030e030909150612010b090909030c0a17040e090106170615150702040504150b0a08150a02040f06030c030c080f190e15060f0f06070803090309101107 68
    0x84454503540700d80c141c1d50342c0035210604c0504c514a409000ca5400e02c5038034640f9540050140010a14041390b10041003082c004640d18211034881086080d180c1c403900e060420680e00030440c15000540001e00031080d401407081d0310b401d00780d0720b01030841c200d0411100450580d40d03a41c0140039011210a502c0c04219005004001c00d15201030112541200a142948102c02d405a01001898140101c4962603405081030140e400d2614100d07858040e0101180102c03818030080b18550306003002001c04481a1000812100c00a00001070324500003070900002c040d001c00c00400e211000050545c001c0046680000f4407030094000102210700208407001042186028401d4000d191a00c41e504208801040c03160011045c4406000340070b0440040c3c09405801c4200608142031b009061190009440b00c10640301d280013044840c0030a440c9450344007800f4002352010a2400000d1548100b04200f20387c50500300324001122040c5010000c00020004084400f020303009010b403800902c1195 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 643128111 1250 643126861 643126867
    0x30a11190305040b07170703030207020a050907090b070609050a0c180b0105190207081e0c0306040302030f03090c0310052401020d05070302011410030308180a0b04210302030106030e03 81
    0xd81c008005101e41d1049400203080414483e091041d0040710741c062044190000380e5914461030003401940111105034410360b44580700146904080030094850f500750354a15150314102102d03e184d035008204207441030355a48244400086080104d00e80c0700e4024503402e0303005c0c0c2c0342405000805241d4a02c0e00c2030b09040101c61a040e9801c001540d100c4680070381c08051144000c02e080b4a4502c0682c4002050301c51a400010955034078074042c048001d500080e24a152090400d0599030b1a0588004006901c10001ca07445c0c000b10303001842e00000d0150569412405c0300c0006880d180c01c0304d00038002c1e90343e60000d10104400e0b02024098000c80e141002d1840050000040e4a0748410b00d400c2040c0f0600042503c00c2520039805260611803118001016080405001c0c01425a07408210301041e000004650a08100c404049034060440014108072415a85240703076194007074821251502507207003101e9600e5461580c41d90b81000daa03801603d943c5010001005d8640401c0d041095400c20 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 643129361 1250 643128111 643128113
    0xa0902010801050105072406080f1501090e0f010c02010506120d020a0813050901030503071205040f180f0203040f12210506030c060c0a110f0f090612030a1119 70
    0x301d2414111002400c043d6160801410454003140c00c0d44100e8190a03c04403c014240200740d0120301605c01100844031004a046020b40d600e45811103000d1001560381c0041200d0f400a40000e50b4190f0300d10284c4081ca00d20012031030039502c0401075600540d440e07204205081c1005607280462903058002019181c14201d00a5103c01c10804003400946000030111183d01d40c00361820000e140207400e008230707503035a41405034490b0010141200c040c80d210304c40f071907142d100303109a40a8504c0d417500d414040b494548640d26840e61800141441a220b040001803001c40f440598460350180c0c192141964507845c1c06082d000c4030100d40d00911500d0300e8411b840c40602896925004094603001400d511507100291800c030601c0074807940845c0010741c0c101200b03004100000001d1080500c0e00101c0c451300100b09980700e90007020b54004804614454a0307141c0f2840c50343d0000006010300c001c2158841d003c9085038810b80c89440801d846a41d90808144100000314140460161540c405820303 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 643130611 1250 643129361 643129367
    0x151608040615080a0308100b040b04150e270610023a0f02010e030708090405061311120c0f040302091806010303110c030705090a0f18060209090a090201 67
    0x40c00140049540e9001070005400301c000440150a200c001c58a68116074500204400411283c150400364122000249642100103890903650468a60b40c02c2c0340c1860b501c05030303034007104c6031000401409261441b20790b21400b0714281c2400000d81c821000791446201c14000d054054203203030244020700803171194288e02103051400340911440c41c184503070701c00002380c8103e403001e054109940b00c0c160f81d4803002504402240f002e512103400a1008204402000e5203c0c043c4100c05031a0a03000c100e80c1c4d0480c90158496a440381c00102105807210181040307a00b1111000740e081024100091109601c48510b25001d074001002c1e43d010b032914150f030814210038062840f00070b010750000710100e01c1c00c006118800b01c90022510442d40f40e51703560f050040030351034802c40714038142c00b50903600034072400c0c04500038003a1030000d40156256110185284000c4c8100c40f031558910b6900c4003d0091080411440c00340c50380035040c017513141c1c0d003664100102d503a005000704080b640741248000041c7d030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 643131861 1250 643130611 643130627
    0x16240f0206071b0602122d070c1e03050c1506060910091205010b1806032e060311010311120a0506120118031b030516030306171516 58
    0x9400c3c50030052800c0300d03110000c0c41c804140c1004100900100700050704a54040d00c05109600f142c103e4885e081881c00e100c2480482c0681c0704000c05141c1c00040c400c2c6004444d194800c40c8200228004c040301040742c00d40865000c001240010b0b030003d440815220204158100a15007940e511024203010300000e220341710303a01d0101e01030310411003e107013018001d03034441008080c25040e80030705e01400d01d0f10500030607201280500c1362848200c0843c1c3c40200d070340303d9481030b2009401800c1e042c00c10545071444104943c202c034800100b400c04039032640c41e18000c00005505c103244805007500c4010000d0166034131103d800e070110f4020312040308500c03001b0608640041100c1c80004541c1c0b60342e40890b50070400c00d080b5482e00d40c203000460744101204010180550300940e20f50055800c5604c2c011810595603401400141c0140107102051a5000201d00081d220f8180000d0896540036500c25400b100b00f99100e450300010300c0d00240d9101201c04690149040d0202003403c4c55013400070785501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 643133111 1250 643131861 643131871
    0x30e24131d10080f071403030f0f130e060f120111040308030f07020a1e0317040f0605071b020103110702040e0d03050703140c0a03110309010221060108061216240f0206 74
    0x6c0181c00201e4030b070341b0b003441180c502d240e000d1072a9a03948038425520445074880d21045440340c00402c0c00160300950b005441e8080c040081c40d002580c504542003100300c00500043d0011075599000b20440c1c40c85620081000b144104002c0b6284d01d410884030b40008c20042c031000941d000b40980c44001001c00303141a031034020743c0c01d140203105a1400d0440700100b85038000c82400c0a80400d01c02403141d09640e01c44080d01c5004140155941c0f0501181d0181007580100c0040200c00f14240040d03020760030500308280d034200010b0030482c40ba000a01610901601c1218a4018040103560681e050141c3e950000080c1001e1001c1c0d0a8100c0c6481c440200810100b903105003c80c10248051098004040005071030700e0464403818120507444c001d501220b602882d40905d440014220103206009078442e82058689603080d9a41d2000d0100c0c05804e41c0500075a8080c1c1d00d0010034201841c8003403805403400c459211484643c1802c2d90303404010a14107401400040310100d00760b258002940c950103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 643134361 1250 643133111 643133129
    0x1008060105011202120a090501150f050d03020309150703080702060c0d0f0e100b0a0504050915130f060b090609090d030b0402070519030e24131d10080f07 68
    0x1000d81a03190f00e00034040c64840c480c1200e441070038881c815080750000050107004400800c800380c0c0308e000c0310303e1011040c815041c05000c46a4100a646002011902528068010749142403012070009d01c403620596000e4445c4c1c0c80200301c00e001c0c1740e400b00582d507003c1d8260009140c01d0911b02540036070707801482c5411000c4c0d5240c0101c0d41030f44005801a54054080c40103c0d502e01070f006072580080c011b8207a9850061b105c003480050549040e00910740200f420b00040c1041f1440011403a50415001301500b901040c42544540015030092030800d03014000c4030001a003104010401080b004060416445100c07908140025840c02048044c890b98650400181c002c071703c8408a006030140d030401134814021280603103a03403030108600143d010304c00d948200d00030815804220b106210303503000980c1080009580c0740040386c03a100400381005d20044220036190b813158103280304110680c0d9503042001081c00d01600d403500c1e002035030151000c607020307280310501c0c0900940d6820541c4102511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 643135611 1250 643134361 643134377
    0x450070519090305031201080c150708032208030604110a17191a04050108030708071707060c0507020f031b270c071205120f1b04080114100806010501 66
    0x70780180300b2000199880015030382c48029007840140825024815034a040c0500080d81c0641e180482c84900d80322003404042d4182100b90f240c903041500001c01c07060941c4000c100255003003500107100301e00c0510503400141d80746050700600059504111700408120000c0c041c2181050b002003000c4103900e11160b90303960300d540d1030350781307191441d0181d200c000903e1604016000c111410f1a00944502c02a00c05103c217980c0c4010469513440354080c05020404144040f60000f050f0401072840c0407a20440c00c2e0902d80f15440d944100d40b080340c0e41d0303004078000144140843c1032201550105c02000c8000e4040c005012490300c2030a81d1419045105801c241110b02c0718003c1d00142040c6a909461090903170301c0c0ca44010100b0750b10800050f01c1034603007140c0c0a420203202d0011940c0ca211218071814094540203260200120040e040010000710510610303404200800a0002020050000310b0b00e03400024811074001c00281050a50000c1d4000903c02003000040792030440318280fa08142c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 643136861 1250 643135611 643135657
    0x231060314132004020a020d0e09010807060f050c03120603160323010f020c0a0b0a05090c01140d05070306090b03060108060c070c03060507050403151a04500705 71
    0x544504a03800f00d43d0207480401d0041010780d001820a00080c100e80b110304240c0705580c2003114484003440707a401c050307001e03010601125105129140035180c8908065040102c0341c9441811034000e609029060840c0e50200701d513070f150401112050030b40c2c82685805890450b00c400c5e80103c4810050081d000d101014010350403025882030080b4401c510003103485001d111071041c3c4030a0055410741d5105030100c0402c07180006407203a1800b542c1014020840b07104d4bc88010b4915011940e070781001c010081c440b039180c00806024031403241e007032035030001002c03410208108100c44101480034001e510100c01442101d1000030404d0b002044520b155881c0c54071361500b24404d05c010740004040c207003802c051020341c9800001900650b44105a80a040305001e10031303804842c000c50845007801000a09160030341815805081803125281e0361864001c025411402e00c800103c08541c0d4510541100c152403004180d540100c004d0106401d482d1400c00e0f18004090f0301611907404401416000002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 643138111 1250 643136861 643136903
    0x5060307050a09050402010e010816180510031d24060f030f0c130b0d020904080c01060b04050a170d030f0204050a03051c0201150603023106031413 65
    0x745001481103240584070a54000500380c2a5000c07804925002040c00003580541ca400340b0a1030700c14031420b845840444111505050b000308541c5800c40c0400c00b184a0319022031400c0080e40c0c0c2c0e180424070f88150569000680b0003880340741226082100c02101600340c294014510418141c0d0580c5591510760002d620a40510b496aa2501c80d80050580307207000071944507140b1508031510351300314000d00e15101c01d032024031207250f501c0704030303810007900614042d0030b095003143c060042c132801c21429a03402401c450540e08001014000490308000500e004403c0d08040e08035814001d8800c0961281c00b6620040c60810034249034595066121440301a4191001483c00a00d500b680d10303031320300700581c94040380c500ba081e0000034170810340700701d0b03005000d03050444a852810200c801e04e4910110003d40040b9040b42c1d41d100c0c0001011042c40c0e80400311040210f10810f095822032920801404895005003407003000002c072020080000b464a200e41c481c26003010f03545070000244042d01d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 643139361 1250 643138111 643138123
    0x606010f091e1707060e090f010512010f15030506060d03081303050c15180a030e0621090d080f0708010b0f12010e0907170d050a020a14030304060b0402071203050603 73
    0x1022261900031025480c841c3c0000e80001140d0158642945600d003000610a9644048038950102c41e24100104034605207900d0300d440007207003800005080c50581001509941c0181088000003124440500901a00307102d1142c000c0b0301110200041c0e803041d6009002c0b140c005142682e40c100c524114024940160108c0c2c4000b032140c01a90000e140160a5100380310054806003d400900e1034404001900028076107015034041c0c8520181922201c20064150300c03202140d0b80395400388104014201840d440b041c010f401400280c501e6201048008081180052071071100714074050600c44415000b684040c159090061165990319089810100b248102d1b103064450100c42000020720505907007107580030700c518206960380d0380c0c1c0e07460358066100380c122b110b6070303590b000001c61080a074021070082c00b40f10701c1c41c015686070316150f1b102c40e500c0000d001031000054100100300001c0045034407440c800584125021400c15015031501e0b648050800141000c2c15520004142c0d255010010 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 643140611 1250 643139361 643139369
    0x60402010f1803081c0b01021213050a030501062c0c0f071e110609060405060c01060b04120309150c030c1401090501060302030c01050405060f0310030b07080601020606010f091e 78
    0x1a02e500d541e0380b41950369030348909420f1a003e00103000030f0803414110b018029840d02d0507401054420700d610310126841e031007041200707981d10300c0e0f9200103499200d400d803580086004600001d61700f40340c44651011103603a180c02c00341000d1000c10f02002d2248041207503420105a41172103442e07d02c0b06a8102d160321648402034403002c886080500c10030160320380d01e88028410000c0c003002c0750301740c01444003078055654142d40c0075005000c01e000c03c0c2015400303042c11810078800802c000d40d58011a011940c840c5c0c0007040310080c901015000d050700809e0034001040ca21012900d01c10070b032800200080f01e04d6000400308241c4400520170701510111504109504900801c000041031030001e0082016101c00c034064040c5090b05041c0d980200252400c5440c050401c900d07000301d030b43e00f040344c5c0c1d4002880e0303030800c85c282000403001c0364903002140d100b0906071310303240c0b0030741040000039140138802880e031030400811070180810b07243d10400d0384e011070308002409a00b2003c100c10180c20f486141d00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 643141861 1250 643140611 643140647
    0x1b080d0606050f032d1f08010c232b0e07030807110f09090723010918060e040b04020301050a061a070c0b0a0c0c0e250c140607020f0f060402010f 64
    0x3091148581b007811254228824000d099508a5524407529090b1000644083d0100c1c41201c0681c012042d6070301c00710400000f9062480c58114a0318048180441240f00403107070800203410802c600d03aa030302c0f032a417105c06504000d080640ca1903480300035500c18400000c0030702d010102003c05d00c1d1280980300e1181d010040681100e850568a80d560310040c0f80308007100131003e9020310b038003000745203246022504180c1d02c2a0740f1909129221140380d100741c480350300300b60355400d0020b0b160a42a071000d00803840f61f18038200074103245c010582510005800d112900345448410059411520320110452011003801038580d20103080ca00343c48525640151181d81001806507116540f2030540104581f0469030503030f0752500c0e006201c00c4243c080b11004102c074030003e900b216860248101c140815058508051052401e5403040ea8004204004a007282d000320180180c0f203805101c0070040c905194000d05220000921441d95803001410180c10300040f40f514503a264031410f02c56245081c514 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 643143111 1250 643141861 643141951
    0x50d0819081915030311071d0123090118020d1802090f040c030609060b130b0a090b0607080309010b060f0c01050601090e0a0c1b080d0606050f03 64
    0xe0041c1030160215000d0700c07122914240c5200b001801d204010f8070120100c06200310034219941564611601c0851502521511000048940403038040007204c03280502540900e5260614150341e00d000c0103040c40907410001c0c521400c545681c0702141c112982d403403004034420a6566103030028400c000e02d03c1100d0b42003410003000c5003098002211024402d0f01c2d651030322354402e12080c84032a01540c000b0a400d01d05201040815032176004400540c0c010200081e0100b02c090001d000041e010721000021034865030222228506050124010060320b20113000301020a800034140b0310540b00700070200040070010401031082507121185001c00079181c1983e07080440005600c607088840b50944542c01c1400041c1e182d44501c40b0b002c01c4a4068103084e00a4540708102e50180c00c200071024108480740390620100c0e0b050000e2401d1300f6000f070809640d2001c9603194030040da9a01d42001081c454100400c0e000c441e03a0b54100c1340d20000024624500581110310110000d1000748044140c0c003240e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 643144361 1250 643143111 643143157
    0x1706090c27060d0915020304030c301806091203030906020903030301060801140303090f010e040b090c070302060c190f03061214060703090b1302011e030203061018050d08 75
    0x40d50221300444e000d608038161508050b685081030b4403040350010005168000705e44002443e5000601d80340801d640e1020b0201440a2003116030551610420005484040c016600303210040400018007503a2420000311411700314500800c8020750002420550703681c4c01c641c1440840c0e81640c0c81c100d00181500e80d0b95070341e5003005265503000e0142d81031030300c7c4502801d1510300d4004100d0350704500240c10000c100884400642c0e82c17801445526130850380300e85403c51070b030780c4501c45c1c188a205509602600d0701c407103080003894403600420600a1003810031030700c900a0003141c403803801020342d031412504e000d110314800c501400d4a03a00c48544400c07003a42d203808220380175a5480350005c4483c200c0306c80d65240756040f400d5a0f00504007a1401442d1400304c0c1c00c0541d80c812401100380107041c208001c4c10700c1d0442036862071500300c62800195000c0107000c160303d04010188802812850401780f0050108908115803245200c0c95100c0c084440c016400c00208100340d560840c005528080d500da12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 643145611 1250 643144361 643144387
    0x5160e2d220204060906020609060f04061d06180601053007080d0e0405040b221704060905030604051b0a1e050306130b0c1e04061706090c2706 63
    0x16000303d8001c03510051000c906d0742e00c00501140b14072404001891280c9a03091034a0450402910139a1080d4523254000004040c060005410002440040c882460708001d0b81a2180991850031540c0e084a401000310341c0e600f0304030400354418074400200400400c5881d2400c030407440091001070003031a10003d0710410110f2000380490003611740c54140c40c100c004000864074221401001413060401145031440400c28101c1180c1030008180e54002c410b44804800c003041107010701500d100041d0510946034803060a10040c1010f500034902800e080c1c2c1c0e0581c0307507004000e00300c1d0004800b4818000030303a00c4804600092400d0842c080d0001092280d0f04580907a81c010365000b4880c1e000420b14101145429414650b004001c00c807840d11070b141c2c00340d840d0b440760780c81d4003148000b800b45007405116080104020055600c60842d009980ca2000003e814000e000500c07c2010204004440c40000201c030b20881511015420040d404080c1d40308506684c880103070481004a4500c1103610 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 643146861 1250 643145611 643145617
    0x20309072418051021090f061d0a0305090406030b010915080f07030b10030206041e090b090f091c051b01020910050a1205160e2d2202 59
    0x1c0c1c02e40d40c1d80081804504082c0b0216254032955800000804035810928031039814500000900e20f550300f0104107640e000c00654268580aa520305465100001000381c10303c41e04c87c40180407103901100130301108100c0d4952044800103010700900041c8440035a81c2c1e90300c000d000e5603010300c190100d940c403078080c9030040c8001116a51007444101010500600000701080c0d001414002820307014119035500300c01d003030701810b80594911281c2010005035640340142025141281404036200000ca1007078051000c1c56000ca10b00c58942142c0c2a82900c03403140c0540d004840c403c002000303440340c0261600d040b20020b0014052800d503c040c0d016190700c803009000c40074202c0c500c05091200c041400d400c0380300d00d981c41c5510240000d290f501c4d450190020303040120322400c0400039200010320034415501e08481e800320f070103203500d08069580d4000600c4a85100c017501d513001d01d41040d1824490303007900744100291008590120b046650b5076480c0000c201400a6540f40a00d0700400c92040690 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 643148111 1250 643146861 643146929
    0xf02030d0c060506030c030706200a03020d140f071e1a160801050a1703310e0402090402120a140d02060603030304111c0206123702030907 61
    0x40c10031012803401d117400117101c40392640041c01750850502c2c100e41950038445940c99011000700b001c014800924080c000c845180d8020740151401c4003002100030b02240c0440940800c10070305100ca001d130380b0540c03c19103000e035920185482030f0185460702c0310a00d521420008046070182ca681d440200e040e030080354000c10141c0280050121014026901c0503424015260072046030002000304013801c0d050610116028002da074601038944000d035500c4507003070480d41c040500c0060620040d90203412910024014565501080e08242e400554400b4010700080e10992600c45c111a504030140a04051290301c0101255030b10803044109484100c10881c1e08054003a541c00a81d05050101c1241c0c41540d01098100341c01c0710b540c0070080143c80d0006240d480d001006803140050b150314006044640c01d406c506010351429180c10075000c08501c841110080c400d2425448205026040100101c00480c0140c2c0380da44200005e840c0c80c443e0ba00511602c450210850b8200c0c0b0100c201c86540 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 643149361 1250 643148111 643148123
    0x60e01051e2406030a1107030503070e010503150405091216020307060c08070605090c04050c09041d07030f02060c1f0509070311220510062304050d0f02030d0c 70
    0x541c0c9440901841c07003a507101215502d5800254241c00d80f07005401190720031580c40c0002410749501c544880160045041207021500000038003203d01d420541d40c0702160307001d01c3c00b1441d51501206090341110703c03030b40c21405280c542c0c0214808480c1170040b4501d02e1411001d054a6110300c504200c446400c528091303009005200c0080344a03441542030035034407a00100d5aa282140741d503035500040000074020203150051500000007035a5a000701401204100e04440d103a00519041108450144254502d10300101500030038005002c2009030072a5001004201c50789070500110704240304401145106000749483c2019400da030039004031107060035610400599a410b140340e544c80086020240c0413141d2041c0303d200c145024500c0051003d440b084100320020045411401e82d21309580141107240314142c00d01c45103600251444c101c054070080100148503551440c4c01d1842203020341400340c00c010312040f040c44059011054090303409003ca0349000010a0000e00030700c8441811244 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 643150611 1250 643149361 643149421
    0x306080f0c040b061608030c040504050a091a0907090f0b0a0b1c0b03060604020c0a0b09251809020a030515010e06090f0a050a060e161404080c0d060e0105 68
    0xc81d042804c00c1d107280c01688007525030081000d0f21226040c1c1c00082c104002d21504000100300e907259401000c0c0a125013140c081042d008030326103101e6101c40c8079285c2c002d1005c40b004120304500c0010b000c40894161140004503103864940c1800a000006600780d0007948112001500d00d9107140103003078010385620103040b040e041e00f01d0384050355404d07803e040c0d15034002e8010802c4d0b80343c998010b008440303400c4211070f041203441e9140514404201d684c40c5031508045416494281c548a00c03070580300307803182034888031420401c4034100340300141e04a40305140e0741c031080c43c1191900c154481c00b8603041403c0320b034540a01041c0821056090090f1640800360002241ca14100f4a15850194040d41843d66403941c031608940000c1074001c140c1100191260030003e818004040c00740d000c0c20810918001150701c0040240003413010900d1103d403890204020000d8100c00301d4241c4506100315840c100447c06402c040e4003a00848240003020351800c401d10980e100b091085081c4841405642c00b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 643151861 1250 643150611 643150631
    0x21203040617100e0a0603060f0b0102100c020a0b04140601080616050a02030d05060f041103091209180c0d14041109090a1103030f030f0703061401120c0306080f0c04 73
    0x1460380000c3d0340c1000d482d0301d86003090011a02102e01c0c1540700c022000005400d83d42ca8841c0800d40e000d07110443d246c150390765003076000c5581c1402040d0900178199800d00c0000a88076000b90703100111180070f41400000e1000c203040159400c08044116008402c4982c40d5031916102c1d6101e203016a58105000441122449030034050420344010b402250086e40c00c0c00e00c003440440180100502140d4015811a1400241d54039072050840e803254141300c80341c40c2d1a040c50071500c0c14480e030000c640c8501e403d0001040d2070359948541c0011507001c60107100e01341c8440c42d21480e5130090f0b400e01300141d810030951860f1640c0c07280f21548a14000d40e00e07180030170034032424495000400e90305c0c0b24054100300d50400100e000c4030001d41980d9006012240340500e40c0e90b0b82c8510390015a8100382400484007401582c503410300954010741100d07000801c2403614100080c204da400744590380b0606881d841c204a0f058001d900000081142c0010f4960544070244442d40b03841030b180c400ca114030f1070800094 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 643153111 1250 643151861 643151897
    0xf0a0314060a0608130804142106041707080316020c1801120c0302330a051206060702030a0c06031d250f12060b03030922090212030406 60
    0x39016020241c5201d200c2400c0000c11544400d0007005d07100d050380c06001000c0002d40140040c0010486050107206680423501040381100542d0b0714030f00507220750502140d1114000c24080d4010782d000f68070443c01c5482d0f45044a403809000b50244c0040808010031080e410a101c14914401c0582e0980e003c44551a080140700d43c000000000341c4422080148550300034003e401a03c00d0103102d03201c0c02580d9950010b002d0700c080f04080d02d0307147e4942d032400316100e29204114040d411068030203030805401450040c0903000307602480045801e82d40224400b41c464804039101a038000e419034115a400707082000108d000d600c1820000303031605008540020301c02880106406c160806031a500d1644240040380000e0b88030582400400c6400004041c81e000312103000820b14900160043c52039801c1c80e0302113844032542180260410400c8922682d6643e602c1018100f40000a10a60441c02d503840c00074200c105009400ca10125030480e000c80000000d0310440310150307600c2d040b094a80c000d00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 643154361 1250 643153111 643153151
    0x60f050a08030a0816050d09060c09061103030c03040c050405040302010518030a1403100e0a15090b030606010809071505220303120e031204060b040c03020a050403080d02040302060f0a03 82
    0xd0f80002c1c081501041c41c030400340340d030025401601d00e011070070807003541e0542d000c0300d541c0442119181d40e1120380c0e064140c1c000c940e0100902140c10240e11070140c041540c0c1e182d1000825080700703070b40c00000040030417030741034072903800703054050010001460140b401a000300020350b143c2604922412500580413000812149410110381e92030f00046101401e0320f1071600050000c0180715580d0310007080007502c4804a030300c21085400c012510740172203c00d00c022480f0981240240a00303140c0c0405c81a00c1c0000c409400000a10b0000c050303035203185400e4200200c903082074031180d03c801c10440340641e0080140c1300d034200c00d0a403003011185512558070383c00518840100412203005901c840e00c00030741d2041400000e04400d13a440c01214000d81805250121005c4401b5075a03040b0319403081c101803040703050310a81400e0442c030307064070303000068210302440c80020006140003880803401c240380d03019200116400340040c0e1300c0e048046010140350b04060328000001c1e2070070500b0a503191501c010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 643155611 1250 643154361 643154377
    0xe0607020114090a060f020c0a2105035b090e07060507030c050607170f0c190e060315130504030e0d1a01060207080c010221070213060f050a0803 64
    0xb4040c40f4040c0e030303c00300a86006040c4d217045030f50901c048042c032320b01888401c0310144103441c1e8082c0050200c8411500c0001c190000003006000e10401968130411510000c5000707029942410398100c11051107261000d070040209440c2442c0c00d0100c60341d1042d1001c9140e00780d05d840c241030050300c81c0c50b414101e0382c1c0e02048210ba58418441000020702410042410740d02070b00e00103000b200a5262103151810070746040c8005030b10b040001c1907049404103c1908404000020041c9040008803141e00340280c45c8840300a001610713040c076580c2c0c041d410220403648007801a5459280500305c041021411050300c83c0901c1040540c0c4a08407014452603104e658103468801d4080e84e24024041c0030840c030712081701d08482c01590031500000d242d241e54020b14140d0b000b0074001d03061400c0345040448482069040d0f50003203e080c850070701481d000076003010007000440d0f101d100c18000106d851091640820725145004c602084144442c52a079003030302d0f0265031410650f41d40d000704a9480c403c40396 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 643156861 1250 643155611 643155613
    0x150d210801230d0204050606070b25050c0d180806130512030c040311060405040509011d0a03080a0c05131206051e0414120c031917160903060e060702011409 69
    0x35080010f05c1c059018540182d805030401c0d09010300d943c0e4000002c1403d4544810004145c41c2c58540300213007035011491929980b410504100c06004000d80d6060911695402d10003c0a101da0301d0148012525000700700c035408232945030030074070b090504528140005858178040c14003803000050000080320b0050f90240c28180c80d040c41c1d501c44d00c0b80102d414101c50791100e82004005010380c0c3e54000c550160801c01c00000d0780c8501540008035a006090b847c0c001038200d2039004012035080248103034030110368407011038558001306003121503110300d8401c03000301c0f4079080d00400c03500030580003c10382c14421801000680c41e03a4650400c10312503006641900c89401d000a00002d203900f03102d02003503c841d800c039070600d600c00703120f080c06030405403030f41905038408240191000390003545400008114241048400c012035900012940003c0109141c1c400da24000e0304003910071200c0400a60700b014041091690340905079494aa058444000540c02c20840e142c91901d4009194001c0340600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 643158111 1250 643156861 643156879
    0x15091a010f0f0c02010e09010621052403010e070b07030f1403070e030c03072304090809091f03030302030103061a03030d0c03020f030408070506070305150d21080123 73
    0x10350110f41c0b0015000e0100e04001c121000a00d80e03803034480f0564081c10064481c1c150204107000a032200004040c002803401d81407209010003042030229482c01300c074810303000b60644a400000700307000d087e0080c00d4081a22803010001030861020000c1c0086901c44d940741c40d41001c0d000001c6801a0041c00290401c003420002715603414020502c050303112002a0540d4615603070b090010b400c112080e0301c4407800b040c910b804032009000b11441ca10b10110100c42c01c100c100c0c6281c43e0380030136000d43c0494501800d0780038080703074040b041c800700307403140540c60160403429035282d1400070040c1d0028402210b0f92411300c140040c0801c500480842d07140c1001e0000c43c14801c501044030003512008090b001855800c0200e511440c0b8980d00940c0300394020b9a415030b5a00052401902d040c070300500d2481010304d00781c2400800140d4403412100c140742240e0750050052181007080618062111201901038081c03030000c2081c1d00405020304a880003d00305074440c041c089803402c0014841c1030759500c00070341 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 643159361 1250 643158111 643158137
    0x1030c0b0a0c0c0f06020d03020403260705010c030209120606090c0f04090f09330c11100501030c0b0a17070c0c03080904270b06030115091a010f 64
    0x220103042107001c285404900e0305441d0300d4021210099800c1010066141d40080c0006a0100414100242c1c5880c04518181ca50384400c3c19842030b8801c004400c00052410303085070b903498400d0701c1c600ca4000000304121012080c007e80254403131240c00707010302904d9075480380819011031a1171040d80040d00320320b505d0381c80d18000911903201000c02d42415100f0701c008151070016205170301c01352807150300c0041d024005042924035044218140d104550201c2e1111543d1701e0108502481e0302c40c20710340424101ca498009491001d2405000c0303a85215010281c440d04c0300c1c0703801060407a80540002c0520541b80e68420401d4400c181290000c5814171981007000b4942c01c3c06161310000c00c1c83e00d25084042580c4441d1004015441a5401c100c0400c420702c41d0f150034881c5d6408140b07810361110302440f050369041742c402d2003a10301a004540d03200c0041c0d203685080d0444107400c01ca80030038110380d9840d03000c1c40009007240c0c400c0c400b007000d140c01c55400550203040b0710220919140c6130311404481d2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 643160611 1250 643159361 643159379
    0xc02030316030f0e160902031009020c03070230122d07030f02010e03090a1203090504050907080c060a02071502101505030d031b030c030905070807051801030c 70
    0x48030000700209990b031032048015942e0741c460038100083c00c002800c41480882008000ca08654201c60901403041040c88060f01d80d610701001190508400540c45641100c0198114056210040d41012f0080080c3c03140c4c06901070ba11101840c880320000d840b0600c03216083d40c0b400b83e0b078440c335002d01040000310461103c460820760303140350100001060669130f54203114039130007425049002c0340e810580c61003042d4081c000c070240d40681c84015800d108030302d40050185881071050380074020842a0002c02e041c4994040005000017400c02d200310304100d640c0355616816840f032040640a2070403140c80a142110886900720120303070080030400c1c1400c4004050480e912101d4003540b0842c012140b044255004d99154000c4944800751407074501000d06080407000d8800404240c40e0051100c0c5140600c0e01000844941e8a000a283c80403400181c0080545540141c1144038118000814413800114038003615000c1d1142c2208000c41110004400e03000c0c0402171102158039004c5c0f00141c1 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 643161861 1250 643160611 643160641
    0xb010f0e03010b040f0b03060f09060a0e1c0908101103040204051815010609270513050a0b060f1509150706050a1b0c1106030907210c090c020303 64
    0x800400015008000b0343c0000c0484221a0074001c2039a1100c10106581c82d007030201c43d5014042780900c202d10b01c0d100a80d0754032031400400c044210741c0d9400100e0020310003041541502c005062035000150540708028110030b10340d02c1000038078450352240005900003406131009040741c9903d05810340d1038a900f0030020305002414502c0c0003002105807904280100003142d2a5511440e61b03405079418070f0300082c000c201503009051040f540d6065660781c44001c55041d00084c039403903000111520381c135641200c1e03001c20400180c1740e885800ca904080c803542400b0306001d044102ca00405441510007405403041c1d1400414582c3e200c14402d64030541450103c1104440740141c48a2400312269642d008a034015107401c698141c0c0e60700d00b0f00e03100182c81900c1c600320f50241009082ca2556070340302654000d11850542c0100700100101d00307441420007414014012a5504611946c400b1043c011740e500e2810b41aa401c0c160070724002880d5404c0d2064414160302e0b580030f107103542d0703a1004041a444c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 643163111 1250 643161861 643161887
    0x5060f16020624180402040501050402040608130c0518010906050d05030703030f0b120d120e0322150f030f06150807091e06030509010b030606090901020712050712030b010f 76
    0x1e2031480c002001a41c1d007603011804c440300400c2500c0c443c1002e0051004440c0140c100500030b5204020504c0000d4104148070740c0071508486585840d041850b01000080c225800590400815403220310040068a1494144c4110360000c1250356955000c002045600100140c83c0f60410040c9101003442500a0b00031561030751070204e61503070703064003045500c800d500c07050740075401401400d00550b500076104007000801e00303014444100c0c0116825168811400c1011100c01c01040d140145c02c000140900180380380314141c07000c1c540000b40070748164009403070440003d01e00050798a06105621909051b42d2040740700521040b80702005075851030003d40008103001c0c4c0d030f480004000c102e0055082000c0844c01c09805150714280c400380c29070b4070150800342c03030303906105c0654100c1e200000d10079802282114020150348a9290090080c42107803405407507401011903c824440c1c001006200d0180f040302d44159528090000300c0880301302148890003d01c64690003900300b0310901d483e000c82 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 643164361 1250 643163111 643163161
    0x9020114030a1401030f05240610090504020c0102190c030c030e0301020d06080708070f1505160503070501091205030f0a2003090a020f060301060516110d05060f160206 74
    0x90020f5002c0c0700030300c000c01d901c1200c501007200034402c10030105000f6203c3c0d080311610020301003c0c804481c80d0000708024a080d0055804c4088103003e07520075402c0c036008280180086540d42058100c2d24042d50101d2000c0074605074982030468180c0c8160b19001c8a240c1641c2d070265038251560b011590103028641d640d60540d02445402800c491a204000040c4040c00003080c0d4a803508486038100103641d0f210103160807588104120700c41801007810076428035403403e96511104100c3c514400e84134001d0280c098440868084200700741584221203650003858070314074140003550b00700c4640c0720403a80040c0150412000c25481c1d4031030340000784500c2000c03007107420304000c0018581054204846444160b4800c26000707040d41000056451400c0066038054903660401601510300c2c4501c5c03000d41c5039185418226014042c00804125030307042c0040005640c120079082407075941101365842c41011440c840852882191382e5101c404500e01600580001e90380c4000280940412000704069 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 643165467 1106 643164361 643164371
    0x13021c0c12110d0206120108070e060f0d03030903020c03160906050619120605100c0308072303090a0c06050703030b1921080406030e1009020114030a 66
    0x440b9800d44840481000c503201080041c4100081000800d00a80000c510450089500310448143d50448000da84035070381000641458132070a03580c000308800300c03140040c1c080d0300548541c0d80039005449900d48030304013007418219416000b200e20411300303a007805000c98621405001c0c0c54103480a1b0b05101e56528a0385181c0300f900034203410300074141c03800e03400f440d10394021030080c02e0064045058554404000f8101101c5200c04902091200b40014030a52041c0f240c101340d08082501d041540c490507210190507480900556000d025081401b004075201e05181001032005584240d502c1c074180c14000c0071a464490703164851103480340c901c40e8210b104218074042e510f41c0f0000d0002d22450201d41c1d10055034100700102080c4010800240756034140c1e01003c1203800302000e503102d010324410440c003100c0342030f400280414205101030400c2c00c8000d02031503100c0c3d408100028 = true := by decide +kernel

theorem cover : BRFrame.Cov 642985611 643165467 := by
  have h0 := BRFrame.cov_init 642985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642985611 ≤ n) (h2 : n < 643165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
